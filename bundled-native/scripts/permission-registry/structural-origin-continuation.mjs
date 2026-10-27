import { createHash } from "node:crypto";
import { digest, stable } from "./ledger-format.mjs";
import { sourceHeadFamily } from "./source-head-selection.mjs";
import {
  sourceHeadReceiptReference,
  sourceHeadClassificationDigest,
  validateStructuralSourceHeadContinuations,
} from "./source-head-continuation.mjs";
import {
  STRUCTURAL_MERGE_FAMILIES,
  structuralFamilyProjection,
  structuralFamilyOrder,
} from "./structural-merge-history.mjs";

const fail = () => {
  throw new Error("INVALID_PERMISSION_STRUCTURAL_ORIGIN_CONTINUATION");
};
const eq = (a, b) => stable(a) === stable(b);
const exact = (x, keys) =>
  x && typeof x === "object" && !Array.isArray(x) && Object.keys(x).sort().join(",") === keys;
const meta = (r) =>
  [r.reason, r.owner, r.ticket].every(
    (x, i) => typeof x === "string" && x.trim().length >= [12, 2, 3][i],
  );
const intrinsic = (e) => {
  const { replaces, replacedBy, ...rest } = e;
  return rest;
};
const derive = (entries) =>
  entries.map((e, i) => ({
    ...intrinsic(e),
    ...(i ? { replaces: entries[i - 1].id } : {}),
    ...(i + 1 < entries.length ? { replacedBy: entries[i + 1].id } : {}),
  }));
const lineage = (entries) => entries.map((e) => ({ id: e.id, attestation: digest(e) }));
const touches = (p) => p.entries.length || p.transitions.length || Object.keys(p.receipts).length;
function facts(parent, previous) {
  if (
    !/^[a-f0-9]{40}$/u.test(parent.revision) ||
    parent.files.size > 2000 ||
    [...parent.files.values()].reduce((n, text) => n + Buffer.byteLength(text), 0) >
      128 * 1024 * 1024 ||
    parent.fragments.some((f) => f.schemaVersion === 14) ||
    (previous
      ? parent.fragments.filter((f) => f.schemaVersion === 13).length !== 1
      : parent.fragments.some((f) => f.schemaVersion === 13))
  )
    fail();
  return {
    revision: parent.revision,
    files: [...parent.files]
      .sort(([a], [b]) => a.localeCompare(b))
      .map(([path, text]) => ({
        path,
        sha256: createHash("sha256").update(text).digest("hex"),
      })),
    ledger: digest(parent.ledger),
    baseline: digest(parent.baseline),
  };
}
function raw(seed, fragments, family) {
  return digest({
    seed: seed.entries.filter((e) => sourceHeadFamily(e.id) === family),
    fragments: fragments
      .map((f) => ({ fragment: digest(f), ...structuralFamilyProjection(f, family) }))
      .filter(touches)
      .sort((a, b) => a.fragment.localeCompare(b.fragment)),
  });
}
function baseFacts(seed, previous, incoming) {
  facts(previous, true);
  facts(incoming, false);
  if (previous.revision === incoming.revision || !previous.structuralProof?.origin) fail();
  // Recheck the complete previous source chain on its untouched full ledger.
  const selections = validateStructuralSourceHeadContinuations(
    previous.fragments,
    previous.ledger,
    previous.structuralProof.origin,
  );
  const selected = selections.filter((r) => r.family === STRUCTURAL_MERGE_FAMILIES[0]);
  if (selected.length !== 1) fail();
  const previousHashes = new Set(previous.fragments.map(digest));
  const union = [
    ...new Map([...previous.fragments, ...incoming.fragments].map((f) => [digest(f), f])).values(),
  ];
  const families = STRUCTURAL_MERGE_FAMILIES.map((family, index) => {
    const order = structuralFamilyOrder(previous.ledger.entries, family);
    const byid = new Map(previous.ledger.entries.map((e) => [e.id, e]));
    const old = order.map((id) => byid.get(id));
    const extras = incoming.fragments
      .filter((f) => !previousHashes.has(digest(f)))
      .map((f) => ({ fragment: f, p: structuralFamilyProjection(f, family) }))
      .filter(({ p }) => touches(p));
    let added = [];
    if (!index) {
      if (extras.length !== 1 || extras[0].fragment.schemaVersion !== 1) fail();
      const { p } = extras[0];
      if (p.entries.length !== 1 || Object.keys(p.receipts).length) fail();
      const e = p.entries[0],
        terminal = old.at(-1),
        predecessor = old.at(-2);
      if (
        !terminal ||
        !predecessor ||
        selected[0].head !== terminal.id ||
        !exact(
          e,
          "disposition,file,handler,handlerFile,id,kind,owner,reason,replaces,tags,ticket",
        ) ||
        e.file !== family.split(":next:")[1] ||
        e.handlerFile !== e.file ||
        e.handler !== "next" ||
        !eq(e.tags, terminal.tags) ||
        e.kind !== "permission-source-sentinel" ||
        e.disposition !== "EXEMPT" ||
        sourceHeadFamily(e.id) !== family ||
        byid.has(e.id) ||
        e.replacedBy ||
        e.retiredBy ||
        e.replaces !== predecessor.id ||
        !meta(e) ||
        !eq(p.transitions, [{ id: predecessor.id, field: "replacedBy", target: e.id }])
      )
        fail();
      // The existing terminal must be an actual paired classification sibling,
      // not merely a node whose effective predecessor happened to be rewritten.
      const paired = previous.fragments
        .filter((f) => f.schemaVersion === 12)
        .filter((f) => f.entries.some((x) => x.id === terminal.id));
      if (
        paired.length !== 1 ||
        paired[0].entries.filter((x) => x.id === terminal.id).length !== 1 ||
        paired[0].entries.find((x) => x.id === terminal.id).replaces !== predecessor.id ||
        !eq(structuralFamilyProjection(paired[0], family).transitions, [
          { id: predecessor.id, field: "replacedBy", target: terminal.id },
        ])
      )
        fail();
      added = [e];
    } else if (extras.length) fail();
    // Every incoming historical occurrence is already present and identical in
    // previous, apart from the exact new sibling proven above.
    for (const e of incoming.ledger.entries.filter((e) => sourceHeadFamily(e.id) === family)) {
      if (added.some((a) => a.id === e.id)) continue;
      if (!byid.has(e.id) || !eq(intrinsic(byid.get(e.id)), intrinsic(e))) fail();
    }
    const derived = derive([...old, ...added]);
    return {
      family,
      order: derived.map((e) => e.id),
      lineage: lineage(derived),
      previousLineage: lineage(old),
      raw: raw(seed, union, family),
      derived,
    };
  });
  const chain = previous.fragments
    .flatMap((f) => {
      const records =
        f.schemaVersion === 11
          ? f.sourceHeadSelections
          : f.schemaVersion === 12
            ? f.sourceHeadContinuations
            : [];
      return records
        .filter((r) => r.family === STRUCTURAL_MERGE_FAMILIES[0])
        .map((r) => ({
          fragment: digest(f),
          receipt: sourceHeadReceiptReference(f.schemaVersion, r),
        }));
    })
    .sort((a, b) => stable(a).localeCompare(stable(b)));
  return {
    families,
    union,
    previousHashes,
    previousSourceSelection: { selection: selected[0], chain },
    origin: previous.structuralProof.origin.anchor,
  };
}

/** Pure candidate facts; no return value from this module issues authority. */
export function constructStructuralOriginContinuation(seed, previous, incoming, document) {
  if (
    !exact(document, "families,incoming,owner,previous,reason,ticket") ||
    !meta(document) ||
    document.previous !== previous.revision ||
    document.incoming !== incoming.revision
  )
    fail();
  const base = baseFacts(seed, previous, incoming);
  if (
    !eq(
      document.families,
      base.families.map(({ family, order }) => ({ family, order })),
    )
  )
    fail();
  return {
    schemaVersion: 14,
    entries: [],
    transitions: [],
    structuralMergeContinuations: [
      {
        reason: document.reason,
        owner: document.owner,
        ticket: document.ticket,
        previous: facts(previous, true),
        incoming: facts(incoming, false),
        origin: base.origin,
        previousSourceSelection: base.previousSourceSelection,
        families: base.families.map(({ derived, ...descriptor }) => descriptor),
      },
    ],
  };
}

/** Called only with privately authenticated snapshots by the owning reader. */
export function validateStructuralOriginContinuation(seed, fragments, previous, incoming, files) {
  const original = previous.fragments.filter((f) => f.schemaVersion === 13);
  const current = fragments.filter((f) => f.schemaVersion === 13);
  // A14 continues the single independently authenticated origin. Projection
  // cannot hide empty, malformed or competing13 envelopes from the full union.
  if (original.length !== 1 || current.length !== 1 || digest(current[0]) !== digest(original[0]))
    fail();
  const fs = fragments.filter((f) => f.schemaVersion === 14);
  if (fs.length !== 1) fail();
  const f = fs[0];
  if (
    !exact(f, "entries,schemaVersion,structuralMergeContinuations,transitions") ||
    !Array.isArray(f.entries) ||
    f.entries.length ||
    !Array.isArray(f.transitions) ||
    f.transitions.length ||
    !Array.isArray(f.structuralMergeContinuations) ||
    f.structuralMergeContinuations.length !== 1
  )
    fail();
  const r = f.structuralMergeContinuations[0];
  if (
    !exact(r, "families,incoming,origin,owner,previous,previousSourceSelection,reason,ticket") ||
    !meta(r)
  )
    fail();
  const expected = constructStructuralOriginContinuation(seed, previous, incoming, {
    previous: previous.revision,
    incoming: incoming.revision,
    families: r.families?.map(({ family, order }) => ({ family, order })),
    reason: r.reason,
    owner: r.owner,
    ticket: r.ticket,
  });
  if (!eq(expected, f)) fail();
  for (const p of [previous, incoming])
    for (const [path, text] of p.files) {
      if (files.get(path) !== text) fail();
    }
  const base = baseFacts(seed, previous, incoming),
    hashes = new Set(base.union.map(digest));
  const plans = base.families.map((b, index) => {
    const extras = fragments
      .filter((x) => x !== f && !hashes.has(digest(x)))
      .map((fragment) => ({ fragment, p: structuralFamilyProjection(fragment, b.family) }))
      .filter(({ p }) => touches(p));
    if (extras.length > 128) fail();
    let terminal = b.order.at(-1);
    const tail = [],
      used = new Set();
    while (used.size < extras.length) {
      const next = extras.filter(
        (x) => !used.has(x) && x.p.entries.length === 1 && x.p.entries[0].replaces === terminal,
      );
      if (next.length !== 1) fail();
      const x = next[0],
        e = x.p.entries[0];
      if (
        ![1, 12].includes(x.fragment.schemaVersion) ||
        e.kind !== "permission-source-sentinel" ||
        e.disposition !== "EXEMPT" ||
        sourceHeadFamily(e.id) !== b.family ||
        e.replacedBy ||
        e.retiredBy ||
        b.order.includes(e.id) ||
        tail.some((t) => t.id === e.id) ||
        !eq(x.p.transitions, [{ id: terminal, field: "replacedBy", target: e.id }])
      )
        fail();
      if (!index) {
        if (
          x.fragment.schemaVersion !== 12 ||
          Object.keys(x.p.receipts).join(",") !== "sourceHeadContinuations" ||
          x.p.receipts.sourceHeadContinuations.length !== 1 ||
          x.p.receipts.sourceHeadContinuations[0].classification !==
            sourceHeadClassificationDigest(x.fragment)
        )
          fail();
      } else if (Object.keys(x.p.receipts).length) fail();
      used.add(x);
      tail.push(e);
      terminal = e.id;
    }
    return {
      family: b.family,
      derived: derive([...b.derived, ...tail]),
      base: b.derived,
      descriptor: r.families[index],
    };
  });
  return {
    continuation: true,
    plans,
    origin: {
      family: STRUCTURAL_MERGE_FAMILIES[0],
      selection: {
        family: STRUCTURAL_MERGE_FAMILIES[0],
        head: r.previousSourceSelection.selection.head,
        lineage: r.families[0].lineage,
        reason: r.reason,
        owner: r.owner,
        ticket: r.ticket,
      },
      anchor: { fragment: digest(f), receipt: sourceHeadReceiptReference(14, r.families[0]) },
      // Unchanged validator checks every whole12 envelope/digest and skips only
      // BOARD claims in exact fully prevalidated previous fragments. Other claims
      // remain in the same whole classification context; no fragment is rehashed.
      parentHashes: base.previousHashes,
    },
  };
}
