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
  structuralFamilyBase,
  structuralFamilyProjection,
} from "./structural-merge-history.mjs";

const fail = () => {
  throw new Error("INVALID_PERMISSION_STRUCTURAL_COMPOSITION");
};
const eq = (a, b) => stable(a) === stable(b);
const exact = (o, keys) =>
  o && typeof o === "object" && !Array.isArray(o) && Object.keys(o).sort().join(",") === keys;
const metadata = (r) =>
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
const touches = (p) => p.entries.length || p.transitions.length || Object.keys(p.receipts).length;

function parentFacts(parent) {
  if (
    !/^[a-f0-9]{40}$/u.test(parent.revision) ||
    !parent.structuralProof?.continuation ||
    parent.fragments.some((f) => f.schemaVersion > 14) ||
    parent.fragments.filter((f) => f.schemaVersion === 13).length !== 1 ||
    parent.fragments.filter((f) => f.schemaVersion === 14).length !== 1 ||
    parent.files.size > 2000 ||
    [...parent.files.values()].reduce((n, text) => n + Buffer.byteLength(text), 0) >
      128 * 1024 * 1024
  )
    fail();
  const selection = validateStructuralSourceHeadContinuations(
    parent.fragments,
    parent.ledger,
    parent.structuralProof.origin,
  ).filter((r) => r.family === STRUCTURAL_MERGE_FAMILIES[0]);
  if (selection.length !== 1) fail();
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
    origin: parent.structuralProof.origin.anchor,
    sourceSelection: selection[0],
    // Entire selector histories, including the common origin and14 descriptor,
    // remain byte pinned by files and individually reference pinned here.
    selectorChain: parent.fragments
      .flatMap((f) => {
        const records =
          f.schemaVersion === 11
            ? f.sourceHeadSelections
            : f.schemaVersion === 12
              ? f.sourceHeadContinuations
              : f.schemaVersion === 13
                ? f.structuralMergeExtensions[0].families
                : f.schemaVersion === 14
                  ? f.structuralMergeContinuations[0].families
                  : [];
        return records
          .filter((r) => r.family === STRUCTURAL_MERGE_FAMILIES[0])
          .map((r) => ({
            fragment: digest(f),
            receipt: sourceHeadReceiptReference(f.schemaVersion, r),
          }));
      })
      .sort((a, b) => stable(a).localeCompare(stable(b))),
  };
}
function baseFacts(seed, parents, document) {
  if (
    !exact(document, "families,owner,parents,reason,ticket") ||
    !metadata(document) ||
    !Array.isArray(parents) ||
    parents.length !== 2 ||
    parents[0].revision === parents[1].revision ||
    !eq(
      document.parents,
      parents.map((p) => p.revision),
    ) ||
    !Array.isArray(document.families) ||
    document.families.length !== 2
  )
    fail();
  const facts = parents.map(parentFacts);
  const closures = parents.map((p) =>
    p.fragments
      .filter((f) => [13, 14].includes(f.schemaVersion))
      .map(digest)
      .sort(),
  );
  if (!eq(closures[0], closures[1]) || !eq(facts[0].origin, facts[1].origin)) fail();
  for (const [path, text] of parents[0].files)
    if (parents[1].files.has(path) && parents[1].files.get(path) !== text) fail();
  const families = document.families.map((r, i) => {
    if (!exact(r, "family,order") || r.family !== STRUCTURAL_MERGE_FAMILIES[i]) fail();
    const base = structuralFamilyBase(seed, parents, r.family, r.order);
    // Patient card has no selector; it must be the identical unchanged lineage.
    if (
      i &&
      !eq(
        parents[0].ledger.entries.filter((e) => sourceHeadFamily(e.id) === r.family),
        parents[1].ledger.entries.filter((e) => sourceHeadFamily(e.id) === r.family),
      )
    )
      fail();
    return { ...r, lineage: base.lineage, raw: base.raw, derived: base.derived };
  });
  return { facts, families, closures: closures[0] };
}

/** Pure facts only. Only the owning Git reader can authenticate these parents. */
export function constructStructuralComposition(seed, parents, document) {
  const base = baseFacts(seed, parents, document);
  return {
    schemaVersion: 15,
    entries: [],
    transitions: [],
    structuralMergeCompositions: [
      {
        reason: document.reason,
        owner: document.owner,
        ticket: document.ticket,
        parents: base.facts,
        structuralClosure: base.closures,
        families: base.families.map(({ derived, ...r }) => r),
      },
    ],
  };
}

export function validateStructuralComposition(seed, fragments, parents, files) {
  const compositions = fragments.filter((f) => f.schemaVersion === 15);
  if (compositions.length !== 1) fail();
  const f = compositions[0];
  if (
    !exact(f, "entries,schemaVersion,structuralMergeCompositions,transitions") ||
    !Array.isArray(f.entries) ||
    f.entries.length ||
    !Array.isArray(f.transitions) ||
    f.transitions.length ||
    !Array.isArray(f.structuralMergeCompositions) ||
    f.structuralMergeCompositions.length !== 1
  )
    fail();
  const r = f.structuralMergeCompositions[0];
  if (!exact(r, "families,owner,parents,reason,structuralClosure,ticket") || !metadata(r)) fail();
  const document = {
    parents: parents.map((p) => p.revision),
    families: r.families?.map(({ family, order }) => ({ family, order })),
    reason: r.reason,
    owner: r.owner,
    ticket: r.ticket,
  };
  if (!eq(f, constructStructuralComposition(seed, parents, document))) fail();
  for (const parent of parents)
    for (const [path, text] of parent.files) if (files.get(path) !== text) fail();
  const parentHashes = new Set(parents.flatMap((p) => p.fragments.map(digest)));
  // The old structural envelopes must be the complete exact shared closure.
  if (
    !eq(
      fragments
        .filter((x) => [13, 14].includes(x.schemaVersion))
        .map(digest)
        .sort(),
      r.structuralClosure,
    )
  )
    fail();
  const base = baseFacts(seed, parents, document);
  const plans = base.families.map((b, i) => {
    const extra = fragments
      .filter((x) => x !== f && !parentHashes.has(digest(x)))
      .map((fragment) => ({ fragment, p: structuralFamilyProjection(fragment, b.family) }))
      .filter(({ p }) => touches(p));
    if (extra.length > 128) fail();
    const tail = [],
      used = new Set();
    let terminal = b.order.at(-1);
    while (used.size < extra.length) {
      const next = extra.filter(
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
        tail.some((old) => old.id === e.id) ||
        !eq(x.p.transitions, [{ id: terminal, field: "replacedBy", target: e.id }])
      )
        fail();
      if (!i) {
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
      base: b.derived,
      derived: derive([...b.derived, ...tail]),
      descriptor: r.families[i],
    };
  });
  return {
    continuation: true,
    composition: true,
    plans,
    origin: {
      family: STRUCTURAL_MERGE_FAMILIES[0],
      schemaVersion: 15,
      selection: {
        family: STRUCTURAL_MERGE_FAMILIES[0],
        head: r.parents[0].sourceSelection.head,
        lineage: r.families[0].lineage,
        reason: r.reason,
        owner: r.owner,
        ticket: r.ticket,
      },
      anchor: { fragment: digest(f), receipt: sourceHeadReceiptReference(15, r.families[0]) },
      parentHashes,
    },
  };
}
