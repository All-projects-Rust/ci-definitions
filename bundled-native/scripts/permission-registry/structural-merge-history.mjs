import { createHash } from "node:crypto";
import { digest, stable } from "./ledger-format.mjs";
import { sourceHeadFamily } from "./source-head-selection.mjs";
import {
  validateSourceHeadContinuations,
  sourceHeadReceiptReference,
  sourceHeadClassificationDigest,
} from "./source-head-continuation.mjs";

export const STRUCTURAL_MERGE_FAMILIES = Object.freeze([
  "permission-source-sentinel:next:apps/web/app/app/crm/crm-board.tsx",
  "permission-source-sentinel:next:apps/web/app/app/crm-patient-card/crm-patient-card-page.tsx",
]);
const fields = [
  "reconciliations",
  "spliceReconciliations",
  "compositionReconciliations",
  "compositionExtensions",
  "compositionSupersessions",
  "sourceHeadSelections",
  "sourceHeadContinuations",
  "occurrenceReconciliations",
  "rootReconciliations",
  "linkedRootReconciliations",
  "completeOccurrenceReconciliations",
];
const fail = () => {
  throw new Error("INVALID_PERMISSION_STRUCTURAL_MERGE_EXTENSION");
};
const exact = (x, keys) =>
  x && typeof x === "object" && !Array.isArray(x) && Object.keys(x).sort().join(",") === keys;
const equal = (a, b) => stable(a) === stable(b);
const metadata = (r) =>
  [r.reason, r.owner, r.ticket].every(
    (x, i) => typeof x === "string" && x.trim().length >= [12, 2, 3][i],
  );
const byteHash = (text) => createHash("sha256").update(text).digest("hex");
const intrinsic = (e) => {
  const { replaces, replacedBy, ...rest } = e;
  return rest;
};
const mentions = (x, family) =>
  typeof x === "string"
    ? x === family || sourceHeadFamily(x) === family
    : Array.isArray(x)
      ? x.some((y) => mentions(y, family))
      : x && typeof x === "object"
        ? Object.values(x).some((y) => mentions(y, family))
        : false;
export function structuralFamilyProjection(f, family) {
  if (
    !Array.isArray(f?.entries) ||
    !Array.isArray(f.transitions) ||
    fields.some((key) => f[key] !== undefined && !Array.isArray(f[key]))
  )
    fail();
  const entries = f.entries.filter(
    (e) =>
      sourceHeadFamily(e.id) === family ||
      (e.kind === "permission-source-sentinel" && e.file === family.split(":next:")[1]),
  );
  if (entries.some((e) => sourceHeadFamily(e.id) !== family)) fail();
  const transitions = f.transitions.filter((e) => mentions(e, family));
  const receipts = Object.fromEntries(
    fields.flatMap((key) => {
      const records = (f[key] ?? []).filter((r) => mentions(r, family));
      return records.length ? [[key, records]] : [];
    }),
  );
  return { entries, transitions, receipts };
}
const projection = structuralFamilyProjection;
const touches = (p) => p.entries.length || p.transitions.length || Object.keys(p.receipts).length;
export function structuralFamilyOrder(entries, family) {
  const own = entries.filter((e) => sourceHeadFamily(e.id) === family);
  const byid = new Map(own.map((e) => [e.id, e]));
  const roots = own.filter((e) => !e.replaces);
  if (roots.length !== 1 || own.some((e) => e.retiredBy)) fail();
  const order = [],
    seen = new Set();
  let current = roots[0];
  while (current) {
    if (seen.has(current.id)) fail();
    seen.add(current.id);
    order.push(current.id);
    if (!current.replacedBy) break;
    const next = byid.get(current.replacedBy);
    if (!next || next.replaces !== current.id) fail();
    current = next;
  }
  if (seen.size !== own.length) fail();
  return order;
}
const parentOrder = structuralFamilyOrder;

/** Pure facts only: the owning reader authenticates the actual Git snapshots. */
export function structuralParentFacts(parent) {
  if (
    !/^[a-f0-9]{40}$/u.test(parent.revision) ||
    parent.fragments.some((f) => f.schemaVersion === 13) ||
    parent.files.size > 2000 ||
    [...parent.files.values()].reduce((n, x) => n + Buffer.byteLength(x), 0) > 128 * 1024 * 1024
  )
    fail();
  return {
    revision: parent.revision,
    files: [...parent.files]
      .sort(([a], [b]) => a.localeCompare(b))
      .map(([path, text]) => ({ path, sha256: byteHash(text) })),
    ledger: digest(parent.ledger),
    baseline: digest(parent.baseline),
  };
}
export function structuralFamilyBase(seed, parents, family, order) {
  const entries = new Map();
  for (const parent of parents)
    for (const entry of parent.ledger.entries) {
      if (sourceHeadFamily(entry.id) !== family) continue;
      if (entries.has(entry.id) && !equal(intrinsic(entries.get(entry.id)), intrinsic(entry)))
        fail();
      entries.set(entry.id, entry);
    }
  if (
    !Array.isArray(order) ||
    order.length !== entries.size ||
    new Set(order).size !== order.length ||
    order.some((id) => !entries.has(id))
  )
    fail();
  for (const parent of parents) {
    const positions = parentOrder(parent.ledger.entries, family).map((id) => order.indexOf(id));
    if (positions.some((p, i) => p < 0 || (i && p <= positions[i - 1]))) fail();
  }
  const fragments = new Map(parents.flatMap((p) => p.fragments.map((f) => [digest(f), f])));
  const raw = [...fragments]
    .sort(([a], [b]) => a.localeCompare(b))
    .flatMap(([hash, f]) => {
      const p = projection(f, family);
      if (!touches(p)) return [];
      for (const edge of p.transitions) {
        if (
          edge.field !== "replacedBy" ||
          !entries.has(edge.id) ||
          !entries.has(edge.target) ||
          order.indexOf(edge.id) >= order.indexOf(edge.target)
        )
          fail();
      }
      return [{ fragment: hash, ...p }];
    });
  const derived = order.map((id, i) => ({
    ...intrinsic(entries.get(id)),
    ...(i ? { replaces: order[i - 1] } : {}),
    ...(i < order.length - 1 ? { replacedBy: order[i + 1] } : {}),
  }));
  const lineage = derived.map((e) => ({ id: e.id, attestation: digest(e) }));
  return {
    derived,
    lineage,
    raw: digest({
      seed: seed.entries.filter((e) => sourceHeadFamily(e.id) === family),
      fragments: raw,
    }),
  };
}
function parentSelector(parents, family) {
  const found = parents.flatMap((parent) =>
    validateSourceHeadContinuations(parent.fragments, parent.ledger)
      .filter((r) => r.family === family)
      .map((selection) => ({ parent, selection })),
  );
  if (family !== STRUCTURAL_MERGE_FAMILIES[0]) {
    if (found.length) fail();
    return null;
  }
  if (found.length !== 1) fail();
  const { parent, selection } = found[0];
  const chain = parent.fragments
    .flatMap((f) =>
      (f.schemaVersion === 11
        ? f.sourceHeadSelections
        : f.schemaVersion === 12
          ? f.sourceHeadContinuations
          : []
      )
        .filter((r) => r.family === family)
        .map((r) => ({
          fragment: digest(f),
          receipt: sourceHeadReceiptReference(f.schemaVersion, r),
        })),
    )
    .sort((a, b) => a.fragment.localeCompare(b.fragment));
  return { parent: parent.revision, head: selection.head, chain };
}

export function constructStructuralMerge(seed, parents, document) {
  if (
    !exact(document, "families,owner,parents,reason,ticket") ||
    !metadata(document) ||
    !Array.isArray(parents) ||
    parents.length !== 2 ||
    parents[0].revision === parents[1].revision ||
    !equal(
      document.parents,
      parents.map((p) => p.revision),
    ) ||
    !Array.isArray(document.families) ||
    document.families.length !== 2
  )
    fail();
  const families = document.families.map((r, i) => {
    if (!exact(r, "family,order") || r.family !== STRUCTURAL_MERGE_FAMILIES[i]) fail();
    const base = structuralFamilyBase(seed, parents, r.family, r.order);
    return {
      ...r,
      lineage: base.lineage,
      raw: base.raw,
      previousSourceSelection: parentSelector(parents, r.family),
    };
  });
  return {
    schemaVersion: 13,
    entries: [],
    transitions: [],
    structuralMergeExtensions: [
      {
        reason: document.reason,
        owner: document.owner,
        ticket: document.ticket,
        parents: parents.map(structuralParentFacts),
        families,
      },
    ],
  };
}

/** Complete parent closure plus strict ordinary tails. Does not issue reader authority. */
export function validateStructuralMerge(seed, fragments, parents, currentFiles) {
  const extensions = fragments.filter((f) => f.schemaVersion === 13);
  if (extensions.length !== 1) fail();
  const extension = extensions[0];
  if (
    !exact(extension, "entries,schemaVersion,structuralMergeExtensions,transitions") ||
    !Array.isArray(extension.entries) ||
    !Array.isArray(extension.transitions) ||
    extension.entries.length ||
    extension.transitions.length ||
    !Array.isArray(extension.structuralMergeExtensions) ||
    extension.structuralMergeExtensions.length !== 1
  )
    fail();
  const receipt = extension.structuralMergeExtensions[0];
  if (
    !exact(receipt, "families,owner,parents,reason,ticket") ||
    !metadata(receipt) ||
    !Array.isArray(parents) ||
    parents.length !== 2 ||
    parents[0].revision === parents[1].revision ||
    !equal(receipt.parents, parents.map(structuralParentFacts)) ||
    !Array.isArray(receipt.families) ||
    receipt.families.length !== 2
  )
    fail();
  const parentHashes = new Set(parents.flatMap((p) => p.fragments.map(digest)));
  for (const p of parents)
    for (const [path, text] of p.files) if (currentFiles.get(path) !== text) fail();
  const plans = receipt.families.map((r, index) => {
    if (
      !exact(r, "family,lineage,order,previousSourceSelection,raw") ||
      r.family !== STRUCTURAL_MERGE_FAMILIES[index]
    )
      fail();
    const base = structuralFamilyBase(seed, parents, r.family, r.order);
    if (
      !equal(r.lineage, base.lineage) ||
      r.raw !== base.raw ||
      !equal(r.previousSourceSelection, parentSelector(parents, r.family))
    )
      fail();
    const extra = fragments
      .filter((f) => f !== extension && !parentHashes.has(digest(f)))
      .map((f) => ({ fragment: f, projection: projection(f, r.family) }))
      .filter((x) => touches(x.projection));
    if (extra.length > 128) fail();
    let terminal = r.order.at(-1);
    const tail = [],
      used = new Set();
    while (used.size < extra.length) {
      const candidates = extra.filter(
        (x) =>
          !used.has(x) &&
          x.projection.entries.length === 1 &&
          x.projection.entries[0].replaces === terminal,
      );
      if (candidates.length !== 1) fail();
      const x = candidates[0],
        p = x.projection,
        e = p.entries[0],
        f = x.fragment;
      if (
        ![1, 12].includes(f.schemaVersion) ||
        e.kind !== "permission-source-sentinel" ||
        e.disposition !== "EXEMPT" ||
        sourceHeadFamily(e.id) !== r.family ||
        e.replacedBy ||
        e.retiredBy ||
        r.order.includes(e.id) ||
        tail.some((t) => t.id === e.id) ||
        !equal(p.transitions, [{ id: terminal, field: "replacedBy", target: e.id }])
      )
        fail();
      if (index === 0) {
        if (
          f.schemaVersion !== 12 ||
          Object.keys(p.receipts).join(",") !== "sourceHeadContinuations" ||
          p.receipts.sourceHeadContinuations.length !== 1 ||
          p.receipts.sourceHeadContinuations[0].classification !== sourceHeadClassificationDigest(f)
        )
          fail();
      } else if (Object.keys(p.receipts).length) fail();
      used.add(x);
      tail.push(e);
      terminal = e.id;
    }
    const derived = [...base.derived, ...tail].map((e, i, all) => {
      const { replaces, replacedBy, ...unchanged } = e;
      return {
        ...unchanged,
        ...(i ? { replaces: all[i - 1].id } : {}),
        ...(i < all.length - 1 ? { replacedBy: all[i + 1].id } : {}),
      };
    });
    return { family: r.family, derived, base: base.derived, descriptor: r };
  });
  const board = plans[0];
  return {
    plans,
    origin: {
      family: board.family,
      selection: {
        family: board.family,
        head: board.descriptor.previousSourceSelection.head,
        lineage: board.descriptor.lineage,
        reason: receipt.reason,
        owner: receipt.owner,
        ticket: receipt.ticket,
      },
      anchor: {
        fragment: digest(extension),
        receipt: sourceHeadReceiptReference(13, board.descriptor),
      },
      parentHashes,
    },
  };
}
