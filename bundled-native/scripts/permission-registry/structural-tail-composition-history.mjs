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
  structuralFamilyOrder,
  structuralFamilyProjection,
} from "./structural-merge-history.mjs";
import { structuralFamilyTailPlans } from "./structural-catchup-history.mjs";
const fail = () => {
  throw new Error("INVALID_PERMISSION_STRUCTURAL_TAIL_COMPOSITION");
};
const eq = (a, b) => stable(a) === stable(b);
const exact = (o, keys) =>
  o && typeof o === "object" && !Array.isArray(o) && Object.keys(o).sort().join(",") === keys;
const bytesHash = (s) => createHash("sha256").update(s).digest("hex");
const gitBlob = (s) =>
  createHash("sha1")
    .update(`blob ${Buffer.byteLength(s)}\0`)
    .update(s)
    .digest("hex");
const touches = (p) => p.entries.length || p.transitions.length || Object.keys(p.receipts).length;
const metadata = (r) =>
  [r.reason, r.owner, r.ticket].every(
    (v, i) => typeof v === "string" && v.trim().length >= [12, 2, 3][i],
  );
const [BOARD, CARD] = STRUCTURAL_MERGE_FAMILIES;
function parentFacts(parent) {
  // Pure facts only; the owning reader separately authenticates these complete
  // committed snapshots under its private, bounded schema16-parent role.
  if (
    !/^[a-f0-9]{40}$/u.test(parent.revision) ||
    !parent.structuralProof?.catchup ||
    parent.structuralProof.origin?.schemaVersion !== 16 ||
    parent.fragments.some((f) => f.schemaVersion > 16) ||
    parent.fragments.filter((f) => f.schemaVersion === 16).length !== 1 ||
    parent.files.size > 2000 ||
    [...parent.files.values()].reduce((n, s) => n + Buffer.byteLength(s), 0) > 128 * 1024 * 1024 ||
    !Array.isArray(parent.inventory) ||
    parent.inventory.length !== parent.files.size
  )
    fail();
  const seen = new Set();
  for (const row of parent.inventory) {
    if (
      !exact(row, "blob,mode,path") ||
      !["100644", "100755"].includes(row.mode) ||
      seen.has(row.path) ||
      !parent.files.has(row.path) ||
      gitBlob(parent.files.get(row.path)) !== row.blob
    )
      fail();
    seen.add(row.path);
  }
  const selection = validateStructuralSourceHeadContinuations(
    parent.fragments,
    parent.ledger,
    parent.structuralProof.origin,
  ).filter((r) => r.family === BOARD);
  if (selection.length !== 1) fail();
  const selectorChain = parent.fragments
    .flatMap((f) => {
      const records =
        f.schemaVersion === 11
          ? f.sourceHeadSelections
          : f.schemaVersion === 12
            ? f.sourceHeadContinuations
            : [];
      return records
        .filter((r) => r.family === BOARD)
        .map((r) => ({
          fragment: digest(f),
          receipt: sourceHeadReceiptReference(f.schemaVersion, r),
        }));
    })
    .sort((a, b) => stable(a).localeCompare(stable(b)));
  return {
    revision: parent.revision,
    files: [...parent.files]
      .sort(([a], [b]) => a.localeCompare(b))
      .map(([path, s]) => ({
        path,
        sha256: bytesHash(s),
        ...parent.inventory.find((r) => r.path === path),
      })),
    ledger: digest(parent.ledger),
    baseline: digest(parent.baseline),
    origin: parent.structuralProof.origin.anchor,
    sourceSelection: selection[0],
    selectorChain,
  };
}
function baseFacts(seed, parents, document) {
  if (
    !exact(document, "families,merge,owner,parents,reason,ticket") ||
    !metadata(document) ||
    !/^[a-f0-9]{40}$/u.test(document.merge) ||
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
      .filter((f) => [13, 14, 15, 16].includes(f.schemaVersion))
      .map(digest)
      .sort(),
  );
  if (
    !eq(closures[0], closures[1]) ||
    !eq(facts[0].origin, facts[1].origin) ||
    facts[0].baseline !== facts[1].baseline
  )
    fail();
  // Only the two distinct immediate Board siblings after an identical complete
  // schema16-descendant prefix are admitted. Attestations on the shared terminal
  // legitimately differ; intrinsic metadata and forward edges are checked below.
  const orders = parents.map((p) => structuralFamilyOrder(p.ledger.entries, BOARD));
  if (
    orders[0].length < 3 ||
    orders[0].length !== orders[1].length ||
    !eq(orders[0].slice(0, -1), orders[1].slice(0, -1)) ||
    orders[0].at(-1) === orders[1].at(-1)
  )
    fail();
  const parentHashes = new Set(parents.flatMap((p) => p.fragments.map(digest)));
  const tails = parents.map((parent, i) => {
    const other = new Set(parents[1 - i].fragments.map(digest));
    const own = parent.fragments
      .filter((f) => !other.has(digest(f)))
      .map((f) => ({ f, p: structuralFamilyProjection(f, BOARD) }))
      .filter(({ p }) => touches(p));
    if (own.length !== 1) fail();
    const { f, p } = own[0];
    if (
      f.schemaVersion !== 12 ||
      p.entries.length !== 1 ||
      p.entries[0].id !== orders[i].at(-1) ||
      p.entries[0].replaces !== orders[i].at(-2) ||
      !eq(p.transitions, [
        { id: orders[i].at(-2), field: "replacedBy", target: orders[i].at(-1) },
      ]) ||
      Object.keys(p.receipts).join(",") !== "sourceHeadContinuations" ||
      p.receipts.sourceHeadContinuations.length !== 1 ||
      p.receipts.sourceHeadContinuations[0].classification !== sourceHeadClassificationDigest(f)
    )
      fail();
    return p.receipts.sourceHeadContinuations[0];
  });
  if (!eq(tails[0].previous, tails[1].previous)) fail();
  // Card receives NO structural reconciliation. One authenticated parent may
  // already carry an ordinary linear Card suffix in the mixed schema12 payload.
  // Preserve that parent's complete existing chain verbatim; forks/new orders
  // are refused rather than selected by this Board capability.
  const cardOrders = parents.map((p) => structuralFamilyOrder(p.ledger.entries, CARD));
  const cardIndex = cardOrders[0].length >= cardOrders[1].length ? 0 : 1;
  const cardOrder = cardOrders[cardIndex];
  if (
    cardOrders.some((order) => order.some((id, i) => cardOrder[i] !== id)) ||
    !eq(document.families[1]?.order, cardOrder)
  )
    fail();
  for (const [path, bytes] of parents[0].files)
    if (
      parents[1].files.has(path) &&
      (parents[1].files.get(path) !== bytes ||
        parents[0].inventory.find((r) => r.path === path).mode !==
          parents[1].inventory.find((r) => r.path === path).mode)
    )
      fail();
  const families = document.families.map((r, i) => {
    if (!exact(r, "family,order") || r.family !== STRUCTURAL_MERGE_FAMILIES[i]) fail();
    const base = structuralFamilyBase(seed, parents, r.family, r.order);
    if (i === 1) {
      const byId = new Map(parents[cardIndex].ledger.entries.map((e) => [e.id, e]));
      if (
        !eq(
          base.derived,
          cardOrder.map((id) => byId.get(id)),
        )
      )
        fail();
    }
    return { ...r, ...base };
  });
  return { facts, families, closure: closures[0], parentHashes };
}
export function constructStructuralTailComposition(seed, parents, document) {
  const b = baseFacts(seed, parents, document);
  return {
    schemaVersion: 17,
    entries: [],
    transitions: [],
    structuralTailCompositions: [
      {
        merge: document.merge,
        reason: document.reason,
        owner: document.owner,
        ticket: document.ticket,
        parents: b.facts,
        structuralClosure: b.closure,
        families: b.families.map(({ derived, ...r }) => r),
      },
    ],
  };
}
export function validateStructuralTailComposition(seed, fragments, parents, files, modes) {
  const matches = fragments.filter((f) => f.schemaVersion === 17);
  if (matches.length !== 1) fail();
  const f = matches[0];
  if (
    !exact(f, "entries,schemaVersion,structuralTailCompositions,transitions") ||
    !Array.isArray(f.entries) ||
    f.entries.length ||
    !Array.isArray(f.transitions) ||
    f.transitions.length ||
    !Array.isArray(f.structuralTailCompositions) ||
    f.structuralTailCompositions.length !== 1
  )
    fail();
  const r = f.structuralTailCompositions[0];
  if (!exact(r, "families,merge,owner,parents,reason,structuralClosure,ticket") || !metadata(r))
    fail();
  const document = {
    merge: r.merge,
    parents: parents.map((p) => p.revision),
    reason: r.reason,
    owner: r.owner,
    ticket: r.ticket,
    families: r.families?.map(({ family, order }) => ({ family, order })),
  };
  if (!eq(f, constructStructuralTailComposition(seed, parents, document))) fail();
  for (const parent of parents)
    for (const row of parent.inventory)
      if (files.get(row.path) !== parent.files.get(row.path) || modes.get(row.path) !== row.mode)
        fail();
  if (
    !eq(
      fragments
        .filter((x) => [13, 14, 15, 16].includes(x.schemaVersion))
        .map(digest)
        .sort(),
      r.structuralClosure,
    )
  )
    fail();
  const b = baseFacts(seed, parents, document);
  const plans = structuralFamilyTailPlans(
    b.families.map((x, i) => ({ ...x, descriptor: r.families[i] })),
    fragments,
    f,
    b.parentHashes,
  );
  return {
    continuation: true,
    tailComposition: true,
    plans,
    origin: {
      family: BOARD,
      schemaVersion: 17,
      selection: {
        family: BOARD,
        head: r.families[0].order.at(-2),
        lineage: r.families[0].lineage,
        reason: r.reason,
        owner: r.owner,
        ticket: r.ticket,
      },
      anchor: { fragment: digest(f), receipt: sourceHeadReceiptReference(17, r.families[0]) },
      parentHashes: b.parentHashes,
    },
  };
}
