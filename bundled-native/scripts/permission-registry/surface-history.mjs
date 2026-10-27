import { readSourceInputs } from "../access-census/inventory.mjs";
import {
  discoverPermissionSurfaces,
  verifySurfaceLedger,
  verifySurfaceBindingProofs,
} from "./surface-gate.mjs";
import {
  validateSourceHeadContinuations,
  validateStructuralSourceHeadContinuations,
} from "./source-head-continuation.mjs";
import { constructStructuralMerge, validateStructuralMerge } from "./structural-merge-history.mjs";
import {
  constructStructuralOriginContinuation,
  validateStructuralOriginContinuation,
} from "./structural-origin-continuation.mjs";
import {
  constructStructuralComposition,
  validateStructuralComposition,
} from "./structural-composition-history.mjs";
import {
  constructStructuralCatchup,
  validateStructuralCatchup,
} from "./structural-catchup-history.mjs";
import {
  constructStructuralTailComposition,
  validateStructuralTailComposition,
} from "./structural-tail-composition-history.mjs";
import { sourceHeadFamily } from "./source-head-selection.mjs";
import {
  prepareCompleteOccurrences,
  projectOccurrenceSubset,
  hasPlainRegistryContainers,
} from "./complete-occurrence-history.mjs";
import { createHash } from "node:crypto";
import { prepareLinkedRootHistory, applyLinkedRootHistory } from "./linked-root-history.mjs";
import { reconcileRootFamilies } from "./root-family-history.mjs";
import { execFileSync } from "node:child_process";
import { openInstalledHistoryReader } from "./history-revision-io.mjs";
import {
  existsSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  writeFileSync,
  lstatSync,
  realpathSync,
} from "node:fs";
import { resolve } from "node:path";
import {
  buildLedgerFromEntries,
  buildLegacyBaselineAnchor,
  digest,
  stable,
} from "./ledger-format.mjs";

export const SURFACE_HISTORY_PATH = "scripts/permission-registry/surface-history";
export const LEGACY_LEDGER_PATH = "scripts/permission-registry/permission-surface-ledger.json";
export const LEGACY_BASELINE_PATH = "scripts/permission-registry/permission-surface-baseline.json";
const SEED_LEDGER = `${SURFACE_HISTORY_PATH}/seed-ledger.json`;
const SEED_BASELINE = `${SURFACE_HISTORY_PATH}/seed-baseline.json`;
const FRAGMENTS = `${SURFACE_HISTORY_PATH}/fragments`;
const GIT_OPTIONS = { encoding: "utf8", timeout: 15_000, maxBuffer: 256 * 1024 * 1024 };
const canonicalDigest = digest;

function sourceFamily(id) {
  return /^permission-source-sentinel:[^:]+:.+#sha256:[a-f0-9]{64}$/u.test(id)
    ? id.slice(0, id.lastIndexOf("#sha256:"))
    : null;
}

function hasReviewedReceiptMetadata(receipt) {
  return (
    [receipt.reason, receipt.owner, receipt.ticket].every(
      (value) => typeof value === "string" && value.trim(),
    ) &&
    receipt.reason.trim().length >= 12 &&
    receipt.owner.trim().length >= 2 &&
    receipt.ticket.trim().length >= 3
  );
}

const COMPOSITION_ERROR = "INVALID_PERMISSION_SURFACE_COMPOSITION_RECONCILIATION";
const compositionFailure = () => {
  throw new Error(COMPOSITION_ERROR);
};
const receiptReference = (schemaVersion, receipt) => digest({ schemaVersion, receipt });
const exactSet = (left, right) =>
  Array.isArray(left) &&
  Array.isArray(right) &&
  left.length === right.length &&
  new Set(left).size === left.length &&
  new Set(right).size === right.length &&
  left.every((id) => right.includes(id));

/** Validate a receipt against its original raw branch, before any virtual joins. */
function validateReferencedReceipt(
  record,
  entries,
  groups,
  compositionRecords = [],
  pinnedThird = false,
) {
  const { schemaVersion, receipt: r } = record;
  const keys =
    schemaVersion === 2
      ? `${pinnedThird ? "continuationOf," : ""}owner,predecessor,reason,successors,ticket`
      : "branches,mainline,owner,predecessor,reason,ticket";
  if (!r || Object.keys(r).sort().join(",") !== keys || !hasReviewedReceiptMetadata(r))
    compositionFailure();
  const sequence =
    schemaVersion === 2
      ? r.successors
      : Array.isArray(r.mainline) && Array.isArray(r.branches)
        ? [...r.mainline, ...r.branches]
        : null;
  const heads =
    schemaVersion === 2
      ? r.successors
      : Array.isArray(r.mainline) && Array.isArray(r.branches)
        ? [r.mainline[0], ...r.branches]
        : null;
  const family = sourceFamily(r.predecessor);
  if (
    !family ||
    !Array.isArray(sequence) ||
    sequence.length < 2 ||
    new Set(sequence).size !== sequence.length ||
    sequence.includes(r.predecessor) ||
    sequence.some((id) => !entries.has(id) || sourceFamily(id) !== family) ||
    !Array.isArray(heads) ||
    heads.length < 2 ||
    new Set(heads).size !== heads.length ||
    heads.some(
      (id) =>
        entries.get(id)?.replaces !== r.predecessor ||
        !groups
          .get(r.predecessor)
          ?.some((edge) => edge.field === "replacedBy" && edge.target === id),
    )
  )
    compositionFailure();
  if (schemaVersion === 2) {
    // A historic v2 head may acquire an ordinary published tail. A v4 must
    // explicitly pin a separately reviewed v3 containing that complete path;
    // the v3 validation and composition's raw-edge checks still run below.
    // Standalone v2 receipts continue to reject a non-terminal earlier head.
    if (
      sequence
        .slice(0, -1)
        .some(
          (id) =>
            groups.has(id) &&
            compositionRecords.filter(
              (candidate) =>
                candidate.schemaVersion === 3 &&
                candidate.receipt?.predecessor === r.predecessor &&
                candidate.receipt?.mainline?.[0] === id,
            ).length !== 1,
        )
    )
      compositionFailure();
  } else {
    if (
      r.mainline.length < 2 ||
      !r.branches.length ||
      r.mainline.some((id, index) => {
        if (entries.get(id)?.replaces !== (index ? r.mainline[index - 1] : r.predecessor))
          return true;
        const edges = groups.get(id);
        return index === r.mainline.length - 1
          ? Boolean(edges)
          : edges?.length !== 1 ||
              edges[0].field !== "replacedBy" ||
              edges[0].target !== r.mainline[index + 1];
      }) ||
      r.branches.slice(0, -1).some((id) => groups.has(id))
    )
      compositionFailure();
  }
  return sequence;
}

/** A composition attests the complete union explicitly; never infer an order. */
function validateComposition(r, catalog, entries, groups, claimed) {
  if (
    !r ||
    Object.keys(r).sort().join(",") !==
      "lineage,owner,predecessor,reason,receipts,successors,ticket" ||
    !hasReviewedReceiptMetadata(r) ||
    !sourceFamily(r.predecessor) ||
    !Array.isArray(r.receipts) ||
    r.receipts.length < 2 ||
    r.receipts.some((ref) => typeof ref !== "string" || !/^[a-f0-9]{64}$/u.test(ref)) ||
    new Set(r.receipts).size !== r.receipts.length ||
    !Array.isArray(r.lineage) ||
    r.lineage.length < 2 ||
    new Set(r.lineage).size !== r.lineage.length ||
    r.lineage.includes(r.predecessor) ||
    r.lineage.some((id) => !entries.has(id) || sourceFamily(id) !== sourceFamily(r.predecessor)) ||
    !entries.has(r.predecessor) ||
    entries.get(r.predecessor).replacedBy ||
    entries.get(r.predecessor).retiredBy
  )
    compositionFailure();
  const records = catalog.filter((record) => record.receipt?.predecessor === r.predecessor);
  if (
    !exactSet(
      r.receipts,
      records.map((record) => record.reference),
    )
  )
    compositionFailure();
  const direct = groups.get(r.predecessor);
  if (
    !direct ||
    direct.some((edge) => edge.field !== "replacedBy") ||
    !exactSet(
      r.successors,
      direct.map((edge) => edge.target),
    ) ||
    stable(r.successors) !== stable(r.lineage.filter((id) => r.successors.includes(id)))
  )
    compositionFailure();
  const sequences = records.map((record) =>
    validateReferencedReceipt(record, entries, groups, records),
  );
  for (const sequence of sequences) {
    const positions = sequence.map((id) => r.lineage.indexOf(id));
    if (
      positions.some(
        (position, index) => position < 0 || (index && position <= positions[index - 1]),
      )
    )
      compositionFailure();
  }
  // Ordinary edges retain adjacency. Only receipt-derived joins are subsequences.
  // At most one ordinary future tail may extend the last attested lineage node.
  const reachable = new Set([r.predecessor]);
  for (const head of r.successors) {
    let id = head;
    let inFutureTail = false;
    while (true) {
      if (
        reachable.has(id) ||
        !entries.has(id) ||
        sourceFamily(id) !== sourceFamily(r.predecessor) ||
        entries.get(id).replacedBy ||
        entries.get(id).retiredBy
      )
        compositionFailure();
      reachable.add(id);
      const index = r.lineage.indexOf(id);
      if ((index < 0 && !inFutureTail) || (index >= 0 && inFutureTail)) compositionFailure();
      if (id === head && entries.get(id).replaces !== r.predecessor) compositionFailure();
      const edges = groups.get(id);
      if (!edges) break;
      if (
        edges.length !== 1 ||
        edges[0].field !== "replacedBy" ||
        entries.get(edges[0].target)?.replaces !== id
      )
        compositionFailure();
      const next = edges[0].target;
      if (index >= 0 && index < r.lineage.length - 1 && next !== r.lineage[index + 1])
        compositionFailure();
      if (index === r.lineage.length - 1) inFutureTail = true;
      id = next;
    }
  }
  if (
    r.lineage.some((id) => !reachable.has(id)) ||
    [...reachable].some((id) => claimed.has(id)) ||
    catalog.some(
      (record) =>
        record.receipt?.predecessor !== r.predecessor && reachable.has(record.receipt?.predecessor),
    )
  )
    compositionFailure();
  for (const id of reachable) claimed.add(id);
}

// Bounded v5: append one independently published raw branch to a sealed v4.
// Validate the original v4 against the exact raw graph before that branch existed.
function validateCompositionExtension(r, compositions, catalog, entries, groups, claimed) {
  if (
    !r ||
    Object.keys(r).sort().join(",") !==
      "branch,composition,lineage,mainline,owner,predecessor,reason,ticket" ||
    !hasReviewedReceiptMetadata(r) ||
    !/^[a-f0-9]{64}$/u.test(r.composition ?? "") ||
    !Array.isArray(r.branch) ||
    r.branch.length < 2 ||
    new Set(r.branch).size !== r.branch.length
  )
    compositionFailure();
  const matches = compositions.filter((c) => receiptReference(4, c) === r.composition);
  if (matches.length !== 1) compositionFailure();
  const base = matches[0];
  if (
    !Array.isArray(r.mainline) ||
    r.mainline.length < base.lineage.length ||
    stable(r.mainline.slice(0, base.lineage.length)) !== stable(base.lineage) ||
    r.predecessor !== base.predecessor ||
    !r.mainline.includes(r.branch[0]) ||
    stable(r.lineage) !== stable([...r.mainline, ...r.branch.slice(1)]) ||
    new Set(r.lineage).size !== r.lineage.length ||
    r.branch
      .slice(1)
      .some(
        (id) =>
          !entries.has(id) ||
          sourceFamily(id) !== sourceFamily(base.predecessor) ||
          entries.get(id).replacedBy ||
          entries.get(id).retiredBy,
      )
  )
    compositionFailure();
  const snapshot = new Map(groups);
  const first = groups.get(r.branch[0]);
  const removed = first?.filter((e) => e.field === "replacedBy" && e.target === r.branch[1]);
  if (removed?.length !== 1 || entries.get(r.branch[1]).replaces !== r.branch[0])
    compositionFailure();
  const remaining = first.filter((e) => !removed.includes(e));
  if (remaining.length) snapshot.set(r.branch[0], remaining);
  else snapshot.delete(r.branch[0]);
  const baseClaimed = new Set();
  validateComposition(base, catalog, entries, snapshot, baseClaimed);
  // Every pre-existing node is sealed by the referenced v4, including its tail.
  if (!exactSet([...baseClaimed], [base.predecessor, ...r.mainline])) compositionFailure();
  for (let i = base.lineage.length; i < r.mainline.length; i++) {
    const edges = snapshot.get(r.mainline[i - 1]);
    if (edges?.length !== 1 || edges[0].field !== "replacedBy" || edges[0].target !== r.mainline[i])
      compositionFailure();
  }
  for (let i = 1; i < r.branch.length; i++) {
    const id = r.branch[i];
    if (entries.get(id).replaces !== r.branch[i - 1]) compositionFailure();
    const edges = groups.get(id);
    if (
      i < r.branch.length - 1 &&
      (edges?.length !== 1 ||
        edges[0].field !== "replacedBy" ||
        edges[0].target !== r.branch[i + 1])
    )
      compositionFailure();
  }
  const owned = new Set([r.predecessor, ...r.lineage]);
  let tail = r.lineage.at(-1);
  while (groups.has(tail)) {
    const edges = groups.get(tail);
    const next = edges[0]?.target;
    if (
      edges.length !== 1 ||
      edges[0].field !== "replacedBy" ||
      owned.has(next) ||
      !entries.has(next) ||
      sourceFamily(next) !== sourceFamily(r.predecessor) ||
      entries.get(next).replaces !== tail ||
      entries.get(next).replacedBy ||
      entries.get(next).retiredBy
    )
      compositionFailure();
    owned.add(next);
    tail = next;
  }
  if (
    [...owned].some((id) => claimed.has(id)) ||
    catalog.some(
      (record) =>
        record.receipt?.predecessor !== r.predecessor && owned.has(record.receipt?.predecessor),
    )
  )
    compositionFailure();
  for (const id of owned) claimed.add(id);
  return base;
}

// Evolution may project a new composition into a broken merged base only when
// that base contains every referenced immutable receipt and every declared node.
function canInheritComposition(r, catalog, entries, groups) {
  return (
    Array.isArray(r?.receipts) &&
    Array.isArray(r?.lineage) &&
    r.lineage.every((id) => entries.has(id)) &&
    exactSet(
      r.receipts,
      catalog
        .filter((record) => record.receipt?.predecessor === r.predecessor)
        .map((record) => record.reference),
    ) &&
    exactSet(
      r.successors,
      groups.get(r.predecessor)?.map((edge) => edge.target),
    )
  );
}

function fragmentReceipts(fragments) {
  return fragments.flatMap((fragment) => {
    const receipts =
      fragment.reconciliations ??
      fragment.spliceReconciliations ??
      fragment.compositionReconciliations ??
      fragment.compositionExtensions ??
      [];
    return receipts.map((receipt) => ({
      schemaVersion: fragment.schemaVersion,
      receipt,
      reference: receiptReference(fragment.schemaVersion, receipt),
    }));
  });
}

function supersessionRefsMatch(r, catalog, structural, entries, fragments) {
  return (
    exactSet(
      r?.receipts,
      catalog.filter((c) => c.receipt?.predecessor === r?.predecessor).map((c) => c.reference),
    ) &&
    exactSet(
      r?.supersedes,
      structural.filter((c) => c.receipt?.predecessor === r?.predecessor).map((c) => c.reference),
    ) &&
    Array.isArray(r?.lineage) &&
    r.lineage.every((id) => entries.has(id)) &&
    Array.isArray(r?.snapshots) &&
    r.snapshots.every(
      (snapshot) =>
        Array.isArray(snapshot?.fragments) &&
        snapshot.fragments.every((hash) => fragments.has(hash)),
    )
  );
}

const SNAPSHOT_FAMILIES = Symbol("private supersession snapshot ancestors");
const MAX_SNAPSHOT_DEPTH = 8;
const SEALED_SNAPSHOT_READER = Symbol("native complete committed supersession snapshot");
// A v6 never rehabilitates old receipts by deleting individual raw edges. Whole
// sealed snapshots validate independently. Occurrence-only v7 and disjoint v6
// siblings may be needed by other source families in those same immutable blobs.
function validateCompositionSupersession(
  r,
  catalog,
  structural,
  entries,
  groups,
  claimed,
  fragments,
  seedLedger,
  seedBaseline,
  ancestors,
  readSealedSnapshot,
  pinnedThirdReceipts,
) {
  if (
    !r ||
    Object.keys(r).sort().join(",") !==
      "lineage,owner,predecessor,reason,receipts,snapshots,successors,supersedes,ticket" ||
    !hasReviewedReceiptMetadata(r) ||
    !sourceFamily(r.predecessor) ||
    !r.receipts?.length ||
    !r.supersedes?.length ||
    !r.snapshots?.length ||
    !Array.isArray(r.lineage) ||
    r.lineage.length < 2 ||
    new Set(r.lineage).size !== r.lineage.length ||
    r.lineage.includes(r.predecessor) ||
    !entries.has(r.predecessor) ||
    !supersessionRefsMatch(r, catalog, structural, entries, fragments) ||
    ancestors.has(sourceFamily(r.predecessor)) ||
    ancestors.size >= MAX_SNAPSHOT_DEPTH
  )
    compositionFailure();
  const records = [...catalog, ...structural].filter(
    (c) => c.receipt?.predecessor === r.predecessor,
  );
  const expected = [...r.receipts, ...r.supersedes];
  const covered = new Set();
  const snapshots = new Set();
  for (const snapshot of r.snapshots) {
    if (
      !snapshot ||
      !["fragments", "fragments,revision"].includes(Object.keys(snapshot).sort().join(",")) ||
      !Array.isArray(snapshot.fragments) ||
      !snapshot.fragments.length ||
      new Set(snapshot.fragments).size !== snapshot.fragments.length
    )
      compositionFailure();
    const key = digest([...snapshot.fragments].sort());
    if (snapshots.has(key)) compositionFailure();
    snapshots.add(key);
    const selected = snapshot.fragments.map((hash) => fragments.get(hash));
    if (
      selected.some((f) => !f) ||
      (snapshot.revision === undefined &&
        selected.some((f) => ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12].includes(f.schemaVersion)))
    )
      compositionFailure();
    const refs = fragmentReceipts(selected)
      .filter((c) => c.receipt?.predecessor === r.predecessor)
      .map((c) => c.reference);
    if (!refs.length || refs.some((ref) => !expected.includes(ref))) compositionFailure();
    // No inherited decisions. Structural history needs its own native reader;
    // the current union's private structural plan cannot authenticate a subset.
    if (Object.hasOwn(snapshot, "revision")) {
      if (typeof readSealedSnapshot !== "function") compositionFailure();
      readSealedSnapshot(snapshot);
    } else {
      assembleSurfaceHistory(seedLedger, seedBaseline, selected, [], {
        [SNAPSHOT_FAMILIES]: new Set([...ancestors, sourceFamily(r.predecessor)]),
        [SEALED_SNAPSHOT_READER]: readSealedSnapshot,
        [VALIDATING_UNION]: true,
      });
    }
    refs.forEach((ref) => covered.add(ref));
  }
  if (!exactSet([...covered], expected)) compositionFailure();
  const sequence = [r.predecessor, ...r.lineage];
  const positions = new Map(sequence.map((id, index) => [id, index]));
  for (const { schemaVersion, receipt } of records) {
    const order =
      schemaVersion === 2
        ? receipt.successors
        : schemaVersion === 3
          ? [...receipt.mainline, ...receipt.branches]
          : receipt.lineage;
    if (
      order.some(
        (id, index) =>
          !positions.has(id) || (index && positions.get(id) <= positions.get(order[index - 1])),
      )
    )
      compositionFailure();
  }
  const heads = groups.get(r.predecessor);
  if (
    !heads ||
    !exactSet(
      r.successors,
      heads.map((e) => e.target),
    ) ||
    stable(r.successors) !== stable(r.lineage.filter((id) => r.successors.includes(id)))
  )
    compositionFailure();
  const reachable = new Set();
  const pending = [r.predecessor];
  const continuations = [];
  while (pending.length) {
    const id = pending.pop();
    if (
      reachable.has(id) ||
      !positions.has(id) ||
      !entries.has(id) ||
      sourceFamily(id) !== sourceFamily(r.predecessor) ||
      entries.get(id).replacedBy ||
      entries.get(id).retiredBy
    )
      compositionFailure();
    reachable.add(id);
    const outgoing = groups.get(id) ?? [];
    if (outgoing.length > 1 && (!sequence.includes(id) || id === sequence.at(-1))) {
      // Preserve the original v2 then v3. A third leaf order requires its own
      // exact typed binding to this validated v6 and both prior continuations;
      // it does not grant authority for an unbound third or any fourth fork.
      const candidates = [...catalog, ...structural].filter(
        (record) => record.receipt?.predecessor === id,
      );
      if (
        continuations.length >= 3 ||
        positions.get(id) !== positions.size - 1 ||
        candidates.length !== 1 ||
        candidates[0].schemaVersion !== (continuations.length === 1 ? 3 : 2)
      )
        compositionFailure();
      const candidate = candidates[0];
      const pinnedThird = continuations.length === 2;
      if (pinnedThird) {
        const binding = candidate.receipt.continuationOf;
        if (
          !binding ||
          Object.keys(binding).sort().join(",") !== "receipts,supersession" ||
          binding.supersession !== receiptReference(6, r) ||
          !Array.isArray(binding.receipts) ||
          stable(binding.receipts) !== stable(continuations.map((record) => record.reference))
        )
          compositionFailure();
      }
      const ordered = validateReferencedReceipt(candidate, entries, groups, [], pinnedThird);
      const directHeads =
        candidate.schemaVersion === 2
          ? ordered
          : [candidate.receipt.mainline[0], ...candidate.receipt.branches];
      if (
        !exactSet(
          directHeads,
          outgoing.map((edge) => edge.target),
        ) ||
        outgoing.some((edge) => edge.field !== "replacedBy") ||
        ordered.some((next) => positions.has(next))
      )
        compositionFailure();
      continuations.push(candidate);
      if (pinnedThird) pinnedThirdReceipts.add(candidate.receipt);
      for (const next of ordered) positions.set(next, positions.size);
    }
    for (const edge of outgoing) {
      // Preserve the normal publish -> classify workflow: only the final
      // attested node may acquire one ordinary linear tail. A new internal
      // branch/head/receipt still needs another explicitly reviewed mechanism.
      if (!positions.has(edge.target)) {
        if (positions.get(id) < sequence.length - 1 || groups.get(id).length !== 1)
          compositionFailure();
        positions.set(edge.target, positions.size);
      }
      if (
        edge.field !== "replacedBy" ||
        !positions.has(edge.target) ||
        positions.get(edge.target) <= positions.get(id) ||
        entries.get(edge.target)?.replaces !== id
      )
        compositionFailure();
      pending.push(edge.target);
    }
  }
  if (
    !exactSet([...reachable], [...positions.keys()]) ||
    [...reachable].some((id) => claimed.has(id)) ||
    [...catalog, ...structural].some(
      (c) =>
        !continuations.includes(c) &&
        c.receipt?.predecessor !== r.predecessor &&
        reachable.has(c.receipt?.predecessor),
    )
  )
    compositionFailure();
  for (const id of reachable) claimed.add(id);
}

function assertSealed(document, code) {
  const { contentHash, ...content } = document;
  if (contentHash !== digest(content)) throw new Error(code);
}

const OCCURRENCE_ERROR = "INVALID_PERMISSION_SURFACE_OCCURRENCE_RECONCILIATION";
const occurrenceFailure = () => {
  throw new Error(OCCURRENCE_ERROR);
};
// Only an already validated assembly can issue a baseline projection capability.
// JSON receipts remain durable provenance, but are not trusted inherited input.
const validatedOccurrenceEvidence = new WeakMap();
const validatedRootEvidence = new WeakMap();
const validatedLinkedRootEvidence = new WeakMap();
const validatedCompleteEvidence = new WeakMap();
const catchupCandidates = new WeakMap();
const tailCompositionCandidates = new WeakMap();
// Unexported role: only this reader may reconstruct two schema16 parents.
// Those reads cannot contain schema17 or issue current source capabilities.
const TAIL_PARENT_ROLE = Symbol("schema16-tail-parent");
const sourceHeadCapabilities = new WeakMap();
const sourceReaderCapabilities = new WeakMap();
const structuralReaderProofs = new WeakMap();
/** No serialized field or caller-provided evidence can mint this capability. */
export function getSourceHeadSelections(ledger) {
  const proof = sourceHeadCapabilities.get(ledger);
  if (!proof) return [];
  if (digest(ledger) !== proof.snapshot)
    throw new Error("INVALID_PERMISSION_SOURCE_HEAD_CAPABILITY");
  return structuredClone(proof.selections);
}
export function buildClassifiedSourceLedger(previous, entries) {
  const next = buildLedgerFromEntries(entries, previous.legacyBoundaryCommit);
  const selections = getSourceHeadSelections(previous);
  if (!selections.length) return next;
  for (const selection of selections) {
    const family = (l) => l.entries.filter((e) => sourceHeadFamily(e.id) === selection.family);
    if (digest(family(previous)) !== digest(family(next)))
      throw new Error("SOURCE_HEAD_SELECTION_FAMILY_CHANGED");
  }
  sourceHeadCapabilities.set(next, {
    ...sourceHeadCapabilities.get(previous),
    snapshot: digest(next),
    selections,
  });
  return next;
}

const unionOwners = new WeakMap();
const validatedUnions = new WeakMap();
const VALIDATING_UNION = Symbol("validate full union without issuing evidence");
const VALIDATION_RESULT = Symbol("internally prepared full union");
const READER_FILES = Symbol("actual reader byte snapshot");
const READER_ROOT = Symbol("actual owning reader root");
const STRUCTURAL_MERGE_PROOF = Symbol("actual independently validated Git parents");
const CANONICAL_COMPUTATIONS = Symbol("owning reader authenticated committed JSON inputs");
const evidenceFailure = (candidate) => {
  throw new Error(
    candidate?.rootEvidence
      ? "INVALID_PERMISSION_SURFACE_ROOT_RECONCILIATION"
      : candidate?.linkedRootEvidence
        ? "INVALID_PERMISSION_SURFACE_LINKED_ROOT_RECONCILIATION"
        : candidate?.completeOccurrenceEvidence || candidate?.unionEvidence
          ? "INVALID_PERMISSION_SURFACE_COMPLETE_OCCURRENCE_RECONCILIATION"
          : "INVALID_PERMISSION_SURFACE_OCCURRENCE_RECONCILIATION",
  );
};
const byteHash = (text) => createHash("sha256").update(text, "utf8").digest("hex");
function inheritedUnionProof(inherited, seed, baseline) {
  let scope, token, candidate;
  for (const item of inherited) {
    if (!hasPlainRegistryContainers(item)) evidenceFailure(item);
    const maps = item?.occurrenceEvidence
      ? validatedOccurrenceEvidence
      : item?.rootEvidence
        ? validatedRootEvidence
        : item?.linkedRootEvidence
          ? validatedLinkedRootEvidence
          : item?.completeOccurrenceEvidence
            ? validatedCompleteEvidence
            : null;
    if (!maps && !item?.unionEvidence) continue;
    if (maps && (!maps.has(item) || stable(item) !== stable(maps.get(item)))) evidenceFailure(item);
    const owner = item?.unionEvidence ? item : unionOwners.get(item),
      record = validatedUnions.get(owner);
    if (
      !record ||
      !hasPlainRegistryContainers(owner) ||
      record.tokenSnapshot.scope !== digest(record.snapshot) ||
      stable(owner) !== stable(record.tokenSnapshot) ||
      (record.readerFiles &&
        stable(
          [...Map.prototype.entries.call(record.readerFiles)].sort(([a], [b]) =>
            a.localeCompare(b),
          ),
        ) !== stable(record.snapshot.bytes))
    )
      evidenceFailure(
        item?.unionEvidence
          ? (inherited.find(
              (r) =>
                r?.occurrenceEvidence ||
                r?.rootEvidence ||
                r?.linkedRootEvidence ||
                r?.completeOccurrenceEvidence,
            ) ?? item)
          : item,
      );
    if (scope && scope !== record.tokenSnapshot.scope)
      evidenceFailure(
        item?.unionEvidence
          ? (inherited.find((r) => unionOwners.get(r) === item) ??
              inherited.find(
                (r) =>
                  r?.rootEvidence ||
                  r?.linkedRootEvidence ||
                  r?.occurrenceEvidence ||
                  r?.completeOccurrenceEvidence,
              ) ??
              item)
          : item,
      );
    scope = record.tokenSnapshot.scope;
    token = owner;
    if (maps || !candidate) candidate = item;
  }
  if (!token) return null;
  const record = validatedUnions.get(token),
    snapshot = record.snapshot;
  if (
    candidate?.occurrenceEvidence &&
    seed.entries.some((e) =>
      snapshot.fragments.some((f) => f.entries.some((raw) => raw.id === e.id)),
    )
  )
    throw new Error("DUPLICATE_SURFACE_LEDGER_ENTRY");
  if (stable(seed) !== stable(snapshot.seed) || stable(baseline) !== stable(snapshot.baseline))
    evidenceFailure(candidate);
  const revalidated = assembleSurfaceHistory(
    snapshot.seed,
    snapshot.baseline,
    snapshot.fragments,
    [],
    {
      [VALIDATING_UNION]: true,
      [STRUCTURAL_MERGE_PROOF]: record.structuralMerge,
      [SEALED_SNAPSHOT_READER]: record.readSealedSnapshot,
    },
  );
  return { snapshot, result: revalidated[VALIDATION_RESULT] };
}
// Comparison only: a validated receipt join may point to an absent peer, just
// like a schema8 root join. Ordinary raw tail edges are never inferred here.
function projectStructuralJoins(proof, fragments, entries) {
  const joins = proof.result.virtualJoins;
  const families = new Set(joins.map(({ id }) => sourceFamily(id)));
  const files = new Set(
    [...families].map((family) => /^permission-source-sentinel:[^:]+:(.+)$/u.exec(family)[1]),
  );
  const mentions = (value) =>
    typeof value === "string"
      ? families.has(sourceFamily(value)) || families.has(value)
      : Array.isArray(value)
        ? value.some(mentions)
        : value && typeof value === "object"
          ? Object.values(value).some(mentions)
          : false;
  const originals = new Set(proof.snapshot.fragments.map(digest));
  for (const fragment of fragments) {
    const touching =
      fragment.entries.some(
        (entry) =>
          families.has(sourceFamily(entry.id)) ||
          (entry.kind === "permission-source-sentinel" && files.has(entry.file)),
      ) ||
      fragment.transitions.some(
        (edge) => families.has(sourceFamily(edge.id)) || families.has(sourceFamily(edge.target)),
      ) ||
      [
        "reconciliations",
        "spliceReconciliations",
        "compositionReconciliations",
        "compositionExtensions",
        "compositionSupersessions",
        "occurrenceReconciliations",
        "rootReconciliations",
        "linkedRootReconciliations",
        "completeOccurrenceReconciliations",
      ].some((key) => mentions(fragment[key]));
    // Pin receipt-only fragments too: an independently reordered local receipt
    // cannot become a silent loser of a later canonical comparison projection.
    if (touching && !originals.has(digest(fragment))) compositionFailure();
  }
  const outgoing = new Map(),
    incoming = new Map();
  for (const { id, target } of joins) {
    if (
      (outgoing.has(id) && outgoing.get(id) !== target) ||
      (incoming.has(target) && incoming.get(target) !== id)
    )
      compositionFailure();
    outgoing.set(id, target);
    incoming.set(target, id);
  }
  for (const [id, target] of outgoing) if (entries.has(id)) entries.get(id).replacedBy = target;
  for (const [id, source] of incoming) if (entries.has(id)) entries.get(id).replaces = source;
}
const exactKeys = (value, keys) =>
  value &&
  typeof value === "object" &&
  !Array.isArray(value) &&
  Object.keys(value).sort().join(",") === keys;
const metadataFree = (entry) => {
  const { reason, owner, ticket, ...identity } = entry;
  return identity;
};
const occurrenceRef = (fragment, attestation) => ({ fragment, attestation: digest(attestation) });

/** Validate every raw occurrence before constructing a unique entry/edge view. */
function reconcileOccurrences(
  seedLedger,
  fragments,
  receipts,
  linkedEntries = new Map(),
  extraEdges = new Set(),
) {
  const additions = new Map(),
    edges = new Map();
  const seedIds = new Set(seedLedger.entries.map((entry) => entry.id));
  for (const fragment of fragments) {
    const hash = digest(fragment);
    for (const entry of fragment.entries) {
      if (
        !entry ||
        typeof entry.id !== "string" ||
        !entry.id ||
        entry.replacedBy ||
        entry.retiredBy
      )
        throw new Error("INVALID_PERMISSION_SURFACE_FRAGMENT_ENTRY");
      if (seedIds.has(entry.id)) throw new Error(`DUPLICATE_SURFACE_LEDGER_ENTRY ${entry.id}`);
      if (!additions.has(entry.id)) additions.set(entry.id, []);
      additions.get(entry.id).push({ ...occurrenceRef(hash, entry), entry });
    }
    for (const edge of fragment.transitions) {
      if (
        !exactKeys(edge, "field,id,target") ||
        typeof edge.id !== "string" ||
        typeof edge.target !== "string" ||
        !["replacedBy", "retiredBy"].includes(edge.field)
      )
        throw new Error("INVALID_PERMISSION_SURFACE_TRANSITION");
      const key = stable(edge);
      if (!edges.has(key)) edges.set(key, []);
      edges.get(key).push({ ...occurrenceRef(hash, edge), edge });
    }
  }
  const resolvedEntries = new Map(),
    resolvedEdges = new Set(),
    provenance = [];
  const match = (refs, occurrences) => {
    if (
      !Array.isArray(refs) ||
      refs.length !== 2 ||
      occurrences?.length !== 2 ||
      refs.some(
        (ref) =>
          !exactKeys(ref, "attestation,fragment") ||
          !/^[a-f0-9]{64}$/u.test(ref.fragment) ||
          !/^[a-f0-9]{64}$/u.test(ref.attestation),
      ) ||
      !exactSet(
        refs.map(stable),
        occurrences.map(({ fragment, attestation }) => stable({ fragment, attestation })),
      )
    )
      occurrenceFailure();
  };
  for (const receipt of receipts) {
    if (
      !exactKeys(receipt, "entries,owner,reason,ticket,transitions") ||
      !hasReviewedReceiptMetadata(receipt) ||
      !Array.isArray(receipt.entries) ||
      !Array.isArray(receipt.transitions) ||
      (!receipt.entries.length && !receipt.transitions.length)
    )
      occurrenceFailure();
    const proof = {
      reference: receiptReference(7, receipt),
      receipt: structuredClone(receipt),
      entries: [],
      transitions: [],
    };
    for (const decision of receipt.entries) {
      if (
        !exactKeys(decision, "effectiveMetadata,id,occurrences") ||
        typeof decision.id !== "string" ||
        resolvedEntries.has(decision.id) ||
        !exactKeys(decision.effectiveMetadata, "owner,reason,ticket") ||
        !hasReviewedReceiptMetadata(decision.effectiveMetadata)
      )
        occurrenceFailure();
      const occurrences = additions.get(decision.id);
      match(decision.occurrences, occurrences);
      if (
        occurrences.some(
          ({ entry }) =>
            entry.disposition !== "EXEMPT" ||
            entry.kind !== "permission-source-sentinel" ||
            !sourceFamily(entry.id) ||
            Object.hasOwn(entry, "replacedBy") ||
            Object.hasOwn(entry, "retiredBy") ||
            !hasReviewedReceiptMetadata(entry),
        ) ||
        stable(metadataFree(occurrences[0].entry)) !== stable(metadataFree(occurrences[1].entry))
      )
        occurrenceFailure();
      resolvedEntries.set(decision.id, {
        ...structuredClone(occurrences[0].entry),
        ...decision.effectiveMetadata,
      });
      proof.entries.push({
        id: decision.id,
        occurrences: structuredClone(occurrences).sort((a, b) =>
          stable(a).localeCompare(stable(b)),
        ),
      });
    }
    for (const decision of receipt.transitions) {
      if (!exactKeys(decision, "field,id,occurrences,target") || decision.field !== "replacedBy")
        occurrenceFailure();
      const edge = { id: decision.id, field: decision.field, target: decision.target },
        key = stable(edge);
      if (
        resolvedEdges.has(key) ||
        !receipt.entries.some((entry) => entry.id === edge.target) ||
        !resolvedEntries.has(edge.target) ||
        resolvedEntries.get(edge.target).replaces !== edge.id ||
        sourceFamily(edge.id) !== sourceFamily(edge.target)
      )
        occurrenceFailure();
      const occurrences = edges.get(key);
      match(decision.occurrences, occurrences);
      resolvedEdges.add(key);
      proof.transitions.push({
        ...edge,
        occurrences: structuredClone(occurrences).sort((a, b) =>
          stable(a).localeCompare(stable(b)),
        ),
      });
    }
    provenance.push(proof);
  }
  for (const key of extraEdges) {
    if (resolvedEdges.has(key))
      throw new Error("INVALID_PERMISSION_SURFACE_COMPLETE_OCCURRENCE_RECONCILIATION");
    resolvedEdges.add(key);
  }
  for (const [id, entry] of linkedEntries) {
    if (resolvedEntries.has(id))
      throw new Error("INVALID_PERMISSION_SURFACE_LINKED_ROOT_RECONCILIATION");
    resolvedEntries.set(id, structuredClone(entry));
  }
  for (const [id, occurrences] of additions) {
    if (occurrences.length > 1 && !resolvedEntries.has(id))
      throw new Error(`DUPLICATE_SURFACE_LEDGER_ENTRY ${id}`);
    if (!resolvedEntries.has(id)) resolvedEntries.set(id, structuredClone(occurrences[0].entry));
  }
  return {
    additions,
    entries: resolvedEntries,
    transitions: [...edges].flatMap(([key, occurrences]) =>
      (resolvedEdges.has(key) ? occurrences.slice(0, 1) : occurrences).map(({ edge }) => edge),
    ),
    provenance: provenance.sort((a, b) => a.reference.localeCompare(b.reference)),
  };
}

/** Combine immutable additions and transitions without depending on branch/merge order. */
export function assembleSurfaceHistory(
  seedLedger,
  seedBaseline,
  fragments,
  inheritedReconciliations = [],
  options = {},
) {
  const { historicalProjection = false } = options;
  // Pure canonical computations live only for this synchronous assembly. The
  // owning reader marks JSON parsed from authenticated committed bytes; caller
  // objects, live source authority and result/evidence snapshots are not cached.
  const canonicalValues = new Map();
  const digest = (value) => {
    if (!options[CANONICAL_COMPUTATIONS]?.has(value)) return canonicalDigest(value);
    if (!canonicalValues.has(value)) canonicalValues.set(value, canonicalDigest(value));
    return canonicalValues.get(value);
  };
  const validationOnly = options[VALIDATING_UNION] === true;
  const readerFiles = options[READER_FILES];
  const structuralMerge = options[STRUCTURAL_MERGE_PROOF];
  if (fragments.some((f) => [13, 14, 15, 16, 17].includes(f?.schemaVersion)) && !structuralMerge)
    throw new Error("PERMISSION_STRUCTURAL_MERGE_AUTHENTIC_READER_REQUIRED");
  const protectedFamily = (r) =>
    structuralMerge?.plans.some((p) => p.family === sourceFamily(r?.predecessor));
  assertSealed(seedLedger, "LEDGER_CONTENT_HASH_MISMATCH");
  assertSealed(seedBaseline, "LEGACY_BASELINE_ANCHOR_MISMATCH");
  if (
    seedLedger.schemaVersion !== 1 ||
    seedLedger.task !== "SIG-909" ||
    !Array.isArray(seedLedger.entries) ||
    stable(buildLedgerFromEntries(seedLedger.entries, seedLedger.legacyBoundaryCommit)) !==
      stable(seedLedger)
  )
    throw new Error("INVALID_PERMISSION_SURFACE_SEED");
  if (stable(buildLegacyBaselineAnchor(seedLedger, seedBaseline)) !== stable(seedBaseline)) {
    throw new Error("LEGACY_BASELINE_ANCHOR_MISMATCH");
  }
  const entries = new Map(seedLedger.entries.map((entry) => [entry.id, structuredClone(entry)]));
  if (entries.size !== seedLedger.entries.length) throw new Error("DUPLICATE_SURFACE_LEDGER_ENTRY");
  let transitions = [];
  const occurrenceReconciliations = [];
  const rootReconciliations = [];
  const linkedRootReconciliations = [];
  const completeOccurrenceReconciliations = [];
  const reconciliations = [];
  const spliceReconciliations = [];
  const compositionReconciliations = [];
  const compositionExtensions = [];
  const compositionSupersessions = [];
  const receiptCatalog = [];
  for (const fragment of fragments) {
    if (
      ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17].includes(
        fragment?.schemaVersion,
      ) ||
      !Array.isArray(fragment.entries) ||
      !Array.isArray(fragment.transitions) ||
      Object.keys(fragment).some(
        (key) =>
          ![
            "schemaVersion",
            "entries",
            "transitions",
            ...(fragment.schemaVersion === 2 ? ["reconciliations"] : []),
            ...(fragment.schemaVersion === 3 ? ["spliceReconciliations"] : []),
            ...(fragment.schemaVersion === 4 ? ["compositionReconciliations"] : []),
            ...(fragment.schemaVersion === 5 ? ["compositionExtensions"] : []),
            ...(fragment.schemaVersion === 6 ? ["compositionSupersessions"] : []),
            ...(fragment.schemaVersion === 7 ? ["occurrenceReconciliations"] : []),
            ...(fragment.schemaVersion === 8 ? ["rootReconciliations"] : []),
            ...(fragment.schemaVersion === 9 ? ["linkedRootReconciliations"] : []),
            ...(fragment.schemaVersion === 10 ? ["completeOccurrenceReconciliations"] : []),
            ...(fragment.schemaVersion === 11 ? ["sourceHeadSelections"] : []),
            ...(fragment.schemaVersion === 12 ? ["sourceHeadContinuations"] : []),
            ...(fragment.schemaVersion === 13 ? ["structuralMergeExtensions"] : []),
            ...(fragment.schemaVersion === 14 ? ["structuralMergeContinuations"] : []),
            ...(fragment.schemaVersion === 15 ? ["structuralMergeCompositions"] : []),
            ...(fragment.schemaVersion === 16 ? ["structuralMergeCatchups"] : []),
            ...(fragment.schemaVersion === 17 ? ["structuralTailCompositions"] : []),
          ].includes(key),
      )
    )
      throw new Error("INVALID_PERMISSION_SURFACE_FRAGMENT");
    if (fragment.schemaVersion === 2) {
      if (!Array.isArray(fragment.reconciliations) || !fragment.reconciliations.length)
        throw new Error("INVALID_PERMISSION_SURFACE_RECONCILIATION");
      reconciliations.push(...fragment.reconciliations);
      receiptCatalog.push(
        ...fragment.reconciliations.map((receipt) => ({
          schemaVersion: 2,
          receipt,
          reference: receiptReference(2, receipt),
        })),
      );
    }
    if (fragment.schemaVersion === 3) {
      if (
        fragment.entries.length ||
        fragment.transitions.length ||
        !Array.isArray(fragment.spliceReconciliations) ||
        !fragment.spliceReconciliations.length
      )
        throw new Error("INVALID_PERMISSION_SURFACE_SPLICE_RECONCILIATION");
      spliceReconciliations.push(...fragment.spliceReconciliations);
      receiptCatalog.push(
        ...fragment.spliceReconciliations.map((receipt) => ({
          schemaVersion: 3,
          receipt,
          reference: receiptReference(3, receipt),
        })),
      );
    }
    if (fragment.schemaVersion === 4) {
      if (
        fragment.entries.length ||
        fragment.transitions.length ||
        !Array.isArray(fragment.compositionReconciliations) ||
        !fragment.compositionReconciliations.length
      )
        compositionFailure();
      compositionReconciliations.push(...fragment.compositionReconciliations);
    }
    if (fragment.schemaVersion === 5) {
      if (
        fragment.entries.length ||
        fragment.transitions.length ||
        !Array.isArray(fragment.compositionExtensions) ||
        !fragment.compositionExtensions.length
      )
        compositionFailure();
      compositionExtensions.push(...fragment.compositionExtensions);
    }
    if (fragment.schemaVersion === 6) {
      if (
        fragment.entries.length ||
        fragment.transitions.length ||
        !Array.isArray(fragment.compositionSupersessions) ||
        !fragment.compositionSupersessions.length
      )
        compositionFailure();
      compositionSupersessions.push(...fragment.compositionSupersessions);
    }
    if (fragment.schemaVersion === 7) {
      if (
        fragment.entries.length ||
        fragment.transitions.length ||
        !Array.isArray(fragment.occurrenceReconciliations) ||
        !fragment.occurrenceReconciliations.length
      )
        occurrenceFailure();
      occurrenceReconciliations.push(...fragment.occurrenceReconciliations);
    }
    if (fragment.schemaVersion === 8) {
      if (
        fragment.entries.length ||
        fragment.transitions.length ||
        !Array.isArray(fragment.rootReconciliations) ||
        !fragment.rootReconciliations.length
      )
        throw new Error("INVALID_PERMISSION_SURFACE_ROOT_RECONCILIATION");
      rootReconciliations.push(...fragment.rootReconciliations);
    }
    if (fragment.schemaVersion === 9) {
      if (
        fragment.entries.length ||
        fragment.transitions.length ||
        !Array.isArray(fragment.linkedRootReconciliations) ||
        !fragment.linkedRootReconciliations.length
      )
        throw new Error("INVALID_PERMISSION_SURFACE_LINKED_ROOT_RECONCILIATION");
      linkedRootReconciliations.push(...fragment.linkedRootReconciliations);
    }
    if (fragment.schemaVersion === 10) {
      if (
        fragment.entries.length ||
        fragment.transitions.length ||
        !Array.isArray(fragment.completeOccurrenceReconciliations) ||
        !fragment.completeOccurrenceReconciliations.length
      )
        throw new Error("INVALID_PERMISSION_SURFACE_COMPLETE_OCCURRENCE_RECONCILIATION");
      completeOccurrenceReconciliations.push(...fragment.completeOccurrenceReconciliations);
    }
  }
  for (const candidate of inheritedReconciliations)
    if (
      candidate &&
      (Object.hasOwn(candidate, "completeOccurrenceReconciliations") ||
        Object.hasOwn(candidate, "rootBindings")) &&
      !Object.hasOwn(candidate, "completeOccurrenceEvidence")
    )
      throw new Error("INVALID_PERMISSION_SURFACE_COMPLETE_OCCURRENCE_RECONCILIATION");
  for (const fragment of fragments)
    for (const entry of fragment.entries)
      if (seedLedger.entries.some((seed) => seed.id === entry.id))
        throw new Error(`DUPLICATE_SURFACE_LEDGER_ENTRY ${entry.id}`);
  const unionProof = inheritedUnionProof(inheritedReconciliations, seedLedger, seedBaseline);
  if (unionProof)
    for (const field of [
      "occurrenceReconciliations",
      "completeOccurrenceReconciliations",
      "linkedRootReconciliations",
      "rootReconciliations",
    ]) {
      const full = unionProof.snapshot.fragments.flatMap((f) => f[field] ?? []);
      for (const fragment of fragments)
        for (const receipt of fragment[field] ?? []) {
          const ownIds =
            field === "rootReconciliations"
              ? [receipt.family]
              : field === "linkedRootReconciliations"
                ? [receipt.entry.id]
                : receipt.entries.map((e) => e.id);
          const overlaps = full.filter((other) => {
            const ids =
              field === "rootReconciliations"
                ? [other.family]
                : field === "linkedRootReconciliations"
                  ? [other.entry.id]
                  : other.entries.map((e) => e.id);
            return ownIds.some((id) => ids.includes(id));
          });
          if (overlaps.some((other) => stable(other) !== stable(receipt)))
            evidenceFailure(
              inheritedReconciliations.find(
                (r) =>
                  r?.occurrenceEvidence ||
                  r?.completeOccurrenceEvidence ||
                  r?.linkedRootEvidence ||
                  r?.rootEvidence,
              ),
            );
        }
    }
  if (unionProof) {
    const claims = (input) =>
      input.flatMap((f) => [
        ...(f.occurrenceReconciliations ?? []).flatMap((r) =>
          r.entries.map((e) => ({ id: e.id, owner: digest({ schemaVersion: 7, receipt: r }) })),
        ),
        ...(f.completeOccurrenceReconciliations ?? []).flatMap((r) =>
          r.entries.map((e) => ({ id: e.id, owner: digest({ schemaVersion: 10, receipt: r }) })),
        ),
        ...(f.linkedRootReconciliations ?? []).map((r) => ({
          id: r.entry.id,
          owner: digest({ schemaVersion: 9, receipt: r }),
        })),
      ]);
    const currentClaims = claims(unionProof.snapshot.fragments);
    for (const own of claims(fragments))
      if (currentClaims.some((claim) => claim.id === own.id && claim.owner !== own.owner))
        evidenceFailure(
          inheritedReconciliations.find(
            (r) =>
              r?.occurrenceEvidence ||
              r?.completeOccurrenceEvidence ||
              r?.linkedRootEvidence ||
              r?.rootEvidence,
          ),
        );
  }
  const completeResult = prepareCompleteOccurrences(
    seedLedger,
    fragments,
    completeOccurrenceReconciliations,
  );
  const inheritedLinkedRootEvidence = [];
  for (const candidate of inheritedReconciliations) {
    if (!candidate) continue;
    if (Object.hasOwn(candidate, "linkedRootEvidence")) {
      const verified = validatedLinkedRootEvidence.get(candidate);
      if (!verified || stable(candidate) !== stable(verified))
        throw new Error("INVALID_PERMISSION_SURFACE_LINKED_ROOT_RECONCILIATION");
      inheritedLinkedRootEvidence.push({ ...verified, fragments: unionProof.snapshot.fragments });
    } else if (
      Object.hasOwn(candidate, "linkedRootReconciliations") ||
      (Object.hasOwn(candidate, "entry") && Object.hasOwn(candidate, "transition"))
    ) {
      throw new Error("INVALID_PERMISSION_SURFACE_LINKED_ROOT_RECONCILIATION");
    }
  }
  const linkedRootResult = prepareLinkedRootHistory(
    seedLedger,
    fragments,
    linkedRootReconciliations,
    inheritedLinkedRootEvidence,
    historicalProjection,
    inheritedReconciliations.filter(
      (candidate) => !Object.hasOwn(candidate ?? {}, "linkedRootEvidence"),
    ),
  );
  const preparedEntries = new Map(linkedRootResult.canonicalEntries),
    preparedEdges = new Set(completeResult.edgeKeys);
  for (const [id, value] of completeResult.entries) {
    if (
      preparedEntries.has(id) ||
      occurrenceReconciliations.some((r) => r.entries.some((e) => e.id === id))
    )
      throw new Error("INVALID_PERMISSION_SURFACE_COMPLETE_OCCURRENCE_RECONCILIATION");
    preparedEntries.set(id, value);
  }
  if (unionProof) {
    const full = unionProof.result;
    for (const schema of [7, 10]) {
      const handles = inheritedReconciliations.filter((r) =>
        schema === 7 ? r?.occurrenceEvidence : r?.completeOccurrenceEvidence,
      );
      if (!handles.length) continue;
      const decisions = handles.flatMap((r) =>
        schema === 7
          ? r.occurrenceReconciliations.flatMap((x) => x.entries)
          : r.completeOccurrenceReconciliations.flatMap((x) => x.entries),
      );
      const effective = schema === 7 ? full.occurrences.entries : full.complete.entries;
      const subset = projectOccurrenceSubset(
        seedLedger,
        fragments,
        unionProof.snapshot.fragments,
        effective,
        decisions,
        { historical: historicalProjection, requireHistorical: schema === 10 },
      );
      for (const [id, value] of subset.entries) {
        if (occurrenceReconciliations.some((r) => r.entries.some((e) => e.id === id))) {
          const own = occurrenceReconciliations.flatMap((r) => r.entries).find((e) => e.id === id);
          if (
            stable(own.effectiveMetadata) !==
            stable((({ reason, owner, ticket }) => ({ reason, owner, ticket }))(value))
          )
            occurrenceFailure();
          continue;
        }
        if (preparedEntries.has(id) && stable(preparedEntries.get(id)) !== stable(value))
          throw new Error("INVALID_PERMISSION_SURFACE_COMPLETE_OCCURRENCE_RECONCILIATION");
        preparedEntries.set(id, value);
      }
      for (const key of subset.edges)
        if (
          !completeResult.edgeKeys.has(key) &&
          !occurrenceReconciliations.some((r) =>
            r.transitions.some(
              (e) => stable({ id: e.id, field: e.field, target: e.target }) === key,
            ),
          )
        )
          preparedEdges.add(key);
    }
  }
  const occurrences = reconcileOccurrences(
    seedLedger,
    fragments,
    occurrenceReconciliations,
    preparedEntries,
    preparedEdges,
  );
  for (const [id, entry] of occurrences.entries) entries.set(id, entry);
  // A schema9 historical linked-only subset may retain its exact pinned incoming
  // edge while the raw predecessor blob is absent. Keep the immutable raw edge
  // and provenance; comparison applies its proved replaces field without P.
  transitions = occurrences.transitions.filter(
    (edge) => !linkedRootResult.comparisonIncomingEdges.has(stable(edge)),
  );
  for (const candidate of inheritedReconciliations)
    if (
      candidate &&
      (Object.hasOwn(candidate, "occurrenceReconciliations") ||
        (Array.isArray(candidate.entries) && Array.isArray(candidate.transitions))) &&
      !Object.hasOwn(candidate, "occurrenceEvidence")
    )
      occurrenceFailure();
  const occurrenceProvenance = occurrences.provenance;
  let occurrenceEvidence;
  if (occurrenceReconciliations.length) {
    const hashes = new Set(
      occurrenceReconciliations.flatMap((r) =>
        [...r.entries, ...r.transitions].flatMap((d) => d.occurrences.map((ref) => ref.fragment)),
      ),
    );
    occurrenceEvidence = {
      occurrenceEvidence: true,
      occurrenceReconciliations: structuredClone(occurrenceReconciliations).sort((a, b) =>
        digest(a).localeCompare(digest(b)),
      ),
      fragments: structuredClone(fragments.filter((f) => hashes.has(digest(f)))).sort((a, b) =>
        digest(a).localeCompare(digest(b)),
      ),
    };
  }
  // Reconciliation is an explicit, immutable lineage decision, never an
  // automatic winner selection. Preserve every attestation in a linear history.
  const groups = new Map();
  for (const transition of transitions) {
    const { id, field, target } = transition ?? {};
    if (
      !transition ||
      Object.keys(transition).length !== 3 ||
      typeof id !== "string" ||
      typeof target !== "string" ||
      !["replacedBy", "retiredBy"].includes(field)
    )
      throw new Error("INVALID_PERMISSION_SURFACE_TRANSITION");
    if (!groups.has(id)) groups.set(id, []);
    groups.get(id).push(transition);
  }
  const inheritedRootEvidence = [];
  for (const candidate of inheritedReconciliations) {
    if (!candidate) continue;
    if (Object.hasOwn(candidate, "rootEvidence")) {
      const verified = validatedRootEvidence.get(candidate);
      if (!verified || stable(candidate) !== stable(verified))
        throw new Error("INVALID_PERMISSION_SURFACE_ROOT_RECONCILIATION");
      inheritedRootEvidence.push({
        ...verified,
        fragments: unionProof.snapshot.fragments,
        occurrenceView: unionProof.result.complete,
      });
    } else if (
      Object.hasOwn(candidate, "rootReconciliations") ||
      Object.hasOwn(candidate, "roots")
    ) {
      throw new Error("INVALID_PERMISSION_SURFACE_ROOT_RECONCILIATION");
    }
  }
  const rootResult = reconcileRootFamilies(
    seedLedger,
    fragments,
    entries,
    groups,
    rootReconciliations,
    inheritedRootEvidence,
    historicalProjection,
    completeResult,
  );
  applyLinkedRootHistory(linkedRootResult, entries, groups);
  const applied = new Set();
  const virtualJoins = [];
  const join = (id, target) => virtualJoins.push({ id, target });
  const compositions = [
    ...compositionReconciliations,
    ...inheritedReconciliations.filter(
      (r) =>
        Array.isArray(r?.receipts) &&
        !Array.isArray(r?.supersedes) &&
        !compositionReconciliations.some((own) => own.predecessor === r.predecessor) &&
        canInheritComposition(r, receiptCatalog, entries, groups),
    ),
  ].filter((r) => !protectedFamily(r));
  const claimed = new Set();
  // Local object identity: copied/inherited JSON cannot grant this authority.
  const pinnedThirdReceipts = new Set();
  const sealedFragments = new Map(fragments.map((f) => [digest(f), f]));
  const structural = fragmentReceipts(fragments).filter((c) => [4, 5].includes(c.schemaVersion));
  const supersessions = [
    ...compositionSupersessions,
    ...inheritedReconciliations.filter(
      (r) =>
        Array.isArray(r?.supersedes) &&
        !compositionSupersessions.some((own) => own.predecessor === r.predecessor) &&
        supersessionRefsMatch(r, receiptCatalog, structural, entries, sealedFragments),
    ),
  ].filter((r) => !protectedFamily(r));
  const superseded = new Set();
  // Check incoming edges as well: an unrelated raw predecessor must not point
  // into a branch with inconsistent replaces that a virtual join would mask.
  if (
    compositions.length ||
    compositionExtensions.length ||
    supersessions.length ||
    structuralMerge
  ) {
    for (const edges of groups.values()) {
      for (const edge of edges) {
        const entry = entries.get(edge.id),
          target = entries.get(edge.target);
        if (
          !entry ||
          !target ||
          entry.replacedBy ||
          entry.retiredBy ||
          (edge.field === "replacedBy" && target.replaces !== edge.id)
        )
          compositionFailure();
      }
    }
  }
  // Validate all raw receipts/edges before any composition can rewrite them.
  for (const r of supersessions) {
    if (superseded.has(r.predecessor)) compositionFailure();
    validateCompositionSupersession(
      r,
      receiptCatalog,
      structural,
      entries,
      groups,
      claimed,
      sealedFragments,
      seedLedger,
      seedBaseline,
      options[SNAPSHOT_FAMILIES] ?? new Set(),
      options[SEALED_SNAPSHOT_READER],
      pinnedThirdReceipts,
    );
    superseded.add(r.predecessor);
  }
  const extended = new Set();
  for (const r of compositionExtensions.filter(
    (r) => !protectedFamily(r) && !superseded.has(r.predecessor),
  )) {
    const base = validateCompositionExtension(
      r,
      compositions,
      receiptCatalog,
      entries,
      groups,
      claimed,
    );
    if (extended.has(base)) compositionFailure();
    extended.add(base);
  }
  const effectiveCompositions = [
    ...compositions.filter((r) => !extended.has(r) && !superseded.has(r.predecessor)),
    ...compositionExtensions.filter((r) => !protectedFamily(r) && !superseded.has(r.predecessor)),
    ...supersessions,
  ];
  for (const r of compositions.filter((r) => !extended.has(r) && !superseded.has(r.predecessor)))
    validateComposition(r, receiptCatalog, entries, groups, claimed);
  for (const r of effectiveCompositions) {
    applied.add(r.predecessor);
    const sequence = [r.predecessor, ...r.lineage];
    for (let i = 0; i < sequence.length - 1; i++) {
      const previous = sequence[i],
        next = sequence[i + 1];
      groups.set(previous, [{ id: previous, field: "replacedBy", target: next }]);
      entries.get(next).replaces = previous;
      join(previous, next);
    }
  }
  const inherited = inheritedReconciliations.filter(
    (r) =>
      !Array.isArray(r?.receipts) &&
      !Array.isArray(r?.supersedes) &&
      !applied.has(r?.predecessor) &&
      groups.get(r.predecessor)?.length > 1 &&
      exactSet(
        r.successors,
        groups.get(r.predecessor).map((edge) => edge.target),
      ) &&
      !reconciliations.some((own) => own.predecessor === r.predecessor) &&
      // An authentic local splice already owns this fork and validates its
      // published ordinary tail; a later peer's v2 ordering cannot replace it.
      !spliceReconciliations.some((own) => own.predecessor === r.predecessor),
  );
  for (const r of [...reconciliations, ...inherited].filter(
    (r) =>
      !superseded.has(r?.predecessor) &&
      !protectedFamily(r) &&
      !compositions.some((c) => c.predecessor === r?.predecessor),
  )) {
    const edges = groups.get(r?.predecessor);
    if (
      !r ||
      Object.keys(r).sort().join(",") !==
        `${pinnedThirdReceipts.has(r) ? "continuationOf," : ""}owner,predecessor,reason,successors,ticket` ||
      !Array.isArray(r.successors) ||
      r.successors.length < 2 ||
      new Set(r.successors).size !== r.successors.length ||
      !hasReviewedReceiptMetadata(r) ||
      applied.has(r.predecessor) ||
      !sourceFamily(r.predecessor) ||
      !edges ||
      edges.length !== r.successors.length ||
      edges.some((e) => e.field !== "replacedBy") ||
      new Set(edges.map((e) => e.target)).size !== edges.length ||
      r.successors.some(
        (id) =>
          !edges.some((e) => e.target === id) ||
          sourceFamily(id) !== sourceFamily(r.predecessor) ||
          entries.get(id)?.replaces !== r.predecessor,
      ) ||
      r.successors.slice(0, -1).some((id) => groups.has(id)) ||
      entries.get(r.predecessor)?.replacedBy ||
      entries.get(r.predecessor)?.retiredBy
    )
      throw new Error("INVALID_PERMISSION_SURFACE_RECONCILIATION");
    applied.add(r.predecessor);
    groups.set(r.predecessor, [
      { id: r.predecessor, field: "replacedBy", target: r.successors[0] },
    ]);
    join(r.predecessor, r.successors[0]);
    for (let i = 1; i < r.successors.length; i++) {
      const previous = r.successors[i - 1],
        next = r.successors[i];
      entries.get(next).replaces = previous;
      groups.set(previous, [{ id: previous, field: "replacedBy", target: next }]);
      join(previous, next);
    }
  }
  // A v3 splice appends a separately reviewed branch after a complete, already
  // published mainline. It never rewrites the mainline's historic edges.
  for (const r of spliceReconciliations.filter(
    (r) =>
      !superseded.has(r?.predecessor) &&
      !protectedFamily(r) &&
      !compositions.some((c) => c.predecessor === r?.predecessor),
  )) {
    const direct = groups.get(r?.predecessor);
    const mainline = Array.isArray(r?.mainline) ? r.mainline : null;
    const branches = Array.isArray(r?.branches) ? r.branches : null;
    const declaredNodes = mainline && branches ? [...mainline, ...branches] : [];
    const allSuccessors = mainline && branches ? [mainline[0], ...branches] : [];
    const directTargets = direct?.map((edge) => edge.target);
    const hasExactDirectTargets =
      Array.isArray(directTargets) &&
      directTargets.length === allSuccessors.length &&
      new Set(directTargets).size === directTargets.length &&
      allSuccessors.length === new Set(allSuccessors).size &&
      allSuccessors.every((id) => directTargets.includes(id));
    const sameFamily =
      sourceFamily(r?.predecessor) &&
      declaredNodes.length === new Set(declaredNodes).size &&
      !declaredNodes.includes(r.predecessor) &&
      declaredNodes.every((id) => sourceFamily(id) === sourceFamily(r.predecessor));
    const mainlineIsPublishedPath =
      Array.isArray(mainline) &&
      mainline.length >= 2 &&
      mainline.every((id, index) => {
        if (
          !entries.get(id) ||
          entries.get(id)?.replaces !== (index ? mainline[index - 1] : r.predecessor)
        )
          return false;
        if (index === mainline.length - 1) return !groups.has(id);
        const edges = groups.get(id);
        return (
          edges?.length === 1 &&
          edges[0].field === "replacedBy" &&
          edges[0].target === mainline[index + 1]
        );
      });
    const hasValidOrdinaryTail = (start) => {
      const protectedNodes = new Set([r.predecessor, ...declaredNodes]);
      const seen = new Set();
      let current = start;
      while (true) {
        const edges = groups.get(current);
        if (!edges) return true;
        if (
          edges.length !== 1 ||
          edges[0].field !== "replacedBy" ||
          sourceFamily(edges[0].target) !== sourceFamily(r.predecessor) ||
          entries.get(edges[0].target)?.replaces !== current ||
          protectedNodes.has(edges[0].target) ||
          seen.has(edges[0].target)
        )
          return false;
        seen.add(current);
        current = edges[0].target;
      }
    };
    if (
      !r ||
      Object.keys(r).sort().join(",") !== "branches,mainline,owner,predecessor,reason,ticket" ||
      !mainline ||
      !branches ||
      !branches.length ||
      !hasReviewedReceiptMetadata(r) ||
      applied.has(r.predecessor) ||
      !sameFamily ||
      !direct ||
      direct.some((edge) => edge.field !== "replacedBy") ||
      !hasExactDirectTargets ||
      !mainlineIsPublishedPath ||
      !branches.every(
        (id, index) =>
          entries.get(id)?.replaces === r.predecessor &&
          (index === branches.length - 1 ? hasValidOrdinaryTail(id) : !groups.has(id)),
      ) ||
      entries.get(r.predecessor)?.replacedBy ||
      entries.get(r.predecessor)?.retiredBy
    )
      throw new Error("INVALID_PERMISSION_SURFACE_SPLICE_RECONCILIATION");
    applied.add(r.predecessor);
    groups.set(r.predecessor, [{ id: r.predecessor, field: "replacedBy", target: mainline[0] }]);
    join(r.predecessor, mainline[0]);
    let tail = mainline.at(-1);
    for (const branch of branches) {
      entries.get(branch).replaces = tail;
      groups.set(tail, [{ id: tail, field: "replacedBy", target: branch }]);
      join(tail, branch);
      tail = branch;
    }
  }
  if (structuralMerge)
    for (const plan of structuralMerge.plans) {
      // Only explicit derived lineage fields change. All raw entries, generic
      // occurrence/root decisions and full whole-fragment checks remain above.
      const actual = [...entries.values()].filter((e) => sourceFamily(e.id) === plan.family);
      const intrinsic = (e) => {
        const { replaces, replacedBy, ...rest } = e;
        return rest;
      };
      if (
        actual.length !== plan.derived.length ||
        plan.derived.some(
          (e) =>
            !entries.has(e.id) || stable(intrinsic(entries.get(e.id))) !== stable(intrinsic(e)),
        )
      )
        throw new Error("INVALID_PERMISSION_STRUCTURAL_MERGE_EXTENSION");
      for (const e of plan.derived) {
        const entry = entries.get(e.id);
        delete entry.replaces;
        delete entry.replacedBy;
        if (e.replaces !== undefined) entry.replaces = e.replaces;
        groups.delete(e.id);
        if (e.replacedBy !== undefined) {
          groups.set(e.id, [{ id: e.id, field: "replacedBy", target: e.replacedBy }]);
          // A14 authenticates its exact base ordering. Later genuine paired
          // tails remain ordinary raw evolution, never inferred into old bases.
          if (!structuralMerge.continuation || plan.base.some((x) => x.id === e.replacedBy))
            join(e.id, e.replacedBy);
        }
      }
    }
  const effectiveTransitions = [...groups.values()].flat();
  // Load every addition first: a successor may live in a lexically earlier fragment.
  const transitioned = new Set();
  for (const transition of effectiveTransitions) {
    const { id, field, target } = transition ?? {};
    if (
      !transition ||
      Object.keys(transition).length !== 3 ||
      typeof id !== "string" ||
      typeof target !== "string" ||
      !["replacedBy", "retiredBy"].includes(field)
    )
      throw new Error("INVALID_PERMISSION_SURFACE_TRANSITION");
    const entry = entries.get(id);
    if (
      !entry ||
      !entries.has(target) ||
      entry.replacedBy ||
      entry.retiredBy ||
      transitioned.has(id)
    ) {
      throw new Error(`CONFLICTING_PERMISSION_SURFACE_TRANSITION ${id}`);
    }
    entry[field] = target;
    transitioned.add(id);
  }
  if (
    validationOnly &&
    virtualJoins.some(
      ({ id, target }) =>
        entries.get(id)?.replacedBy !== target || entries.get(target)?.replaces !== id,
    )
  )
    compositionFailure();
  if (historicalProjection && unionProof) {
    // Old receipts attest the authentic parent chain, before comparison-only
    // joins to peer nodes. Validate that complete chain before projecting it.
    const parentLedger = buildLedgerFromEntries(
      [...entries.values()].map((entry) => structuredClone(entry)),
      seedLedger.legacyBoundaryCommit,
    );
    if (structuralMerge)
      validateStructuralSourceHeadContinuations(fragments, parentLedger, structuralMerge.origin);
    else validateSourceHeadContinuations(fragments, parentLedger);
    projectStructuralJoins(unionProof, fragments, entries);
  }
  const ordered = [...entries.values()].sort((left, right) =>
    left.id < right.id ? -1 : left.id > right.id ? 1 : 0,
  );
  const ledger = buildLedgerFromEntries(ordered, seedLedger.legacyBoundaryCommit);
  const baseline = buildLegacyBaselineAnchor(ledger, seedBaseline);
  // Validation never issues source authority. Only the full reader owns authentic file bytes.
  if (!(historicalProjection && unionProof)) {
    if (structuralMerge)
      validateStructuralSourceHeadContinuations(fragments, ledger, structuralMerge.origin);
    else validateSourceHeadContinuations(fragments, ledger);
  }
  const completeEvidence = completeOccurrenceReconciliations.length
    ? {
        completeOccurrenceEvidence: true,
        completeOccurrenceReconciliations: structuredClone(completeOccurrenceReconciliations).sort(
          (a, b) => digest(a).localeCompare(digest(b)),
        ),
      }
    : null;
  const handles = [
    ...(occurrenceEvidence ? [occurrenceEvidence] : []),
    ...(rootResult.evidence ? [rootResult.evidence] : []),
    ...(linkedRootResult.evidence ? [linkedRootResult.evidence] : []),
    ...(completeEvidence ? [completeEvidence] : []),
  ];
  let unionEvidence;
  if (
    !historicalProjection &&
    !validationOnly &&
    (handles.length || structuralMerge?.continuation)
  ) {
    const snapshot = {
      seed: structuredClone(seedLedger),
      baseline: structuredClone(seedBaseline),
      fragments: structuredClone(fragments).sort((a, b) => digest(a).localeCompare(digest(b))),
      bytes: readerFiles
        ? [...Map.prototype.entries.call(readerFiles)].sort(([a], [b]) => a.localeCompare(b))
        : null,
    };
    unionEvidence = {
      unionEvidence: true,
      scope: digest(snapshot),
      byteIdentities: snapshot.bytes
        ? snapshot.bytes.map(([path, text]) => ({ path, sha256: byteHash(text) }))
        : null,
    };
    validatedUnions.set(unionEvidence, {
      snapshot,
      readerFiles,
      tokenSnapshot: structuredClone(unionEvidence),
      structuralMerge,
      readerRoot: options[READER_ROOT],
      readSealedSnapshot: options[SEALED_SNAPSHOT_READER],
    });
    for (const handle of handles) {
      unionOwners.set(handle, unionEvidence);
      const map = handle.occurrenceEvidence
        ? validatedOccurrenceEvidence
        : handle.rootEvidence
          ? validatedRootEvidence
          : handle.linkedRootEvidence
            ? validatedLinkedRootEvidence
            : validatedCompleteEvidence;
      map.set(handle, structuredClone(handle));
    }
  }
  const result = {
    ledger,
    baseline,
    occurrenceProvenance,
    completeOccurrenceProvenance: completeResult.provenance,
    linkedRootProvenance: linkedRootResult.provenance,
    rootProvenance: rootResult.provenance,
    reconciliations: [
      ...reconciliations,
      ...compositionReconciliations,
      ...compositionSupersessions,
      ...(!historicalProjection && !validationOnly ? handles : []),
      ...(unionEvidence ? [unionEvidence] : []),
    ].sort((a, b) => digest(a).localeCompare(digest(b))),
  };
  if (validationOnly)
    Object.defineProperty(result, VALIDATION_RESULT, {
      value: { occurrences, complete: completeResult, virtualJoins },
    });
  // Detect any accidental mutation before an owning reader can issue authority.
  for (const [value, hash] of canonicalValues) if (canonicalDigest(value) !== hash) memoFailure();
  return result;
}

// A memo belongs to one owning read or one privately branded catch-up transaction.
// Only fully authenticated historical facts enter it. Live source/evolution
// capabilities and caller-supplied evidence never enter or escape this memo.
function historicalMemo(root) {
  return {
    root: resolve(root),
    historyReader: openInstalledHistoryReader(resolve(root)),
    records: new Map(),
    frames: [],
    sealedSnapshots: new Set(),
  };
}
function memoFailure() {
  throw new Error("PERMISSION_STRUCTURAL_COMMITTED_FACTS_CHANGED");
}
function authenticatedGitBatch(root, ids) {
  const output = execFileSync("/usr/bin/git", ["cat-file", "--batch"], {
    ...GIT_OPTIONS,
    cwd: root,
    encoding: null,
    input: ids.join("\n") + "\n",
  });
  const objects = new Map();
  let offset = 0;
  for (const id of ids) {
    const end = output.indexOf(10, offset);
    const header = output.subarray(offset, end).toString("utf8").split(" ");
    const length = Number(header[2]);
    if (
      end < offset ||
      header[0] !== id ||
      !["commit", "tree", "blob"].includes(header[1]) ||
      !Number.isSafeInteger(length) ||
      length < 0 ||
      length > 128 * 1024 * 1024 ||
      end + 1 + length >= output.length ||
      output[end + 1 + length] !== 10
    )
      memoFailure();
    const bytes = output.subarray(end + 1, end + 1 + length);
    if (createHash("sha1").update(`${header[1]} ${length}\0`).update(bytes).digest("hex") !== id)
      memoFailure();
    objects.set(id, { type: header[1], bytes });
    offset = end + 1 + length + 1;
  }
  if (offset !== output.length) memoFailure();
  return objects;
}
function committedSnapshot(
  root,
  revision,
  historyReader = openInstalledHistoryReader(resolve(root)),
) {
  if (historyReader) {
    const snapshot = historyReader.readSnapshot(revision);
    if (!snapshot.files.has(SEED_LEDGER)) return null;
    return {
      ...snapshot,
      files: new Map(
        [...snapshot.files].filter(([path]) => path.startsWith(SURFACE_HISTORY_PATH + "/")),
      ),
      inventory: snapshot.inventory.filter(({ path }) =>
        path.startsWith(SURFACE_HISTORY_PATH + "/"),
      ),
    };
  }
  const git = (args, input) =>
    execFileSync("/usr/bin/git", args, {
      ...GIT_OPTIONS,
      cwd: root,
      encoding: null,
      ...(input !== undefined ? { input } : {}),
    });
  const batch = (ids) => authenticatedGitBatch(root, ids);
  const commit = batch([revision]).get(revision);
  if (commit.type !== "commit") memoFailure();
  const tree = /^tree ([a-f0-9]{40})\n/u.exec(commit.bytes.toString("utf8"))?.[1];
  if (!tree) memoFailure();
  const inventory = git(["ls-tree", "-r", "-t", "-z", revision, "--", SURFACE_HISTORY_PATH]);
  const items = inventory
    .toString("utf8")
    .split("\0")
    .filter(Boolean)
    .map((line) => {
      const match = /^(040000 tree|100644 blob|100755 blob) ([a-f0-9]{40})\t(.+)$/u.exec(line);
      if (!match) memoFailure();
      const [mode, type] = match[1].split(" ");
      const path = match[3];
      if (type === "tree") {
        if (
          !["scripts", "scripts/permission-registry", SURFACE_HISTORY_PATH, FRAGMENTS].includes(
            path,
          )
        )
          memoFailure();
      } else if (
        ![SEED_LEDGER, SEED_BASELINE].includes(path) &&
        !new RegExp(`^${FRAGMENTS}/[a-f0-9]{64}\\.json$`, "u").test(path)
      )
        memoFailure();
      return { mode, type, id: match[2], path };
    });
  // Keep the original pre-storage migration path unchanged and uncached.
  if (!items.some((item) => item.path === SEED_LEDGER)) return null;
  if (items.filter((item) => item.type === "blob").length > 2000) memoFailure();
  const objects = batch([...new Set([tree, ...items.map((item) => item.id)])]);
  if (objects.get(tree)?.type !== "tree") memoFailure();
  const files = new Map();
  const identity = createHash("sha256").update(commit.bytes).update(inventory);
  let size = 0;
  for (const [id, object] of objects) {
    identity.update(`${id} ${object.type} ${object.bytes.length}\0`).update(object.bytes);
  }
  for (const item of items) {
    const object = objects.get(item.id);
    if (object?.type !== item.type) memoFailure();
    if (item.type === "blob") {
      size += object.bytes.length;
      if (size > 128 * 1024 * 1024 || files.has(item.path)) memoFailure();
      files.set(item.path, object.bytes.toString("utf8"));
    }
  }
  return {
    identity: identity.digest("hex"),
    files,
    inventory: items
      .filter((x) => x.type === "blob")
      .map((x) => ({ path: x.path, mode: x.mode, blob: x.id })),
  };
}
function rememberDependency(memo, revision, identity) {
  for (const frame of memo.frames) {
    if (frame.has(revision) && frame.get(revision) !== identity) memoFailure();
    frame.set(revision, identity);
  }
}
function restoreHistorical(memo, record, snapshot, revision) {
  for (const [dependency, identity] of record.dependencies) {
    const actual =
      dependency === revision
        ? snapshot
        : committedSnapshot(memo.root, dependency, memo.historyReader);
    if (!actual || actual.identity !== identity) memoFailure();
    rememberDependency(memo, dependency, identity);
  }
  const result = structuredClone(record.result);
  if (record.proof) structuralReaderProofs.set(result.ledger, structuredClone(record.proof));
  return result;
}

// A paired publisher can retain historical facts across its fresh owning reads.
// This private brand belongs only to the original, fully authenticated ledger.
// Current proofs, additional fragments and capabilities are never memo records.
const pairedHistoricalMemos = new WeakMap();
export function readPairedSourceHistory(root) {
  const memo = historicalMemo(root);
  const result = readOwnedSurfaceHistory(
    root,
    undefined,
    [],
    [],
    false,
    false,
    false,
    false,
    false,
    false,
    false,
    memo,
  );
  pairedHistoricalMemos.set(result.ledger, memo);
  return result;
}
function pairedHistoricalMemo(root, previous) {
  const memo = pairedHistoricalMemos.get(previous);
  const proof = sourceReaderCapabilities.get(previous);
  memo?.historyReader?.assertCurrent();
  if (
    !memo ||
    memo.root !== resolve(root) ||
    !proof ||
    !proof.publishedOnly ||
    proof.root !== resolve(root) ||
    proof.historyTrust !== (memo.historyReader?.trustDigest ?? null) ||
    proof.snapshot !== digest(previous)
  )
    throw new Error("SOURCE_HEAD_CONTINUATION_AUTHENTIC_READER_REQUIRED");
  return memo;
}
export function readPairedSourceHistoryCurrent(root, previous) {
  return readOwnedSurfaceHistory(
    root,
    undefined,
    [],
    [],
    false,
    false,
    false,
    false,
    false,
    false,
    false,
    pairedHistoricalMemo(root, previous),
  );
}

// An evolution transaction retains its one native current read, never a cached
// current proof. Every use checks live bytes/context and committed dependencies.
const evolutionReaders = new WeakMap();
function evolutionContext(root) {
  const git = (args) => execFileSync("/usr/bin/git", args, { ...GIT_OPTIONS, cwd: root }).trim();
  const mergePath = resolve(root, git(["rev-parse", "--git-path", "MERGE_HEAD"]));
  return {
    head: git(["rev-parse", "--verify", "HEAD^{commit}"]),
    merge: existsSync(mergePath) ? readFileSync(mergePath, "utf8") : null,
  };
}
function evolutionBaseMetadataSnapshot(
  root,
  revision,
  legacy,
  historyReader = openInstalledHistoryReader(resolve(root)),
) {
  if (historyReader) return historyReader.readSnapshot(revision).identity;
  const git = (args) =>
    execFileSync("/usr/bin/git", args, { ...GIT_OPTIONS, cwd: root, encoding: null });
  const commit = authenticatedGitBatch(root, [revision]).get(revision);
  if (commit.type !== "commit") memoFailure();
  const tree = /^tree ([a-f0-9]{40})\n/u.exec(commit.bytes.toString("utf8"))?.[1];
  if (!tree) memoFailure();
  const paths = [
    "apps/api/src/modules/access-control/permission-identity-history.json",
    ...(legacy ? [LEGACY_LEDGER_PATH, LEGACY_BASELINE_PATH] : []),
  ];
  const inventory = git(["ls-tree", "-r", "-t", "-z", revision, "--", ...paths]);
  const items = inventory
    .toString("utf8")
    .split("\0")
    .filter(Boolean)
    .map((line) => {
      const match = /^(040000 tree|100644 blob|100755 blob) ([a-f0-9]{40})\t(.+)$/u.exec(line);
      if (!match) memoFailure();
      const [mode, type] = match[1].split(" "),
        path = match[3];
      if (
        type === "tree"
          ? !paths.some((target) => target.startsWith(path + "/"))
          : !paths.includes(path)
      )
        memoFailure();
      return { mode, type, id: match[2], path };
    });
  const objects = authenticatedGitBatch(root, [
    ...new Set([tree, ...items.map((item) => item.id)]),
  ]);
  if (objects.get(tree)?.type !== "tree") memoFailure();
  const identity = createHash("sha256").update(commit.bytes).update(inventory);
  let size = 0;
  for (const [id, object] of objects) {
    size += object.bytes.length;
    if (size > 128 * 1024 * 1024) memoFailure();
    identity.update(`${id} ${object.type} ${object.bytes.length}\0`).update(object.bytes);
  }
  for (const item of items) if (objects.get(item.id)?.type !== item.type) memoFailure();
  return identity.digest("hex");
}
export function readEvolutionSurfaceHistory(root) {
  root = realpathSync(root);
  const context = evolutionContext(root),
    memo = historicalMemo(root);
  const current = readOwnedSurfaceHistory(
    root,
    undefined,
    [],
    [],
    false,
    false,
    false,
    false,
    false,
    false,
    false,
    memo,
  );
  evolutionReaders.set(current, {
    root,
    context,
    memo,
    snapshot: digest(current.ledger),
    baseline: digest(current.baseline),
    reconciliations: digest(current.reconciliations),
    files: [...current.files],
    additionalDependencies: new Map(),
    baseMetadata: new Map(),
    identityHistory: readFileSync(
      resolve(root, "apps/api/src/modules/access-control/permission-identity-history.json"),
      "utf8",
    ),
  });
  assertEvolutionSurfaceReaderCurrent(root, current);
  return current;
}
export function assertEvolutionSurfaceReaderCurrent(root, current) {
  const record = evolutionReaders.get(current);
  if (!record || record.root !== realpathSync(root))
    throw new Error("PERMISSION_EVOLUTION_AUTHENTIC_READER_REQUIRED");
  record.memo.historyReader?.assertCurrent();
  if (!record.memo.historyReader && openInstalledHistoryReader(record.root)) memoFailure();
  const filesField = Object.getOwnPropertyDescriptor(current, "files");
  if (
    !filesField ||
    !Object.hasOwn(filesField, "value") ||
    !hasPlainRegistryContainers(filesField.value)
  )
    throw new Error("PERMISSION_EVOLUTION_READER_CHANGED");
  const captured = surfaceReaderComparisonSnapshot(current);
  const files = [...Map.prototype.entries.call(captured.files)];
  const proof = sourceReaderCapabilities.get(captured.ledger);
  const reconciliation = Object.getOwnPropertyDescriptor(current, "reconciliations");
  if (
    !proof ||
    !proof.publishedOnly ||
    proof.root !== record.root ||
    captured.legacy ||
    !reconciliation ||
    !Object.hasOwn(reconciliation, "value") ||
    !hasPlainRegistryContainers(captured.ledger) ||
    !hasPlainRegistryContainers(captured.baseline) ||
    !hasPlainRegistryContainers(reconciliation.value) ||
    digest(captured.ledger) !== record.snapshot ||
    digest(captured.baseline) !== record.baseline ||
    digest(reconciliation.value) !== record.reconciliations ||
    files.some(([path, text]) => typeof path !== "string" || typeof text !== "string") ||
    stable(files) !== stable(record.files) ||
    proof.snapshot !== record.snapshot ||
    proof.baseline !== record.baseline ||
    stable(proof.files) !== stable(record.files)
  )
    throw new Error("PERMISSION_EVOLUTION_READER_CHANGED");
  if (
    readFileSync(
      resolve(record.root, "apps/api/src/modules/access-control/permission-identity-history.json"),
      "utf8",
    ) !== record.identityHistory
  )
    throw new Error("PERMISSION_EVOLUTION_IDENTITY_HISTORY_CHANGED");
  if (stable(evolutionContext(record.root)) !== stable(record.context))
    throw new Error("PERMISSION_EVOLUTION_GIT_CONTEXT_CHANGED");
  const paths = [
    SEED_LEDGER,
    SEED_BASELINE,
    ...readdirSync(resolve(record.root, FRAGMENTS)).map((name) => `${FRAGMENTS}/${name}`),
  ].sort();
  if (
    paths.length !== record.files.length ||
    record.files.some(
      ([path, text]) =>
        !paths.includes(path) ||
        realpathSync(resolve(record.root, path)) !== resolve(record.root, path) ||
        !lstatSync(resolve(record.root, path)).isFile() ||
        readFileSync(resolve(record.root, path), "utf8") !== text,
    )
  )
    throw new Error("PERMISSION_EVOLUTION_HISTORY_CHANGED");
  // Reauthenticate all facts used by the native current read, including parents
  // not needed by the target comparison, without reassembling current history.
  const dependencies = new Map(record.additionalDependencies);
  for (const cached of record.memo.records.values())
    for (const [revision, identity] of cached.dependencies) {
      if (dependencies.has(revision) && dependencies.get(revision) !== identity) memoFailure();
      dependencies.set(revision, identity);
    }
  for (const [revision, identity] of dependencies)
    if (committedSnapshot(record.root, revision, record.memo.historyReader)?.identity !== identity)
      memoFailure();
  for (const [revision, metadata] of record.baseMetadata)
    if (
      evolutionBaseMetadataSnapshot(
        record.root,
        revision,
        metadata.legacy,
        record.memo.historyReader,
      ) !== metadata.identity
    )
      memoFailure();
}
export function readEvolutionSurfaceHistoryBase(root, baseSha, current) {
  assertEvolutionSurfaceReaderCurrent(root, current);
  if (!/^[a-f0-9]{40}$/u.test(baseSha)) throw new Error("INVALID_PERMISSION_REGISTRY_BASE");
  const record = evolutionReaders.get(current);
  baseSha = record.memo.historyReader?.classifyPhysicalRevision(baseSha) ?? baseSha;
  const snapshot = committedSnapshot(record.root, baseSha, record.memo.historyReader);
  if (snapshot) record.additionalDependencies.set(baseSha, snapshot.identity);
  record.baseMetadata.set(baseSha, {
    legacy: !snapshot,
    identity: evolutionBaseMetadataSnapshot(
      record.root,
      baseSha,
      !snapshot,
      record.memo.historyReader,
    ),
  });
  const previous = readOwnedSurfaceHistory(
    record.root,
    baseSha,
    current.reconciliations,
    [],
    false,
    false,
    false,
    false,
    false,
    false,
    false,
    record.memo,
  );
  assertEvolutionSurfaceReaderCurrent(root, current);
  return previous;
}

/** Read either the working history or a historical Git tree (including pre-migration trees). */
export function readSurfaceHistory(
  root,
  revision,
  inheritedReconciliations = [],
  additionalFragments = [],
) {
  const memo = historicalMemo(root);
  if (revision !== undefined && memo.historyReader)
    revision = memo.historyReader.classifyPhysicalRevision(revision);
  return readOwnedSurfaceHistory(
    root,
    revision,
    inheritedReconciliations,
    additionalFragments,
    false,
    false,
    false,
    false,
    false,
    false,
    false,
    memo,
  );
}
function readOwnedSurfaceHistory(
  root,
  revision,
  inheritedReconciliations,
  additionalFragments,
  constructorOwned,
  structuralParent = false,
  continuationParent = false,
  compositionParent = false,
  publicationOwned = false,
  nonissuing = false,
  catchupParent = false,
  memo = historicalMemo(root),
  parentRole,
) {
  if (parentRole !== undefined && parentRole !== TAIL_PARENT_ROLE) memoFailure();
  if (memo.root !== resolve(root)) memoFailure();
  memo.historyReader?.assertCurrent();
  if (!memo.historyReader && openInstalledHistoryReader(resolve(root))) memoFailure();
  if (revision === undefined && memo.historyReader) {
    const currentHead = evolutionContext(root).head;
    if (!memo.historyReader.isPhysicalAncestor(memo.historyReader.publicationTip, currentHead))
      memoFailure();
  }
  if (revision !== undefined && !/^[a-f0-9]{40}$/u.test(revision)) {
    throw new Error("INVALID_PERMISSION_REGISTRY_BASE");
  }
  if (
    !revision &&
    !publicationOwned &&
    existsSync(resolve(root, ".permission-structural-composition-lock"))
  )
    throw new Error("PERMISSION_STRUCTURAL_COMPOSITION_PUBLICATION_IN_PROGRESS");
  const cacheable =
    revision !== undefined && !inheritedReconciliations.length && !additionalFragments.length;
  const snapshot =
    revision !== undefined && (cacheable || memo.historyReader)
      ? committedSnapshot(root, revision, memo.historyReader)
      : null;
  const memoKey = `${revision}:${[constructorOwned, structuralParent, continuationParent, compositionParent, publicationOwned, nonissuing, catchupParent, parentRole === TAIL_PARENT_ROLE].join(",")}`;
  if (snapshot) {
    const record = cacheable ? memo.records.get(memoKey) : null;
    if (record) return restoreHistorical(memo, record, snapshot, revision);
    rememberDependency(memo, revision, snapshot.identity);
  }
  const frame = snapshot ? new Map([[revision, snapshot.identity]]) : null;
  if (frame) memo.frames.push(frame);
  try {
    const result = readUncachedOwnedSurfaceHistory(
      root,
      revision,
      inheritedReconciliations,
      additionalFragments,
      constructorOwned,
      structuralParent,
      continuationParent,
      compositionParent,
      publicationOwned,
      nonissuing,
      catchupParent,
      memo,
      snapshot,
      parentRole,
    );
    if (snapshot && cacheable) {
      if (
        getSourceHeadSelections(result.ledger).length ||
        sourceReaderCapabilities.has(result.ledger)
      )
        memoFailure();
      if (memo.records.size >= 64) memoFailure();
      memo.records.set(memoKey, {
        result: structuredClone(result),
        proof: structuralReaderProofs.has(result.ledger)
          ? structuredClone(structuralReaderProofs.get(result.ledger))
          : null,
        dependencies: new Map(frame),
      });
    }
    return result;
  } finally {
    if (frame && memo.frames.pop() !== frame) memoFailure();
  }
}
function readUncachedOwnedSurfaceHistory(
  root,
  revision,
  inheritedReconciliations,
  additionalFragments,
  constructorOwned,
  structuralParent,
  continuationParent,
  compositionParent,
  publicationOwned,
  nonissuing,
  catchupParent,
  memo,
  snapshot,
  parentRole,
) {
  if (memo.root !== resolve(root)) memoFailure();
  if (revision !== undefined && !/^[a-f0-9]{40}$/u.test(revision)) {
    throw new Error("INVALID_PERMISSION_REGISTRY_BASE");
  }
  if (
    !revision &&
    !publicationOwned &&
    existsSync(resolve(root, ".permission-structural-composition-lock"))
  )
    throw new Error("PERMISSION_STRUCTURAL_COMPOSITION_PUBLICATION_IN_PROGRESS");
  const git = (args) => execFileSync("/usr/bin/git", args, { ...GIT_OPTIONS, cwd: root });
  const files = new Map();
  let parentBytes = 0;
  const read = (path) => {
    const text = revision
      ? snapshot
        ? snapshot.files.get(path)
        : memo.historyReader
          ? memo.historyReader.readFile(revision, path)?.toString("utf8")
          : git(["show", `${revision}:${path}`])
      : readFileSync(resolve(root, path), "utf8");
    if (
      (structuralParent ||
        continuationParent ||
        compositionParent ||
        catchupParent ||
        parentRole === TAIL_PARENT_ROLE) &&
      (files.size >= 2000 || (parentBytes += Buffer.byteLength(text)) > 128 * 1024 * 1024)
    )
      throw new Error("PERMISSION_STRUCTURAL_MERGE_BUDGET_EXCEEDED");
    files.set(path, text);
    return JSON.parse(text);
  };
  const paths = revision
    ? memo.historyReader
      ? memo.historyReader
          .readSnapshot(revision)
          .inventory.map(({ path }) => path)
          .filter((path) => path.startsWith(SURFACE_HISTORY_PATH + "/"))
      : git(["ls-tree", "-r", "--name-only", revision, "--", SURFACE_HISTORY_PATH])
          .trim()
          .split("\n")
          .filter(Boolean)
    : null;
  if (revision && !paths.includes(SEED_LEDGER)) {
    // Kept only for evolution comparison across the one-time storage migration.
    return {
      ledger: read(LEGACY_LEDGER_PATH),
      baseline: read(LEGACY_BASELINE_PATH),
      files,
      legacy: true,
    };
  }
  const ledger = read(SEED_LEDGER);
  const baseline = read(SEED_BASELINE);
  const fragmentPaths = paths
    ? paths.filter((path) => path.startsWith(`${FRAGMENTS}/`))
    : existsSync(resolve(root, FRAGMENTS))
      ? readdirSync(resolve(root, FRAGMENTS)).map((name) => `${FRAGMENTS}/${name}`)
      : [];
  const fragments = fragmentPaths.sort().map((path) => {
    if (!new RegExp(`^${FRAGMENTS}/[a-f0-9]{64}\\.json$`, "u").test(path)) {
      throw new Error(`INVALID_PERMISSION_SURFACE_FRAGMENT_PATH ${path}`);
    }
    const fragment = read(path);
    if (path !== `${FRAGMENTS}/${digest(fragment)}.json`) {
      throw new Error(`PERMISSION_SURFACE_FRAGMENT_HASH_MISMATCH ${path}`);
    }
    return fragment;
  });
  const fullFragments = [...fragments, ...additionalFragments];
  // A14 historical comparison requires the exact live owning union that issued
  // its private capability, not another repository or a superseded file set.
  if (revision !== undefined)
    for (const evidence of inheritedReconciliations) {
      const owner = evidence?.unionEvidence ? evidence : unionOwners.get(evidence);
      const record = validatedUnions.get(owner);
      if (!record?.structuralMerge?.continuation) continue;
      const actualPaths = [
        SEED_LEDGER,
        SEED_BASELINE,
        ...readdirSync(resolve(root, FRAGMENTS)).map((name) => `${FRAGMENTS}/${name}`),
      ].sort();
      if (
        record.readerRoot !== resolve(root) ||
        !record.snapshot.bytes ||
        actualPaths.length !== record.snapshot.bytes.length ||
        record.snapshot.bytes.some(
          ([path, text]) =>
            !actualPaths.includes(path) ||
            realpathSync(resolve(root, path)) !== resolve(root, path) ||
            !lstatSync(resolve(root, path)).isFile() ||
            readFileSync(resolve(root, path), "utf8") !== text,
        )
      )
        throw new Error("INVALID_PERMISSION_STRUCTURAL_ORIGIN_CONTINUATION");
    }
  let structuralMerge;
  let structuralParents;
  if (fullFragments.some((f) => f?.schemaVersion === 17)) {
    if (
      structuralParent ||
      continuationParent ||
      compositionParent ||
      catchupParent ||
      parentRole !== undefined
    )
      throw new Error("PERMISSION_STRUCTURAL_MERGE_RECURSIVE_PARENT");
    const extensions = fullFragments.filter((f) => f?.schemaVersion === 17);
    if (extensions.length !== 1 || extensions[0].structuralTailCompositions?.length !== 1)
      throw new Error("INVALID_PERMISSION_STRUCTURAL_TAIL_COMPOSITION");
    const receipt = extensions[0].structuralTailCompositions[0];
    if (
      stable(readTailMergeParents(root, receipt?.merge, memo.historyReader)) !==
      stable(receipt?.parents?.map((p) => p?.revision))
    )
      throw new Error("PERMISSION_STRUCTURAL_MERGE_PARENT_CONTEXT_CHANGED");
    const parents = readStructuralParents(
      root,
      receipt?.parents?.map((p) => p?.revision),
      files,
      false,
      false,
      false,
      memo,
      TAIL_PARENT_ROLE,
    );
    const inventory = revision
      ? (snapshot?.inventory ??
        git(["ls-tree", "-r", revision, "--", SURFACE_HISTORY_PATH])
          .trim()
          .split("\n")
          .filter(Boolean)
          .map(regularInventoryRow))
      : [...files.keys()].map((path) => ({
          path,
          mode: lstatSync(resolve(root, path)).mode & 0o111 ? "100755" : "100644",
        }));
    structuralMerge = validateStructuralTailComposition(
      ledger,
      fullFragments,
      parents,
      files,
      new Map(inventory.map((row) => [row.path, row.mode])),
    );
  } else if (fullFragments.some((f) => f?.schemaVersion === 16)) {
    if (structuralParent || continuationParent || compositionParent || catchupParent)
      throw new Error("PERMISSION_STRUCTURAL_MERGE_RECURSIVE_PARENT");
    const extensions = fullFragments.filter((f) => f?.schemaVersion === 16);
    if (extensions.length !== 1 || extensions[0].structuralMergeCatchups?.length !== 1)
      throw new Error("INVALID_PERMISSION_STRUCTURAL_CATCHUP");
    const receipt = extensions[0].structuralMergeCatchups[0];
    const parents = readStructuralParents(
      root,
      receipt?.parents?.map((p) => p?.revision),
      files,
      false,
      false,
      true,
      memo,
    );
    structuralMerge = validateStructuralCatchup(ledger, fullFragments, parents, files);
  } else if (fullFragments.some((f) => f?.schemaVersion === 15)) {
    if (structuralParent || continuationParent || compositionParent)
      throw new Error("PERMISSION_STRUCTURAL_MERGE_RECURSIVE_PARENT");
    const extensions = fullFragments.filter((f) => f?.schemaVersion === 15);
    if (extensions.length !== 1 || extensions[0].structuralMergeCompositions?.length !== 1)
      throw new Error("INVALID_PERMISSION_STRUCTURAL_COMPOSITION");
    const r = extensions[0].structuralMergeCompositions[0];
    const parents = readStructuralParents(
      root,
      r?.parents?.map((p) => p?.revision),
      files,
      false,
      true,
      false,
      memo,
    );
    structuralMerge = validateStructuralComposition(ledger, fullFragments, parents, files);
  } else if (fullFragments.some((f) => f?.schemaVersion === 14)) {
    if (structuralParent || continuationParent)
      throw new Error("PERMISSION_STRUCTURAL_MERGE_RECURSIVE_PARENT");
    const extensions = fullFragments.filter((f) => f?.schemaVersion === 14);
    if (extensions.length !== 1 || extensions[0].structuralMergeContinuations?.length !== 1)
      throw new Error("INVALID_PERMISSION_STRUCTURAL_ORIGIN_CONTINUATION");
    const r = extensions[0].structuralMergeContinuations[0];
    const parents = readStructuralParents(
      root,
      [r?.previous?.revision, r?.incoming?.revision],
      files,
      true,
      false,
      false,
      memo,
    );
    structuralMerge = validateStructuralOriginContinuation(
      ledger,
      fullFragments,
      parents[0],
      parents[1],
      files,
    );
  } else if (fullFragments.some((f) => f?.schemaVersion === 13)) {
    if (structuralParent) throw new Error("PERMISSION_STRUCTURAL_MERGE_RECURSIVE_PARENT");
    const extensions = fullFragments.filter((f) => f?.schemaVersion === 13);
    if (extensions.length !== 1 || extensions[0].structuralMergeExtensions?.length !== 1)
      throw new Error("INVALID_PERMISSION_STRUCTURAL_MERGE_EXTENSION");
    const revisions = extensions[0].structuralMergeExtensions[0]?.parents?.map((p) => p?.revision);
    structuralParents = readStructuralParents(root, revisions, files, false, false, false, memo);
  }
  if (structuralMerge || fullFragments.some((f) => f?.schemaVersion === 13)) {
    if (
      files.size + additionalFragments.length > 2000 ||
      [...files.values()].reduce((n, text) => n + Buffer.byteLength(text), 0) > 128 * 1024 * 1024
    )
      throw new Error("PERMISSION_STRUCTURAL_MERGE_BUDGET_EXCEEDED");
    if (!revision)
      for (const path of files.keys()) {
        const target = resolve(root, path);
        if (realpathSync(target) !== target || !lstatSync(target).isFile())
          throw new Error("PERMISSION_STRUCTURAL_MERGE_FILE_IDENTITY");
      }
  }
  if (!structuralMerge && fullFragments.some((f) => f?.schemaVersion === 13)) {
    structuralMerge = validateStructuralMerge(ledger, fullFragments, structuralParents, files);
  }
  const committedValues = new WeakSet();
  const knownBytes = (path, text) =>
    typeof text === "string" &&
    (snapshot?.files.get(path) === text ||
      [...memo.records.values()].some((record) => record.result.files.get(path) === text));
  for (const [path, value] of [
    [SEED_LEDGER, ledger],
    [SEED_BASELINE, baseline],
    ...fragments.map((fragment) => [`${FRAGMENTS}/${canonicalDigest(fragment)}.json`, fragment]),
  ])
    if (knownBytes(path, files.get(path))) committedValues.add(value);
  const readSealedSnapshot = (sealed) => {
    const pinned = sealed.revision;
    if (
      typeof pinned !== "string" ||
      !/^[a-f0-9]{40}$/u.test(pinned) ||
      pinned === revision ||
      memo.sealedSnapshots.has(pinned) ||
      memo.sealedSnapshots.size >= MAX_SNAPSHOT_DEPTH
    )
      compositionFailure();
    // Complete canonical inventory, regular Git objects and byte budgets are
    // authenticated by committedSnapshot/readOwned, not by public JSON claims.
    memo.sealedSnapshots.add(pinned);
    try {
      const parent = readOwnedSurfaceHistory(
        root,
        pinned,
        [],
        [],
        false,
        false,
        false,
        false,
        false,
        true,
        false,
        memo,
      );
      const expectedPaths = [
        SEED_LEDGER,
        SEED_BASELINE,
        ...sealed.fragments.map((hash) => `${FRAGMENTS}/${hash}.json`),
      ];
      if (
        parent.legacy ||
        !exactSet([...parent.files.keys()], expectedPaths) ||
        expectedPaths.some((path) => parent.files.get(path) !== files.get(path))
      )
        compositionFailure();
    } finally {
      memo.sealedSnapshots.delete(pinned);
    }
  };
  const result = assembleSurfaceHistory(ledger, baseline, fullFragments, inheritedReconciliations, {
    [CANONICAL_COMPUTATIONS]: committedValues,
    historicalProjection: revision !== undefined,
    [READER_FILES]: files,
    [READER_ROOT]: resolve(root),
    [STRUCTURAL_MERGE_PROOF]: structuralMerge,
    [SEALED_SNAPSHOT_READER]: readSealedSnapshot,
    ...(nonissuing ||
    (structuralMerge?.continuation && additionalFragments.length && !constructorOwned)
      ? { [VALIDATING_UNION]: true }
      : {}),
  });
  if (
    !revision &&
    !publicationOwned &&
    existsSync(resolve(root, ".permission-structural-composition-lock"))
  )
    throw new Error("PERMISSION_STRUCTURAL_COMPOSITION_PUBLICATION_IN_PROGRESS");
  if (structuralMerge) structuralReaderProofs.set(result.ledger, structuralMerge);
  if (
    !nonissuing &&
    revision === undefined &&
    (additionalFragments.length === 0 || constructorOwned)
  ) {
    const selections = structuralMerge
      ? validateStructuralSourceHeadContinuations(
          fullFragments,
          result.ledger,
          structuralMerge.origin,
        )
      : validateSourceHeadContinuations(fullFragments, result.ledger);
    if (selections.length)
      sourceHeadCapabilities.set(result.ledger, {
        snapshot: digest(result.ledger),
        selections,
        // Private complete chain anchors; getter exposes only checked selectors.
        anchors: [...fragments, ...additionalFragments]
          .filter((f) => [11, 12, 13, 14, 15, 16, 17].includes(f.schemaVersion))
          .map((f) => ({ schemaVersion: f.schemaVersion, fragment: digest(f) }))
          .sort((a, b) => a.fragment.localeCompare(b.fragment)),
      });
    sourceReaderCapabilities.set(result.ledger, {
      root: resolve(root),
      historyTrust: memo.historyReader?.trustDigest ?? null,
      historyReader: memo.historyReader,
      snapshot: digest(result.ledger),
      baseline: digest(result.baseline),
      files: [...files].map(([path, text]) => [path, text]),
      publishedOnly: additionalFragments.length === 0,
    });
  }
  return { ...result, files, legacy: false };
}

function regularInventoryRow(line) {
  const match = /^(100644|100755) blob ([a-f0-9]{40})\t(.+)$/u.exec(line);
  if (
    !match ||
    (![SEED_LEDGER, SEED_BASELINE].includes(match[3]) &&
      !new RegExp(`^${FRAGMENTS}/[a-f0-9]{64}\\.json$`, "u").test(match[3]))
  )
    throw new Error("PERMISSION_STRUCTURAL_MERGE_PARENT_INVENTORY_INVALID");
  return { mode: match[1], blob: match[2], path: match[3] };
}

// Only this module can attach the private proof to assembly. Both parent
// ledgers are computed from actual immutable Git blobs by the original reader.
function readStructuralParents(
  root,
  revisions,
  currentFiles,
  continuation = false,
  composition = false,
  catchup = false,
  memo = historicalMemo(root),
  parentRole,
) {
  if (
    !Array.isArray(revisions) ||
    revisions.length !== 2 ||
    revisions[0] === revisions[1] ||
    revisions.some((r) => !/^[a-f0-9]{40}$/u.test(r))
  )
    throw new Error("INVALID_PERMISSION_STRUCTURAL_MERGE_PARENTS");
  return revisions.map((revision, index) => {
    const activeSnapshot = memo.historyReader
      ? committedSnapshot(root, revision, memo.historyReader)
      : null;
    if (memo.historyReader && !activeSnapshot)
      throw new Error("PERMISSION_STRUCTURAL_MERGE_PARENT_INVENTORY_INVALID");
    const git = (args) => execFileSync("/usr/bin/git", args, { ...GIT_OPTIONS, cwd: root });
    if (
      !memo.historyReader &&
      git(["rev-parse", "--verify", `${revision}^{commit}`]).trim() !== revision
    )
      throw new Error("INVALID_PERMISSION_STRUCTURAL_MERGE_PARENTS");
    const paths = activeSnapshot
      ? [...activeSnapshot.files.keys()]
      : git(["ls-tree", "-r", "--name-only", revision, "--", SURFACE_HISTORY_PATH])
          .trim()
          .split("\n")
          .filter(Boolean);
    if (paths.length > 2000) throw new Error("PERMISSION_STRUCTURAL_MERGE_BUDGET_EXCEEDED");
    // A structural parent is a complete committed inventory, not a filtered
    // seed/fragment sample. Unknown files and nonregular Git objects refuse.
    const inventory = activeSnapshot
      ? activeSnapshot.inventory.map(({ path, mode, blob }) => `${mode} blob ${blob}\t${path}`)
      : git(["ls-tree", "-r", revision, "--", SURFACE_HISTORY_PATH])
          .trim()
          .split("\n")
          .filter(Boolean);
    if (inventory.length !== paths.length)
      throw new Error("PERMISSION_STRUCTURAL_MERGE_PARENT_INVENTORY_INVALID");
    const inventoryRows = inventory.map(regularInventoryRow);
    const previousContinuation = continuation && index === 0;
    const previousCatchup = catchup && index === 0;
    const parent = readOwnedSurfaceHistory(
      root,
      revision,
      [],
      [],
      false,
      !previousContinuation && !composition && !catchup && parentRole !== TAIL_PARENT_ROLE,
      previousContinuation,
      composition || (catchup && index === 1),
      false,
      false,
      previousCatchup,
      memo,
      parentRole,
    );
    if (parent.files.size !== paths.length || paths.some((path) => !parent.files.has(path)))
      throw new Error("PERMISSION_STRUCTURAL_MERGE_PARENT_INVENTORY_INVALID");
    for (const path of [SEED_LEDGER, SEED_BASELINE])
      if (parent.files.get(path) !== currentFiles.get(path))
        throw new Error("PERMISSION_STRUCTURAL_MERGE_SEED_CHANGED");
    return {
      ...parent,
      revision,
      inventory: inventoryRows,
      structuralProof: structuralReaderProofs.get(parent.ledger),
      fragments: [...parent.files]
        .filter(([p]) => p.startsWith(`${FRAGMENTS}/`))
        .map(([, text]) => JSON.parse(text)),
    };
  });
}

// Publication decisions are CLI/working-Git physical IDs. Immutable receipts
// keep logical IDs; normalize once before their native constructors run.
function publicationDocument(root, document, kind) {
  const reader = openInstalledHistoryReader(resolve(root));
  if (!reader) return document;
  const result = structuredClone(document);
  if (kind === "origin") {
    result.previous = reader.classifyPhysicalRevision(result.previous);
    result.incoming = reader.classifyPhysicalRevision(result.incoming);
  } else {
    if (!Array.isArray(result.parents))
      throw new Error("INVALID_PERMISSION_STRUCTURAL_MERGE_PARENTS");
    result.parents = result.parents.map((id) => reader.classifyPhysicalRevision(id));
    if (kind === "tail") result.merge = reader.classifyPhysicalRevision(result.merge);
  }
  return result;
}

/** Checked pure candidate; it does not publish or issue current source authority. */
export function buildStructuralMergeCandidate(root, document) {
  document = publicationDocument(root, document, "parents");
  const git = (args) => execFileSync("/usr/bin/git", args, { ...GIT_OPTIONS, cwd: root });
  const reader = openInstalledHistoryReader(resolve(root));
  const actualParents = [
    git(["rev-parse", "HEAD"]).trim(),
    git(["rev-parse", "MERGE_HEAD"]).trim(),
  ].map((id) => (reader ? reader.classifyPhysicalRevision(id) : id));
  if (stable(document?.parents) !== stable(actualParents))
    throw new Error("PERMISSION_STRUCTURAL_MERGE_PARENT_CONTEXT_CHANGED");
  const seedText = readFileSync(resolve(root, SEED_LEDGER), "utf8");
  const baselineText = readFileSync(resolve(root, SEED_BASELINE), "utf8");
  const parents = readStructuralParents(
    root,
    document.parents,
    new Map([
      [SEED_LEDGER, seedText],
      [SEED_BASELINE, baselineText],
    ]),
  );
  const fragment = constructStructuralMerge(JSON.parse(seedText), parents, document);
  const result = readOwnedSurfaceHistory(root, undefined, [], [fragment], false);
  return { ...result, fragment };
}

const compositionCandidates = new WeakMap();
function checkedCompositionReconciliations(reconciliations) {
  if (
    !Array.isArray(reconciliations) ||
    reconciliations.length > 16 ||
    new Set(reconciliations.map(digest)).size !== reconciliations.length ||
    reconciliations.some((f) => {
      const key = {
        2: "reconciliations",
        3: "spliceReconciliations",
        4: "compositionReconciliations",
      }[f?.schemaVersion];
      return (
        !key ||
        !exactKeys(f, ["entries", "schemaVersion", key, "transitions"].sort().join(",")) ||
        !Array.isArray(f.entries) ||
        f.entries.length ||
        !Array.isArray(f.transitions) ||
        f.transitions.length ||
        !Array.isArray(f[key]) ||
        !f[key].length
      );
    })
  )
    throw new Error("INVALID_PERMISSION_STRUCTURAL_COMPOSITION_RECONCILIATIONS");
}
function constructOwnedStructuralComposition(
  root,
  document,
  reconciliations,
  publicationOwned = false,
) {
  checkedCompositionReconciliations(reconciliations);
  const git = (args) => execFileSync("/usr/bin/git", args, { ...GIT_OPTIONS, cwd: root });
  const reader = openInstalledHistoryReader(resolve(root));
  if (
    stable(document?.parents) !==
    stable(
      [git(["rev-parse", "HEAD"]).trim(), git(["rev-parse", "MERGE_HEAD"]).trim()].map((id) =>
        reader ? reader.classifyPhysicalRevision(id) : id,
      ),
    )
  )
    throw new Error("PERMISSION_STRUCTURAL_MERGE_PARENT_CONTEXT_CHANGED");
  const files = new Map(
    [SEED_LEDGER, SEED_BASELINE].map((path) => [path, readFileSync(resolve(root, path), "utf8")]),
  );
  const parents = readStructuralParents(root, document.parents, files, false, true);
  const fragment = constructStructuralComposition(
    JSON.parse(files.get(SEED_LEDGER)),
    parents,
    document,
  );
  const result = readOwnedSurfaceHistory(
    root,
    undefined,
    [],
    [fragment, ...reconciliations],
    false,
    false,
    false,
    false,
    publicationOwned,
    true,
  );
  return { ...result, fragment, fragments: [fragment, ...reconciliations] };
}
/** Owns real Git snapshots; candidate has no source or historical evolution authority. */
export function buildStructuralCompositionCandidate(root, document, reconciliations = []) {
  document = publicationDocument(root, document, "parents");
  const result = constructOwnedStructuralComposition(root, document, reconciliations);
  compositionCandidates.set(result, {
    root: resolve(root),
    snapshot: digest(result),
    document: structuredClone(document),
    reconciliations: structuredClone(reconciliations),
  });
  return result;
}
/** Revalidation under the publisher's fail-closed lock remains nonissuing. */
export function recheckStructuralCompositionCandidate(root, result, { installed = false } = {}) {
  const record = compositionCandidates.get(result);
  if (!record || record.root !== resolve(root) || digest(result) !== record.snapshot)
    throw new Error("PERMISSION_STRUCTURAL_COMPOSITION_AUTHENTIC_CANDIDATE_REQUIRED");
  return installed
    ? readOwnedSurfaceHistory(root, undefined, [], [], false, false, false, false, true, true)
    : constructOwnedStructuralComposition(root, record.document, record.reconciliations, true);
}

function constructOwnedStructuralCatchup(
  root,
  document,
  reconciliations,
  publicationOwned = false,
  memo = historicalMemo(root),
) {
  checkedCompositionReconciliations(reconciliations);
  const git = (args) => execFileSync("/usr/bin/git", args, { ...GIT_OPTIONS, cwd: root });
  const reader = memo.historyReader;
  if (
    stable(document?.parents) !==
    stable(
      [git(["rev-parse", "HEAD"]).trim(), git(["rev-parse", "MERGE_HEAD"]).trim()].map((id) =>
        reader ? reader.classifyPhysicalRevision(id) : id,
      ),
    )
  )
    throw new Error("PERMISSION_STRUCTURAL_MERGE_PARENT_CONTEXT_CHANGED");
  const files = new Map(
    [SEED_LEDGER, SEED_BASELINE].map((path) => [path, readFileSync(resolve(root, path), "utf8")]),
  );
  const parents = readStructuralParents(root, document.parents, files, false, false, true, memo);
  const fragment = constructStructuralCatchup(
    JSON.parse(files.get(SEED_LEDGER)),
    parents,
    document,
  );
  const result = readOwnedSurfaceHistory(
    root,
    undefined,
    [],
    [fragment, ...reconciliations],
    false,
    false,
    false,
    false,
    publicationOwned,
    true,
    false,
    memo,
  );
  return { ...result, fragment, fragments: [fragment, ...reconciliations] };
}
/** Owns real Git snapshots; candidate has no source or historical evolution authority. */
export function buildStructuralCatchupCandidate(root, document, reconciliations = []) {
  document = publicationDocument(root, document, "parents");
  const memo = historicalMemo(root);
  const result = constructOwnedStructuralCatchup(root, document, reconciliations, false, memo);
  catchupCandidates.set(result, {
    memo,
    root: resolve(root),
    snapshot: digest(result),
    document: structuredClone(document),
    reconciliations: structuredClone(reconciliations),
  });
  return result;
}
/** Revalidation under the publisher's fail-closed lock remains nonissuing. */
export function recheckStructuralCatchupCandidate(root, result, { installed = false } = {}) {
  const record = catchupCandidates.get(result);
  if (!record || record.root !== resolve(root) || digest(result) !== record.snapshot)
    throw new Error("PERMISSION_STRUCTURAL_CATCHUP_AUTHENTIC_CANDIDATE_REQUIRED");
  return installed
    ? readOwnedSurfaceHistory(
        root,
        undefined,
        [],
        [],
        false,
        false,
        false,
        false,
        true,
        true,
        false,
        record.memo,
      )
    : constructOwnedStructuralCatchup(
        root,
        record.document,
        record.reconciliations,
        true,
        record.memo,
      );
}

function readTailMergeParents(
  root,
  merge,
  historyReader = openInstalledHistoryReader(resolve(root)),
) {
  if (!/^[a-f0-9]{40}$/u.test(merge))
    throw new Error("INVALID_PERMISSION_STRUCTURAL_MERGE_PARENTS");
  if (historyReader) {
    const parents = historyReader.readLogicalParents(merge);
    if (parents.length !== 2 || parents[0] === parents[1])
      throw new Error("INVALID_PERMISSION_STRUCTURAL_MERGE_PARENTS");
    return parents;
  }
  const git = (args) => execFileSync("/usr/bin/git", args, { ...GIT_OPTIONS, cwd: root }).trim();
  if (git(["rev-parse", "--verify", `${merge}^{commit}`]) !== merge)
    throw new Error("INVALID_PERMISSION_STRUCTURAL_MERGE_PARENTS");
  const parents = git(["show", "-s", "--format=%P", merge]).split(" ");
  if (
    parents.length !== 2 ||
    parents[0] === parents[1] ||
    parents.some((p) => !/^[a-f0-9]{40}$/u.test(p))
  )
    throw new Error("INVALID_PERMISSION_STRUCTURAL_MERGE_PARENTS");
  return parents;
}
/** Exact named merge admission for publication. A later squash reader instead
 * authenticates the immutable merge witness and complete parent inventories. */
export function structuralTailParentContext(root, merge) {
  const reader = openInstalledHistoryReader(resolve(root));
  return logicalTailParentContext(
    root,
    reader ? reader.classifyPhysicalRevision(merge) : merge,
    reader,
  );
}
function logicalTailParentContext(root, merge, reader = openInstalledHistoryReader(resolve(root))) {
  const git = (args) =>
    execFileSync("/usr/bin/git", args, {
      ...GIT_OPTIONS,
      cwd: root,
      stdio: ["ignore", "pipe", "pipe"],
    }).trim();
  const parents = readTailMergeParents(root, merge, reader);
  const head = git(["rev-parse", "HEAD"]);
  if (reader) {
    if (!reader.isPhysicalAncestor(reader.resolveReceiptRevision(merge).physicalRevision, head))
      throw new Error("PERMISSION_STRUCTURAL_MERGE_PARENT_CONTEXT_CHANGED");
  } else git(["merge-base", "--is-ancestor", merge, head]);
  let incoming;
  try {
    incoming = git(["rev-parse", "--verify", "--quiet", "MERGE_HEAD"]);
  } catch (error) {
    if (error.status !== 1) throw error;
  }
  return { head, incoming: incoming ?? null, merge, parents };
}
function constructOwnedStructuralTailComposition(
  root,
  document,
  reconciliations,
  publicationOwned,
  memo,
) {
  checkedCompositionReconciliations(reconciliations);
  if (
    stable(document?.parents) !==
    stable(logicalTailParentContext(root, document?.merge, memo.historyReader).parents)
  )
    throw new Error("PERMISSION_STRUCTURAL_MERGE_PARENT_CONTEXT_CHANGED");
  const files = new Map(
    [SEED_LEDGER, SEED_BASELINE].map((p) => [p, readFileSync(resolve(root, p), "utf8")]),
  );
  const parents = readStructuralParents(
    root,
    document.parents,
    files,
    false,
    false,
    false,
    memo,
    TAIL_PARENT_ROLE,
  );
  const fragment = constructStructuralTailComposition(
    JSON.parse(files.get(SEED_LEDGER)),
    parents,
    document,
  );
  const result = readOwnedSurfaceHistory(
    root,
    undefined,
    [],
    [fragment, ...reconciliations],
    false,
    false,
    false,
    false,
    publicationOwned,
    true,
    false,
    memo,
  );
  const expected = new Map(parents.flatMap((p) => [...p.files]));
  if (
    result.files.size !== expected.size ||
    [...expected].some(([p, text]) => result.files.get(p) !== text)
  )
    throw new Error("PERMISSION_STRUCTURAL_TAIL_COMPOSITION_NOT_EXACT_PARENT_UNION");
  return { ...result, fragment, fragments: [fragment, ...reconciliations] };
}
/** No current source authority; only this reader owns authentic complete parents. */
export function buildStructuralTailCompositionCandidate(root, document, reconciliations = []) {
  document = publicationDocument(root, document, "tail");
  const memo = historicalMemo(root);
  const result = constructOwnedStructuralTailComposition(
    root,
    document,
    reconciliations,
    false,
    memo,
  );
  tailCompositionCandidates.set(result, {
    root: resolve(root),
    memo,
    snapshot: digest(result),
    document: structuredClone(document),
    reconciliations: structuredClone(reconciliations),
  });
  return result;
}
export function recheckStructuralTailCompositionCandidate(
  root,
  result,
  { installed = false } = {},
) {
  const record = tailCompositionCandidates.get(result);
  if (!record || record.root !== resolve(root) || digest(result) !== record.snapshot)
    throw new Error("PERMISSION_STRUCTURAL_TAIL_COMPOSITION_AUTHENTIC_CANDIDATE_REQUIRED");
  return installed
    ? readOwnedSurfaceHistory(
        root,
        undefined,
        [],
        [],
        false,
        false,
        false,
        false,
        true,
        true,
        false,
        record.memo,
      )
    : constructOwnedStructuralTailComposition(
        root,
        record.document,
        record.reconciliations,
        true,
        record.memo,
      );
}

/** Nonissuing exact-context continuation constructor; root owns reviewed publication. */
export function buildStructuralOriginContinuationCandidate(root, document, reconciliations = []) {
  document = publicationDocument(root, document, "origin");
  if (
    !Array.isArray(reconciliations) ||
    reconciliations.some(
      (f) =>
        !f ||
        ![2, 3, 4].includes(f.schemaVersion) ||
        !Array.isArray(f.entries) ||
        f.entries.length ||
        !Array.isArray(f.transitions) ||
        f.transitions.length ||
        !Array.isArray(
          f[
            { 2: "reconciliations", 3: "spliceReconciliations", 4: "compositionReconciliations" }[
              f.schemaVersion
            ]
          ],
        ) ||
        !f[
          { 2: "reconciliations", 3: "spliceReconciliations", 4: "compositionReconciliations" }[
            f.schemaVersion
          ]
        ].length,
    )
  )
    throw new Error("INVALID_PERMISSION_STRUCTURAL_ORIGIN_CONTINUATION_RECONCILIATIONS");
  const git = (args) => execFileSync("/usr/bin/git", args, { ...GIT_OPTIONS, cwd: root });
  const reader = openInstalledHistoryReader(resolve(root));
  const actual = (name) => {
    const id = git(["rev-parse", name]).trim();
    return reader ? reader.classifyPhysicalRevision(id) : id;
  };
  if (document?.previous !== actual("HEAD") || document?.incoming !== actual("MERGE_HEAD"))
    throw new Error("PERMISSION_STRUCTURAL_MERGE_PARENT_CONTEXT_CHANGED");
  const files = new Map(
    [SEED_LEDGER, SEED_BASELINE].map((path) => [path, readFileSync(resolve(root, path), "utf8")]),
  );
  const parents = readStructuralParents(root, [document.previous, document.incoming], files, true);
  const fragment = constructStructuralOriginContinuation(
    JSON.parse(files.get(SEED_LEDGER)),
    parents[0],
    parents[1],
    document,
  );
  const result = readOwnedSurfaceHistory(
    root,
    undefined,
    [],
    [fragment, ...reconciliations],
    false,
  );
  return { ...result, fragment };
}

/** Seed and published fragments are immutable, even when a rewrite reseals their hashes. */
export function assertSurfaceHistoryEvolution(previous, current) {
  if (current.legacy) throw new Error("PERMISSION_SURFACE_HISTORY_MISSING");
  if (previous.legacy) {
    for (const [path, value] of [
      [SEED_LEDGER, previous.ledger],
      [SEED_BASELINE, previous.baseline],
    ]) {
      if (stable(JSON.parse(current.files.get(path))) !== stable(value)) {
        throw new Error(`PERMISSION_SURFACE_MIGRATION_SEED_CHANGED ${path}`);
      }
    }
    return;
  }
  for (const [path, text] of previous.files) {
    if (current.files.get(path) !== text) {
      throw new Error(`PERMISSION_SURFACE_HISTORY_NOT_APPEND_ONLY ${path}`);
    }
  }
}

/** Persist only the reviewed delta. No common hash or predecessor file is rewritten. */
export function surfaceFragmentDelta(previousLedger, nextLedger) {
  const previous = new Map(previousLedger.entries.map((entry) => [entry.id, entry]));
  const nextIds = new Set(nextLedger.entries.map((entry) => entry.id));
  for (const id of previous.keys()) {
    if (!nextIds.has(id)) throw new Error(`PERMISSION_SURFACE_LEDGER_ENTRY_REMOVED ${id}`);
  }
  const entries = [];
  const transitions = [];
  for (const entry of nextLedger.entries) {
    const before = previous.get(entry.id);
    if (!before) {
      entries.push(entry);
      continue;
    }
    if (stable(before) === stable(entry)) continue;
    const { replacedBy, retiredBy, ...unchanged } = entry;
    if (
      before.replacedBy ||
      before.retiredBy ||
      stable(before) !== stable(unchanged) ||
      Boolean(replacedBy) === Boolean(retiredBy)
    ) {
      throw new Error(`PERMISSION_SURFACE_LEDGER_ENTRY_CHANGED ${entry.id}`);
    }
    transitions.push({
      id: entry.id,
      field: replacedBy ? "replacedBy" : "retiredBy",
      target: replacedBy ?? retiredBy,
    });
  }
  return { schemaVersion: 1, entries, transitions };
}
export function writeSurfaceFragment(root, previousLedger, nextLedger) {
  if (
    getSourceHeadSelections(previousLedger).some(
      (r) =>
        digest(previousLedger.entries.filter((e) => sourceHeadFamily(e.id) === r.family)) !==
        digest(nextLedger.entries.filter((e) => sourceHeadFamily(e.id) === r.family)),
    )
  )
    throw new Error("SOURCE_HEAD_CONTINUATION_PAIRED_PUBLICATION_REQUIRED");
  const fragment = surfaceFragmentDelta(previousLedger, nextLedger);
  if (!fragment.entries.length && !fragment.transitions.length) return null;
  const path = `${FRAGMENTS}/${digest(fragment)}.json`;
  mkdirSync(resolve(root, FRAGMENTS), { recursive: true });
  if (existsSync(resolve(root, path))) {
    if (stable(JSON.parse(readFileSync(resolve(root, path), "utf8"))) !== stable(fragment)) {
      throw new Error("PERMISSION_SURFACE_FRAGMENT_HASH_MISMATCH");
    }
  } else {
    writeFileSync(resolve(root, path), `${JSON.stringify(fragment, null, 2)}\n`, { flag: "wx" });
  }
  return path;
}

/** Capture plain data fields before any consumer-controlled lookup or iteration. */
export function surfaceReaderComparisonSnapshot(current) {
  if (!current || Object.getPrototypeOf(current) !== Object.prototype)
    throw new Error("PERMISSION_SURFACE_COMPARISON_CONTAINER_REQUIRED");
  const descriptors = Object.getOwnPropertyDescriptors(current);
  for (const name of ["ledger", "baseline", "files", "legacy"])
    if (!descriptors[name] || !Object.hasOwn(descriptors[name], "value"))
      throw new Error("PERMISSION_SURFACE_COMPARISON_CONTAINER_REQUIRED");
  const files = descriptors.files.value;
  if (!files || Object.getPrototypeOf(files) !== Map.prototype || Reflect.ownKeys(files).length)
    throw new Error("PERMISSION_SURFACE_COMPARISON_NATIVE_MAP_REQUIRED");
  return {
    ledger: descriptors.ledger.value,
    baseline: descriptors.baseline.value,
    files,
    legacy: descriptors.legacy.value,
  };
}

/** Accept only a published structural snapshot issued by this module's reader. */
export function assertStructuralSurfaceReaderSnapshot(current) {
  current = surfaceReaderComparisonSnapshot(current);
  const proof = sourceReaderCapabilities.get(current?.ledger);
  if (!proof || !proof.publishedOnly || !structuralReaderProofs.has(current?.ledger))
    throw new Error("PERMISSION_STRUCTURAL_MERGE_AUTHENTIC_READER_REQUIRED");
  proof.historyReader?.assertCurrent();
  if ((openInstalledHistoryReader(proof.root)?.trustDigest ?? null) !== proof.historyTrust)
    throw new Error("PERMISSION_STRUCTURAL_READER_SNAPSHOT_MISMATCH");
  let files;
  try {
    files = [...Map.prototype.entries.call(current.files)];
  } catch {
    throw new Error("PERMISSION_STRUCTURAL_READER_SNAPSHOT_MISMATCH");
  }
  if (
    digest(current.ledger) !== proof.snapshot ||
    digest(current.baseline) !== proof.baseline ||
    stable(files) !== stable(proof.files)
  )
    throw new Error("PERMISSION_STRUCTURAL_READER_SNAPSHOT_MISMATCH");
}

/** Snapshot is checked against disk, never against the caller-visible files Map. */
export function assertSourceHeadReaderCurrent(root, ledger) {
  const proof = sourceReaderCapabilities.get(ledger);
  if (
    !proof ||
    !proof.publishedOnly ||
    proof.root !== resolve(root) ||
    proof.snapshot !== digest(ledger)
  )
    throw new Error("SOURCE_HEAD_CONTINUATION_AUTHENTIC_READER_REQUIRED");
  proof.historyReader?.assertCurrent();
  const current = pairedHistoricalMemos.has(ledger)
    ? readPairedSourceHistoryCurrent(root, ledger)
    : readSurfaceHistory(root);
  const currentProof = sourceReaderCapabilities.get(current.ledger);
  if (
    !currentProof ||
    currentProof.historyTrust !== proof.historyTrust ||
    stable(currentProof.files) !== stable(proof.files) ||
    digest(current.ledger) !== proof.snapshot ||
    digest(current.baseline) !== proof.baseline
  )
    throw new Error("SOURCE_HEAD_CONTINUATION_HISTORY_CHANGED");
}
export function buildContinuedSourceLedger(root, previous, entries, document) {
  assertSourceHeadReaderCurrent(root, previous);
  if (
    !document ||
    Object.keys(document).sort().join(",") !== "schemaVersion,sourceHeadContinuations" ||
    document.schemaVersion !== 12 ||
    !getSourceHeadSelections(previous).length
  )
    throw new Error("INVALID_PERMISSION_SOURCE_HEAD_CONTINUATION");
  const next = buildLedgerFromEntries(structuredClone(entries), previous.legacyBoundaryCommit);
  const delta = surfaceFragmentDelta(previous, next);
  const fragment = {
    ...delta,
    schemaVersion: 12,
    sourceHeadContinuations: structuredClone(document.sourceHeadContinuations),
  };
  const assembled = readOwnedSurfaceHistory(
    root,
    undefined,
    [],
    [fragment],
    true,
    false,
    false,
    false,
    false,
    false,
    false,
    pairedHistoricalMemos.has(previous)
      ? pairedHistoricalMemo(root, previous)
      : historicalMemo(root),
  );
  if (stable(assembled.ledger) !== stable(next))
    throw new Error("SOURCE_HEAD_CONTINUATION_CANDIDATE_MISMATCH");
  // Never return a selected constructor result against guessed or stale source bytes.
  const inputs = readSourceInputs(root);
  const surfaces = discoverPermissionSurfaces(inputs);
  verifySurfaceLedger(surfaces, assembled.ledger, assembled.baseline);
  verifySurfaceBindingProofs(surfaces, assembled.ledger, inputs);
  return { ledger: assembled.ledger, fragment };
}
