#!/usr/bin/env node
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { readFileSync, realpathSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { openInstalledHistoryReader } from "./history-revision-io.mjs";

import {
  SURFACE_HISTORY_PATH,
  assembleSurfaceHistory,
  assertSurfaceHistoryEvolution,
  assertStructuralSurfaceReaderSnapshot,
  surfaceReaderComparisonSnapshot,
  readEvolutionSurfaceHistory,
  readEvolutionSurfaceHistoryBase,
  assertEvolutionSurfaceReaderCurrent,
} from "./surface-history.mjs";
import {
  buildLedgerFromEntries,
  buildLegacyBaselineAnchor,
  digest as canonicalDigest,
} from "./ledger-format.mjs";

export const SIG909_BOOTSTRAP_BASE_COMMIT = "096a460784ce3cfb2e82908467fb527cd47b8936";
export const PERMISSION_HISTORY_PATH =
  "apps/api/src/modules/access-control/permission-identity-history.json";
export const PERMISSION_SURFACE_BASELINE_PATH =
  "scripts/permission-registry/permission-surface-baseline.json";
export const PERMISSION_SURFACE_LEDGER_PATH =
  "scripts/permission-registry/permission-surface-ledger.json";

function parseJson(text, code) {
  try {
    return JSON.parse(text);
  } catch {
    throw new Error(code);
  }
}

function stable(value) {
  if (Array.isArray(value)) return `[${value.map(stable).join(",")}]`;
  if (value && typeof value === "object") {
    return `{${Object.entries(value)
      .sort(([left], [right]) => left.localeCompare(right))
      .map(([key, item]) => `${JSON.stringify(key)}:${stable(item)}`)
      .join(",")}}`;
  }
  return JSON.stringify(value) ?? "null";
}

function digest(value) {
  return createHash("sha256").update(stable(value)).digest("hex");
}

function assertHistoryShape(history) {
  if (
    !history ||
    history.schemaVersion !== 1 ||
    history.bootstrapBaseCommit !== SIG909_BOOTSTRAP_BASE_COMMIT ||
    !Array.isArray(history.records)
  ) {
    throw new Error("INVALID_PERMISSION_IDENTITY_HISTORY");
  }
}

function assertSurfaceBaselineShape(baseline) {
  if (
    !baseline ||
    baseline.schemaVersion !== 1 ||
    baseline.task !== "SIG-909" ||
    baseline.legacyBoundaryCommit !== SIG909_BOOTSTRAP_BASE_COMMIT ||
    !Number.isSafeInteger(baseline.legacyCount) ||
    typeof baseline.legacyIdsDigest !== "string" ||
    !Array.isArray(baseline.retirements)
  ) {
    throw new Error("INVALID_PERMISSION_SURFACE_BASELINE");
  }
}

function assertAppendOnlySurfaceBaseline(previous, current) {
  assertSurfaceBaselineShape(previous);
  assertSurfaceBaselineShape(current);
  const immutable = (baseline) => ({
    schemaVersion: baseline.schemaVersion,
    task: baseline.task,
    legacyBoundaryCommit: baseline.legacyBoundaryCommit,
    legacyCount: baseline.legacyCount,
    legacyIdsDigest: baseline.legacyIdsDigest,
  });
  if (stable(immutable(previous)) !== stable(immutable(current))) {
    throw new Error("PERMISSION_SURFACE_BASELINE_CHANGED");
  }
  if (current.retirements.length < previous.retirements.length) {
    throw new Error("PERMISSION_SURFACE_RETIREMENTS_NOT_APPEND_ONLY");
  }
  for (let index = 0; index < previous.retirements.length; index += 1) {
    if (stable(previous.retirements[index]) !== stable(current.retirements[index])) {
      throw new Error("PERMISSION_SURFACE_RETIREMENTS_NOT_APPEND_ONLY");
    }
  }
}

function assertAppendOnlyHistory(previous, current) {
  if (current.records.length < previous.records.length) {
    throw new Error("PERMISSION_HISTORY_NOT_APPEND_ONLY");
  }
  for (let recordIndex = 0; recordIndex < previous.records.length; recordIndex += 1) {
    const before = previous.records[recordIndex];
    const after = current.records[recordIndex];
    if (
      !after ||
      before.resourceKey !== after.resourceKey ||
      !Array.isArray(before.events) ||
      !Array.isArray(after.events) ||
      after.events.length < before.events.length
    ) {
      throw new Error("PERMISSION_HISTORY_NOT_APPEND_ONLY");
    }
    for (let eventIndex = 0; eventIndex < before.events.length; eventIndex += 1) {
      if (stable(before.events[eventIndex]) !== stable(after.events[eventIndex])) {
        throw new Error("PERMISSION_HISTORY_NOT_APPEND_ONLY");
      }
    }
    if (before.events.at(-1)?.status === "RETIRED" && after.events.length > before.events.length) {
      throw new Error("PERMISSION_HISTORY_NOT_APPEND_ONLY");
    }
  }
}

function assertSurfaceLedgerShape(ledger, code) {
  if (
    !ledger ||
    ledger.schemaVersion !== 1 ||
    ledger.task !== "SIG-909" ||
    ledger.legacyBoundaryCommit !== SIG909_BOOTSTRAP_BASE_COMMIT ||
    !Array.isArray(ledger.entries)
  ) {
    throw new Error(code);
  }
  const { contentHash, ...content } = ledger;
  if (typeof contentHash !== "string" || contentHash !== digest(content)) {
    throw new Error(code);
  }
  if (new Set(ledger.entries.map((entry) => entry?.id)).size !== ledger.entries.length) {
    throw new Error(code);
  }
}

function assertAppendOnlySurfaceLedger(previous, current) {
  assertSurfaceLedgerShape(previous, "INVALID_PREVIOUS_PERMISSION_SURFACE_LEDGER");
  assertSurfaceLedgerShape(current, "INVALID_PERMISSION_SURFACE_LEDGER");
  const before = new Map(previous.entries.map((entry) => [entry.id, entry]));
  const after = new Map(current.entries.map((entry) => [entry.id, entry]));
  for (const predecessor of previous.entries) {
    const successor = after.get(predecessor.id);
    if (!successor) {
      throw new Error(`PERMISSION_SURFACE_LEDGER_ENTRY_REMOVED ${predecessor.id}`);
    }
    if (stable(predecessor) === stable(successor)) continue;
    if (predecessor.replacedBy || predecessor.retiredBy) {
      throw new Error(`PERMISSION_SURFACE_LEDGER_ENTRY_CHANGED ${predecessor.id}`);
    }
    const { replacedBy, retiredBy, ...unchanged } = successor;
    if (stable(predecessor) !== stable(unchanged) || Boolean(replacedBy) === Boolean(retiredBy)) {
      throw new Error(`PERMISSION_SURFACE_LEDGER_ENTRY_CHANGED ${predecessor.id}`);
    }
    const transitionId = replacedBy ?? retiredBy;
    const target = after.get(transitionId);
    if (!target || before.has(transitionId)) {
      throw new Error(`PERMISSION_SURFACE_LEDGER_INVALID_TRANSITION ${predecessor.id}`);
    }
    if (replacedBy && target.replaces !== predecessor.id) {
      throw new Error(`PERMISSION_SURFACE_LEDGER_INVALID_TRANSITION ${predecessor.id}`);
    }
    if (
      retiredBy &&
      ((target.kind !== "permission-source-tombstone" &&
        target.kind !== "permission-surface-tombstone") ||
        target.disposition !== "RETIRED" ||
        target.file !== (predecessor.handlerFile ?? predecessor.file) ||
        (target.kind === "permission-surface-tombstone" && target.replaces !== predecessor.id))
    ) {
      throw new Error(`PERMISSION_SURFACE_LEDGER_INVALID_TRANSITION ${predecessor.id}`);
    }
  }
}

// The target can independently publish the branch side of a later v3 splice.
// Collapse only newly inserted mainline nodes in a comparison-only clone. Raw
// history and the fully assembled current graph remain immutable and validated;
// the ordinary append-only check still verifies every other field and tail.
export function spliceComparisonLedger(previous, current) {
  current = surfaceReaderComparisonSnapshot(current);
  assertSurfaceHistoryEvolution(previous, current);
  if (previous.legacy) return current.ledger;
  const fragments = [];
  for (const [path, text] of current.files) {
    if (!path.startsWith(`${SURFACE_HISTORY_PATH}/fragments/`)) continue;
    const fragment = parseJson(text, "INVALID_PERMISSION_SURFACE_FRAGMENT");
    if (path !== `${SURFACE_HISTORY_PATH}/fragments/${canonicalDigest(fragment)}.json`) {
      throw new Error("INVALID_PERMISSION_SURFACE_FRAGMENT_DIGEST");
    }
    fragments.push(fragment);
  }
  const seed = parseJson(
    current.files.get(`${SURFACE_HISTORY_PATH}/seed-ledger.json`),
    "INVALID_PERMISSION_SURFACE_SEED",
  );
  const baseline = parseJson(
    current.files.get(`${SURFACE_HISTORY_PATH}/seed-baseline.json`),
    "INVALID_PERMISSION_SURFACE_BASELINE",
  );
  if (fragments.some((fragment) => [13, 14].includes(fragment.schemaVersion))) {
    // The canonical reader already checked immutable parents and the complete
    // structural graph. Bind its private proof to every caller-visible value;
    // generic assembly deliberately cannot issue that authority.
    assertStructuralSurfaceReaderSnapshot(current);
  } else {
    const assembled = assembleSurfaceHistory(seed, baseline, fragments);
    if (
      stable(assembled.ledger) !== stable(current.ledger) ||
      stable(assembled.baseline) !== stable(current.baseline)
    ) {
      throw new Error("PERMISSION_SURFACE_SPLICE_GRAPH_MISMATCH");
    }
  }
  const before = new Map(previous.ledger.entries.map((entry) => [entry.id, entry]));
  const after = new Map(current.ledger.entries.map((entry) => [entry.id, structuredClone(entry)]));
  const blocked = new Set(
    fragments
      .flatMap((fragment) => [
        ...(fragment.compositionReconciliations ?? []),
        ...(fragment.compositionSupersessions ?? []),
        ...(fragment.compositionExtensions ?? []),
      ])
      .map((receipt) => receipt.predecessor),
  );
  const touched = new Set();
  for (const receipt of fragments.flatMap((fragment) =>
    fragment.schemaVersion === 3 ? fragment.spliceReconciliations : [],
  )) {
    const { predecessor, mainline, branches } = receipt;
    if (blocked.has(predecessor) || branches.length !== 1) continue;
    const present = mainline.filter((id) => before.has(id)).length;
    if (before.has(branches[0]) && present > 0 && present < mainline.length) {
      throw new Error("PARTIAL_PERMISSION_SURFACE_SPLICE_BASE");
    }
    if (present > 0) continue;
    const branch = branches[0];
    const oldPredecessor = before.get(predecessor),
      oldBranch = before.get(branch);
    if (
      !oldPredecessor ||
      !oldBranch ||
      oldPredecessor.retiredBy ||
      oldPredecessor.replacedBy !== branch ||
      oldBranch.replaces !== predecessor
    )
      continue;
    const chain = [predecessor, ...mainline, branch];
    // Historic or superseded receipts cannot justify a live projection.
    if (
      !chain.every((id, index) => {
        const entry = after.get(id);
        return (
          entry &&
          (index === 0 || entry.replaces === chain[index - 1]) &&
          (index === chain.length - 1 ||
            (!entry.retiredBy && entry.replacedBy === chain[index + 1]))
        );
      })
    )
      continue;
    if (chain.some((id) => touched.has(id)))
      throw new Error("OVERLAPPING_PERMISSION_SURFACE_SPLICE_PROJECTION");
    for (const id of chain) touched.add(id);
    for (const id of mainline) after.delete(id);
    after.get(predecessor).replacedBy = branch;
    after.get(branch).replaces = predecessor;
  }
  return buildLedgerFromEntries([...after.values()], current.ledger.legacyBoundaryCommit);
}

export function assertPermissionRegistryEvolution(input) {
  if (!/^[a-f0-9]{40}$/u.test(input?.baseSha ?? "")) {
    throw new Error("INVALID_PERMISSION_REGISTRY_BASE");
  }
  const currentHistory = parseJson(input.currentHistoryText, "INVALID_PERMISSION_IDENTITY_HISTORY");
  const currentBaseline = parseJson(
    input.currentBaselineText,
    "INVALID_PERMISSION_SURFACE_BASELINE",
  );
  const currentLedger = parseJson(input.currentLedgerText, "INVALID_PERMISSION_SURFACE_LEDGER");
  assertHistoryShape(currentHistory);
  assertSurfaceBaselineShape(currentBaseline);
  assertSurfaceLedgerShape(currentLedger, "INVALID_PERMISSION_SURFACE_LEDGER");

  const historyBootstrapping = input.previousHistoryText === null;
  const baselineBootstrapping = input.previousBaselineText === null;
  const ledgerBootstrapping = input.previousLedgerText === null;
  if (historyBootstrapping || baselineBootstrapping || ledgerBootstrapping) {
    if (
      !historyBootstrapping ||
      !baselineBootstrapping ||
      !ledgerBootstrapping ||
      !input.baseIsBootstrapDescendant ||
      currentBaseline.legacyBoundaryCommit !== SIG909_BOOTSTRAP_BASE_COMMIT
    ) {
      throw new Error("INVALID_PERMISSION_REGISTRY_BOOTSTRAP");
    }
    return;
  }

  const previousHistory = parseJson(
    input.previousHistoryText,
    "INVALID_PREVIOUS_PERMISSION_IDENTITY_HISTORY",
  );
  assertHistoryShape(previousHistory);
  assertAppendOnlyHistory(previousHistory, currentHistory);
  const previousBaseline = parseJson(
    input.previousBaselineText,
    "INVALID_PREVIOUS_PERMISSION_SURFACE_BASELINE",
  );
  assertAppendOnlySurfaceBaseline(previousBaseline, currentBaseline);
  const previousLedger = parseJson(
    input.previousLedgerText,
    "INVALID_PREVIOUS_PERMISSION_SURFACE_LEDGER",
  );
  assertAppendOnlySurfaceLedger(previousLedger, currentLedger);
}

function repositoryRoot() {
  return resolve(dirname(fileURLToPath(import.meta.url)), "../..");
}

// execFileSync/spawnSync default to maxBuffer = 1 MiB; the permission registry
// on main is ~4.4 MB, so `git show` failed with `spawnSync git ENOBUFS`.
// The registry only grows, so the ceiling is generous rather than exact.
export const GIT_MAX_BUFFER_BYTES = 256 * 1024 * 1024;

export function predecessorText(root, baseSha, path) {
  const historyReader = openInstalledHistoryReader(realpathSync(root));
  if (historyReader) {
    const logical = historyReader.classifyPhysicalRevision(baseSha);
    const bytes = historyReader.readFile(logical, path);
    historyReader.assertCurrent();
    return bytes === null ? null : bytes.toString("utf8");
  }
  // An invalid revision, failed process or corrupt store is never path absence.
  execFileSync(
    "/usr/bin/git",
    ["--no-replace-objects", "rev-parse", "--verify", `${baseSha}^{commit}`],
    {
      cwd: root,
      stdio: "ignore",
      timeout: 15_000,
      maxBuffer: GIT_MAX_BUFFER_BYTES,
    },
  );
  const listing = execFileSync(
    "/usr/bin/git",
    ["--no-replace-objects", "ls-tree", "-z", baseSha, "--", path],
    { cwd: root, encoding: "utf8", timeout: 15_000, maxBuffer: GIT_MAX_BUFFER_BYTES },
  );
  if (!listing) return null;
  return execFileSync("/usr/bin/git", ["--no-replace-objects", "show", `${baseSha}:${path}`], {
    cwd: root,
    encoding: "utf8",
    timeout: 15_000,
    maxBuffer: GIT_MAX_BUFFER_BYTES,
  });
}

function argument(name) {
  const index = process.argv.indexOf(name);
  return index === -1 ? "" : (process.argv[index + 1] ?? "");
}

// main always moves ahead of the one-time SIG909_BOOTSTRAP_BASE_COMMIT, so a
// real PR's target base is never that exact SHA again after the first
// publication. Bootstrap eligibility is ancestry, not equality: the base must
// still be that commit or a descendant of it, so the legacy census computed
// at the bootstrap commit remains a valid predecessor for it.
export function isBootstrapDescendant(root, baseSha, anchor = SIG909_BOOTSTRAP_BASE_COMMIT) {
  const historyReader = openInstalledHistoryReader(realpathSync(root));
  if (historyReader) {
    historyReader.classifyPhysicalRevision(baseSha);
    const before = historyReader.resolveReceiptRevision(anchor).physicalRevision;
    return historyReader.isPhysicalAncestor(before, baseSha);
  }
  if (baseSha === anchor) return true;
  try {
    execFileSync("/usr/bin/git", ["merge-base", "--is-ancestor", anchor, baseSha], {
      cwd: root,
      stdio: "ignore",
      timeout: 15_000,
      maxBuffer: GIT_MAX_BUFFER_BYTES,
    });
    return true;
  } catch {
    return false;
  }
}

export function verifyPermissionRegistryEvolution(root, baseSha, current) {
  if (!/^[a-f0-9]{40}$/u.test(baseSha)) {
    throw new Error("INVALID_PERMISSION_REGISTRY_BASE");
  }
  current ??= readEvolutionSurfaceHistory(root);
  // A corrupt merged base cannot be assembled without its newly reviewed
  // reconciliation. Only complete existing conflicts consume these receipts;
  // immutable base bytes are still checked below, with no skipped ledger checks.
  const previous = readEvolutionSurfaceHistoryBase(root, baseSha, current);
  assertSurfaceHistoryEvolution(previous, current);
  // Retirement order is a derived view. Keep the base order for the existing
  // append-only comparison, while fragment storage itself is order-independent.
  const currentBaseline = buildLegacyBaselineAnchor(current.ledger, previous.baseline);
  assertPermissionRegistryEvolution({
    baseSha,
    baseIsBootstrapDescendant: isBootstrapDescendant(root, baseSha),
    previousHistoryText: predecessorText(root, baseSha, PERMISSION_HISTORY_PATH),
    currentHistoryText: readFileSync(resolve(root, PERMISSION_HISTORY_PATH), "utf8"),
    previousBaselineText: JSON.stringify(previous.baseline),
    currentBaselineText: JSON.stringify(currentBaseline),
    previousLedgerText: JSON.stringify(previous.ledger),
    currentLedgerText: JSON.stringify(spliceComparisonLedger(previous, current)),
  });
  assertEvolutionSurfaceReaderCurrent(root, current);
}

function main() {
  const baseSha = argument("--base");
  verifyPermissionRegistryEvolution(repositoryRoot(), baseSha);
  process.stdout.write(`permission registry evolution valid from ${baseSha}\n`);
}

if (process.argv[1] && pathToFileURL(realpathSync(process.argv[1])).href === import.meta.url) {
  main();
}
