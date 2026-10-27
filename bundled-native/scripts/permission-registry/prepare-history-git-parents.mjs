// Checkout ancestry does not include every parent named by immutable receipts:
// a closed/squashed PR can leave an exact structural parent without a branch ref.
// Prepare Git objects only; canonical readers still validate the complete history.
import { execFileSync } from "node:child_process";
import { performance } from "node:perf_hooks";
import { resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { digest } from "./ledger-format.mjs";
import { openInstalledHistoryReader } from "./history-revision-io.mjs";

const FRAGMENTS = "scripts/permission-registry/surface-history/fragments";
const SHA = /^[a-f0-9]{40}$/u;
const PATH = new RegExp(`^${FRAGMENTS}/[a-f0-9]{64}\\.json$`, "u");
const BUDGET_MS = 180_000;
const MAX_REVISIONS = 64;
const MAX_FILES = 2000;
const MAX_BYTES = 128 * 1024 * 1024;
const refuse = () => {
  throw new Error("PERMISSION_HISTORY_PARENT_PREPARATION_REFUSED");
};

const RETENTION_PREFIX = "refs/tags/signalo-permission-history/";
export function historyRetentionRef(revision) {
  if (typeof revision !== "string" || !SHA.test(revision)) refuse();
  const reader = openInstalledHistoryReader(resolve(process.cwd()));
  if (reader) return reader.cleanRetentionRef(revision);
  return RETENTION_PREFIX + revision;
}
function boundedGit(root) {
  const deadline = performance.now() + BUDGET_MS;
  const assertDeadline = () => {
    if (performance.now() >= deadline) refuse();
  };
  const git = (args) => {
    const remaining = Math.floor(deadline - performance.now());
    if (remaining <= 0) refuse();
    let output;
    try {
      output = execFileSync("/usr/bin/git", ["--no-replace-objects", ...args], {
        cwd: root,
        encoding: "utf8",
        timeout: Math.min(remaining, 60_000),
        maxBuffer: MAX_BYTES,
        stdio: ["ignore", "pipe", "pipe"],
        env: { ...process.env, GIT_TERMINAL_PROMPT: "0" },
      });
    } catch {
      // Programmatic publisher callers must not expose Git stderr / remote URLs.
      refuse();
    }
    assertDeadline();
    const text = output.trim();
    assertDeadline();
    return text;
  };
  return { git, assertDeadline };
}
function parentsOf(git, merge, reader = null) {
  if (reader) {
    const parents = reader.readLogicalParents(merge);
    if (parents.length !== 2 || parents[0] === parents[1]) refuse();
    return parents;
  }
  historyRetentionRef(merge);
  if (git(["rev-parse", "--verify", `${merge}^{commit}`]) !== merge) refuse();
  const parents = git(["show", "-s", "--format=%P", merge]).split(" ");
  if (
    parents.length !== 2 ||
    new Set(parents).size !== 2 ||
    parents.some((p) => typeof p !== "string" || !SHA.test(p))
  )
    refuse();
  return parents;
}
// Pin one unambiguous origin. Never log credential-bearing URLs or accept a
// different push destination. Exact refs provide reachability, not authority.
function originOf(git, reader = null) {
  const fetch = git(["remote", "get-url", "--all", "origin"]);
  const push = git(["remote", "get-url", "--push", "--all", "origin"]);
  if (!fetch || fetch.includes("\n") || push !== fetch) refuse();
  if (reader) {
    const match =
      /^(?:https:\/\/github\.com\/|git@github\.com:)(signalorust\/signalo|All-projects-Rust\/signalo)(?:\.git)?$/u.exec(
        fetch,
      );
    if (!match) refuse();
    let metadata;
    try {
      metadata = JSON.parse(
        execFileSync("/usr/bin/gh", ["api", "--hostname", "github.com", `repos/${match[1]}`], {
          encoding: "utf8",
          timeout: 15_000,
          maxBuffer: 128 * 1024,
          stdio: ["ignore", "pipe", "pipe"],
        }),
      );
    } catch {
      refuse();
    }
    const ownerId = match[1] === "signalorust/signalo" ? 345015266 : 348736467;
    if (
      metadata.id !== 1201945594 ||
      metadata.full_name !== match[1] ||
      metadata.owner?.id !== ownerId ||
      metadata.owner?.login !== match[1].split("/")[0]
    )
      refuse();
    reader.assertCurrent();
  }
  return fetch;
}
function retained(git, origin, revisions, required, count = 3, reader = null) {
  if (!Array.isArray(revisions) || revisions.length !== count || new Set(revisions).size !== count)
    refuse();
  const refs = new Map(
    revisions.map((r) => [
      reader ? reader.cleanRetentionRef(r) : historyRetentionRef(r),
      reader ? reader.resolveReceiptRevision(r).physicalRevision : r,
    ]),
  );
  if (refs.size !== count) refuse();
  const response = git(["ls-remote", "--refs", origin, ...refs.keys()]);
  const seen = new Set();
  for (const line of response ? response.split("\n") : []) {
    const match = /^([a-f0-9]{40})\t([^\t]+)$/u.exec(line);
    if (!match || !refs.has(match[2]) || seen.has(match[2]) || refs.get(match[2]) !== match[1])
      refuse();
    seen.add(match[2]);
  }
  if (required && seen.size !== refs.size) refuse();
  return [...refs.keys()].filter((ref) => !seen.has(ref));
}
/** Read-only publication precondition. No remote ref is implicitly created. */
export function assertStructuralTailGitRetention(root, merge, expectedParents) {
  const reader = openInstalledHistoryReader(resolve(root));
  if (reader) merge = reader.classifyPhysicalRevision(merge);
  const { git } = boundedGit(reader?.cleanStoreRoot ?? root),
    parents = parentsOf(git, merge, reader);
  if (JSON.stringify(parents) !== JSON.stringify(expectedParents)) refuse();
  const origin = originOf(git, reader);
  retained(git, origin, [merge, ...parents], true, 3, reader);
  if (originOf(git, reader) !== origin) refuse();
}
/** Explicit separate owner action, after independent review of the command and
 * current tag-trigger safety. Atomic ordinary tag push is CREATE-ONLY: equal
 * refs are reused, a concurrent conflicting ref rejects, never force/delete.
 * This operation does not publish a receipt or grant reader/source authority.
 */
export function retainStructuralTailGitParents(root, merge, { createOnly = false } = {}) {
  const reader = openInstalledHistoryReader(resolve(root));
  if (reader) merge = reader.classifyPhysicalRevision(merge);
  const { git } = boundedGit(reader?.cleanStoreRoot ?? root),
    parents = parentsOf(git, merge, reader);
  const revisions = [merge, ...parents],
    origin = originOf(git, reader);
  const missing = retained(git, origin, revisions, false, 3, reader);
  if (createOnly === true && missing.length) {
    if (originOf(git, reader) !== origin) refuse();
    git([
      "push",
      "--atomic",
      origin,
      ...revisions.map(
        (r) =>
          `${reader ? reader.resolveReceiptRevision(r).physicalRevision : r}:${reader ? reader.cleanRetentionRef(r) : historyRetentionRef(r)}`,
      ),
    ]);
  }
  const remaining = retained(git, origin, revisions, createOnly === true, 3, reader);
  if (originOf(git, reader) !== origin) refuse();
  return {
    merge,
    parents,
    refs: revisions.map((r) => (reader ? reader.cleanRetentionRef(r) : historyRetentionRef(r))),
    missing: remaining,
  };
}

// Snapshot refs preserve exact committed inventories after protected squash.
// Reachability is not reader authority; canonical validation still owns that.
export function retainSealedSnapshotGitParent(root, revision, { createOnly = false } = {}) {
  const reader = openInstalledHistoryReader(resolve(root));
  if (reader) revision = reader.classifyPhysicalRevision(revision);
  const ref = reader ? reader.cleanRetentionRef(revision) : historyRetentionRef(revision);
  const physical = reader ? reader.resolveReceiptRevision(revision).physicalRevision : revision;
  const { git } = boundedGit(reader?.cleanStoreRoot ?? root);
  if (!reader && git(["rev-parse", "--verify", `${physical}^{commit}`]) !== physical) refuse();
  const origin = originOf(git, reader);
  const missing = retained(git, origin, [revision], false, 1, reader);
  if (createOnly === true && missing.length) {
    if (originOf(git, reader) !== origin) refuse();
    git(["push", "--atomic", origin, `${physical}:${ref}`]);
  }
  const remaining = retained(git, origin, [revision], createOnly === true, 1, reader);
  if (originOf(git, reader) !== origin) refuse();
  return { revision, ref, missing: remaining };
}

/** Publisher precondition only: never creates or repairs remote references. */
export function assertSealedSnapshotGitRetention(root, revision) {
  if (retainSealedSnapshotGitParent(root, revision).missing.length) refuse();
}

export function prepareHistoryGitParents(root, revisions = []) {
  if (
    !Array.isArray(revisions) ||
    revisions.length > 2 ||
    revisions.some((r) => typeof r !== "string" || !SHA.test(r))
  )
    refuse();
  const { git, assertDeadline } = boundedGit(root);
  const reader = openInstalledHistoryReader(resolve(root));
  const physicalHead = git(["rev-parse", "--verify", "HEAD^{commit}"]);
  const head = reader ? reader.classifyPhysicalRevision(physicalHead) : physicalHead;
  if (!SHA.test(head)) refuse();
  const queue = new Set([
    head,
    ...revisions.map((r) => (reader ? reader.classifyPhysicalRevision(r) : r)),
    ...(reader ? [reader.bootstrapRevision] : []),
  ]);
  const parsed = new Map();
  let bytes = 0;
  let fetched = 0;
  let origin;
  const tails = new Map();
  const sealedSnapshots = new Set();
  for (const revision of queue) {
    if (queue.size > MAX_REVISIONS) refuse();
    const activeSnapshot = reader ? reader.readSnapshot(revision) : null;
    let available = Boolean(activeSnapshot);
    try {
      if (!reader) available = git(["rev-parse", "--verify", `${revision}^{commit}`]) === revision;
    } catch {
      /* Missing objects are the sole reason to fetch an exact receipt SHA. */
    }
    if (!available) {
      // Active stores are provisioned unfiltered by trusted transport tooling.
      // Never hydrate from the candidate's partial clone or fetch a logical ID.
      if (reader) refuse();
      // No refspec, tags, shallow boundary, worktree update or FETCH_HEAD write.
      // Filtering avoids downloading unrelated historical source blobs. Git may
      // hydrate the exact history blobs below through the same checkout origin.
      git([
        "-c",
        "fetch.fsckObjects=true",
        "fetch",
        "--no-tags",
        "--no-recurse-submodules",
        "--no-write-fetch-head",
        "--no-auto-maintenance",
        "--filter=blob:none",
        origin ?? "origin",
        revision,
      ]);
      if (git(["rev-parse", "--verify", `${revision}^{commit}`]) !== revision) refuse();
      fetched++;
    }
    const listing = activeSnapshot
      ? activeSnapshot.inventory
          .filter(({ path }) => path.startsWith(FRAGMENTS + "/"))
          .map(({ path, mode, blob }) => `${mode} blob ${blob}\t${path}`)
          .join("\n")
      : git(["ls-tree", "-r", revision, "--", FRAGMENTS]);
    const lines = listing ? listing.split("\n") : [];
    if (lines.length > MAX_FILES) refuse();
    assertDeadline();
    for (const line of lines) {
      assertDeadline();
      const match = /^(100644|100755) blob ([a-f0-9]{40})\t(.+)$/u.exec(line);
      if (!match || !PATH.test(match[3])) refuse();
      const [, , blob, path] = match;
      let fragment = parsed.get(blob);
      if (!fragment) {
        if (parsed.size >= MAX_FILES) refuse();
        const text = activeSnapshot
          ? activeSnapshot.files.get(path)
          : git(["show", `${revision}:${path}`]);
        bytes += Buffer.byteLength(text);
        if (bytes > MAX_BYTES) refuse();
        assertDeadline();
        fragment = JSON.parse(text);
        assertDeadline();
        if (path !== `${FRAGMENTS}/${digest(fragment)}.json`) refuse();
        parsed.set(blob, fragment);
      } else if (path !== `${FRAGMENTS}/${digest(fragment)}.json`) refuse();
      assertDeadline();
      // Native v6 snapshots may name squashed/unreferenced branch commits.
      if (fragment?.schemaVersion === 6) {
        if (!Array.isArray(fragment.compositionSupersessions)) refuse();
        for (const receipt of fragment.compositionSupersessions) {
          if (!Array.isArray(receipt?.snapshots)) refuse();
          for (const snapshot of receipt.snapshots) {
            if (!snapshot || !Object.hasOwn(snapshot, "revision")) continue;
            historyRetentionRef(snapshot.revision);
            if (!sealedSnapshots.has(snapshot.revision)) {
              if (sealedSnapshots.size >= MAX_REVISIONS) refuse();
              origin ??= originOf(git, reader);
              retained(git, origin, [snapshot.revision], true, 1, reader);
              sealedSnapshots.add(snapshot.revision);
              queue.add(snapshot.revision);
            }
          }
        }
        continue;
      }
      let parents;
      if (fragment?.schemaVersion === 13) {
        if (fragment.structuralMergeExtensions?.length !== 1) refuse();
        parents = fragment.structuralMergeExtensions[0]?.parents?.map((p) => p?.revision);
      } else if (fragment?.schemaVersion === 14) {
        if (fragment.structuralMergeContinuations?.length !== 1) refuse();
        const receipt = fragment.structuralMergeContinuations[0];
        parents = [receipt?.previous?.revision, receipt?.incoming?.revision];
      } else if (fragment?.schemaVersion === 15 || fragment?.schemaVersion === 16) {
        const receipts =
          fragment.schemaVersion === 15
            ? fragment.structuralMergeCompositions
            : fragment.structuralMergeCatchups;
        if (!Array.isArray(receipts) || receipts.length !== 1) refuse();
        if (!Array.isArray(receipts[0]?.parents)) refuse();
        parents = receipts[0].parents.map((p) => p?.revision);
      } else if (fragment?.schemaVersion === 17) {
        const receipts = fragment.structuralTailCompositions;
        if (
          !Array.isArray(receipts) ||
          receipts.length !== 1 ||
          !Array.isArray(receipts[0]?.parents)
        )
          refuse();
        const receipt = receipts[0];
        parents = receipt.parents.map((p) => p?.revision);
        historyRetentionRef(receipt.merge);
        if (!tails.has(receipt.merge)) {
          if (tails.size >= MAX_REVISIONS) refuse();
          origin ??= originOf(git, reader);
          retained(git, origin, [receipt.merge, ...parents], true, 3, reader);
          tails.set(receipt.merge, parents);
        } else if (JSON.stringify(tails.get(receipt.merge)) !== JSON.stringify(parents)) refuse();
        queue.add(receipt.merge);
      } else continue;
      if (
        !Array.isArray(parents) ||
        parents.length !== 2 ||
        parents[0] === parents[1] ||
        parents.some((r) => typeof r !== "string" || !SHA.test(r))
      )
        refuse();
      for (const parent of parents) queue.add(parent);
      assertDeadline();
    }
  }
  for (const [merge, parents] of tails) {
    if (JSON.stringify(parentsOf(git, merge, reader)) !== JSON.stringify(parents)) refuse();
    retained(git, origin, [merge, ...parents], true, 3, reader);
  }
  for (const revision of sealedSnapshots) retained(git, origin, [revision], true, 1, reader);
  if (origin !== undefined && originOf(git, reader) !== origin) refuse();
  reader?.assertCurrent();
  assertDeadline();
  return { revisions: queue.size, fetched, fragments: parsed.size };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const args = process.argv.slice(2);
    if (
      args.length === 3 &&
      args[0] === "--retain-v6-snapshot" &&
      SHA.test(args[1]) &&
      ["--dry-run", "--create-only"].includes(args[2])
    ) {
      console.log(
        JSON.stringify(
          retainSealedSnapshotGitParent(process.cwd(), args[1], {
            createOnly: args[2] === "--create-only",
          }),
        ),
      );
    } else if (
      args.length === 3 &&
      args[0] === "--retain-schema17-merge" &&
      SHA.test(args[1]) &&
      ["--dry-run", "--create-only"].includes(args[2])
    ) {
      console.log(
        JSON.stringify(
          retainStructuralTailGitParents(process.cwd(), args[1], {
            createOnly: args[2] === "--create-only",
          }),
        ),
      );
    } else {
      if (
        args.length > 4 ||
        args.length % 2 ||
        args.some((v, i) => (i % 2 === 0 ? v !== "--revision" : !SHA.test(v)))
      )
        refuse();
      console.log(
        JSON.stringify(
          prepareHistoryGitParents(
            process.cwd(),
            args.filter((_, i) => i % 2),
          ),
        ),
      );
    }
  } catch {
    console.error("PERMISSION_HISTORY_PARENT_PREPARATION_REFUSED");
    process.exitCode = 1;
  }
}
