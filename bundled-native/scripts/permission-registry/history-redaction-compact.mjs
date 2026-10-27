// Data-only format/preparation primitive; this never issues native authority.
// Trust AND verifier provenance must be installed independently of a candidate.
// Raw-object callbacks remain synchronous and offline. The distinct Git builder
// internally authenticates bounded batches, without installing native trust.
import { createHash, createPublicKey, verify } from "node:crypto";
import { digest, stable } from "./ledger-format.mjs";
import { openIsolatedGitObjectStores } from "./history-redaction-git-io.mjs";
import { createBoundedTreeArena } from "./history-redaction-tree-arena.mjs";

const SHA = /^[a-f0-9]{40}$/u;
const HASH = /^[a-f0-9]{64}$/u;
const SECTIONS = ["commits", "projections", "objects", "refs", "dependencies"];
const COUNT_KEYS = [...SECTIONS, "edges", "sourceObjects"];
const PAGE_ROWS = 1024;
const PAGE_BYTES = 1024 * 1024;
const TYPE = { commit: "c", tree: "t", blob: "b" };
const SCOPES = [
  "scripts/permission-registry/surface-history",
  "scripts/permission-registry/permission-surface-ledger.json",
  "scripts/permission-registry/permission-surface-baseline.json",
  "apps/api/src/modules/access-control/permission-identity-history.json",
];
const DOMAIN = Buffer.from("signalo-history-redaction-compact-v1\n");
const fail = () => {
  throw new Error("COMPACT_HISTORY_REDACTION_REFUSED");
};
const guarded = (operation) => {
  try {
    return operation();
  } catch {
    fail();
  }
};
const hash = (bytes) => createHash("sha256").update(bytes).digest("hex");
const equal = (left, right) => stable(left) === stable(right);
const check = (condition) => {
  if (!condition) fail();
};
function keys(value, names) {
  check(value && typeof value === "object" && !Array.isArray(value));
  check(Object.keys(value).sort().join(",") === [...names].sort().join(","));
}
function integer(value, minimum = 0) {
  check(Number.isSafeInteger(value) && value >= minimum);
  return value;
}
function sha(value) {
  check(typeof value === "string" && SHA.test(value));
  return value;
}
function hashed(value) {
  check(typeof value === "string" && HASH.test(value));
  return value;
}
function ordered(rows, key = (row) => row) {
  check(Array.isArray(rows));
  for (let index = 1; index < rows.length; index++) check(key(rows[index - 1]) < key(rows[index]));
}
function pathOf(path) {
  check(typeof path === "string" && path.length > 0 && Buffer.byteLength(path) <= 4096);
  check(!/[\\\u0000-\u001f\u007f]/u.test(path));
  check(path.split("/").every((part) => part && part !== "." && part !== ".."));
  return path;
}
const protectedPath = (path) =>
  SCOPES.some((scope) => path === scope || path.startsWith(scope + "/"));
export const canonicalCompactBytes = (value) => Buffer.from(stable(value) + "\n");
export const compactSignatureMessage = (bytes) => Buffer.concat([DOMAIN, bytes]);
function document(bytes, budget) {
  integer(budget, 1);
  check(Buffer.isBuffer(bytes) && bytes.length > 0 && bytes.length <= budget);
  const value = JSON.parse(bytes.toString("utf8"));
  check(canonicalCompactBytes(value).equals(bytes)); // duplicate keys / invalid UTF-8 refuse
  return value;
}
function identity(value) {
  check(value.schemaVersion === 1);
  check(
    typeof value.migrationId === "string" && /^[a-z0-9][a-z0-9-]{0,63}$/u.test(value.migrationId),
  );
  check(typeof value.repositoryId === "string" && /^[1-9][0-9]{0,19}$/u.test(value.repositoryId));
}
function scopeDocument(bytes) {
  const value = document(bytes, 4 * 1024 * 1024);
  keys(value, [
    "schemaVersion",
    "migrationId",
    "repositoryId",
    "sourceAnchor",
    "bootstrapRevision",
    "sourceRefs",
    "dependencyRoots",
    "policySha256",
    "sourceCommitCount",
    "sourceParentEdges",
    "sourceObjectCount",
    "cleanObjectCount",
    "maxParents",
    "maxObjectBytes",
  ]);
  identity(value);
  sha(value.sourceAnchor);
  sha(value.bootstrapRevision);
  hashed(value.policySha256);
  integer(value.sourceCommitCount, 1);
  integer(value.sourceParentEdges);
  integer(value.sourceObjectCount, value.sourceCommitCount);
  integer(value.cleanObjectCount, value.sourceCommitCount);
  integer(value.maxParents);
  check(value.maxParents <= 16);
  integer(value.maxObjectBytes, 1);
  check(value.maxObjectBytes <= 128 * 1024 * 1024);
  ordered(value.sourceRefs, (ref) => ref.name);
  check(value.sourceRefs.length > 0);
  for (const ref of value.sourceRefs) {
    keys(ref, ["name", "revision"]);
    sha(ref.revision);
    pathOf(ref.name);
    check(/^refs\/(heads|tags)\//u.test(ref.name) && !/[~^:?*\[]/u.test(ref.name));
    check(!ref.name.includes("..") && !ref.name.includes("@{"));
    check(ref.name.split("/").every((part) => !part.endsWith(".lock") && !part.endsWith(".")));
  }
  check(
    value.sourceRefs.some(
      (ref) => ref.name.startsWith("refs/heads/") && ref.revision === value.sourceAnchor,
    ),
  );
  ordered(value.dependencyRoots);
  value.dependencyRoots.forEach(sha);
  check(value.dependencyRoots.includes(value.bootstrapRevision));
  return value;
}
function stateShape(value) {
  if (value === null) return;
  keys(value, ["mode", "oid", "sha256"]);
  check(["100644", "100755", "120000"].includes(value.mode));
  sha(value.oid);
  hashed(value.sha256);
}
function policyDocument(bytes, scope) {
  check(hash(bytes) === scope.policySha256);
  // Private exact policy size scales with independently measured object and
  // commit counts. It is not a per-commit multiplied file inventory.
  const budget = integer(4096 + scope.sourceObjectCount * 384 + scope.sourceCommitCount * 256, 1);
  const policy = document(bytes, budget);
  keys(policy, ["schemaVersion", "migrationId", "repositoryId", "files", "metadata"]);
  identity(policy);
  check(policy.migrationId === scope.migrationId && policy.repositoryId === scope.repositoryId);
  check(Array.isArray(policy.files) && policy.files.length <= scope.sourceObjectCount * 2);
  ordered(policy.files, (rule) => stable(rule));
  const files = new Map();
  policy.files.forEach((rule, index) => {
    keys(rule, ["path", "before", "after"]);
    pathOf(rule.path);
    check(!protectedPath(rule.path));
    stateShape(rule.before);
    stateShape(rule.after);
    check(!equal(rule.before, rule.after));
    files.set(stable(rule), index);
  });
  ordered(policy.metadata, (rule) => rule.logicalRevision);
  check(policy.metadata.length <= scope.sourceCommitCount);
  const metadata = new Map();
  policy.metadata.forEach((rule) => {
    keys(rule, ["logicalRevision", "beforeSha256", "afterSha256"]);
    sha(rule.logicalRevision);
    hashed(rule.beforeSha256);
    hashed(rule.afterSha256);
    check(rule.beforeSha256 !== rule.afterSha256);
    metadata.set(rule.logicalRevision, rule);
  });
  return { policy, files, metadata, usedFiles: new Set(), usedMetadata: new Set() };
}

function parseCommit(bytes) {
  const separator = bytes.indexOf(Buffer.from("\n\n"));
  check(separator >= 0);
  const lines = bytes.subarray(0, separator).toString("latin1").split("\n");
  check(/^tree [a-f0-9]{40}$/u.test(lines[0]));
  const parents = [];
  let index = 1;
  while (lines[index]?.startsWith("parent ")) parents.push(sha(lines[index++].slice(7)));
  check(!lines.slice(index).some((line) => line.startsWith("tree ") || line.startsWith("parent ")));
  const metadata = Buffer.concat([
    Buffer.from(lines.slice(index).join("\n") + "\n\n", "latin1"),
    bytes.subarray(separator + 2),
  ]);
  return { tree: lines[0].slice(5), parents, metadataSha256: hash(metadata) };
}
function parseTree(bytes) {
  const entries = [];
  const names = new Set();
  let offset = 0;
  let previous;
  while (offset < bytes.length) {
    const space = bytes.indexOf(32, offset),
      nul = bytes.indexOf(0, space + 1);
    check(space > offset && nul > space + 1 && nul + 21 <= bytes.length);
    const rawMode = bytes.subarray(offset, space);
    check(rawMode.every((byte) => byte >= 0x30 && byte <= 0x37));
    const mode = rawMode.toString("utf8");
    check(["40000", "100644", "100755", "120000"].includes(mode)); // measured gitlinks = 0
    const rawName = bytes.subarray(space + 1, nul),
      name = rawName.toString("utf8");
    check(Buffer.from(name).equals(rawName));
    pathOf(name);
    check(!name.includes("/"));
    check(!names.has(name));
    names.add(name);
    const sortKey = Buffer.concat([rawName, Buffer.from([mode === "40000" ? 47 : 0])]);
    check(!previous || Buffer.compare(previous, sortKey) < 0);
    previous = sortKey;
    entries.push({ name, mode, oid: bytes.subarray(nul + 1, nul + 21).toString("hex") });
    offset = nul + 21;
  }
  return entries;
}
function objectReader(read, countLimit, maxBytes, expected) {
  check(typeof read === "function");
  const facts = new Map(),
    content = new Map(),
    provenance = new Map();
  const raw = (oid) => {
    sha(oid);
    if (expected) check(expected.has(oid));
    const response = read(oid);
    const type = response?.type,
      inputBytes = response?.bytes;
    check(response && ["commit", "tree", "blob"].includes(type) && Buffer.isBuffer(inputBytes));
    check(inputBytes.length <= maxBytes);
    const bytes = Buffer.from(inputBytes);
    check(
      createHash("sha1").update(`${type} ${bytes.length}\0`).update(bytes).digest("hex") === oid,
    );
    const sha256 = hash(bytes),
      row = expected?.get(oid);
    if (expected)
      check(row && row[1] === TYPE[type] && row[2] === bytes.length && row[3] === sha256);
    return { type, bytes, sha256 };
  };
  const get = (oid) => {
    if (facts.has(oid)) return facts.get(oid);
    check(facts.size < countLimit);
    const value = raw(oid);
    const fact = {
      type: value.type,
      size: value.bytes.length,
      sha256: value.sha256,
      ...(value.type === "commit" ? parseCommit(value.bytes) : {}),
      ...(value.type === "tree" ? { entries: parseTree(value.bytes) } : {}),
    };
    facts.set(oid, fact);
    return fact;
  };
  return { facts, content, provenance, get, raw };
}
function contentDigest(reader, start) {
  if (reader.content.has(start)) return reader.content.get(start);
  const active = new Set(),
    stack = [{ oid: start, index: 0 }];
  while (stack.length) {
    reader.budget?.step(stack.length);
    const frame = stack.at(-1),
      fact = reader.get(frame.oid);
    check(fact.type !== "commit");
    if (fact.type === "blob") {
      reader.content.set(frame.oid, digest(["b", fact.size, fact.sha256]));
      stack.pop();
      continue;
    }
    if (!frame.entered) {
      check(!active.has(frame.oid));
      active.add(frame.oid);
      frame.entered = true;
    }
    if (frame.index < fact.entries.length) {
      const entry = fact.entries[frame.index++],
        child = reader.get(entry.oid);
      check(child.type === (entry.mode === "40000" ? "tree" : "blob"));
      if (!reader.content.has(entry.oid)) {
        check(!active.has(entry.oid));
        stack.push({ oid: entry.oid, index: 0 });
      }
      continue;
    }
    reader.content.set(
      frame.oid,
      digest([
        "t",
        fact.entries.map((entry) => [entry.name, entry.mode, reader.content.get(entry.oid)]),
      ]),
    );
    active.delete(frame.oid);
    stack.pop();
  }
  return reader.content.get(start);
}
function lookup(reader, root, path) {
  let oid = root;
  const parts = pathOf(path).split("/");
  for (let index = 0; index < parts.length; index++) {
    const fact = reader.get(oid);
    check(fact.type === "tree");
    const entry = fact.entries.find((candidate) => candidate.name === parts[index]);
    if (!entry) return null;
    if (index === parts.length - 1) return entry;
    if (entry.mode !== "40000") return null;
    oid = entry.oid;
  }
  fail();
}
function provenanceDigest(reader, tree) {
  if (!reader.provenance.has(tree))
    reader.provenance.set(
      tree,
      digest(
        SCOPES.map((path) => {
          const entry = lookup(reader, tree, path);
          return [path, entry ? [entry.mode, contentDigest(reader, entry.oid)] : null];
        }),
      ),
    );
  return reader.provenance.get(tree);
}
function boundedProvenanceRoots(reader, tree, limits) {
  const roots = [],
    memo = new Map();
  const escapedBytes = (text) => Buffer.byteLength(JSON.stringify(text)) - 2;
  let expandedPaths = 0,
    rows = 0,
    outputBytes = 3; // Exact canonical JSON array bytes, including trailing newline.
  for (const path of SCOPES) {
    const entry = lookup(reader, tree, path);
    if (!entry) continue;
    const keyOf = (entry) => `${entry.mode}:${entry.oid}`;
    const stack = [{ entry, index: 0 }],
      active = new Set();
    while (stack.length) {
      const frame = stack.at(-1),
        key = keyOf(frame.entry);
      if (memo.has(key)) {
        stack.pop();
        continue;
      }
      const fact = reader.get(frame.entry.oid);
      if (!frame.stats) {
        check(!active.has(key));
        active.add(key);
        frame.stats = { paths: 1, rows: 0, baseBytes: 0, suffixBytes: 0 };
        if (frame.entry.mode !== "40000") {
          check(["100644", "100755"].includes(frame.entry.mode) && fact.type === "blob");
          frame.stats.rows = 1;
          frame.stats.baseBytes =
            canonicalCompactBytes({
              path: "",
              mode: frame.entry.mode,
              oid: frame.entry.oid,
              sha256: fact.sha256,
            }).length - 1;
        } else check(fact.type === "tree");
      }
      if (frame.entry.mode === "40000" && frame.index < fact.entries.length) {
        const child = fact.entries[frame.index],
          childKey = keyOf(child);
        if (!memo.has(childKey)) {
          check(!active.has(childKey));
          stack.push({ entry: child, index: 0 });
          continue;
        }
        const childStats = memo.get(childKey);
        frame.stats.paths += childStats.paths;
        frame.stats.rows += childStats.rows;
        frame.stats.baseBytes +=
          childStats.baseBytes + childStats.rows * (1 + escapedBytes(child.name));
        frame.stats.suffixBytes = Math.max(
          frame.stats.suffixBytes,
          1 + Buffer.byteLength(child.name) + childStats.suffixBytes,
        );
        frame.index++;
      } else {
        memo.set(key, frame.stats);
        active.delete(key);
        stack.pop();
      }
      check(frame.stats.paths <= limits.maxExpandedPaths);
      check(frame.stats.baseBytes <= limits.maxOutputBytes && frame.stats.suffixBytes <= 4096);
    }
    const stats = memo.get(keyOf(entry));
    expandedPaths += stats.paths;
    outputBytes += stats.baseBytes + stats.rows * escapedBytes(path);
    if (stats.rows) outputBytes += stats.rows - (rows ? 0 : 1);
    rows += stats.rows;
    check(expandedPaths <= limits.maxExpandedPaths && outputBytes <= limits.maxOutputBytes);
    check(Buffer.byteLength(path) + stats.suffixBytes <= 4096);
    roots.push({ path, entry });
  }
  // Count repeated subtree paths by multiplicity without allocating those paths
  // or output rows. Only after the complete externally pinned bounds pass may
  // the caller expand this authenticated DAG into its result array.
  return roots;
}
function leafState(reader, entry) {
  if (!entry) return null;
  check(entry.mode !== "40000");
  const fact = reader.get(entry.oid);
  check(fact.type === "blob");
  return { mode: entry.mode, oid: entry.oid, sha256: fact.sha256 };
}
function compareTrees(source, clean, before, after, rules, memo) {
  const keyOf = (oldTree, newTree, path) => `${path}\0${oldTree ?? "-"}\0${newTree ?? "-"}`;
  const rootKey = keyOf(before, after, "");
  const stack = [{ before, after, path: "", index: 0 }];
  while (stack.length) {
    source.budget?.step(stack.length, memo.size + 1);
    const frame = stack.at(-1),
      key = keyOf(frame.before, frame.after, frame.path);
    if (memo.has(key)) {
      source.budget?.release(frame.activeEntries ?? 0);
      stack.pop();
      continue;
    }
    if (frame.before === frame.after && frame.before !== null) {
      check(contentDigest(source, frame.before) === contentDigest(clean, frame.after));
      memo.set(key, digest(["preserved", contentDigest(source, frame.before)]));
      stack.pop();
      continue;
    }
    if (!frame.names) {
      const oldFact = frame.before ? source.get(frame.before) : null;
      const newFact = frame.after ? clean.get(frame.after) : null;
      check(!oldFact || oldFact.type === "tree");
      check(!newFact || newFact.type === "tree");
      const oldEntries = oldFact?.entries ?? [],
        newEntries = newFact?.entries ?? [];
      frame.activeEntries = 3 * (oldEntries.length + newEntries.length);
      source.budget?.retain(frame.activeEntries);
      frame.old = new Map(oldEntries.map((entry) => [entry.name, entry]));
      frame.new = new Map(newEntries.map((entry) => [entry.name, entry]));
      frame.names = [...new Set([...frame.old.keys(), ...frame.new.keys()])].sort();
      check(frame.names.length > 0); // no unmanifested empty-directory topology change
      frame.parts = [];
    }
    if (frame.index === frame.names.length) {
      memo.set(key, digest(["changed-tree", frame.parts]));
      source.budget?.release(frame.activeEntries);
      stack.pop();
      continue;
    }
    const name = frame.names[frame.index],
      oldEntry = frame.old.get(name),
      newEntry = frame.new.get(name);
    const path = frame.path ? `${frame.path}/${name}` : name;
    pathOf(path);
    if (oldEntry?.mode === "40000" || newEntry?.mode === "40000") {
      check(!oldEntry || oldEntry.mode === "40000");
      check(!newEntry || newEntry.mode === "40000");
      const childKey = keyOf(oldEntry?.oid ?? null, newEntry?.oid ?? null, path);
      if (!memo.has(childKey)) {
        stack.push({ before: oldEntry?.oid ?? null, after: newEntry?.oid ?? null, path, index: 0 });
        continue;
      }
      frame.parts.push([name, memo.get(childKey)]);
      frame.index++;
      continue;
    }
    const oldState = leafState(source, oldEntry),
      newState = leafState(clean, newEntry);
    if (equal(oldState, newState)) frame.parts.push([name, digest(["preserved-leaf", oldState])]);
    else {
      check(!protectedPath(path));
      const rule = rules.files.get(stable({ path, before: oldState, after: newState }));
      check(rule !== undefined);
      rules.usedFiles.add(rule);
      frame.parts.push([name, digest(["policy-leaf", rule, oldState, newState])]);
    }
    frame.index++;
  }
  return memo.get(rootKey);
}

function closedGraph(records, rootIndexes, edges, maxParents) {
  const children = records.map(() => []),
    remaining = records.map((row) => row[2].length);
  let actualEdges = 0,
    actualMax = 0;
  records.forEach((row, index) => {
    check(new Set(row[2]).size === row[2].length);
    actualMax = Math.max(actualMax, row[2].length);
    row[2].forEach((parent) => {
      integer(parent);
      check(parent < records.length);
      children[parent].push(index);
      actualEdges++;
    });
  });
  check(actualEdges === edges && actualMax === maxParents);
  const ready = [];
  remaining.forEach((count, index) => {
    if (count === 0) ready.push(index);
  });
  for (let cursor = 0; cursor < ready.length; cursor++)
    for (const child of children[ready[cursor]]) if (--remaining[child] === 0) ready.push(child);
  check(ready.length === records.length); // iterative Kahn: deep chains and cycles
  const reachable = new Set(),
    pending = [...rootIndexes];
  while (pending.length) {
    const index = pending.pop();
    integer(index);
    check(index < records.length);
    if (!reachable.has(index)) {
      reachable.add(index);
      pending.push(...records[index][2]);
    }
  }
  check(reachable.size === records.length);
}
function ancestor(records, before, after) {
  const pending = [after],
    seen = new Set();
  while (pending.length) {
    const index = pending.pop();
    if (index === before) return true;
    if (!seen.has(index)) {
      seen.add(index);
      pending.push(...records[index][2]);
    }
  }
  return false;
}
function pageSections(sections) {
  const pages = {},
    descriptors = {};
  for (const name of SECTIONS) {
    pages[name] = [];
    descriptors[name] = [];
    for (let start = 0; start < sections[name].length; start += PAGE_ROWS) {
      const rows = sections[name].slice(start, start + PAGE_ROWS),
        bytes = canonicalCompactBytes(rows);
      check(bytes.length <= PAGE_BYTES);
      pages[name].push(bytes);
      descriptors[name].push([hash(bytes), rows.length]);
    }
  }
  return { pages, descriptors };
}
function prepare({ scopeBytes, policyBytes, mapping, sourceRead, cleanRead }, readers) {
  const scope = scopeDocument(scopeBytes),
    rules = policyDocument(policyBytes, scope);
  check(Array.isArray(mapping) && mapping.length === scope.sourceCommitCount);
  const map = new Map(),
    physical = new Set();
  for (const row of mapping) {
    check(Array.isArray(row) && row.length === 2);
    sha(row[0]);
    sha(row[1]);
    check(!map.has(row[0]) && !physical.has(row[1]));
    map.set(row[0], row[1]);
    physical.add(row[1]);
  }
  const source =
    readers?.source ?? objectReader(sourceRead, scope.sourceObjectCount, scope.maxObjectBytes);
  const clean =
    readers?.clean ?? objectReader(cleanRead, scope.cleanObjectCount, scope.maxObjectBytes);
  const logical = [...map.keys()].sort(),
    indexes = new Map(logical.map((id, index) => [id, index]));
  const pairs = new Map(),
    comparisonMemo = new Map();
  const records = logical.map((id) => {
    const old = source.get(id),
      next = clean.get(map.get(id));
    check(old.type === "commit" && next.type === "commit");
    check(old.parents.length <= scope.maxParents && next.parents.length <= scope.maxParents);
    check(
      equal(
        next.parents,
        old.parents.map((parent) => {
          check(map.has(parent));
          return map.get(parent);
        }),
      ),
    );
    const metadata = rules.metadata.get(id);
    if (metadata) {
      check(
        metadata.beforeSha256 === old.metadataSha256 &&
          metadata.afterSha256 === next.metadataSha256,
      );
      rules.usedMetadata.add(id);
    } else check(old.metadataSha256 === next.metadataSha256);
    const immutable = provenanceDigest(source, old.tree);
    check(immutable === provenanceDigest(clean, next.tree));
    const pairKey = `${old.tree}:${next.tree}`;
    if (!pairs.has(pairKey))
      pairs.set(pairKey, [
        old.tree,
        next.tree,
        immutable,
        compareTrees(source, clean, old.tree, next.tree, rules, comparisonMemo),
      ]);
    return [
      id,
      map.get(id),
      old.parents.map((parent) => indexes.get(parent)),
      old.sha256,
      old.metadataSha256,
      next.metadataSha256,
      pairKey,
    ];
  });
  const refs = scope.sourceRefs
    .map((ref) => [digest(ref.name), ref.name.startsWith("refs/heads/") ? "h" : "t", ref.revision])
    .sort((a, b) => a[0].localeCompare(b[0]));
  const roots = [...refs.map((ref) => ref[2]), ...scope.dependencyRoots].map((id) => {
    check(indexes.has(id));
    return indexes.get(id);
  });
  closedGraph(records, roots, scope.sourceParentEdges, scope.maxParents);
  check(indexes.has(scope.sourceAnchor) && indexes.has(scope.bootstrapRevision));
  check(ancestor(records, indexes.get(scope.bootstrapRevision), indexes.get(scope.sourceAnchor)));
  check(
    source.facts.size === scope.sourceObjectCount && clean.facts.size === scope.cleanObjectCount,
  );
  check(
    rules.usedFiles.size === rules.policy.files.length &&
      rules.usedMetadata.size === rules.policy.metadata.length,
  );
  const projections = [...pairs.values()].sort((a, b) =>
    `${a[0]}:${a[1]}`.localeCompare(`${b[0]}:${b[1]}`),
  );
  const projectionIndexes = new Map(
    projections.map((row, index) => [`${row[0]}:${row[1]}`, index]),
  );
  records.forEach((row) => {
    row[6] = projectionIndexes.get(row[6]);
  });
  const objects = [...clean.facts]
    .map(([oid, fact]) => [oid, TYPE[fact.type], fact.size, fact.sha256])
    .sort((a, b) => a[0].localeCompare(b[0]));
  const counts = {
    commits: records.length,
    projections: projections.length,
    objects: objects.length,
    refs: refs.length,
    dependencies: scope.dependencyRoots.length,
    edges: scope.sourceParentEdges,
    sourceObjects: scope.sourceObjectCount,
  };
  const { pages, descriptors } = pageSections({
    commits: records,
    projections,
    objects,
    refs,
    dependencies: scope.dependencyRoots,
  });
  const header = {
    schemaVersion: 1,
    repositoryId: scope.repositoryId,
    migrationId: scope.migrationId,
    scopeSha256: hash(scopeBytes),
    policySha256: hash(policyBytes),
    sourceAnchor: scope.sourceAnchor,
    bootstrapRevision: scope.bootstrapRevision,
    cleanAnchor: map.get(scope.sourceAnchor),
    counts,
    maxParents: scope.maxParents,
    maxObjectBytes: scope.maxObjectBytes,
    pages: descriptors,
  };
  return { headerBytes: canonicalCompactBytes(header), pages };
}
export function prepareCompactRedaction(input) {
  return guarded(() => prepare(input));
}

// The only path to these preloaded facts is authenticated raw Git IO below.
// Neither this index nor a hash-only facts import is part of the public API.
const PREPARATION_CAPS = {
  normalBatchBytes: 64 * 1024 ** 2,
  objectsPerBatch: 4096,
  maxObjects: 500_000,
  maxCommits: 32768,
  maxCommitBytes: 256 * 1024,
  maxCommitTotalBytes: 32 * 1024 ** 2,
  maxTreeRounds: 128,
  maxSteps: 100_000_000,
  maxComparisonEntries: 2_000_000,
  maxActiveEntries: 262144,
  maxDepth: 4096,
  maxRssBytes: 8 * 1024 ** 3,
  maxDurationMs: 30 * 60 * 1000,
};
function preparationBudget(input) {
  keys(input, [...Object.keys(PREPARATION_CAPS), "treeArenaLimits"]);
  const limits = { ...input, treeArenaLimits: { ...input.treeArenaLimits } };
  for (const [key, cap] of Object.entries(PREPARATION_CAPS)) {
    integer(limits[key], 1);
    check(limits[key] <= cap);
  }
  const deadline = performance.now() + limits.maxDurationMs;
  let steps = 0,
    active = 0;
  const budget = {
    step(depth = 0, memo = 0) {
      check(
        ++steps <= limits.maxSteps &&
          depth <= limits.maxDepth &&
          memo <= limits.maxComparisonEntries,
      );
      check(performance.now() < deadline && process.memoryUsage.rss() <= limits.maxRssBytes);
    },
    retain(count) {
      check(active + count <= limits.maxActiveEntries);
      active += count;
    },
    release(count) {
      active -= count;
      check(active >= 0);
    },
  };
  budget.step();
  return { limits, budget };
}
function ingestGitStore(store, commitIds, count, scope, limits, budget) {
  check(count <= limits.maxObjects && commitIds.length <= limits.maxCommits);
  const arena = createBoundedTreeArena(limits.treeArenaLimits);
  try {
    const started = performance.now(),
      contentBatches = { commit: 0, tree: 0, blob: 0 };
    let largestPayloadBatchBytes = 0;
    const index = new Map(),
      expected = new Map(),
      used = new Map();
    let commitBytes = 0,
      sealed = false;
    const discover = (oid, type) => {
      sha(oid);
      if (expected.has(oid)) check(expected.get(oid) === type);
      else {
        check(expected.size < count);
        expected.set(oid, type);
      }
    };
    const ingest = (object, hint) => {
      budget.step();
      check(
        object.oid === hint.oid && object.type === hint.type && object.bytes.length === hint.size,
      );
      check(expected.get(object.oid) === object.type && !index.has(object.oid));
      const bytes = object.bytes;
      check(bytes.length <= scope.maxObjectBytes);
      check(
        createHash("sha1")
          .update(`${object.type} ${bytes.length}\0`)
          .update(bytes)
          .digest("hex") === object.oid,
      );
      const fact = { type: object.type, size: bytes.length, sha256: hash(bytes) };
      if (object.type === "commit") {
        commitBytes += bytes.length;
        check(bytes.length <= limits.maxCommitBytes && commitBytes <= limits.maxCommitTotalBytes);
        Object.assign(fact, parseCommit(bytes));
        discover(fact.tree, "tree");
      } else if (object.type === "tree") {
        arena.put(object.oid, bytes);
        const treeOid = object.oid;
        Object.defineProperty(fact, "entries", { get: () => arena.entries(treeOid) });
        for (const entry of fact.entries)
          discover(entry.oid, entry.mode === "40000" ? "tree" : "blob");
      }
      index.set(object.oid, Object.freeze(fact));
    };
    const batches = (oids) => {
      // Size hints are only scheduling data. readBatch and ingest re-authenticate
      // actual type/size/content and reject a changed hint instead of trusting it.
      for (let start = 0; start < oids.length; start += limits.objectsPerBatch) {
        budget.step();
        const hints = store.inspectBatch(oids.slice(start, start + limits.objectsPerBatch));
        let pack = [],
          bytes = 0;
        const flush = () => {
          if (!pack.length) return;
          contentBatches[pack[0].type]++;
          largestPayloadBatchBytes = Math.max(largestPayloadBatchBytes, bytes);
          const objects = store.readBatch(pack.map((hint) => hint.oid));
          check(objects.length === pack.length);
          for (let i = 0; i < objects.length; i++) ingest(objects[i], pack[i]);
          pack = [];
          bytes = 0;
          // No object bytes escape this batch. Blobs retain only their digest.
        };
        for (const hint of hints) {
          check(expected.get(hint.oid) === hint.type && hint.size <= scope.maxObjectBytes);
          if (pack.length && bytes + hint.size > limits.normalBatchBytes) flush();
          pack.push(hint);
          bytes += hint.size;
          if (bytes >= limits.normalBatchBytes) flush();
        }
        flush();
      }
    };
    commitIds.forEach((oid) => discover(oid, "commit"));
    batches(commitIds);
    let rounds = 0;
    // Each frontier is a bounded OID set, never expanded per path/commit.
    while (true) {
      const frontier = [];
      for (const [oid, type] of expected)
        if (type === "tree" && !index.has(oid)) frontier.push(oid);
      if (!frontier.length) break;
      check(++rounds <= limits.maxTreeRounds);
      batches(frontier);
    }
    batches([...expected].filter(([, type]) => type === "blob").map(([oid]) => oid));
    check(index.size === count && expected.size === count);
    sealed = true;
    const reader = {
      facts: used,
      content: new Map(),
      provenance: new Map(),
      budget,
      get(oid) {
        budget.step();
        sha(oid);
        check(sealed && index.has(oid));
        const fact = index.get(oid);
        used.set(oid, fact);
        return fact;
      },
      raw() {
        fail();
      }, // No old payload fallback after the raw ingestion phase.
    };
    return {
      reader,
      arena,
      assertComplete: () => check(used.size === index.size),
      statistics: Object.freeze({
        contentBatches: Object.freeze(contentBatches),
        largestPayloadBatchBytes,
        ingestionDurationMs: Math.round(performance.now() - started),
      }),
    };
  } catch (error) {
    arena.close();
    throw error;
  }
}
export function prepareCompactRedactionFromGit(input) {
  return guarded(() => {
    keys(input, [
      "scopeBytes",
      "policyBytes",
      "mapping",
      "sourceDescriptor",
      "cleanDescriptor",
      "preparationLimits",
    ]);
    const scope = scopeDocument(input.scopeBytes);
    policyDocument(input.policyBytes, scope);
    const { limits, budget } = preparationBudget(input.preparationLimits);
    check(scope.sourceCommitCount <= limits.maxCommits);
    check(
      scope.sourceObjectCount <= limits.maxObjects && scope.cleanObjectCount <= limits.maxObjects,
    );
    check(Array.isArray(input.mapping) && input.mapping.length === scope.sourceCommitCount);
    const old = new Set(),
      clean = new Set();
    for (const row of input.mapping) {
      check(Array.isArray(row) && row.length === 2);
      sha(row[0]);
      sha(row[1]);
      check(!old.has(row[0]) && !clean.has(row[1]));
      old.add(row[0]);
      clean.add(row[1]);
    }
    for (const descriptor of [input.sourceDescriptor, input.cleanDescriptor]) {
      check(descriptor?.limits?.maxBatchObjects >= limits.objectsPerBatch);
      check(
        descriptor.limits.maxBatchBytes >= scope.maxObjectBytes &&
          descriptor.limits.maxBatchBytes >= limits.normalBatchBytes,
      );
    }
    // Descriptors must be supplied by a protected offline caller. This result
    // remains unsigned and cannot install a key or native source capability.
    const stores = openIsolatedGitObjectStores({
      source: input.sourceDescriptor,
      clean: input.cleanDescriptor,
    });
    let source, next;
    try {
      source = ingestGitStore(
        stores.source,
        [...old],
        scope.sourceObjectCount,
        scope,
        limits,
        budget,
      );
      next = ingestGitStore(
        stores.clean,
        [...clean],
        scope.cleanObjectCount,
        scope,
        limits,
        budget,
      );
      const result = prepare(input, { source: source.reader, clean: next.reader });
      source.assertComplete();
      next.assertComplete();
      budget.step();
      stores.source.assertCurrentIsolation();
      stores.clean.assertCurrentIsolation();
      return {
        ...result,
        preparationStatistics: Object.freeze({
          source: stores.source.statistics(),
          clean: stores.clean.statistics(),
          sourceTrees: source.arena.statistics(),
          cleanTrees: next.arena.statistics(),
          sourcePreparation: source.statistics,
          cleanPreparation: next.statistics,
        }),
      };
    } finally {
      source?.arena.close();
      next?.arena.close();
      stores.source.close();
      stores.clean.close();
    }
  });
}

function countsShape(counts) {
  keys(counts, COUNT_KEYS);
  COUNT_KEYS.forEach((key) => integer(counts[key], ["edges"].includes(key) ? 0 : 1));
  check(counts.objects >= counts.commits && counts.sourceObjects >= counts.commits);
}
function headerBudget(counts) {
  countsShape(counts);
  const pageCount = SECTIONS.reduce(
    (total, name) => total + Math.ceil(counts[name] / PAGE_ROWS),
    0,
  );
  return Math.min(1024 * 1024, integer(4096 + pageCount * 128, 1));
}
function signatureValid(bytes, signatureBase64, publicKeySpkiBase64) {
  const base64 = (text) => {
    check(typeof text === "string" && text.length <= 1024);
    const bytes = Buffer.from(text, "base64");
    check(bytes.toString("base64") === text);
    return bytes;
  };
  const key = createPublicKey({ key: base64(publicKeySpkiBase64), format: "der", type: "spki" });
  const signature = base64(signatureBase64);
  check(key.asymmetricKeyType === "ed25519" && signature.length === 64);
  check(verify(null, compactSignatureMessage(bytes), key, signature));
}
function verifyFormat({ headerBytes, pages, signatureBase64, trust }) {
  keys(trust, [
    "schemaVersion",
    "migrationId",
    "repositoryId",
    "sourceAnchor",
    "bootstrapRevision",
    "cleanAnchor",
    "scopeSha256",
    "policySha256",
    "headerSha256",
    "counts",
    "maxParents",
    "maxObjectBytes",
    "publicKeySpkiBase64",
    "provenanceInventoryLimits",
  ]);
  identity(trust);
  countsShape(trust.counts);
  hashed(trust.headerSha256);
  hashed(trust.scopeSha256);
  hashed(trust.policySha256);
  integer(trust.maxParents);
  check(trust.maxParents <= 16);
  integer(trust.maxObjectBytes, 1);
  check(trust.maxObjectBytes <= 128 * 1024 * 1024);
  keys(trust.provenanceInventoryLimits, ["maxExpandedPaths", "maxOutputBytes"]);
  const inventoryLimits = { ...trust.provenanceInventoryLimits };
  integer(inventoryLimits.maxExpandedPaths, 1);
  integer(inventoryLimits.maxOutputBytes, 3);
  // Independently installed trust may tighten these explicit ceilings. A real
  // inventory (currently 893 fragments) still needs its own reviewed limits.
  check(inventoryLimits.maxExpandedPaths <= 4096);
  check(inventoryLimits.maxOutputBytes <= 4 * 1024 * 1024);
  check(Buffer.isBuffer(headerBytes) && headerBytes.length <= headerBudget(trust.counts));
  check(hash(headerBytes) === trust.headerSha256);
  signatureValid(headerBytes, signatureBase64, trust.publicKeySpkiBase64);
  const header = document(headerBytes, headerBudget(trust.counts));
  keys(header, [
    "schemaVersion",
    "migrationId",
    "repositoryId",
    "sourceAnchor",
    "bootstrapRevision",
    "cleanAnchor",
    "scopeSha256",
    "policySha256",
    "counts",
    "maxParents",
    "maxObjectBytes",
    "pages",
  ]);
  identity(header);
  for (const name of [
    "migrationId",
    "repositoryId",
    "sourceAnchor",
    "bootstrapRevision",
    "cleanAnchor",
    "scopeSha256",
    "policySha256",
    "maxParents",
    "maxObjectBytes",
  ])
    check(header[name] === trust[name]);
  check(equal(header.counts, trust.counts));
  sha(header.sourceAnchor);
  sha(header.cleanAnchor);
  sha(header.bootstrapRevision);
  keys(header.pages, SECTIONS);
  keys(pages, SECTIONS);
  const sections = {};
  const rowBudgets = {
    commits: 416 + header.maxParents * 12,
    projections: 256,
    objects: 160,
    refs: 128,
    dependencies: 48,
  };
  for (const name of SECTIONS) {
    const total = header.counts[name],
      expectedPages = Math.ceil(total / PAGE_ROWS);
    check(Array.isArray(header.pages[name]) && header.pages[name].length === expectedPages);
    check(Array.isArray(pages[name]) && pages[name].length === expectedPages);
    sections[name] = [];
    header.pages[name].forEach((descriptor, index) => {
      check(Array.isArray(descriptor) && descriptor.length === 2);
      hashed(descriptor[0]);
      const count = Math.min(PAGE_ROWS, total - index * PAGE_ROWS);
      check(descriptor[1] === count);
      const bytes = pages[name][index];
      check(Buffer.isBuffer(bytes) && hash(bytes) === descriptor[0]);
      const rows = document(bytes, Math.min(PAGE_BYTES, count * rowBudgets[name] + 32));
      check(Array.isArray(rows) && rows.length === count);
      sections[name].push(...rows);
    });
  }
  const { commits: records, projections, objects, refs, dependencies } = sections;
  ordered(records, (row) => row[0]);
  ordered(projections, (row) => `${row[0]}:${row[1]}`);
  ordered(objects, (row) => row[0]);
  ordered(refs, (row) => row[0]);
  ordered(dependencies);
  const logical = new Map(),
    physical = new Set(),
    usedProjections = new Set();
  records.forEach((row, index) => {
    check(Array.isArray(row) && row.length === 7);
    sha(row[0]);
    sha(row[1]);
    check(Array.isArray(row[2]));
    check(row[2].length <= header.maxParents);
    hashed(row[3]);
    hashed(row[4]);
    hashed(row[5]);
    integer(row[6]);
    check(row[6] < projections.length && !physical.has(row[1]));
    logical.set(row[0], index);
    physical.add(row[1]);
    usedProjections.add(row[6]);
  });
  check(usedProjections.size === projections.length);
  const catalogue = new Map();
  for (const row of objects) {
    check(Array.isArray(row) && row.length === 4);
    sha(row[0]);
    hashed(row[3]);
    check(["c", "t", "b"].includes(row[1]));
    integer(row[2]);
    check(row[2] <= header.maxObjectBytes);
    if (row[1] === "c") check(physical.has(row[0]));
    catalogue.set(row[0], row);
  }
  check(objects.filter((row) => row[1] === "c").length === records.length);
  records.forEach((row) => check(catalogue.get(row[1])?.[1] === "c"));
  for (const row of projections) {
    check(Array.isArray(row) && row.length === 4);
    sha(row[0]);
    sha(row[1]);
    hashed(row[2]);
    hashed(row[3]);
    check(catalogue.get(row[1])?.[1] === "t");
  }
  for (const row of refs) {
    check(Array.isArray(row) && row.length === 3);
    hashed(row[0]);
    check(row[1] === "h" || row[1] === "t");
    check(logical.has(row[2]));
  }
  dependencies.forEach((id) => {
    sha(id);
    check(logical.has(id));
  });
  check(dependencies.includes(header.bootstrapRevision));
  check(logical.has(header.sourceAnchor) && logical.has(header.bootstrapRevision));
  check(records[logical.get(header.sourceAnchor)][1] === header.cleanAnchor);
  check(refs.some((ref) => ref[1] === "h" && ref[2] === header.sourceAnchor));
  closedGraph(
    records,
    [...refs.map((ref) => logical.get(ref[2])), ...dependencies.map((id) => logical.get(id))],
    header.counts.edges,
    header.maxParents,
  );
  check(ancestor(records, logical.get(header.bootstrapRevision), logical.get(header.sourceAnchor)));
  const rowFor = (revision) => {
    sha(revision);
    check(logical.has(revision));
    return records[logical.get(revision)];
  };

  // This proves the signed FORMAT, not repository completeness, store isolation
  // or a native permission/deployment capability. External trusted IO remains a
  // separate boundary; no source/old-object callback exists on this consumer.
  return Object.freeze({
    status: "inactive-signed-format",
    counts: Object.freeze({ ...header.counts }),
    mappedRevisionPairs() {
      return Object.freeze(records.map((row) => Object.freeze([row[0], row[1]])));
    },
    resolveMapped(revision) {
      return rowFor(revision)[1];
    },
    logicalParents(revision) {
      return Object.freeze(rowFor(revision)[2].map((index) => records[index][0]));
    },
    isLogicalAncestor(before, after) {
      rowFor(before);
      rowFor(after);
      return ancestor(records, logical.get(before), logical.get(after));
    },
    cleanRetentionRef(revision) {
      rowFor(revision);
      return `refs/tags/signalo-permission-clean/${header.migrationId}/${revision}`;
    },
    openCleanReader(readObject) {
      check(typeof readObject === "function");
      const frame = () =>
        objectReader(readObject, header.counts.objects, header.maxObjectBytes, catalogue);
      const commit = (reader, revision) => {
        const row = rowFor(revision),
          fact = reader.get(row[1]);
        check(fact.type === "commit" && fact.metadataSha256 === row[5]);
        check(
          equal(
            fact.parents,
            row[2].map((index) => records[index][1]),
          ),
        );
        check(fact.tree === projections[row[6]][1]);
        return { row, fact };
      };
      return Object.freeze({
        readMappedCommit(revision) {
          return guarded(() => {
            const reader = frame(),
              current = commit(reader, revision);
            return Object.freeze({
              tree: current.fact.tree,
              parents: Object.freeze([...current.fact.parents]),
              metadataSha256: current.fact.metadataSha256,
            });
          });
        },
        readMappedFile(revision, path) {
          return guarded(() => {
            pathOf(path);
            const reader = frame(),
              current = commit(reader, revision);
            const entry = lookup(reader, current.fact.tree, path);
            if (!entry) return null;
            check(entry.mode !== "40000");
            const value = reader.raw(entry.oid);
            check(value.type === "blob");
            return value.bytes;
          });
        },
        readProvenanceInventory(revision) {
          return guarded(() => {
            const reader = frame(),
              current = commit(reader, revision);
            check(provenanceDigest(reader, current.fact.tree) === projections[current.row[6]][2]);
            const pending = boundedProvenanceRoots(reader, current.fact.tree, inventoryLimits),
              result = [];
            while (pending.length) {
              const { path, entry } = pending.pop(),
                fact = reader.get(entry.oid);
              if (entry.mode === "40000") {
                check(fact.type === "tree");
                fact.entries.forEach((child) =>
                  pending.push({ path: `${path}/${child.name}`, entry: child }),
                );
              } else {
                check(["100644", "100755"].includes(entry.mode) && fact.type === "blob");
                result.push({ path, mode: entry.mode, oid: entry.oid, sha256: fact.sha256 });
              }
            }
            result.sort((a, b) => (a.path < b.path ? -1 : a.path > b.path ? 1 : 0));
            return result;
          });
        },
        // Explicit offline audit, never called by a lazy read. This checks
        // complete clean catalogue reachability, including extra tree/blob
        // rows which cannot be disproved from hashes without materialization.
        auditCleanCatalogue() {
          return guarded(() => {
            const reader = frame();
            for (const row of records) {
              const current = commit(reader, row[0]);
              contentDigest(reader, current.fact.tree);
              check(provenanceDigest(reader, current.fact.tree) === projections[row[6]][2]);
            }
            check(reader.facts.size === catalogue.size);
            return Object.freeze({
              authenticatedObjects: reader.facts.size,
              commits: records.length,
            });
          });
        },
      });
    },
  });
}
export function verifyCompactRedaction(input) {
  return guarded(() => verifyFormat(input));
}
