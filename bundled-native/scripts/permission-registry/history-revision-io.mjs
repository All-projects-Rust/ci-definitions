// Native history reads use independently installed trust. Candidate files,
// CLI arguments and environment variables cannot select that trust.
import { createHash } from "node:crypto";
import {
  constants,
  closeSync,
  fstatSync,
  lstatSync,
  openSync,
  readFileSync,
  realpathSync,
} from "node:fs";
import { dirname, isAbsolute, join, resolve } from "node:path";
import { verifyCompactRedaction } from "./history-redaction-compact.mjs";
import { openIsolatedGitObjectStore } from "./history-redaction-git-io.mjs";
import { createBoundedTreeArena } from "./history-redaction-tree-arena.mjs";

const DIRECTORY = "/etc/signalo/history-redaction";
const DESCRIPTOR = `${DIRECTORY}/active.json`;
const SHA = /^[a-f0-9]{40}$/u;
const HASH = /^[a-f0-9]{64}$/u;
const SECTIONS = ["commits", "projections", "objects", "refs", "dependencies"];
const SCOPES = [
  "scripts/permission-registry/surface-history",
  "scripts/permission-registry/permission-surface-ledger.json",
  "scripts/permission-registry/permission-surface-baseline.json",
  "apps/api/src/modules/access-control/permission-identity-history.json",
];
const ERROR = "PERMISSION_HISTORY_REDACTION_TRUST_REFUSED";
const refuse = () => {
  throw new Error(ERROR);
};
const check = (condition) => {
  if (!condition) refuse();
};
const hash = (bytes) => createHash("sha256").update(bytes).digest("hex");
const guarded = (operation) => {
  try {
    return operation();
  } catch {
    refuse();
  }
};
const sha = (value) => {
  check(typeof value === "string" && SHA.test(value));
  return value;
};
const keys = (value, names) =>
  check(
    value &&
      typeof value === "object" &&
      !Array.isArray(value) &&
      Object.keys(value).sort().join() === [...names].sort().join(),
  );
const path = (value) => {
  check(
    typeof value === "string" &&
      value.length > 0 &&
      Buffer.byteLength(value) <= 4096 &&
      !/[\x00-\x1f\x7f]/u.test(value) &&
      isAbsolute(value) &&
      resolve(value) === value,
  );
  return value;
};
const signature = (stat) =>
  `${stat.dev}:${stat.ino}:${stat.uid}:${stat.mode}:${stat.size}:${stat.mtimeNs}:${stat.ctimeNs}`;

// Pure data validation; this function neither installs trust nor issues any
// native history/source capability. Only the fixed-path loader below does so.
export function parseHistoryInstallation(bytes) {
  return guarded(() => {
    check(Buffer.isBuffer(bytes) && bytes.length > 0 && bytes.length <= 64 * 1024);
    const text = bytes.toString("utf8");
    check(Buffer.from(text).equals(bytes));
    const value = JSON.parse(text);
    keys(value, [
      "schemaVersion",
      "repositoryId",
      "finalPublicationTip",
      "attestationDirectory",
      "cleanGitDirectory",
      "signatureBase64",
      "trust",
      "ioLimits",
      "verifierSha256",
    ]);
    check(
      value.schemaVersion === 1 &&
        value.repositoryId === "1201945594" &&
        value.trust?.repositoryId === value.repositoryId,
    );
    sha(value.finalPublicationTip);
    path(value.attestationDirectory);
    path(value.cleanGitDirectory);
    check(value.attestationDirectory !== value.cleanGitDirectory);
    check(typeof value.signatureBase64 === "string" && value.signatureBase64.length <= 128);
    check(typeof value.verifierSha256 === "string" && HASH.test(value.verifierSha256));
    check(
      value.trust &&
        typeof value.trust === "object" &&
        value.ioLimits &&
        typeof value.ioLimits === "object",
    );
    return value;
  });
}

function rootParents(file) {
  let current = dirname(file);
  for (;;) {
    const stat = lstatSync(current, { bigint: true });
    check(
      stat.isDirectory() &&
        !stat.isSymbolicLink() &&
        stat.uid === 0n &&
        (stat.mode & 0o022n) === 0n &&
        realpathSync(current) === current,
    );
    if (current === "/") return;
    current = dirname(current);
  }
}
function installationAbsent() {
  for (const current of ["/etc", "/etc/signalo", DIRECTORY]) {
    let stat;
    try {
      stat = lstatSync(current, { bigint: true });
    } catch (error) {
      if (error?.code === "ENOENT") return true;
      throw error;
    }
    check(
      stat.isDirectory() &&
        !stat.isSymbolicLink() &&
        stat.uid === 0n &&
        (stat.mode & 0o022n) === 0n &&
        realpathSync(current) === current,
    );
  }
  return false;
}
function boundedFile(file, maxBytes, administrator = false) {
  if (administrator) rootParents(file);
  const before = lstatSync(file, { bigint: true });
  check(
    before.isFile() &&
      !before.isSymbolicLink() &&
      before.nlink === 1n &&
      before.size > 0n &&
      before.size <= BigInt(maxBytes),
  );
  if (administrator) check(before.uid === 0n && (before.mode & 0o022n) === 0n);
  const fd = openSync(file, constants.O_RDONLY | constants.O_NOFOLLOW);
  try {
    check(signature(fstatSync(fd, { bigint: true })) === signature(before));
    const bytes = readFileSync(fd);
    check(bytes.length === Number(before.size));
    check(signature(fstatSync(fd, { bigint: true })) === signature(before));
    check(signature(lstatSync(file, { bigint: true })) === signature(before));
    return { bytes, identity: `${signature(before)}:${hash(bytes)}` };
  } finally {
    closeSync(fd);
  }
}

function commitFact(object) {
  check(object.type === "commit" && Buffer.isBuffer(object.bytes));
  const end = object.bytes.indexOf(Buffer.from("\n\n"));
  check(end > 0);
  const lines = object.bytes.subarray(0, end).toString("latin1").split("\n");
  check(/^tree [a-f0-9]{40}$/u.test(lines[0]));
  const parents = [];
  let index = 1;
  while (lines[index]?.startsWith("parent ")) parents.push(sha(lines[index++].slice(7)));
  check(
    parents.length <= 16 &&
      !lines.slice(index).some((line) => line.startsWith("tree ") || line.startsWith("parent ")),
  );
  return { tree: lines[0].slice(5), parents, bytes: object.bytes };
}

// This exported data adapter is deliberately nonauthoritative. Native callers
// never accept a returned adapter or user-supplied read callback; their memo
// obtains its reader exclusively from openInstalledHistoryReader(root).
export function inspectHistoryRevisionData(input) {
  return guarded(() => revisionData(input));
}
function revisionData({ format, store, installation, assertInstallation, descriptorSha256 }) {
  const pairs = format.mappedRevisionPairs();
  const logical = new Map(pairs),
    physical = new Map(pairs.map(([a, b]) => [b, a]));
  check(logical.size === pairs.length && physical.size === pairs.length);
  for (const [a, b] of pairs) check(!physical.has(a) || (physical.get(a) === a && a === b));
  let frame = null,
    frameBytes = 0;
  const retain = (oid, object) => {
    check(frame && !frame.has(oid) && Buffer.isBuffer(object?.bytes));
    frameBytes += object.bytes.length;
    check(frameBytes <= 128 * 1024 ** 2);
    frame.set(oid, object);
    return object;
  };
  const readObject = (oid) => {
    sha(oid);
    check(frame);
    return frame.get(oid) ?? retain(oid, store.read(oid));
  };
  const loadMany = (ids) => {
    const unique = [...new Set(ids)].filter((id) => !frame.has(sha(id)));
    const maxObjects = installation.ioLimits.maxBatchObjects ?? 64;
    const maxBytes = installation.ioLimits.maxBatchBytes ?? 32 * 1024 ** 2;
    for (let offset = 0; offset < unique.length; offset += maxObjects) {
      const chunk = unique.slice(offset, offset + maxObjects);
      if (!store.inspectBatch || !store.readBatch) {
        chunk.forEach(readObject);
        continue;
      }
      const descriptors = store.inspectBatch(chunk);
      let batch = [],
        size = 0;
      const flush = () => {
        if (!batch.length) return;
        const values = store.readBatch(batch);
        check(values.length === batch.length);
        values.forEach((value, index) => {
          check(value.oid === batch[index]);
          retain(batch[index], value);
        });
        batch = [];
        size = 0;
      };
      check(descriptors.length === chunk.length);
      descriptors.forEach((value, index) => {
        check(
          value.oid === chunk[index] &&
            Number.isSafeInteger(value.size) &&
            value.size >= 0 &&
            value.size <= maxBytes,
        );
        if (size + value.size > maxBytes) flush();
        batch.push(value.oid);
        size += value.size;
      });
      flush();
    }
  };
  const reader = format.openCleanReader(readObject);
  let closed = false;
  const boundary = (operation) => {
    try {
      check(!closed);
      check(frame === null);
      frame = new Map();
      frameBytes = 0;
      assertInstallation();
      store.assertCurrentIsolation();
      const value = operation();
      assertInstallation();
      store.assertCurrentIsolation();
      return value;
    } catch {
      closed = true;
      refuse();
    } finally {
      frame = null;
      frameBytes = 0;
    }
  };
  const publication = sha(installation.finalPublicationTip);
  // Cutover is a new attestation child, never a revision already represented
  // by either side of the signed historical mapping (including identity rows).
  check(!logical.has(publication) && !physical.has(publication));
  const trustDigest = hash(Buffer.from(JSON.stringify(installation)));
  const getCommit = (id) => commitFact(readObject(sha(id)));
  const validateMapped = (id) => {
    // The format reader freshly authenticates the actual clean commit payload,
    // metadata, root tree and ordered physical parents against the signed row.
    // Complete protected projection equality is checked by inventory() below.
    return reader.readMappedCommit(id);
  };
  const classify = (id) => {
    sha(id);
    if (physical.has(id)) {
      const old = physical.get(id);
      validateMapped(old);
      return old;
    }
    check(!logical.has(id));
    const seen = new Map(),
      active = new Set(),
      stack = [{ id, index: 0, descended: false }];
    let visits = 0;
    while (stack.length) {
      const frame = stack.at(-1),
        current = frame.id;
      if (seen.has(current)) {
        stack.pop();
        continue;
      }
      if (!frame.parents) {
        check(++visits <= 8192 && !active.has(current));
        active.add(current);
        if (physical.has(current)) {
          validateMapped(physical.get(current));
          seen.set(current, false);
          stack.pop();
          active.delete(current);
          continue;
        }
        check(!logical.has(current));
        const fact = getCommit(current);
        if (current === publication) {
          check(fact.parents.length === 1 && fact.parents[0] === installation.trust.cleanAnchor);
          validateMapped(installation.trust.sourceAnchor);
          seen.set(current, true);
          stack.pop();
          active.delete(current);
          continue;
        }
        check(fact.parents.length > 0);
        frame.parents = fact.parents;
      }
      if (frame.index < frame.parents.length) {
        const parent = frame.parents[frame.index];
        if (!seen.has(parent)) {
          check(!active.has(parent));
          stack.push({ id: parent, index: 0, descended: false });
          continue;
        }
        frame.descended = seen.get(parent) || frame.descended;
        frame.index++;
      } else {
        // Every unmapped commit must descend from the pinned publication tip;
        // unrelated historical roots cannot masquerade as post-cutover history.
        check(frame.descended);
        seen.set(current, true);
        stack.pop();
        active.delete(current);
      }
    }
    check(seen.get(id));
    return id;
  };
  const resolveReceipt = (id) => {
    sha(id);
    const actual = logical.has(id) ? logical.get(id) : id;
    if (logical.has(id)) validateMapped(id);
    else check(classify(id) === id);
    return Object.freeze({
      logicalRevision: id,
      physicalRevision: actual,
      migrationId: installation.trust.migrationId,
      trustDigest,
    });
  };
  const arena = createBoundedTreeArena({
    maxRawBytes: 64 * 1024 ** 2,
    maxTrees: 32768,
    maxCachedEntries: 32768,
    maxCachedNameBytes: 4 * 1024 ** 2,
    maxTreeEntries: 32768,
    maxTreeNameBytes: 4 * 1024 ** 2,
  });
  const trees = new Set();
  const entries = (id) => {
    const fact = readObject(id);
    check(fact.type === "tree");
    if (!trees.has(id)) {
      arena.put(id, fact.bytes);
      trees.add(id);
    }
    return arena.entries(id);
  };
  const lookup = (tree, name) => {
    let entry = { mode: "40000", oid: tree };
    for (const part of name.split("/")) {
      check(entry.mode === "40000");
      entry = entries(entry.oid).find((child) => child.name === part);
      if (!entry) return null;
    }
    return entry;
  };
  const inventory = (id) => {
    const resolved = resolveReceipt(id),
      fact = getCommit(resolved.physicalRevision),
      rows = [];
    let bytes = 0,
      expanded = 0;
    const pending = [];
    for (const scope of SCOPES) {
      const entry = lookup(fact.tree, scope);
      if (entry) pending.push({ name: scope, entry });
    }
    while (pending.length) {
      const wave = pending.splice(0);
      loadMany(wave.map(({ entry }) => entry.oid));
      for (const { name, entry } of wave) {
        check(++expanded <= installation.trust.provenanceInventoryLimits.maxExpandedPaths);
        if (entry.mode === "40000") {
          for (const child of entries(entry.oid)) {
            check(
              expanded + pending.length <=
                installation.trust.provenanceInventoryLimits.maxExpandedPaths,
            );
            pending.push({ name: `${name}/${child.name}`, entry: child });
          }
        } else {
          check(["100644", "100755"].includes(entry.mode));
          const object = readObject(entry.oid);
          check(object.type === "blob");
          bytes += object.bytes.length;
          check(bytes <= 128 * 1024 ** 2 && rows.length < 4096);
          rows.push({
            path: name,
            mode: entry.mode,
            oid: entry.oid,
            sha256: hash(object.bytes),
            bytes: object.bytes,
          });
        }
      }
    }
    rows.sort((a, b) => (a.path < b.path ? -1 : a.path > b.path ? 1 : 0));
    if (logical.has(id)) {
      const actual = rows.map(({ bytes: ignored, ...row }) => row);
      check(JSON.stringify(actual) === JSON.stringify(reader.readProvenanceInventory(id)));
    }
    return { resolved, fact, rows };
  };
  return Object.freeze({
    trustDigest,
    migrationId: installation.trust.migrationId,
    publicationTip: publication,
    cleanAnchor: installation.trust.cleanAnchor,
    descriptorSha256: descriptorSha256 ?? null,
    cleanStoreRoot: installation.cleanGitDirectory,
    bootstrapRevision: installation.trust.bootstrapRevision,
    resolveReceiptRevision: (id) => boundary(() => resolveReceipt(id)),
    classifyPhysicalRevision: (id) => boundary(() => classify(id)),
    mappedTransportRevision: (id) =>
      boundary(() => {
        sha(id);
        check(logical.has(id));
        return logical.get(id);
      }),
    cleanRetentionRef: (id) =>
      boundary(() => {
        resolveReceipt(id);
        return `refs/tags/signalo-permission-clean/${installation.trust.migrationId}/${id}`;
      }),
    readLogicalParents: (id) =>
      boundary(() => {
        const resolved = resolveReceipt(id);
        return Object.freeze(
          getCommit(resolved.physicalRevision).parents.map((parent) => classify(parent)),
        );
      }),
    isPhysicalAncestor: (before, after) =>
      boundary(() => {
        sha(before);
        sha(after);
        classify(before);
        classify(after);
        const pending = [after],
          graph = new Map();
        while (pending.length) {
          const id = pending.pop();
          if (graph.has(id)) continue;
          check(graph.size < 32768);
          const parents = physical.has(id)
            ? format.logicalParents(physical.get(id)).map((logicalId) => logical.get(logicalId))
            : getCommit(id).parents;
          graph.set(id, parents);
          if (id !== before) pending.push(...parents);
        }
        // Signed topology is only a discovery hint. Before using it, freshly
        // batch-authenticate every traversed physical commit and parent order.
        loadMany([...graph.keys()]);
        for (const [id, parents] of graph) {
          const actual = physical.has(id) ? validateMapped(physical.get(id)) : getCommit(id);
          check(JSON.stringify(actual.parents) === JSON.stringify(parents));
        }
        return graph.has(before);
      }),
    readSnapshot: (id) =>
      boundary(() => {
        const { resolved, fact, rows } = inventory(id);
        const identity = createHash("sha256")
          .update(trustDigest)
          .update(resolved.physicalRevision)
          .update(fact.bytes);
        const files = new Map();
        for (const row of rows) {
          identity.update(`${row.path}\0${row.mode}\0${row.oid}\0`).update(row.bytes);
          const text = row.bytes.toString("utf8");
          check(Buffer.from(text).equals(row.bytes));
          files.set(row.path, text);
        }
        return {
          identity: identity.digest("hex"),
          files,
          inventory: rows.map(({ path, mode, oid }) => ({ path, mode, blob: oid })),
          ...resolved,
        };
      }),
    readFile: (id, name) =>
      boundary(() => {
        check(
          typeof name === "string" &&
            name.length > 0 &&
            Buffer.byteLength(name) <= 4096 &&
            !/[\\\x00-\x1f\x7f]/u.test(name) &&
            name.split("/").every((part) => part && part !== "." && part !== "..") &&
            (name === SCOPES[0] ||
              name.startsWith(SCOPES[0] + "/") ||
              SCOPES.slice(1).includes(name)),
        );
        const snapshot = inventory(id);
        return snapshot.rows.find((row) => row.path === name)?.bytes ?? null;
      }),
    assertCurrent: () => boundary(() => true),
  });
}

export function openInstalledHistoryReader(repositoryRoot) {
  return guarded(() => {
    check(
      typeof repositoryRoot === "string" &&
        realpathSync(repositoryRoot) === resolve(repositoryRoot),
    );
    // Before installation the directory is absent. Once the administrator has
    // created it, a missing/invalid active.json is fatal, never legacy fallback.
    if (installationAbsent()) return null;
    const descriptor = boundedFile(DESCRIPTOR, 64 * 1024, true);
    const installation = parseHistoryInstallation(descriptor.bytes);
    const files = new Map([
      [DESCRIPTOR, { identity: descriptor.identity, maxBytes: 64 * 1024, administrator: true }],
    ]);
    const read = (name, maxBytes) => {
      const absolute = join(installation.attestationDirectory, name);
      check(realpathSync(dirname(absolute)) === dirname(absolute));
      const value = boundedFile(absolute, maxBytes);
      files.set(absolute, { identity: value.identity, maxBytes, administrator: false });
      return value.bytes;
    };
    const headerBytes = read("header.json", 16 * 1024 * 1024);
    check(hash(headerBytes) === installation.trust.headerSha256);
    const header = JSON.parse(headerBytes.toString("utf8"));
    const pages = {};
    for (const section of SECTIONS) {
      check(Array.isArray(header.pages?.[section]) && header.pages[section].length <= 2000);
      pages[section] = header.pages[section].map((_, index) =>
        read(`${section}/${index}.json`, 1024 * 1024),
      );
    }
    const format = verifyCompactRedaction({
      headerBytes,
      pages,
      signatureBase64: installation.signatureBase64,
      trust: installation.trust,
    });
    const store = openIsolatedGitObjectStore({
      root: installation.cleanGitDirectory,
      storeId: installation.trust.headerSha256,
      role: "clean",
      limits: installation.ioLimits,
    });
    const assertInstallation = () => {
      for (const [name, pinned] of files)
        check(
          boundedFile(name, pinned.maxBytes, pinned.administrator).identity === pinned.identity,
        );
    };
    return revisionData({
      format,
      store,
      installation,
      assertInstallation,
      descriptorSha256: hash(descriptor.bytes),
    });
  });
}
