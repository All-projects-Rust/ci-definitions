// Raw IO primitive. This does not sign, install trust or issue native authority.
// Explicit OID batches amortize Git processes; the synchronous compact callback
// reads one object freshly. The distinct inactive compact Git builder schedules
// size-inspected batches; these hints never authenticate payload contents.
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { lstatSync, opendirSync, realpathSync } from "node:fs";
import { isAbsolute, join, resolve } from "node:path";

const SHA = /^[a-f0-9]{40}$/u;
const ID = /^[a-f0-9]{64}$/u;
const TYPES = new Set(["commit", "tree", "blob"]);
const LIMIT_KEYS = [
  "maxObjectBytes",
  "maxBatchBytes",
  "maxBatchObjects",
  "maxHeaderBytes",
  "maxControlBytes",
  "maxObjectRequests",
  "maxCommands",
  "maxTotalBytes",
  "maxDurationMs",
  "maxCommandMs",
];
const REFUSAL = "HISTORY_REDACTION_GIT_IO_REFUSED";
const fail = () => {
  throw new Error(REFUSAL);
};
const check = (condition) => {
  if (!condition) fail();
};
const guarded = (fn) => {
  try {
    return fn();
  } catch {
    fail();
  }
};
function keys(value, expected) {
  check(value && typeof value === "object" && !Array.isArray(value));
  check(Object.keys(value).sort().join(",") === [...expected].sort().join(","));
}
function bounded(value, low, high) {
  check(Number.isSafeInteger(value) && value >= low && value <= high);
  return value;
}
function limitsOf(input) {
  keys(input, LIMIT_KEYS);
  const value = { ...input };
  bounded(value.maxObjectBytes, 1, 128 * 1024 * 1024);
  bounded(value.maxBatchBytes, value.maxObjectBytes, 256 * 1024 * 1024);
  bounded(value.maxBatchObjects, 1, 4096);
  bounded(value.maxHeaderBytes, 64, 256);
  bounded(value.maxControlBytes, value.maxHeaderBytes * value.maxBatchObjects, 4 * 1024 * 1024);
  bounded(value.maxObjectRequests, 1, 4_000_000);
  bounded(value.maxCommands, 1, 32_000_000);
  bounded(value.maxTotalBytes, value.maxBatchBytes, 64 * 1024 ** 3);
  bounded(value.maxDurationMs, 1, 30 * 60 * 1000);
  bounded(value.maxCommandMs, 1, Math.min(30_000, value.maxDurationMs));
  return Object.freeze(value);
}
function oidsOf(oids, limits) {
  check(Array.isArray(oids) && oids.length > 0 && oids.length <= limits.maxBatchObjects);
  const result = [...oids];
  result.forEach((oid) => check(typeof oid === "string" && SHA.test(oid)));
  check(new Set(result).size === result.length);
  return result;
}
function headerAt(bytes, offset, maxHeaderBytes) {
  check(Buffer.isBuffer(bytes));
  const window = bytes.subarray(offset, Math.min(bytes.length, offset + maxHeaderBytes + 1));
  const end = window.indexOf(10);
  check(end > 0 && end <= maxHeaderBytes);
  const header = window.subarray(0, end).toString("latin1");
  const match = /^([a-f0-9]{40}) (commit|tree|blob) (0|[1-9][0-9]*)$/u.exec(header);
  check(match);
  const size = Number(match[3]);
  check(Number.isSafeInteger(size));
  return { oid: match[1], type: match[2], size, next: offset + end + 1 };
}
function descriptorsOf(rows, limits, enforceTotal = true) {
  check(Array.isArray(rows) && rows.length > 0 && rows.length <= limits.maxBatchObjects);
  oidsOf(
    rows.map((row) => row?.oid),
    limits,
  );
  let total = 0;
  const result = rows.map((row) => {
    keys(row, ["oid", "type", "size"]);
    check(TYPES.has(row.type));
    bounded(row.size, 0, limits.maxObjectBytes);
    total += row.size;
    check(!enforceTotal || total <= limits.maxBatchBytes);
    return { ...row };
  });
  return { rows: result, total };
}
function information(bytes, oids, limits, enforceTotal = true) {
  check(Buffer.isBuffer(bytes) && bytes.length <= limits.maxControlBytes);
  let offset = 0;
  const rows = oids.map((oid) => {
    const row = headerAt(bytes, offset, limits.maxHeaderBytes);
    check(row.oid === oid);
    offset = row.next;
    return { oid, type: row.type, size: row.size };
  });
  check(offset === bytes.length);
  return descriptorsOf(rows, limits, enforceTotal);
}

// Exported pure decoder supports adversarial framing tests without replacing
// the production Git binary or introducing an injectable execution authority.
export function decodeRawGitBatch(input) {
  return guarded(() => {
    keys(input, ["bytes", "descriptors", "limits"]);
    const limits = limitsOf(input.limits),
      { rows, total } = descriptorsOf(input.descriptors, limits),
      bytes = input.bytes;
    check(Buffer.isBuffer(bytes));
    check(bytes.length <= total + rows.length * (limits.maxHeaderBytes + 2));
    const objects = [];
    let offset = 0;
    for (const expected of rows) {
      const row = headerAt(bytes, offset, limits.maxHeaderBytes);
      check(row.oid === expected.oid && row.type === expected.type && row.size === expected.size);
      check(row.next + row.size < bytes.length && bytes[row.next + row.size] === 10);
      const payload = bytes.subarray(row.next, row.next + row.size);
      check(
        createHash("sha1").update(`${row.type} ${row.size}\0`).update(payload).digest("hex") ===
          row.oid,
      );
      objects.push(Object.freeze({ oid: row.oid, type: row.type, bytes: Buffer.from(payload) }));
      offset = row.next + row.size + 1;
    }
    check(offset === bytes.length);
    return Object.freeze(objects);
  });
}

const ENV = Object.freeze({
  PATH: "/usr/bin:/bin",
  HOME: "/nonexistent",
  XDG_CONFIG_HOME: "/nonexistent",
  LANG: "C",
  LC_ALL: "C",
  GIT_CONFIG_NOSYSTEM: "1",
  GIT_CONFIG_SYSTEM: "/dev/null",
  GIT_CONFIG_GLOBAL: "/dev/null",
  GIT_CONFIG_COUNT: "0",
  GIT_ATTR_NOSYSTEM: "1",
  GIT_NO_REPLACE_OBJECTS: "1",
  GIT_NO_LAZY_FETCH: "1",
  GIT_ALLOW_PROTOCOL: "",
  GIT_PROTOCOL_FROM_USER: "0",
  GIT_OPTIONAL_LOCKS: "0",
  GIT_TERMINAL_PROMPT: "0",
});
const ARGS = Object.freeze([
  "--no-replace-objects",
  "-c",
  "protocol.allow=never",
  "-c",
  "core.hooksPath=/dev/null",
  "-c",
  "core.fsmonitor=false",
  "-c",
  "core.attributesFile=/dev/null",
  "-c",
  "credential.helper=",
  "-c",
  "core.askPass=/bin/false",
  "-c",
  "core.pager=cat",
  "-c",
  "maintenance.auto=false",
  "-c",
  "gc.auto=0",
]);
function maybeStat(path) {
  try {
    return lstatSync(path);
  } catch (error) {
    if (error?.code === "ENOENT") return null;
    throw error;
  }
}
function directory(path) {
  const stat = lstatSync(path, { bigint: true });
  check(stat.isDirectory() && !stat.isSymbolicLink() && realpathSync(path) === path);
  return `${stat.dev}:${stat.ino}`;
}
function pathOf(root) {
  check(typeof root === "string" && root.length > 0 && Buffer.byteLength(root) <= 4096);
  check(!/[\u0000-\u001f\u007f]/u.test(root) && isAbsolute(root) && resolve(root) === root);
  directory(root);
  return root;
}
function open(input) {
  keys(input, ["root", "storeId", "role", "limits"]);
  const root = pathOf(input.root),
    storeId = input.storeId,
    role = input.role,
    limits = limitsOf(input.limits);
  check(typeof storeId === "string" && ID.test(storeId));
  check(role === "source" || role === "clean");
  const deadline = performance.now() + limits.maxDurationMs;
  let closed = false,
    commands = 0,
    requests = 0,
    totalBytes = 0;
  const alive = () => check(!closed && performance.now() < deadline);
  const git = (args, maxBuffer = limits.maxControlBytes, input) => {
    alive();
    check(++commands <= limits.maxCommands);
    const remaining = Math.floor(deadline - performance.now());
    check(remaining > 0);
    const result = spawnSync("/usr/bin/git", [...ARGS, ...args], {
      cwd: root,
      env: { ...ENV },
      input,
      encoding: null,
      timeout: Math.min(remaining, limits.maxCommandMs),
      killSignal: "SIGKILL",
      maxBuffer,
      stdio: ["pipe", "pipe", "pipe"],
      shell: false,
    });
    alive();
    check(!result.error && result.status === 0 && result.signal === null);
    check(Buffer.isBuffer(result.stdout) && result.stdout.length <= maxBuffer);
    check(Buffer.isBuffer(result.stderr) && result.stderr.length === 0);
    return result.stdout;
  };
  const location = () => {
    const bytes = git([
      "rev-parse",
      "--path-format=absolute",
      "--git-dir",
      "--git-common-dir",
      "--show-object-format",
      "--is-shallow-repository",
    ]);
    const text = bytes.toString("utf8");
    check(Buffer.from(text).equals(bytes));
    const parts = text.split("\n");
    check(parts.length === 5 && parts[2] === "sha1" && parts[3] === "false" && parts[4] === "");
    return [pathOf(parts[0]), pathOf(parts[1])];
  };
  const [gitDir, commonDir] = location(),
    objectsDir = join(commonDir, "objects");
  const pins = new Map(
    [root, gitDir, commonDir, objectsDir].map((path) => [path, directory(path)]),
  );
  const packDir = join(objectsDir, "pack"),
    infoDir = join(objectsDir, "info");
  const isolation = () => {
    alive();
    for (const [path, identity] of pins) check(directory(path) === identity);
    for (const base of new Set([gitDir, commonDir]))
      for (const marker of [
        "shallow",
        "info/grafts",
        "objects/info/alternates",
        "objects/info/http-alternates",
      ])
        check(!maybeStat(join(base, marker)));
    for (const path of [infoDir, packDir]) if (maybeStat(path)) directory(path);
    if (maybeStat(packDir)) {
      const dir = opendirSync(packDir);
      try {
        let entry,
          count = 0;
        while ((entry = dir.readSync())) {
          check(++count <= 4096);
          check(!entry.name.toLowerCase().endsWith(".promisor"));
          const stat = lstatSync(join(packDir, entry.name));
          check(stat.isFile() && !stat.isSymbolicLink() && stat.nlink === 1);
        }
      } finally {
        dir.closeSync();
      }
    }
    const names = git(["config", "--includes", "--null", "--name-only", "--list"]);
    const text = names.toString("utf8");
    check(Buffer.from(text).equals(names) && text.endsWith("\0"));
    check(
      !text
        .slice(0, -1)
        .split("\0")
        .some((key) => {
          const lower = key.toLowerCase();
          return (
            lower === "extensions.partialclone" ||
            (lower.startsWith("remote.") &&
              (lower.endsWith(".promisor") || lower.endsWith(".partialclonefilter")))
          );
        }),
    );
    const current = location();
    check(current[0] === gitDir && current[1] === commonDir);
    check(git(["for-each-ref", "--format=%(refname)", "refs/replace"]).length === 0);
  };
  const looseObjects = (oids) => {
    for (const oid of oids) {
      const parent = join(objectsDir, oid.slice(0, 2));
      if (!maybeStat(parent)) continue;
      directory(parent);
      const stat = maybeStat(join(parent, oid.slice(2)));
      if (stat) check(stat.isFile() && !stat.isSymbolicLink() && stat.nlink === 1);
    }
  };
  const boundary = (operation) => {
    try {
      alive();
      return operation();
    } catch {
      closed = true;
      fail();
    }
  };
  const batch = (inputOids) =>
    boundary(() => {
      const oids = oidsOf(inputOids, limits);
      requests += oids.length;
      check(requests <= limits.maxObjectRequests);
      isolation();
      looseObjects(oids);
      const requestBytes = Buffer.from(oids.join("\n") + "\n");
      const descriptors = information(
        git(["cat-file", "--batch-check"], limits.maxControlBytes, requestBytes),
        oids,
        limits,
      );
      totalBytes += descriptors.total;
      check(totalBytes <= limits.maxTotalBytes);
      isolation();
      looseObjects(oids);
      const bytes = git(
        ["cat-file", "--batch"],
        descriptors.total + oids.length * (limits.maxHeaderBytes + 2),
        requestBytes,
      );
      const result = decodeRawGitBatch({ bytes, descriptors: descriptors.rows, limits });
      isolation();
      looseObjects(oids);
      return result;
    });
  const inspect = (inputOids) =>
    boundary(() => {
      const oids = oidsOf(inputOids, limits);
      requests += oids.length;
      check(requests <= limits.maxObjectRequests);
      isolation();
      looseObjects(oids);
      // Scheduling hints only. readBatch independently authenticates fresh bytes.
      const { rows } = information(
        git(
          ["cat-file", "--batch-check"],
          limits.maxControlBytes,
          Buffer.from(oids.join("\n") + "\n"),
        ),
        oids,
        limits,
        false,
      );
      isolation();
      looseObjects(oids);
      return Object.freeze(rows.map((row) => Object.freeze(row)));
    });
  isolation();
  const api = Object.freeze({
    storeId,
    role,
    read: (oid) => batch([oid])[0],
    readBatch: batch,
    inspectBatch: inspect,
    assertCurrentIsolation: () => boundary(isolation),
    snapshot(oids) {
      return Object.freeze({ storeId, role, objects: batch(oids) });
    },
    statistics() {
      return boundary(() =>
        Object.freeze({
          gitCommands: commands,
          requestedObjects: requests,
          payloadBytes: totalBytes,
        }),
      );
    },
    close() {
      closed = true;
    },
  });
  return { api, identity: directory(objectsDir) };
}
export function openIsolatedGitObjectStore(input) {
  return guarded(() => open(input).api);
}
export function openIsolatedGitObjectStores(input) {
  return guarded(() => {
    keys(input, ["source", "clean"]);
    check(input.source?.role === "source" && input.clean?.role === "clean");
    const source = open(input.source),
      clean = open(input.clean);
    check(source.api.storeId !== clean.api.storeId && source.identity !== clean.identity);
    return Object.freeze({ source: source.api, clean: clean.api });
  });
}
