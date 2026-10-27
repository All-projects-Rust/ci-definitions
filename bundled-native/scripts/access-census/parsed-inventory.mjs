/** Invocation-local syntax/declaration reuse. Never stores an access verdict or history. */
import { AsyncLocalStorage } from "node:async_hooks";
import { createHash } from "node:crypto";
import ts from "typescript";

const inventory = new AsyncLocalStorage();
const MAX_SOURCE_ENTRIES = 8192;
const MAX_SOURCE_BYTES = 96 * 1024 * 1024;
const MAX_DISCOVERY_ENTRIES = 512;
const MAX_DISCOVERY_BYTES = 32 * 1024 * 1024;
const bytes = (value) => Buffer.byteLength(value, "utf8");

function close(scope) {
  scope.active = false;
  scope.sources.clear();
  scope.sourceOrder.clear();
  scope.discoveries.clear();
  scope.sourceBytes = 0;
  scope.discoveryBytes = 0;
}

/** Nested/concurrent calls get independent storage; late async children cannot reuse it. */
export function withParsedInventory(callback) {
  const scope = {
    active: true,
    compilerVersion: ts.version,
    sources: new Map(),
    sourceOrder: new Map(),
    discoveries: new Map(),
    sourceBytes: 0,
    discoveryBytes: 0,
  };
  return inventory.run(scope, () => {
    try {
      const result = callback();
      if (result && typeof result.then === "function")
        return Promise.resolve(result).finally(() => close(scope));
      close(scope);
      return result;
    } catch (error) {
      close(scope);
      throw error;
    }
  });
}

function current() {
  const scope = inventory.getStore();
  if (!scope?.active) return null;
  if (scope.compilerVersion !== ts.version) throw new Error("PARSED_INVENTORY_TOOLCHAIN_CHANGED");
  return scope;
}

function evictSource(scope) {
  const oldest = scope.sourceOrder.keys().next().value;
  scope.sourceOrder.delete(oldest);
  const versions = scope.sources.get(oldest.file);
  versions.delete(oldest.text);
  if (!versions.size) scope.sources.delete(oldest.file);
  scope.sourceBytes -= oldest.bytes;
}

/** ASTs are reused only by audited read-only consumers, with TypeScript's lazy fields intact. */
export function parseSource(file, text) {
  const scope = current();
  const cached = scope?.sources.get(file)?.get(text);
  if (cached) {
    scope.sourceOrder.delete(cached);
    scope.sourceOrder.set(cached, true);
    return cached.source;
  }
  const kind = /\.[jt]sx$/.test(file) ? ts.ScriptKind.TSX : ts.ScriptKind.TS;
  const source = ts.createSourceFile(file, text, ts.ScriptTarget.Latest, true, kind);
  if (!scope) return source;
  const size = bytes(file) + bytes(text);
  if (size > MAX_SOURCE_BYTES) return source;
  while (
    scope.sourceOrder.size >= MAX_SOURCE_ENTRIES ||
    scope.sourceBytes + size > MAX_SOURCE_BYTES
  )
    evictSource(scope);
  const entry = { file, text, source, bytes: size };
  if (!scope.sources.has(file)) scope.sources.set(file, new Map());
  scope.sources.get(file).set(text, entry);
  scope.sourceOrder.set(entry, true);
  scope.sourceBytes += size;
  return source;
}

/** Only the plain {surfaces, issues} declaration result is reusable, never proof/capability data. */
export function discoverSourceSnapshot(files, discover) {
  const scope = current();
  if (!scope) return discover(files);
  const snapshot = Object.freeze(
    files.map((input) => {
      const { file, text } = input;
      if (typeof file !== "string" || typeof text !== "string")
        throw new TypeError("Invalid source discovery input");
      return Object.freeze({ file, text });
    }),
  );
  // JSON pairs preserve file/text boundaries, list order, composition and duplicates.
  const hash = createHash("sha256").update(`typescript:${scope.compilerVersion}\n`);
  for (const input of snapshot) hash.update(JSON.stringify([input.file, input.text])).update("\n");
  const key = hash.digest("hex");
  const cached = scope.discoveries.get(key);
  if (cached && cached.producer === discover) {
    scope.discoveries.delete(key);
    scope.discoveries.set(key, cached);
    return structuredClone(cached.result);
  }
  const result = discover(snapshot);
  if (
    !result ||
    Object.keys(result).some((field) => field !== "surfaces" && field !== "issues") ||
    !Array.isArray(result.surfaces) ||
    !Array.isArray(result.issues)
  )
    throw new TypeError("Invalid source declaration result");
  const stored = structuredClone(result);
  const size = bytes(key) + bytes(JSON.stringify(stored));
  if (size <= MAX_DISCOVERY_BYTES) {
    if (cached) {
      scope.discoveryBytes -= cached.bytes;
      scope.discoveries.delete(key);
    }
    while (
      scope.discoveries.size >= MAX_DISCOVERY_ENTRIES ||
      scope.discoveryBytes + size > MAX_DISCOVERY_BYTES
    ) {
      const oldest = scope.discoveries.keys().next().value;
      scope.discoveryBytes -= scope.discoveries.get(oldest).bytes;
      scope.discoveries.delete(oldest);
    }
    scope.discoveries.set(key, { producer: discover, result: stored, bytes: size });
    scope.discoveryBytes += size;
  }
  // Even the first caller gets its own object graph; mutations cannot poison stored declarations.
  return structuredClone(stored);
}
