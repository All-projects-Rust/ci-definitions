// Bounded metadata storage. This creates no provenance/trust capability.
import { createHash } from "node:crypto";

const fail = () => {
  throw new Error("HISTORY_REDACTION_TREE_ARENA_REFUSED");
};
const check = (value) => {
  if (!value) fail();
};
const SHA = /^[a-f0-9]{40}$/u;
const LIMITS = {
  maxRawBytes: 384 * 1024 ** 2,
  maxTrees: 500_000,
  maxCachedEntries: 1_000_000,
  maxCachedNameBytes: 32 * 1024 ** 2,
  maxTreeEntries: 32768,
  maxTreeNameBytes: 4 * 1024 ** 2,
};
function parse(bytes, limits) {
  const entries = [],
    names = new Set();
  let offset = 0,
    nameBytes = 0,
    previous;
  while (offset < bytes.length) {
    check(entries.length < Math.min(limits.maxTreeEntries, limits.maxCachedEntries));
    const space = bytes.indexOf(32, offset),
      nul = bytes.indexOf(0, space + 1);
    check(space > offset && nul > space + 1 && nul + 21 <= bytes.length);
    const modeBytes = bytes.subarray(offset, space);
    check(modeBytes.every((byte) => byte >= 0x30 && byte <= 0x37));
    const mode = modeBytes.toString("utf8");
    check(["40000", "100644", "100755", "120000"].includes(mode));
    const rawName = bytes.subarray(space + 1, nul);
    nameBytes += rawName.length;
    check(nameBytes <= limits.maxTreeNameBytes && nameBytes <= limits.maxCachedNameBytes);
    const name = rawName.toString("utf8");
    check(
      rawName.length <= 4096 &&
        Buffer.from(name).equals(rawName) &&
        name !== "." &&
        name !== ".." &&
        !/[\x00-\x1f\x7f\\/]/u.test(name),
    );
    check(!names.has(name));
    const order = Buffer.from(name + (mode === "40000" ? "/" : "\0"));
    check(!previous || Buffer.compare(previous, order) < 0);
    previous = order;
    names.add(name);
    entries.push(
      Object.freeze({ mode, name, oid: bytes.subarray(nul + 1, nul + 21).toString("hex") }),
    );
    offset = nul + 21;
  }
  check(entries.length <= limits.maxCachedEntries);
  return { entries: Object.freeze(entries), nameBytes };
}
export function createBoundedTreeArena(input) {
  try {
    check(input && Object.keys(input).sort().join() === Object.keys(LIMITS).sort().join());
    const limits = { ...input };
    for (const [key, cap] of Object.entries(LIMITS))
      check(Number.isSafeInteger(limits[key]) && limits[key] >= 1 && limits[key] <= cap);
    const raw = new Map(),
      cache = new Map();
    let rawBytes = 0,
      cachedEntries = 0,
      cachedNameBytes = 0,
      reparses = 0,
      closed = false;
    const boundary = (operation) => {
      try {
        check(!closed);
        return operation();
      } catch {
        closed = true;
        raw.clear();
        cache.clear();
        fail();
      }
    };
    const retain = (oid, parsed) => {
      while (
        cachedEntries + parsed.entries.length > limits.maxCachedEntries ||
        cachedNameBytes + parsed.nameBytes > limits.maxCachedNameBytes
      ) {
        const first = cache.keys().next().value,
          removed = cache.get(first);
        check(removed);
        cachedEntries -= removed.entries.length;
        cachedNameBytes -= removed.nameBytes;
        cache.delete(first);
      }
      cache.set(oid, parsed);
      cachedEntries += parsed.entries.length;
      cachedNameBytes += parsed.nameBytes;
      // Empty trees consume a Map entry too; bound independently of entry count.
      while (cache.size > Math.min(limits.maxTrees, limits.maxCachedEntries)) {
        const first = cache.keys().next().value,
          removed = cache.get(first);
        cache.delete(first);
        cachedEntries -= removed.entries.length;
        cachedNameBytes -= removed.nameBytes;
      }
      return parsed.entries;
    };
    return Object.freeze({
      put(oid, bytes) {
        return boundary(() => {
          check(
            typeof oid === "string" && SHA.test(oid) && Buffer.isBuffer(bytes) && !raw.has(oid),
          );
          check(raw.size < limits.maxTrees && rawBytes + bytes.length <= limits.maxRawBytes);
          check(
            createHash("sha1").update(`tree ${bytes.length}\0`).update(bytes).digest("hex") === oid,
          );
          const owned = Buffer.from(bytes),
            parsed = parse(owned, limits);
          raw.set(oid, owned);
          rawBytes += owned.length;
          retain(oid, parsed);
        });
      },
      entries(oid) {
        return boundary(() => {
          check(raw.has(oid));
          const found = cache.get(oid);
          if (found) {
            cache.delete(oid);
            cache.set(oid, found);
            return found.entries;
          }
          reparses++;
          return retain(oid, parse(raw.get(oid), limits));
        });
      },
      statistics() {
        return boundary(() =>
          Object.freeze({
            trees: raw.size,
            rawBytes,
            cachedEntries,
            cachedNameBytes,
            cachedTrees: cache.size,
            reparses,
          }),
        );
      },
      close() {
        closed = true;
        raw.clear();
        cache.clear();
      },
    });
  } catch {
    fail();
  }
}
