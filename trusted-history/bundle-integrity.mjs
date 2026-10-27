import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { lstatSync, readFileSync, realpathSync, readdirSync } from "node:fs";
import { resolve, sep, dirname, relative } from "node:path";
import { builtinModules } from "node:module";
const hash = (bytes) => createHash("sha256").update(bytes).digest("hex");
const keys = (value, names) =>
  assert.deepEqual(Object.keys(value).sort(), [...names].sort());
export function verifyTrustedBundle(root) {
  assert.equal(realpathSync(root), resolve(root));
  const manifestPath = resolve(root, "manifest.json");
  const stat = lstatSync(manifestPath);
  assert.ok(
    stat.isFile() &&
      !stat.isSymbolicLink() &&
      stat.nlink === 1 &&
      stat.size > 0 &&
      stat.size <= 1024 * 1024,
  );
  const bytes = readFileSync(manifestPath);
  const manifest = JSON.parse(bytes.toString("utf8"));
  keys(manifest, ["schemaVersion", "files", "external", "count", "totalBytes"]);
  assert.equal(manifest.schemaVersion, 1);
  assert.ok(
    Array.isArray(manifest.files) &&
      manifest.files.length > 0 &&
      manifest.files.length <= 256,
  );
  assert.equal(manifest.count, manifest.files.length);
  assert.ok(
    Number.isSafeInteger(manifest.totalBytes) &&
      manifest.totalBytes > 0 &&
      manifest.totalBytes <= 16 * 1024 * 1024,
  );
  assert.ok(
    Array.isArray(manifest.external) &&
      manifest.external.every((x) => typeof x === "string"),
  );
  const names = new Set();
  let previous = "",
    total = 0;
  for (const row of manifest.files) {
    keys(row, ["path", "sha256", "bytes", "imports"]);
    assert.match(
      row.path,
      /^scripts\/(permission-registry|access-census|lib)\/[a-zA-Z0-9_.\/-]+\.mjs$/u,
    );
    assert.ok(
      !row.path.split("/").some((x) => x === "." || x === ".." || x === ""),
    );
    assert.ok(previous < row.path);
    previous = row.path;
    assert.match(row.sha256, /^[a-f0-9]{64}$/u);
    assert.ok(
      Number.isSafeInteger(row.bytes) &&
        row.bytes > 0 &&
        row.bytes <= 4 * 1024 * 1024,
    );
    assert.ok(
      Array.isArray(row.imports) &&
        row.imports.every((x) => typeof x === "string"),
    );
    const file = resolve(root, row.path);
    assert.ok(file.startsWith(root + sep));
    assert.equal(realpathSync(file), file);
    const info = lstatSync(file);
    assert.ok(
      info.isFile() &&
        !info.isSymbolicLink() &&
        info.nlink === 1 &&
        info.size === row.bytes,
    );
    const content = readFileSync(file);
    assert.equal(content.length, row.bytes);
    assert.equal(hash(content), row.sha256);
    total += content.length;
    names.add(row.path);
  }
  assert.equal(total, manifest.totalBytes);
  // A pinned bundle is an exact closure, not a directory into which additional
  // executable modules may be injected without changing the pinned manifest.
  const diskFiles = new Set();
  let entries = 0;
  const walk = (directory, depth = 0) => {
    assert.ok(depth <= 8);
    for (const name of readdirSync(directory)) {
      assert.ok(++entries <= 512);
      const file = resolve(directory, name);
      const info = lstatSync(file);
      assert.ok(!info.isSymbolicLink());
      if (info.isDirectory()) walk(file, depth + 1);
      else {
        assert.ok(info.isFile() && info.nlink === 1);
        diskFiles.add(relative(root, file));
      }
    }
  };
  walk(root);
  assert.deepEqual([...diskFiles].sort(), ["manifest.json", ...names].sort());
  const usedExternal = new Set();
  for (const row of manifest.files)
    for (const specifier of row.imports) {
      if (specifier.startsWith(".")) {
        const target = relative(
          root,
          resolve(root, dirname(row.path), specifier),
        );
        assert.ok(
          names.has(target),
          "Import must remain in the exact trusted bundle",
        );
      } else {
        assert.ok(
          specifier === "typescript" ||
            (specifier.startsWith("node:") &&
              builtinModules.includes(specifier.slice(5))),
        );
        usedExternal.add(specifier);
      }
    }
  assert.deepEqual([...usedExternal].sort(), [...manifest.external].sort());
  assert.ok(names.has("scripts/permission-registry/surface-gate.mjs"));
  assert.ok(names.has("scripts/permission-registry/history-revision-io.mjs"));
  assert.ok(
    names.has("scripts/permission-registry/prepare-history-git-parents.mjs"),
  );
  return Object.freeze({
    sha256: hash(bytes),
    files: manifest.count,
    bytes: total,
  });
}
