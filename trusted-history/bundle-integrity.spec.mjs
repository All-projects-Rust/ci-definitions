import { test } from "node:test";
import assert from "node:assert/strict";
import {
  mkdtempSync,
  mkdirSync,
  writeFileSync,
  rmSync,
  symlinkSync,
  linkSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createHash } from "node:crypto";
import { verifyTrustedBundle } from "./bundle-integrity.mjs";
const paths = [
  "history-revision-io.mjs",
  "prepare-history-git-parents.mjs",
  "surface-gate.mjs",
]
  .map((x) => "scripts/permission-registry/" + x)
  .sort();
function fixture(fn) {
  const root = mkdtempSync(join(tmpdir(), "trusted-history-integrity-"));
  try {
    mkdirSync(join(root, "scripts/permission-registry"), { recursive: true });
    const content = Buffer.from("export {};\n");
    for (const name of paths) writeFileSync(join(root, name), content);
    const files = paths.map((path) => ({
      path,
      sha256: createHash("sha256").update(content).digest("hex"),
      bytes: content.length,
      imports: [],
    }));
    const m = {
      schemaVersion: 1,
      files,
      external: [],
      count: files.length,
      totalBytes: files.length * content.length,
    };
    writeFileSync(join(root, "manifest.json"), JSON.stringify(m));
    fn(root, m);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
}
const save = (root, m) =>
  writeFileSync(join(root, "manifest.json"), JSON.stringify(m));
test("exact reviewed bundle bytes pass", () =>
  fixture((root) => assert.equal(verifyTrustedBundle(root).files, 3)));
test("unlisted executable or symlink in the bundle fails", () => {
  fixture((root) => {
    writeFileSync(join(root, "unlisted.mjs"), "export {};\n");
    assert.throws(() => verifyTrustedBundle(root));
  });
  fixture((root) => {
    symlinkSync(join(root, "scripts"), join(root, "extra"));
    assert.throws(() => verifyTrustedBundle(root));
  });
});
test("changed or missing module fails", () => {
  fixture((root) => {
    writeFileSync(join(root, paths[0]), "export {a};\n");
    assert.throws(() => verifyTrustedBundle(root));
  });
  fixture((root) => {
    rmSync(join(root, paths[0]));
    assert.throws(() => verifyTrustedBundle(root));
  });
});
test("symlinks and hardlinks fail", () => {
  fixture((root) => {
    rmSync(join(root, paths[0]));
    symlinkSync(join(root, paths[1]), join(root, paths[0]));
    assert.throws(() => verifyTrustedBundle(root));
  });
  fixture((root) => {
    rmSync(join(root, paths[0]));
    linkSync(join(root, paths[1]), join(root, paths[0]));
    assert.throws(() => verifyTrustedBundle(root));
  });
});
test("duplicate or unsafe paths and omitted mandatory module fail", () => {
  for (const mutate of [
    (m) => m.files.push(m.files[0]),
    (m) => (m.files[0].path = "scripts/permission-registry/../outside.mjs"),
    (m) => m.files.splice(0, 1),
  ])
    fixture((root, m) => {
      mutate(m);
      m.count = m.files.length;
      m.totalBytes = m.files.reduce((n, r) => n + r.bytes, 0);
      save(root, m);
      assert.throws(() => verifyTrustedBundle(root));
    });
});
test("manifest count, size and unexpected metadata fail", () => {
  for (const mutate of [
    (m) => m.count++,
    (m) => m.totalBytes++,
    (m) => (m.untrustedRoot = "elsewhere"),
    (m) => (m.files[0].sha256 = "A".repeat(64)),
  ])
    fixture((root, m) => {
      mutate(m);
      save(root, m);
      assert.throws(() => verifyTrustedBundle(root));
    });
});

test("imports cannot escape into candidate code or undeclared dependencies", () => {
  for (const imports of [
    ["../../../candidate/evil.mjs"],
    ["./missing.mjs"],
    ["untrusted-package"],
  ])
    fixture((root, m) => {
      m.files[0].imports = imports;
      save(root, m);
      assert.throws(() => verifyTrustedBundle(root));
    });
});
