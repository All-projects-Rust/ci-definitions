import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import {
  mkdtempSync,
  mkdirSync,
  writeFileSync,
  rmSync,
  symlinkSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { test } from "node:test";
import {
  assertClassifiedRuntime,
  currentRuntimeClosure,
  isolatedRuntimeContext,
} from "./runtime-binding-acceptance.mjs";
import {
  completeRuntimeResponse,
  readRuntimeResponse,
  runtimeApiDirectory,
  runtimeClosureNames,
  sandboxCandidate,
  validateStageAReceipt,
} from "./runtime-binding-protocol.mjs";
import {
  resolveRuntimeImport,
  transpileRuntimeSource,
} from "./runtime-ts-loader.mjs";
import { verifySurfaceLedgerBindings } from "../bundled-native/scripts/permission-registry/surface-gate.mjs";

const sha = "a".repeat(40),
  base = "b".repeat(40),
  definition = "c".repeat(40),
  hash = "d".repeat(64);
function closure(adapter = `new Set(["patients:READ"])`, manifestPrefix = "") {
  return runtimeClosureNames.map((name) => {
    let source = name.endsWith(".json") ? "{}\n" : "export {};\n";
    if (name === "permission-manifest.ts")
      source = `${manifestPrefix}\nexport const CODE_DEFINED_REPORT_BINDINGS = [{reportId:"clinic",permission:"patients:READ"}];\n`;
    if (name === "permission-adapter.contracts.ts")
      source = `export function permissionRuntimeSurfaceBindingContext(reports: readonly {reportId:string;permission:string}[]){return {knownPermissions:new Set(["patients:READ"]),adapterBindings:new Map([["access-policy-runtime-v1",${adapter}]]),codeDefinedReports:new Map(reports.map(r=>[r.reportId,r.permission]))};}\n`;
    return {
      path: `${runtimeApiDirectory}/${name}`,
      bytes: Buffer.from(source),
    };
  });
}
const ledger = () => ({
  entries: [
    {
      id: "synthetic-bound",
      disposition: "BOUND",
      resourceKey: "patients",
      action: "READ",
      tags: ["report"],
      bindingProof: { enforcementAdapter: "access-policy-runtime-v1" },
      codeDefinedReportId: "clinic",
    },
    ...Array.from({ length: 1000 }, (_, i) => ({
      id: `synthetic-exempt-${i}`,
      disposition: "EXEMPT",
    })),
  ],
});
const checked = (context, patch = {}) =>
  assertClassifiedRuntime({
    ledger: ledger(),
    result: { checked: 1001, bound: 1 },
    sourceProofs: 1,
    context,
    verifyBindings: verifySurfaceLedgerBindings,
    ...patch,
  });

test("completion protocol refuses empty exit-zero, stale nonce, extra output and mutated context", () => {
  const context = {
    knownPermissions: ["patients:READ"],
    adapterBindings: [["access-policy-runtime-v1", ["patients:READ"]]],
    codeDefinedReports: [["clinic", "patients:READ"]],
  };
  const bytes = completeRuntimeResponse(context, hash);
  assert.equal(
    readRuntimeResponse(bytes, hash).knownPermissions.has("patients:READ"),
    true,
  );
  for (const bad of [
    Buffer.alloc(0),
    Buffer.concat([bytes, Buffer.from("extra")]),
    Buffer.from(bytes.toString().replace("patients:READ", "patients:UPDATE")),
    Buffer.from("{}\n"),
  ])
    assert.throws(() => readRuntimeResponse(bad, hash));
  assert.throws(() => readRuntimeResponse(bytes, "e".repeat(64)));
});

test("Stage B requires the exact successful Stage A source/base/definition and legacy or active profile", () => {
  const context = {
    phase: "legacy",
    sourceSha: sha,
    baseSha: base,
    definitionSha: definition,
    descriptorSha256: "",
  };
  const receipt = {
    schemaVersion: 1,
    status: "verified",
    ...context,
    verifierSha256: hash,
    headerSha256: null,
    publicationTip: null,
    preparedRevisions: 2,
  };
  assert.equal(validateStageAReceipt(receipt, context, hash, null), true);
  for (const patch of [
    { status: "accepted" },
    { sourceSha: base },
    { baseSha: sha },
    { definitionSha: sha },
    { verifierSha256: "e".repeat(64) },
    { descriptorSha256: hash },
    { headerSha256: hash },
    { capability: "consumer-data-preparation" },
    { preparedRevisions: 0 },
  ])
    assert.throws(() =>
      validateStageAReceipt({ ...receipt, ...patch }, context, hash, null),
    );
  const active = { ...context, phase: "active", descriptorSha256: hash };
  const profile = {
    installation: {
      trust: { headerSha256: "e".repeat(64) },
      finalPublicationTip: sha,
    },
  };
  const activeReceipt = {
    ...receipt,
    ...active,
    headerSha256: profile.installation.trust.headerSha256,
    publicationTip: sha,
  };
  assert.equal(
    validateStageAReceipt(activeReceipt, active, hash, profile),
    true,
  );
  assert.throws(() =>
    validateStageAReceipt(
      { ...activeReceipt, publicationTip: base },
      active,
      hash,
      profile,
    ),
  );
});

test("runtime loader resolves only nine fixed files, strips types and rejects dynamic/require/external imports", () => {
  const parent = `file://${sandboxCandidate}/${runtimeApiDirectory}/permission-manifest.ts`;
  assert.match(
    resolveRuntimeImport("./permission-adapter.contracts", parent).url,
    /permission-adapter.contracts\.ts$/u,
  );
  assert.equal(resolveRuntimeImport("node:crypto", parent).url, "node:crypto");
  for (const spec of [
    "node:fs",
    "typescript",
    "@nestjs/common",
    "../../../other.ts",
    "./unknown",
    "file:///tmp/runtime/runtime-binding-child.mjs",
  ])
    assert.throws(() => resolveRuntimeImport(spec, parent));
  const file = `${sandboxCandidate}/${runtimeApiDirectory}/permission-manifest.ts`;
  assert.match(
    transpileRuntimeSource(file, Buffer.from("export const value: number=1;")),
    /value = 1/u,
  );
  for (const source of [
    "import('node:fs');",
    "require('node:fs');",
    "import fs from 'node:fs';",
    "import x from './unknown';",
    "import x = require('node:fs');",
  ])
    assert.throws(() => transpileRuntimeSource(file, Buffer.from(source)));
  assert.throws(() =>
    transpileRuntimeSource("/tmp/outside.ts", Buffer.from("export {};")),
  );
});

test("all original classified-current assertions remain, including runtime tuple and count parity", () => {
  const data = {
    knownPermissions: new Set(["patients:READ"]),
    adapterBindings: new Map([
      ["access-policy-runtime-v1", new Set(["patients:READ"])],
    ]),
    codeDefinedReports: new Map([["clinic", "patients:READ"]]),
  };
  assert.equal(checked(data), true);
  assert.throws(() => checked(data, { result: { checked: 1000, bound: 1 } }));
  assert.throws(() =>
    checked(data, {
      ledger: { entries: [] },
      result: { checked: 0, bound: 0 },
      sourceProofs: 0,
    }),
  );
  assert.throws(() => checked(data, { sourceProofs: 0 }));
  assert.throws(
    () => checked({ ...data, knownPermissions: new Set() }),
    /UNKNOWN_BOUND_PERMISSION/u,
  );
  assert.throws(
    () =>
      checked({
        ...data,
        adapterBindings: new Map([
          ["access-policy-runtime-v1", new Set(["patients:UPDATE"])],
        ]),
      }),
    /ADAPTER_TUPLE_MISMATCH/u,
  );
  assert.throws(
    () =>
      checked({
        ...data,
        codeDefinedReports: new Map([["clinic", "patients:UPDATE"]]),
      }),
    /REPORT_PERMISSION_MISMATCH/u,
  );
});

test("actual runtime source must match the exact tracked source SHA and rejects path substitution", () => {
  const root = mkdtempSync(join(tmpdir(), "runtime-current-source-"));
  const git = (...args) =>
    execFileSync("/usr/bin/git", args, {
      cwd: root,
      env: {
        PATH: "/usr/bin:/bin",
        GIT_CONFIG_NOSYSTEM: "1",
        GIT_CONFIG_GLOBAL: "/dev/null",
      },
      encoding: "utf8",
      stdio: ["ignore", "pipe", "pipe"],
    }).trim();
  try {
    for (const row of closure()) {
      const destination = join(root, row.path);
      mkdirSync(dirname(destination), { recursive: true });
      writeFileSync(destination, row.bytes);
    }
    git("init", "-q");
    git("add", ".");
    git(
      "-c",
      "user.name=Synthetic",
      "-c",
      "user.email=fixture@example.invalid",
      "commit",
      "-qm",
      "synthetic runtime fixture",
    );
    const source = git("rev-parse", "HEAD");
    assert.equal(currentRuntimeClosure(root, source).length, 9);
    assert.throws(() => currentRuntimeClosure(root, sha));
    const file = join(root, runtimeApiDirectory, "permission-manifest.ts");
    writeFileSync(file, "export {};\n");
    assert.throws(() => currentRuntimeClosure(root, source));
    rmSync(file);
    symlinkSync(
      join(root, runtimeApiDirectory, "access-policy.types.ts"),
      file,
    );
    assert.throws(() => currentRuntimeClosure(root, source));
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});

test("isolated actual runtime context passes, corrupted tuple fails, early exit-zero cannot pass", () => {
  const originalUmask = process.umask(0o077);
  try {
    const valid = isolatedRuntimeContext(closure());
    assert.equal(checked(valid), true);
  } finally {
    process.umask(originalUmask);
  }
  const corrupt = isolatedRuntimeContext(
    closure(`new Set(["patients:UPDATE"])`),
  );
  assert.throws(() => checked(corrupt), /ADAPTER_TUPLE_MISMATCH/u);
  assert.throws(() =>
    isolatedRuntimeContext(closure(undefined, "process.exit(0);")),
  );
  assert.throws(() =>
    isolatedRuntimeContext(
      closure(
        undefined,
        `process.getBuiltinModule("node:fs").writeFileSync("/tmp/runtime/runtime-binding-child.mjs","tampered");`,
      ),
    ),
  );
});
