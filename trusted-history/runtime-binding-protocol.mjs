import assert from "node:assert/strict";
import { createHash } from "node:crypto";

export const runtimeClosureNames = Object.freeze([
  "access-policy.declaration.ts",
  "access-policy.registry.ts",
  "access-policy.types.ts",
  "permission-adapter.contracts.ts",
  "permission-identity-history.json",
  "permission-manifest.history.ts",
  "permission-manifest.inventory.ts",
  "permission-manifest.shared.ts",
  "permission-manifest.ts",
]);
export const runtimeApiDirectory = "apps/api/src/modules/access-control";
export const sandboxCandidate = "/tmp/candidate";
export const sandboxRuntime = "/tmp/runtime";
export const hashBytes = (bytes) =>
  createHash("sha256").update(bytes).digest("hex");
export function exactKeys(value, names) {
  assert.ok(value && typeof value === "object" && !Array.isArray(value));
  assert.deepEqual(Object.keys(value).sort(), [...names].sort());
}
const string = (value) =>
  assert.ok(
    typeof value === "string" && value.length > 0 && value.length <= 256,
  );
function strings(values) {
  assert.ok(Array.isArray(values) && values.length <= 10000);
  values.forEach(string);
  assert.equal(new Set(values).size, values.length);
}
export function canonicalContext(context) {
  exactKeys(context, [
    "knownPermissions",
    "adapterBindings",
    "codeDefinedReports",
  ]);
  strings(context.knownPermissions);
  assert.ok(
    Array.isArray(context.adapterBindings) &&
      context.adapterBindings.length <= 256,
  );
  assert.ok(
    Array.isArray(context.codeDefinedReports) &&
      context.codeDefinedReports.length <= 10000,
  );
  const adapters = new Set(),
    reports = new Set();
  for (const row of context.adapterBindings) {
    assert.ok(Array.isArray(row) && row.length === 2);
    string(row[0]);
    strings(row[1]);
    assert.ok(!adapters.has(row[0]));
    adapters.add(row[0]);
  }
  for (const row of context.codeDefinedReports) {
    assert.ok(Array.isArray(row) && row.length === 2);
    row.forEach(string);
    assert.ok(!reports.has(row[0]));
    reports.add(row[0]);
  }
  return Buffer.from(
    JSON.stringify({
      knownPermissions: [...context.knownPermissions].sort(),
      adapterBindings: context.adapterBindings
        .map(([name, values]) => [name, [...values].sort()])
        .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)),
      codeDefinedReports: context.codeDefinedReports
        .map(([name, value]) => [name, value])
        .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0)),
    }) + "\n",
  );
}
export function completeRuntimeResponse(context, nonce) {
  assert.match(nonce, /^[a-f0-9]{64}$/u);
  const canonical = canonicalContext(context);
  return Buffer.from(
    JSON.stringify({
      schemaVersion: 1,
      nonce,
      context: JSON.parse(canonical.toString("utf8")),
      contextSha256: hashBytes(canonical),
    }) + "\n",
  );
}
export function readRuntimeResponse(bytes, expectedNonce) {
  assert.ok(
    Buffer.isBuffer(bytes) && bytes.length > 0 && bytes.length <= 1024 * 1024,
  );
  const text = bytes.toString("utf8");
  assert.deepEqual(Buffer.from(text), bytes);
  const value = JSON.parse(text);
  exactKeys(value, ["schemaVersion", "nonce", "context", "contextSha256"]);
  assert.equal(value.schemaVersion, 1);
  assert.equal(value.nonce, expectedNonce);
  const canonical = canonicalContext(value.context);
  assert.equal(hashBytes(canonical), value.contextSha256);
  assert.deepEqual(
    completeRuntimeResponse(value.context, expectedNonce),
    bytes,
  );
  return Object.freeze({
    knownPermissions: new Set(value.context.knownPermissions),
    adapterBindings: new Map(
      value.context.adapterBindings.map(([name, values]) => [
        name,
        new Set(values),
      ]),
    ),
    codeDefinedReports: new Map(value.context.codeDefinedReports),
    contextSha256: value.contextSha256,
  });
}

export function validateStageAReceipt(receipt, context, bundleSha256, profile) {
  exactKeys(receipt, [
    "schemaVersion",
    "status",
    "phase",
    "sourceSha",
    "baseSha",
    "definitionSha",
    "verifierSha256",
    "descriptorSha256",
    "headerSha256",
    "publicationTip",
    "preparedRevisions",
  ]);
  assert.equal(receipt.schemaVersion, 1);
  assert.equal(receipt.status, "verified");
  for (const name of [
    "phase",
    "sourceSha",
    "baseSha",
    "definitionSha",
    "descriptorSha256",
  ])
    assert.equal(receipt[name], context[name]);
  assert.equal(receipt.verifierSha256, bundleSha256);
  assert.equal(
    receipt.headerSha256,
    profile?.installation.trust.headerSha256 ?? null,
  );
  assert.equal(
    receipt.publicationTip,
    profile?.installation.finalPublicationTip ?? null,
  );
  assert.ok(
    Number.isSafeInteger(receipt.preparedRevisions) &&
      receipt.preparedRevisions > 0 &&
      receipt.preparedRevisions <= 64,
  );
  return true;
}
