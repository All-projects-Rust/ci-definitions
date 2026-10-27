import assert from "node:assert/strict";
import { createHash, createPublicKey, verify } from "node:crypto";
const domain = Buffer.from("signalo-history-runtime-cutover-v1\n");
const sha = /^[a-f0-9]{40}$/u,
  hash = /^[a-f0-9]{64}$/u;
const exact = (value, names) => {
  assert.ok(value && typeof value === "object" && !Array.isArray(value));
  assert.deepEqual(Object.keys(value).sort(), [...names].sort());
};
export function canonicalRuntimeAuthorization(value) {
  const stable = (v) =>
    Array.isArray(v)
      ? `[${v.map(stable).join(",")}]`
      : v && typeof v === "object"
        ? `{${Object.entries(v)
            .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
            .map(([k, x]) => `${JSON.stringify(k)}:${stable(x)}`)
            .join(",")}}`
        : JSON.stringify(v);
  return Buffer.from(stable(value) + "\n");
}
export function runtimeCutoverMessage(value) {
  return Buffer.concat([domain, canonicalRuntimeAuthorization(value)]);
}
// Pure signature/data validation. Runtime authority comes only from the fixed
// administrator installation read by runtime-bridge.mjs, never from callers.
export function verifyRuntimeCutoverEnvelope(
  envelope,
  context,
  publicKeySpkiBase64,
  now = Date.now(),
) {
  exact(envelope, ["payload", "signatureBase64"]);
  const p = envelope.payload;
  exact(p, [
    "schemaVersion",
    "repositoryId",
    "migrationId",
    "activeDescriptorSha256",
    "installedLogical",
    "mappedInstalled",
    "publicationTip",
    "ci",
    "expiresAt",
  ]);
  assert.equal(p.schemaVersion, 1);
  assert.equal(p.repositoryId, "1201945594");
  assert.match(p.migrationId, /^[a-z0-9][a-z0-9-]{0,63}$/u);
  assert.equal(p.migrationId, context.migrationId);
  assert.match(p.activeDescriptorSha256, hash);
  assert.equal(p.activeDescriptorSha256, context.descriptorSha256);
  for (const key of ["installedLogical", "mappedInstalled", "publicationTip"])
    assert.match(p[key], sha);
  assert.equal(p.installedLogical, context.installedLogical);
  assert.equal(p.mappedInstalled, context.mappedInstalled);
  assert.equal(p.publicationTip, context.publicationTip);
  exact(p.ci, [
    "runId",
    "runAttempt",
    "workflowId",
    "callerWorkflowSha256",
    "definition",
    "historyJobName",
  ]);
  for (const key of ["runId", "runAttempt", "workflowId"])
    assert.ok(Number.isSafeInteger(p.ci[key]) && p.ci[key] > 0);
  assert.match(p.ci.callerWorkflowSha256, hash);
  assert.equal(p.ci.historyJobName, "Trusted history / History integrity");
  const d = p.ci.definition;
  exact(d, ["repo", "id", "owner", "path", "sha", "blobSha256"]);
  assert.equal(d.repo, "All-projects-Rust/ci-definitions");
  assert.equal(d.id, 1435776151);
  assert.equal(d.owner, 348736467);
  assert.equal(d.path, ".github/workflows/history-redaction-verify.yml");
  assert.match(d.sha, sha);
  assert.match(d.blobSha256, hash);
  assert.ok(
    Number.isSafeInteger(p.expiresAt) &&
      p.expiresAt > Math.floor(now / 1000) &&
      p.expiresAt <= Math.floor(now / 1000) + 86400,
  );
  const decode = (value, max) => {
    assert.ok(typeof value === "string" && value.length <= max);
    const bytes = Buffer.from(value, "base64");
    assert.equal(bytes.toString("base64"), value);
    return bytes;
  };
  const key = createPublicKey({
    key: decode(publicKeySpkiBase64, 1024),
    type: "spki",
    format: "der",
  });
  assert.equal(key.asymmetricKeyType, "ed25519");
  const signature = decode(envelope.signatureBase64, 128);
  assert.equal(signature.length, 64);
  assert.ok(verify(null, runtimeCutoverMessage(p), key, signature));
  return Object.freeze({
    ...p,
    authorizationSha256: createHash("sha256")
      .update(canonicalRuntimeAuthorization(envelope))
      .digest("hex"),
  });
}
