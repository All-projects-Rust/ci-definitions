import { test } from "node:test";
import assert from "node:assert/strict";
import { generateKeyPairSync, sign } from "node:crypto";
import {
  runtimeCutoverMessage,
  verifyRuntimeCutoverEnvelope,
} from "./runtime-authorization.mjs";
const key = generateKeyPairSync("ed25519"),
  other = generateKeyPairSync("ed25519");
const pub = (k) =>
  k.publicKey.export({ type: "spki", format: "der" }).toString("base64");
const now = 1700000000000;
const context = {
  migrationId: "synthetic-migration",
  descriptorSha256: "a".repeat(64),
  installedLogical: "b".repeat(40),
  mappedInstalled: "c".repeat(40),
  publicationTip: "d".repeat(40),
};
const payload = () => ({
  schemaVersion: 1,
  repositoryId: "1201945594",
  migrationId: context.migrationId,
  activeDescriptorSha256: context.descriptorSha256,
  installedLogical: context.installedLogical,
  mappedInstalled: context.mappedInstalled,
  publicationTip: context.publicationTip,
  ci: {
    runId: 1,
    runAttempt: 1,
    workflowId: 2,
    callerWorkflowSha256: "e".repeat(64),
    definition: {
      repo: "All-projects-Rust/ci-definitions",
      id: 1435776151,
      owner: 348736467,
      path: ".github/workflows/history-redaction-verify.yml",
      sha: "f".repeat(40),
      blobSha256: "0".repeat(64),
    },
    historyJobName: "Trusted history / History integrity",
  },
  expiresAt: now / 1000 + 3600,
});
const signed = (p) => ({
  payload: p,
  signatureBase64: sign(
    null,
    runtimeCutoverMessage(p),
    key.privateKey,
  ).toString("base64"),
});
test("exact signed one-time cutover metadata", () =>
  assert.equal(
    verifyRuntimeCutoverEnvelope(signed(payload()), context, pub(key), now)
      .publicationTip,
    context.publicationTip,
  ));
test("wrong key, altered signature and post-signature body substitution fail", () => {
  const e = signed(payload());
  assert.throws(() =>
    verifyRuntimeCutoverEnvelope(e, context, pub(other), now),
  );
  assert.throws(() =>
    verifyRuntimeCutoverEnvelope(
      { ...e, signatureBase64: Buffer.alloc(64).toString("base64") },
      context,
      pub(key),
      now,
    ),
  );
  e.payload.ci.runAttempt = 2;
  assert.throws(() => verifyRuntimeCutoverEnvelope(e, context, pub(key), now));
});
test("even valid signatures cannot authorize different context or caller-selected namespace", () => {
  for (const patch of [
    { repositoryId: "1" },
    { migrationId: "other" },
    { activeDescriptorSha256: "1".repeat(64) },
    { installedLogical: "1".repeat(40) },
    { mappedInstalled: "1".repeat(40) },
    { publicationTip: "1".repeat(40) },
    { expiresAt: now / 1000 },
    { expiresAt: now / 1000 + 86401 },
  ])
    assert.throws(() =>
      verifyRuntimeCutoverEnvelope(
        signed({ ...payload(), ...patch }),
        context,
        pub(key),
        now,
      ),
    );
});
test("exact trusted definition and fresh CI run identity are mandatory", () => {
  for (const patch of [
    { id: 1 },
    { owner: 1 },
    { repo: "other/ci-definitions" },
    { path: ".github/workflows/ci.yml" },
    { sha: "main" },
    { blobSha256: "invalid" },
  ]) {
    const p = payload();
    Object.assign(p.ci.definition, patch);
    assert.throws(() =>
      verifyRuntimeCutoverEnvelope(signed(p), context, pub(key), now),
    );
  }
  for (const patch of [
    { runId: 0 },
    { runAttempt: 0 },
    { workflowId: 0 },
    { historyJobName: "CI required" },
    { callerWorkflowSha256: "main" },
  ]) {
    const p = payload();
    Object.assign(p.ci, patch);
    assert.throws(() =>
      verifyRuntimeCutoverEnvelope(signed(p), context, pub(key), now),
    );
  }
});
test("extra fields, duplicate authority channels and noncanonical signature encodings fail", () => {
  const p = payload();
  p.key = "candidate";
  assert.throws(() =>
    verifyRuntimeCutoverEnvelope(signed(p), context, pub(key), now),
  );
  const e = signed(payload());
  assert.throws(() =>
    verifyRuntimeCutoverEnvelope(
      { ...e, publicKey: pub(key) },
      context,
      pub(key),
      now,
    ),
  );
  assert.throws(() =>
    verifyRuntimeCutoverEnvelope(
      { ...e, signatureBase64: e.signatureBase64.trimEnd() + "\n" },
      context,
      pub(key),
      now,
    ),
  );
});
