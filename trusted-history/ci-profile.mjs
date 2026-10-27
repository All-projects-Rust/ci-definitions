import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { parseHistoryInstallation } from "../bundled-native/scripts/permission-registry/history-revision-io.mjs";
export const ciAttestationDirectory = "/var/lib/signalo-history/attestation";
export const ciCleanGitDirectory = "/var/lib/signalo-history/clean.git";
// Data validation only. The pinned workflow supplies administrator metadata;
// native loading subsequently verifies the signed header/pages and raw objects.
export function decodeCIProfile(context, descriptorBase64, verifierSha256) {
  assert.match(verifierSha256, /^[a-f0-9]{64}$/u);
  if (context.phase === "legacy") {
    assert.equal(context.descriptorSha256, "");
    assert.equal(descriptorBase64, "");
    return null;
  }
  assert.equal(context.phase, "active");
  assert.match(context.descriptorSha256, /^[a-f0-9]{64}$/u);
  assert.ok(
    typeof descriptorBase64 === "string" &&
      descriptorBase64.length > 0 &&
      descriptorBase64.length <= 87384,
  );
  const bytes = Buffer.from(descriptorBase64, "base64");
  assert.equal(bytes.toString("base64"), descriptorBase64);
  assert.ok(bytes.length > 0 && bytes.length <= 65536);
  assert.equal(
    createHash("sha256").update(bytes).digest("hex"),
    context.descriptorSha256,
  );
  const installation = parseHistoryInstallation(bytes);
  assert.equal(installation.repositoryId, "1201945594");
  assert.equal(installation.attestationDirectory, ciAttestationDirectory);
  assert.equal(installation.cleanGitDirectory, ciCleanGitDirectory);
  assert.equal(installation.verifierSha256, verifierSha256);
  return Object.freeze({ bytes, installation });
}
