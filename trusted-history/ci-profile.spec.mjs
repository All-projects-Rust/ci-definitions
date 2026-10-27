import { test } from "node:test";
import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import {
  decodeCIProfile,
  ciAttestationDirectory,
  ciCleanGitDirectory,
} from "./ci-profile.mjs";
const verifier = "a".repeat(64);
const profile = () => ({
  schemaVersion: 1,
  repositoryId: "1201945594",
  finalPublicationTip: "b".repeat(40),
  attestationDirectory: ciAttestationDirectory,
  cleanGitDirectory: ciCleanGitDirectory,
  signatureBase64: "AQ==",
  trust: { repositoryId: "1201945594" },
  ioLimits: {},
  verifierSha256: verifier,
});
const encoded = (p) => {
  const bytes = Buffer.from(JSON.stringify(p));
  return {
    context: {
      phase: "active",
      descriptorSha256: createHash("sha256").update(bytes).digest("hex"),
    },
    value: bytes.toString("base64"),
  };
};
test("legacy phase is explicit and cannot silently load descriptor data", () => {
  assert.equal(
    decodeCIProfile({ phase: "legacy", descriptorSha256: "" }, "", verifier),
    null,
  );
  assert.throws(() => decodeCIProfile({ phase: "" }, "", verifier));
  assert.throws(() =>
    decodeCIProfile(
      { phase: "legacy", descriptorSha256: "" },
      "candidate",
      verifier,
    ),
  );
});
test("both real workflow contexts normalize an absent descriptor before the strict profile decoder", () => {
  // The first live caller emitted JSON null for the missing SHA variable.
  const missingDescriptor = { phase: "legacy", descriptorSha256: null };
  assert.throws(() => decodeCIProfile(missingDescriptor, "", verifier));
  const workflow = readFileSync(
    new URL(
      "../.github/workflows/history-redaction-verify.yml",
      import.meta.url,
    ),
    "utf8",
  );
  const expressions = [
    ...workflow.matchAll(
      /"descriptorSha256":\$\{\{ toJSON\((vars\.HISTORY_REDACTION_DESCRIPTOR_SHA256(?: \|\| '')?)\) \}\}/gu,
    ),
  ];
  assert.equal(expressions.length, 2);
  for (const [, expression] of expressions) {
    // Interpret only this finite variable/default expression, never workflow code.
    const [variable, fallback] = expression.split(" || ");
    assert.equal(variable, "vars.HISTORY_REDACTION_DESCRIPTOR_SHA256");
    assert.ok(fallback === undefined || fallback === "''");
    const emitted =
      fallback === "''"
        ? missingDescriptor.descriptorSha256 || ""
        : missingDescriptor.descriptorSha256;
    const context = JSON.parse(
      JSON.stringify({ ...missingDescriptor, descriptorSha256: emitted }),
    );
    assert.equal(decodeCIProfile(context, "", verifier), null);
    for (const phase of [null, "", "active"])
      assert.throws(() => decodeCIProfile({ ...context, phase }, "", verifier));
    assert.throws(() => decodeCIProfile(context, "candidate", verifier));
  }
});
test("missing or malformed active descriptor SHA still fails closed", () => {
  for (const descriptorSha256 of [null, "", "not-a-digest", "a".repeat(63)])
    assert.throws(() =>
      decodeCIProfile({ phase: "active", descriptorSha256 }, "", verifier),
    );
});
test("exact administrative profile data binds fixed locations and verifier bytes; no signature proof claimed", () => {
  const { context, value } = encoded(profile());
  assert.equal(
    decodeCIProfile(context, value, verifier).installation.cleanGitDirectory,
    ciCleanGitDirectory,
  );
});
test("candidate-selected paths, verifier, repository, extra fields and profile substitution fail", () => {
  for (const patch of [
    { attestationDirectory: "/tmp/candidate" },
    { cleanGitDirectory: "/tmp/candidate.git" },
    { repositoryId: "1" },
    { verifierSha256: "c".repeat(64) },
    { candidatePublicKey: "untrusted" },
  ]) {
    const { context, value } = encoded({ ...profile(), ...patch });
    assert.throws(() => decodeCIProfile(context, value, verifier));
  }
  const { context, value } = encoded(profile());
  assert.throws(() =>
    decodeCIProfile(
      { ...context, descriptorSha256: "c".repeat(64) },
      value,
      verifier,
    ),
  );
  assert.throws(() => decodeCIProfile(context, value + "\n", verifier));
  assert.throws(() => decodeCIProfile(context, "", verifier));
});
