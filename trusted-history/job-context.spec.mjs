import { test } from "node:test";
import assert from "node:assert/strict";
import {
  verifyHistoryJobContext,
  verifyRepositoryMetadata,
} from "./job-context.mjs";
const source = "a".repeat(40),
  base = "b".repeat(40),
  definition = "c".repeat(40);
const context = () => ({
  repository: "signalorust/signalo",
  repositoryId: "1201945594",
  ownerId: "345015266",
  event: "pull_request",
  sourceSha: source,
  requestedSourceSha: source,
  baseSha: base,
  phase: "legacy",
  descriptorSha256: "",
});
const job = () => ({
  workflow_repository: "All-projects-Rust/ci-definitions",
  workflow_file_path: ".github/workflows/history-redaction-verify.yml",
  workflow_sha: definition,
  workflow_ref: `All-projects-Rust/ci-definitions/.github/workflows/history-redaction-verify.yml@${definition}`,
});
test("both exact repository tuples and all supported events", () => {
  for (const event of ["pull_request", "merge_group", "workflow_dispatch"]) {
    assert.equal(
      verifyHistoryJobContext({ ...context(), event }, job()).sourceSha,
      source,
    );
    assert.equal(
      verifyHistoryJobContext(
        {
          ...context(),
          event,
          repository: "All-projects-Rust/signalo",
          ownerId: "348736467",
        },
        job(),
      ).repository,
      "All-projects-Rust/signalo",
    );
  }
});
test("active phase needs exact externally supplied descriptor digest", () => {
  assert.equal(
    verifyHistoryJobContext(
      { ...context(), phase: "active", descriptorSha256: "d".repeat(64) },
      job(),
    ).phase,
    "active",
  );
});
test("reject caller substitution, namespace mixing, source confusion and missing administrative phase", () => {
  for (const patch of [
    { repository: "other/signalo" },
    { repositoryId: "1" },
    { repositoryId: 1201945594 },
    { ownerId: "348736467" },
    { repository: "All-projects-Rust/signalo" },
    { event: "pull_request_target" },
    { event: "push" },
    { sourceSha: "a".repeat(39) },
    { requestedSourceSha: base },
    { baseSha: "main" },
    { phase: "" },
    { phase: "legacy", descriptorSha256: "d".repeat(64) },
    { phase: "active", descriptorSha256: "" },
    { phase: "active", descriptorSha256: "D".repeat(64) },
  ])
    assert.throws(() =>
      verifyHistoryJobContext({ ...context(), ...patch }, job()),
    );
});
test("reject copied job names and unpinned or mixed definition identities", () => {
  for (const patch of [
    { workflow_repository: "signalorust/signalo" },
    { workflow_file_path: ".github/workflows/ci.yml" },
    { workflow_sha: "main" },
    {
      workflow_ref:
        "All-projects-Rust/ci-definitions/.github/workflows/history-redaction-verify.yml@main",
    },
    {
      workflow_ref: `signalorust/signalo/.github/workflows/history-redaction-verify.yml@${definition}`,
    },
  ])
    assert.throws(() =>
      verifyHistoryJobContext(context(), { ...job(), ...patch }),
    );
});
test("numeric repository metadata is bound to exact owner and namespace", () => {
  const r = {
    id: 1201945594,
    full_name: "signalorust/signalo",
    owner: { id: 345015266 },
  };
  assert.equal(
    verifyRepositoryMetadata(r, r.full_name, r.id, r.owner.id),
    true,
  );
  for (const q of [
    { ...r, id: "1201945594" },
    { ...r, owner: { id: 348736467 } },
    { ...r, full_name: "other/signalo" },
  ])
    assert.throws(() =>
      verifyRepositoryMetadata(q, r.full_name, r.id, r.owner.id),
    );
});
