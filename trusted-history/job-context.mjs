import assert from "node:assert/strict";
const sha = /^[a-f0-9]{40}$/u;
const digest = /^[a-f0-9]{64}$/u;
const callers = new Map([
  ["signalorust/signalo", "345015266"],
  ["All-projects-Rust/signalo", "348736467"],
]);
const helper = "All-projects-Rust/ci-definitions";
const workflow = ".github/workflows/history-redaction-verify.yml";
export function verifyHistoryJobContext(context, definition) {
  assert.ok(
    context &&
      definition &&
      typeof context === "object" &&
      typeof definition === "object",
  );
  assert.equal(context.repositoryId, "1201945594");
  assert.equal(callers.get(context.repository), context.ownerId);
  assert.ok(callers.has(context.repository));
  assert.ok(
    ["pull_request", "merge_group", "workflow_dispatch"].includes(
      context.event,
    ),
  );
  assert.match(context.sourceSha, sha);
  assert.equal(context.requestedSourceSha, context.sourceSha);
  assert.match(context.baseSha, sha);
  assert.equal(definition.workflow_repository, helper);
  assert.equal(definition.workflow_file_path, workflow);
  assert.match(definition.workflow_sha, sha);
  assert.equal(
    definition.workflow_ref,
    `${helper}/${workflow}@${definition.workflow_sha}`,
  );
  assert.ok(
    ["legacy", "active"].includes(context.phase),
    "Explicit administrator phase required",
  );
  if (context.phase === "active")
    assert.match(context.descriptorSha256, digest);
  else
    assert.equal(
      context.descriptorSha256,
      "",
      "Legacy phase must not admit an active descriptor",
    );
  return Object.freeze({
    repository: context.repository,
    repositoryId: context.repositoryId,
    ownerId: context.ownerId,
    sourceSha: context.sourceSha,
    baseSha: context.baseSha,
    phase: context.phase,
    descriptorSha256: context.descriptorSha256,
    definitionSha: definition.workflow_sha,
  });
}
export function verifyRepositoryMetadata(
  repository,
  expectedName,
  expectedId,
  expectedOwner,
) {
  assert.ok(repository && typeof repository === "object");
  assert.equal(repository.full_name, expectedName);
  assert.equal(repository.id, expectedId);
  assert.equal(repository.owner?.id, expectedOwner);
  return true;
}
