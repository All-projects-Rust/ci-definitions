import { test } from "node:test";
import assert from "node:assert/strict";
import { validateBridgeRequest } from "./runtime-bridge.mjs";
const sha = "a".repeat(40);
test("only context, explicit-role resolution and exact cutover requests", () => {
  for (const r of [
    { schemaVersion: 1, op: "context" },
    {
      schemaVersion: 1,
      op: "resolve-installed",
      role: "logical",
      revision: sha,
    },
    {
      schemaVersion: 1,
      op: "resolve-installed",
      role: "physical",
      revision: sha,
    },
    {
      schemaVersion: 1,
      op: "authorize-cutover",
      installedLogical: sha,
      candidatePhysical: sha,
    },
  ])
    assert.equal(validateBridgeRequest(r), r);
});
test("caller cannot select trust, path, arbitrary operations or ambiguous revision roles", () => {
  for (const r of [
    { schemaVersion: 1, op: "context", path: "/tmp/candidate" },
    { schemaVersion: 1, op: "context", key: "candidate" },
    { schemaVersion: 1, op: "resolve-installed", revision: sha },
    { schemaVersion: 1, op: "resolve-installed", role: "auto", revision: sha },
    {
      schemaVersion: 1,
      op: "resolve-installed",
      role: "logical",
      revision: "main",
    },
    {
      schemaVersion: 1,
      op: "authorize-cutover",
      installedLogical: sha,
      candidatePhysical: "main",
    },
    { schemaVersion: 1, op: "sign" },
    { schemaVersion: 2, op: "context" },
  ])
    assert.throws(() => validateBridgeRequest(r));
});
