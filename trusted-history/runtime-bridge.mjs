import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import {
  constants,
  openSync,
  closeSync,
  fstatSync,
  lstatSync,
  readFileSync,
  realpathSync,
} from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { verifyTrustedBundle } from "./bundle-integrity.mjs";
import {
  canonicalRuntimeAuthorization,
  verifyRuntimeCutoverEnvelope,
} from "./runtime-authorization.mjs";
const directory = "/etc/signalo/history-redaction";
const sourceRoot = "/var/lib/signalo-api-source.git";
const sha = /^[a-f0-9]{40}$/u;
const hash = (bytes) => createHash("sha256").update(bytes).digest("hex");
const exact = (value, names) => {
  assert.ok(value && typeof value === "object" && !Array.isArray(value));
  assert.deepEqual(Object.keys(value).sort(), [...names].sort());
};
export function validateBridgeRequest(request) {
  assert.equal(request?.schemaVersion, 1);
  if (request.op === "context") exact(request, ["schemaVersion", "op"]);
  else if (request.op === "resolve-installed") {
    exact(request, ["schemaVersion", "op", "role", "revision"]);
    assert.ok(["logical", "physical"].includes(request.role));
    assert.match(request.revision, sha);
  } else {
    assert.equal(request.op, "authorize-cutover");
    exact(request, [
      "schemaVersion",
      "op",
      "installedLogical",
      "candidatePhysical",
    ]);
    assert.match(request.installedLogical, sha);
    assert.match(request.candidatePhysical, sha);
  }
  return request;
}
const identity = (s) =>
  [s.dev, s.ino, s.nlink, s.uid, s.mode, s.size, s.mtimeNs, s.ctimeNs].join(
    ":",
  );
function administratorFile(path) {
  for (let parent = dirname(path); ; parent = dirname(parent)) {
    const s = lstatSync(parent, { bigint: true });
    assert.ok(
      s.isDirectory() &&
        s.uid === 0n &&
        (s.mode & 0o022n) === 0n &&
        realpathSync(parent) === parent,
    );
    if (parent === "/") break;
  }
  const before = lstatSync(path, { bigint: true });
  assert.ok(
    before.isFile() &&
      before.uid === 0n &&
      before.nlink === 1n &&
      (before.mode & 0o022n) === 0n &&
      before.size > 0n &&
      before.size <= 131072n,
  );
  const fd = openSync(path, constants.O_RDONLY | constants.O_NOFOLLOW);
  try {
    assert.equal(identity(fstatSync(fd, { bigint: true })), identity(before));
    const bytes = readFileSync(fd);
    assert.equal(bytes.length, Number(before.size));
    assert.equal(identity(fstatSync(fd, { bigint: true })), identity(before));
    assert.equal(identity(lstatSync(path, { bigint: true })), identity(before));
    return bytes;
  } finally {
    closeSync(fd);
  }
}
async function execute(request) {
  const bundle = resolve(
    dirname(fileURLToPath(import.meta.url)),
    "../bundled-native",
  );
  const bundleProof = verifyTrustedBundle(bundle);
  const { openInstalledHistoryReader } = await import(
    pathToFileURL(
      resolve(bundle, "scripts/permission-registry/history-revision-io.mjs"),
    )
  );
  const reader = openInstalledHistoryReader(sourceRoot);
  if (!reader) {
    assert.equal(request.op, "context");
    return { schemaVersion: 1, phase: "legacy" };
  }
  assert.equal(reader.cleanStoreRoot, sourceRoot);
  const activeBytes = administratorFile(directory + "/active.json");
  assert.equal(hash(activeBytes), reader.descriptorSha256);
  const active = JSON.parse(activeBytes.toString("utf8"));
  assert.equal(active.verifierSha256, bundleProof.sha256);
  const context = {
    schemaVersion: 1,
    phase: "active",
    migrationId: reader.migrationId,
    descriptorSha256: reader.descriptorSha256,
    trustDigest: reader.trustDigest,
    publicationTip: reader.publicationTip,
    cleanAnchor: reader.cleanAnchor,
    cleanStoreRoot: reader.cleanStoreRoot,
    retentionPrefix: `refs/tags/signalo-permission-clean/${reader.migrationId}/`,
  };
  let result;
  if (request.op === "context") result = context;
  else if (request.op === "resolve-installed") {
    if (request.role === "logical") {
      const resolved = reader.resolveReceiptRevision(request.revision);
      result = {
        ...context,
        physicalRevision: resolved.physicalRevision,
        logicalRevision: request.revision,
      };
    } else {
      const logical = reader.classifyPhysicalRevision(request.revision);
      result = {
        ...context,
        physicalRevision: request.revision,
        logicalRevision: logical === request.revision ? null : logical,
      };
    }
  } else {
    assert.equal(request.candidatePhysical, reader.publicationTip);
    const mapped = reader.mappedTransportRevision(request.installedLogical);
    const resolved = reader.resolveReceiptRevision(request.installedLogical);
    assert.equal(resolved.physicalRevision, mapped);
    assert.equal(
      reader.classifyPhysicalRevision(reader.publicationTip),
      reader.publicationTip,
    );
    assert.equal(
      reader.isPhysicalAncestor(mapped, reader.publicationTip),
      true,
    );
    const envelopeBytes = administratorFile(
      directory + "/runtime-cutover.json",
    );
    const envelope = JSON.parse(envelopeBytes.toString("utf8"));
    assert.deepEqual(canonicalRuntimeAuthorization(envelope), envelopeBytes);
    const authorization = verifyRuntimeCutoverEnvelope(
      envelope,
      {
        ...context,
        installedLogical: request.installedLogical,
        mappedInstalled: mapped,
      },
      active.trust.publicKeySpkiBase64,
    );
    result = { ...context, ...authorization };
  }
  reader.assertCurrent();
  return result;
}
export async function runtimeBridgeMain() {
  assert.equal(process.argv.length, 2);
  let size = 0;
  const chunks = [];
  for await (const chunk of process.stdin) {
    size += chunk.length;
    assert.ok(size <= 8192);
    chunks.push(chunk);
  }
  assert.ok(size > 0);
  const bytes = Buffer.concat(chunks);
  const text = bytes.toString("utf8");
  assert.deepEqual(Buffer.from(text), bytes);
  const request = validateBridgeRequest(JSON.parse(text));
  const result = await execute(request);
  process.stdout.write(JSON.stringify(result) + "\n");
}
if (
  process.argv[1] &&
  pathToFileURL(realpathSync(process.argv[1])).href === import.meta.url
)
  runtimeBridgeMain().catch(() => {
    process.stderr.write("HISTORY_RUNTIME_BRIDGE_REFUSED\n");
    process.exitCode = 1;
  });
