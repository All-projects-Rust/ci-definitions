import assert from "node:assert/strict";
import { randomBytes } from "node:crypto";
import { execFileSync, spawnSync } from "node:child_process";
import { createRequire } from "node:module";
import {
  lstatSync,
  readFileSync,
  realpathSync,
  mkdtempSync,
  mkdirSync,
  writeFileSync,
  copyFileSync,
  chmodSync,
  rmSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { verifyTrustedBundle } from "./bundle-integrity.mjs";
import { verifyHistoryJobContext } from "./job-context.mjs";
import { eventBase } from "./ci-verify.mjs";
import {
  hashBytes,
  readRuntimeResponse,
  runtimeApiDirectory,
  runtimeClosureNames,
  sandboxCandidate,
  sandboxRuntime,
  validateStageAReceipt,
} from "./runtime-binding-protocol.mjs";
import { transpileRuntimeSource } from "./runtime-ts-loader.mjs";

const helperDirectory = dirname(fileURLToPath(import.meta.url));
const helperFiles = [
  "runtime-binding-child.mjs",
  "runtime-binding-protocol.mjs",
  "runtime-ts-loader.mjs",
  "runtime-ts-register.mjs",
];
const require = createRequire(import.meta.url);
const gitEnvironment = () => ({
  PATH: "/usr/bin:/bin",
  LANG: "C.UTF-8",
  LC_ALL: "C.UTF-8",
  HOME: "/nonexistent",
  GIT_CONFIG_NOSYSTEM: "1",
  GIT_CONFIG_GLOBAL: "/dev/null",
  GIT_TERMINAL_PROMPT: "0",
  GIT_NO_REPLACE_OBJECTS: "1",
  GIT_NO_LAZY_FETCH: "1",
});
function git(candidate, args) {
  return execFileSync(
    "/usr/bin/git",
    ["--no-replace-objects", "-c", "core.hooksPath=/dev/null", ...args],
    {
      cwd: candidate,
      env: gitEnvironment(),
      timeout: 15000,
      maxBuffer: 1024 * 1024,
      stdio: ["ignore", "pipe", "pipe"],
    },
  );
}
function fileBytes(path, maxBytes) {
  assert.equal(realpathSync(path), resolve(path));
  const stat = lstatSync(path);
  assert.ok(
    stat.isFile() &&
      !stat.isSymbolicLink() &&
      stat.nlink === 1 &&
      stat.size > 0 &&
      stat.size <= maxBytes,
  );
  const bytes = readFileSync(path);
  assert.equal(bytes.length, stat.size);
  return bytes;
}
export function currentRuntimeClosure(candidate, sourceSha) {
  assert.match(sourceSha, /^[a-f0-9]{40}$/u);
  assert.equal(realpathSync(candidate), candidate);
  assert.equal(
    git(candidate, ["rev-parse", "HEAD"]).toString().trim(),
    sourceSha,
  );
  return runtimeClosureNames.map((name) => {
    const path = `${runtimeApiDirectory}/${name}`;
    const bytes = fileBytes(join(candidate, path), 512 * 1024);
    assert.deepEqual(git(candidate, ["show", `${sourceSha}:${path}`]), bytes);
    transpileRuntimeSource(`${sandboxCandidate}/${path}`, bytes);
    return Object.freeze({ path, bytes });
  });
}

// The child is intentionally a runtime regression, after Stage A's data-only
// authority check. Its minimal namespace exposes no host checkout, credentials,
// installed trust, native ledger or writable helper/store; only public snapshots.
export function isolatedRuntimeContext(closure) {
  assert.ok(
    Array.isArray(closure) && closure.length === runtimeClosureNames.length,
  );
  const expected = runtimeClosureNames
    .map((name) => `${runtimeApiDirectory}/${name}`)
    .sort();
  assert.deepEqual(closure.map((row) => row.path).sort(), expected);
  let total = 0;
  for (const row of closure) {
    assert.ok(Buffer.isBuffer(row.bytes));
    total += row.bytes.length;
    transpileRuntimeSource(`${sandboxCandidate}/${row.path}`, row.bytes);
  }
  assert.ok(total > 0 && total <= 4 * 1024 * 1024);
  const temporary = mkdtempSync(join(tmpdir(), "signalo-runtime-binding-"));
  // Public source snapshots contain no credentials, nonce or owning ledger.
  // Traverse permission is needed during privileged user-namespace setup.
  chmodSync(temporary, 0o755);
  const candidateSnapshot = join(temporary, "candidate"),
    runtimeSnapshot = join(temporary, "runtime");
  const publicDirectory = (directory) => {
    assert.ok(directory.startsWith(temporary + "/"));
    mkdirSync(directory, { recursive: true, mode: 0o755 });
    for (
      let current = directory;
      current !== temporary;
      current = dirname(current)
    )
      chmodSync(current, 0o755);
  };
  try {
    for (const row of closure) {
      const destination = join(candidateSnapshot, row.path);
      publicDirectory(dirname(destination));
      writeFileSync(destination, row.bytes, { flag: "wx", mode: 0o644 });
      chmodSync(destination, 0o644);
    }
    publicDirectory(runtimeSnapshot);
    for (const name of helperFiles) {
      writeFileSync(
        join(runtimeSnapshot, name),
        fileBytes(join(helperDirectory, name), 128 * 1024),
        { flag: "wx", mode: 0o644 },
      );
      chmodSync(join(runtimeSnapshot, name), 0o644);
    }
    const typescriptRoot = dirname(
      realpathSync(require.resolve("typescript/package.json")),
    );
    const packageBytes = fileBytes(
      join(typescriptRoot, "package.json"),
      64 * 1024,
    );
    assert.equal(JSON.parse(packageBytes.toString("utf8")).version, "5.9.3");
    const typescriptSnapshot = join(runtimeSnapshot, "node_modules/typescript");
    publicDirectory(join(typescriptSnapshot, "lib"));
    writeFileSync(join(typescriptSnapshot, "package.json"), packageBytes, {
      flag: "wx",
      mode: 0o644,
    });
    chmodSync(join(typescriptSnapshot, "package.json"), 0o644);
    copyFileSync(
      join(typescriptRoot, "lib/typescript.js"),
      join(typescriptSnapshot, "lib/typescript.js"),
    );
    chmodSync(join(typescriptSnapshot, "lib/typescript.js"), 0o644);
    writeFileSync(join(runtimeSnapshot, "node"), "", {
      flag: "wx",
      mode: 0o644,
    });
    const nonce = randomBytes(32).toString("hex");
    const args = [
      "-n",
      "/usr/bin/bwrap",
      "--die-with-parent",
      "--unshare-user",
      "--unshare-ipc",
      "--unshare-pid",
      "--unshare-net",
      "--unshare-uts",
      "--unshare-cgroup",
      "--disable-userns",
      "--assert-userns-disabled",
      "--new-session",
      "--ro-bind",
      "/usr",
      "/usr",
      "--ro-bind",
      "/lib",
      "/lib",
      "--ro-bind",
      "/lib64",
      "/lib64",
      "--ro-bind",
      "/bin",
      "/bin",
      "--dir",
      "/etc",
      "--ro-bind",
      "/etc/ld.so.cache",
      "/etc/ld.so.cache",
      "--tmpfs",
      "/tmp",
      "--proc",
      "/proc",
      "--dev",
      "/dev",
      "--dir",
      sandboxRuntime,
      "--ro-bind",
      runtimeSnapshot,
      sandboxRuntime,
      "--ro-bind",
      realpathSync(process.execPath),
      `${sandboxRuntime}/node`,
      "--dir",
      sandboxCandidate,
      "--ro-bind",
      candidateSnapshot,
      sandboxCandidate,
      "--chdir",
      sandboxCandidate,
      "--clearenv",
      "--setenv",
      "PATH",
      "/usr/bin:/bin",
      "--setenv",
      "HOME",
      "/tmp",
      "--setenv",
      "LANG",
      "C.UTF-8",
      "--setenv",
      "LC_ALL",
      "C.UTF-8",
      "--uid",
      "65534",
      "--gid",
      "65534",
      "--cap-drop",
      "ALL",
      "--remount-ro",
      "/",
      `${sandboxRuntime}/node`,
      "--max-old-space-size=256",
      "--no-addons",
      "--import",
      `${sandboxRuntime}/runtime-ts-register.mjs`,
      `${sandboxRuntime}/runtime-binding-child.mjs`,
    ];
    const child = spawnSync("/usr/bin/sudo", args, {
      env: gitEnvironment(),
      cwd: temporary,
      input: Buffer.from(JSON.stringify({ schemaVersion: 1, nonce }) + "\n"),
      timeout: 60000,
      killSignal: "SIGTERM",
      maxBuffer: 1024 * 1024,
      encoding: null,
      stdio: ["pipe", "pipe", "pipe"],
    });
    assert.ok(!child.error && child.status === 0 && child.signal === null);
    assert.ok(Buffer.isBuffer(child.stderr) && child.stderr.length === 0);
    return readRuntimeResponse(child.stdout, nonce);
  } finally {
    rmSync(temporary, { recursive: true, force: true });
  }
}

export function assertClassifiedRuntime({
  ledger,
  result,
  sourceProofs,
  context,
  verifyBindings,
}) {
  assert.equal(result.checked, ledger.entries.length);
  assert.ok(result.checked > 1000);
  assert.equal(verifyBindings(ledger, context), result.bound);
  assert.equal(sourceProofs, result.bound);
  return true;
}

async function main() {
  assert.equal(process.argv.length, 2);
  for (const name of ["GH_TOKEN", "GITHUB_TOKEN", "NODE_OPTIONS", "NODE_PATH"])
    assert.equal(process.env[name], undefined);
  const original = JSON.parse(process.env.HISTORY_CONTEXT ?? "null");
  const definition = JSON.parse(process.env.HISTORY_DEFINITION ?? "null");
  const candidate = resolve(process.env.GITHUB_WORKSPACE ?? "", "candidate");
  const bundleRoot = resolve(helperDirectory, "../bundled-native");
  const bundle = verifyTrustedBundle(bundleRoot);
  const { decodeCIProfile } = await import("./ci-profile.mjs");
  const profile = decodeCIProfile(
    original,
    process.env.HISTORY_DESCRIPTOR_B64 ?? "",
    bundle.sha256,
  );
  const baseSha = eventBase(original, profile?.installation);
  const context = verifyHistoryJobContext({ ...original, baseSha }, definition);
  const receiptPath = resolve(
    process.env.RUNNER_TEMP ?? "",
    "history-stage-a-receipt.json",
  );
  const stageABytes = fileBytes(receiptPath, 64 * 1024);
  validateStageAReceipt(
    JSON.parse(stageABytes.toString("utf8")),
    context,
    bundle.sha256,
    profile,
  );
  const { readEvolutionSurfaceHistory, assertEvolutionSurfaceReaderCurrent } =
    await import("../bundled-native/scripts/permission-registry/surface-history.mjs");
  const { readSourceInputs } =
    await import("../bundled-native/scripts/access-census/inventory.mjs");
  const { digest } =
    await import("../bundled-native/scripts/permission-registry/ledger-format.mjs");
  const {
    discoverPermissionSurfaces,
    verifySurfaceLedger,
    verifySurfaceBindingProofs,
    verifySurfaceLedgerBindings,
  } =
    await import("../bundled-native/scripts/permission-registry/surface-gate.mjs");
  const closure = currentRuntimeClosure(candidate, context.sourceSha);
  const owning = readEvolutionSurfaceHistory(candidate);
  const inputs = readSourceInputs(candidate),
    inputDigest = digest(inputs);
  const surfaces = discoverPermissionSurfaces(inputs);
  const result = verifySurfaceLedger(surfaces, owning.ledger, owning.baseline);
  const sourceProofs = verifySurfaceBindingProofs(
    surfaces,
    owning.ledger,
    inputs,
  );
  const runtimeContext = isolatedRuntimeContext(closure);
  assertClassifiedRuntime({
    ledger: owning.ledger,
    result,
    sourceProofs,
    context: runtimeContext,
    verifyBindings: verifySurfaceLedgerBindings,
  });
  assert.deepEqual(fileBytes(receiptPath, 64 * 1024), stageABytes);
  assert.equal(verifyTrustedBundle(bundleRoot).sha256, bundle.sha256);
  assert.equal(digest(readSourceInputs(candidate)), inputDigest);
  assertEvolutionSurfaceReaderCurrent(candidate, owning);
  const after = currentRuntimeClosure(candidate, context.sourceSha);
  closure.forEach((row, index) =>
    assert.deepEqual(after[index].bytes, row.bytes),
  );
  process.stdout.write(
    JSON.stringify({
      schemaVersion: 1,
      status: "accepted",
      capability: "runtime-binding-acceptance",
      sourceSha: context.sourceSha,
      definitionSha: context.definitionSha,
      descriptorSha256: context.descriptorSha256,
      stageAReceiptSha256: hashBytes(stageABytes),
      contextSha256: runtimeContext.contextSha256,
      checked: result.checked,
      bound: result.bound,
      sourceProofs,
    }) + "\n",
  );
}
if (
  process.argv[1] &&
  pathToFileURL(realpathSync(process.argv[1])).href === import.meta.url
)
  main().catch(() => {
    process.stderr.write("RUNTIME_BINDING_ACCEPTANCE_REFUSED\n");
    process.exitCode = 1;
  });
