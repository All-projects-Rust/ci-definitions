import fs from "node:fs";
import { resolve } from "node:path";
import { digest, stable } from "./ledger-format.mjs";
import { readSourceInputs } from "../access-census/inventory.mjs";
import {
  classifySurfaceLedger,
  discoverPermissionSurfaces,
  verifySurfaceLedger,
  verifySurfaceBindingProofs,
} from "./surface-gate.mjs";
import {
  readPairedSourceHistory,
  readPairedSourceHistoryCurrent,
  assertSourceHeadReaderCurrent,
  SURFACE_HISTORY_PATH,
} from "./surface-history.mjs";

// Caller-visible result, entries, fragments, files Maps or JSON are never authority.
const prepared = new WeakMap();
const fail = (label) => {
  throw new Error(`SOURCE_HEAD_CONTINUATION_${label}`);
};
function privateText(root, path) {
  const file = resolve(path);
  if (!file.startsWith(root + "/") || fs.realpathSync(file) !== file) fail("DECISION_PATH");
  const fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW);
  try {
    const stat = fs.fstatSync(fd);
    if (!stat.isFile()) fail("DECISION_PATH");
    return fs.readFileSync(fd, "utf8");
  } finally {
    fs.closeSync(fd);
  }
}
function snapshotSources(root) {
  return readSourceInputs(root);
}

/** Actual-reader, actual-source preparation. No publication, and no externally supplied next ledger. */
export function preparePairedSourceClassification(root, decisionsPath, continuationPath) {
  root = fs.realpathSync(root);
  const decisions = privateText(root, decisionsPath),
    continuation = privateText(root, continuationPath);
  const inputs = snapshotSources(root),
    surfaces = discoverPermissionSurfaces(inputs);
  const previous = readPairedSourceHistory(root);
  const result = classifySurfaceLedger({
    surfaces,
    inputs,
    ledger: previous.ledger,
    baseline: previous.baseline,
    decisionDocument: JSON.parse(decisions),
    continuation: { root, document: JSON.parse(continuation) },
  });
  if (!result.continuationFragment) fail("CANDIDATE_REQUIRED");
  prepared.set(result, {
    root,
    previous: previous.ledger,
    resultDigest: digest(result),
    fragment: structuredClone(result.continuationFragment),
    inputs: structuredClone(inputs),
    decisionsPath: resolve(decisionsPath),
    decisions,
    continuationPath: resolve(continuationPath),
    continuation,
  });
  return result;
}

function recheck(record, result) {
  if (digest(result) !== record.resultDigest) fail("PREPARED_RESULT_CHANGED");
  assertSourceHeadReaderCurrent(record.root, record.previous);
  if (
    privateText(record.root, record.decisionsPath) !== record.decisions ||
    privateText(record.root, record.continuationPath) !== record.continuation
  )
    fail("DECISIONS_CHANGED");
  const inputs = snapshotSources(record.root);
  if (stable(inputs) !== stable(record.inputs)) fail("SOURCE_CHANGED");
  const surfaces = discoverPermissionSurfaces(inputs);
  verifySurfaceLedger(surfaces, result.ledger, result.baseline);
  verifySurfaceBindingProofs(surfaces, result.ledger, inputs);
}

/** Exclusive writer is an explicit operating precondition, not a filesystem-wide transaction claim. */
export function publishPairedSourceClassification(root, result, { exclusiveWriter = false } = {}) {
  const record = prepared.get(result);
  if (!record || record.root !== fs.realpathSync(root)) fail("PREPARED_READER_REQUIRED");
  if (exclusiveWriter !== true) fail("EXCLUSIVE_WRITER_REQUIRED");
  recheck(record, result);
  const directory = resolve(record.root, SURFACE_HISTORY_PATH, "fragments");
  if (fs.realpathSync(directory) !== directory || !fs.statSync(directory).isDirectory())
    fail("DESTINATION_PATH");
  const relativePath = `${SURFACE_HISTORY_PATH}/fragments/${digest(record.fragment)}.json`;
  const target = resolve(record.root, relativePath);
  const text = `${JSON.stringify(record.fragment, null, 2)}\n`;
  const staging = fs.mkdtempSync(resolve(record.root, ".source-head-stage-"));
  const temp = resolve(staging, "fragment.json");
  let fd,
    ownedTemp,
    failure,
    installed = false;
  try {
    fd = fs.openSync(
      temp,
      fs.constants.O_CREAT | fs.constants.O_EXCL | fs.constants.O_WRONLY | fs.constants.O_NOFOLLOW,
      0o644,
    );
    ownedTemp = fs.fstatSync(fd);
    fs.writeFileSync(fd, text, "utf8");
    fs.fsyncSync(fd);
    // Recheck all pinned inputs after preparing bytes, immediately before the atomic install.
    recheck(record, result);
    const opened = fs.fstatSync(fd),
      named = fs.lstatSync(temp);
    if (!named.isFile() || opened.ino !== named.ino || opened.dev !== named.dev)
      fail("TEMP_IDENTITY_CHANGED");
    try {
      fs.linkSync(temp, target);
      installed = true;
    } catch (error) {
      if (error.code !== "EEXIST") throw error;
      const existing = fs.lstatSync(target);
      if (
        !existing.isFile() ||
        existing.isSymbolicLink() ||
        fs.readFileSync(target, "utf8") !== text
      )
        fail("DESTINATION_COLLISION");
      installed = true;
    }
    const directoryFd = fs.openSync(
      directory,
      fs.constants.O_RDONLY | fs.constants.O_DIRECTORY | fs.constants.O_NOFOLLOW,
    );
    try {
      fs.fsyncSync(directoryFd);
    } finally {
      fs.closeSync(directoryFd);
    }
    if (fs.readFileSync(target, "utf8") !== text) fail("INSTALLED_BYTES_CHANGED");
    // Post-install failures retain the complete immutable file; they never roll history back.
    const current = readPairedSourceHistoryCurrent(record.root, record.previous);
    if (stable(current.ledger) !== stable(result.ledger)) fail("POSTINSTALL_LEDGER_CHANGED");
    const inputs = snapshotSources(record.root);
    if (stable(inputs) !== stable(record.inputs)) fail("POSTINSTALL_SOURCE_CHANGED");
    verifySurfaceLedger(discoverPermissionSurfaces(inputs), current.ledger, current.baseline);
    verifySurfaceBindingProofs(discoverPermissionSurfaces(inputs), current.ledger, inputs);
    prepared.delete(result);
  } catch (error) {
    failure = error;
  } finally {
    // Never unlink a replaced temp name; keep the first failure and installed-state proof.
    try {
      if (fd !== undefined) fs.closeSync(fd);
      if (ownedTemp) {
        const named = fs.lstatSync(temp);
        if (!named.isFile() || named.ino !== ownedTemp.ino || named.dev !== ownedTemp.dev)
          fail("TEMP_IDENTITY_CHANGED");
        fs.unlinkSync(temp);
      }
      fs.rmdirSync(staging);
    } catch (error) {
      failure ??= error;
    }
  }
  if (failure) {
    if (installed) failure.sourceHeadFragmentInstalled = true;
    throw failure;
  }
  return relativePath;
}
