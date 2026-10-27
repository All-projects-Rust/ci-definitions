import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
import {
  constants,
  closeSync,
  fstatSync,
  lstatSync,
  mkdirSync,
  openSync,
  readFileSync,
  realpathSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { verifyTrustedBundle } from "./bundle-integrity.mjs";
import {
  verifyHistoryJobContext,
  verifyRepositoryMetadata,
} from "./job-context.mjs";

export const candidateAttestationPath =
  "scripts/permission-registry/history-redaction-attestation";
const sections = ["commits", "projections", "objects", "refs", "dependencies"];
const root = "/var/lib/signalo-history";
const activeDirectory = "/etc/signalo/history-redaction";
const sha = /^[a-f0-9]{40}$/u;
const digest = (bytes) => createHash("sha256").update(bytes).digest("hex");

// Pure, non-authoritative event selection. The context guard and signed profile
// are independently checked before the returned base may be used.
export function eventBase(context, installation) {
  if (context.event === "workflow_dispatch") {
    assert.equal(context.phase, "active");
    assert.ok(installation);
    assert.equal(context.sourceSha, installation.finalPublicationTip);
    assert.equal(context.eventBaseSha, "");
    return installation.trust.cleanAnchor;
  }
  assert.ok(["pull_request", "merge_group"].includes(context.event));
  assert.match(context.eventBaseSha, sha);
  return context.eventBaseSha;
}

// Transport does not confer authority: callers must supply the successfully
// verified signed format, and native readers reauthenticate raw fetched bytes.
export function cleanTransportPlan({
  header,
  pages,
  format,
  sourceSha,
  baseSha,
}) {
  assert.match(sourceSha, sha);
  assert.match(baseSha, sha);
  const roots = new Set([sourceSha, baseSha, header.cleanAnchor]);
  for (const name of ["refs", "dependencies"]) {
    assert.ok(Array.isArray(pages[name]));
    for (const bytes of pages[name]) {
      for (const row of JSON.parse(bytes.toString("utf8"))) {
        const logical = name === "refs" ? row[2] : row;
        const physical = format.resolveMapped(logical);
        assert.match(physical, sha);
        roots.add(physical);
      }
    }
  }
  assert.ok(roots.size <= 1024);
  const mapped = new Map(format.mappedRevisionPairs());
  for (const revision of [sourceSha, baseSha])
    assert.ok(
      !mapped.has(revision) || mapped.get(revision) === revision,
      "A pre-cutover logical revision cannot be used as a transport root",
    );
  return Object.freeze({
    roots: Object.freeze([...roots].sort()),
    mapped,
    prefix: `refs/tags/signalo-permission-clean/${header.migrationId}/`,
  });
}

export function parseCleanRetentionRefs(bytes, plan) {
  const text = bytes.toString("utf8");
  assert.deepEqual(Buffer.from(text), bytes);
  assert.ok(bytes.length <= 4 * 1024 * 1024);
  const refs = [];
  const names = new Set();
  assert.ok(text === "" || text.endsWith("\n"));
  for (const line of text ? text.slice(0, -1).split("\n") : []) {
    const match = /^([a-f0-9]{40})\t([^\t\r\n]+)$/u.exec(line);
    assert.ok(match && match[2].startsWith(plan.prefix));
    const logical = match[2].slice(plan.prefix.length);
    assert.match(logical, sha);
    assert.equal(plan.mapped.get(logical), match[1]);
    assert.ok(!names.has(match[2]));
    names.add(match[2]);
    refs.push(Object.freeze({ ref: match[2], physical: match[1] }));
  }
  assert.ok(refs.length <= 16384);
  return Object.freeze(refs);
}

// Quarantine is never a native object store or an authority input. Every raw
// commit and ordered parent edge is authenticated before unfiltered transport.
export function verifyQuarantineGraph({
  listing,
  frames,
  plan,
  publicationTip,
  cleanAnchor,
  sourceSha,
  baseSha,
  manualCutover,
}) {
  const text = listing.toString("utf8");
  assert.deepEqual(Buffer.from(text), listing);
  assert.ok(text.endsWith("\n") && listing.length <= 24 * 1024 * 1024);
  const rows = text
    .slice(0, -1)
    .split("\n")
    .map((line) => {
      assert.match(line, /^[a-f0-9]{40}(?: [a-f0-9]{40}){0,256}$/u);
      return line.split(" ");
    });
  assert.ok(rows.length > 0 && rows.length <= 100000);
  assert.ok(frames.length > 0 && frames.length <= 256 * 1024 * 1024);
  const graph = new Map();
  let offset = 0;
  for (const [oid, ...parents] of rows) {
    assert.ok(!graph.has(oid));
    const end = frames.indexOf(10, offset);
    assert.ok(end > offset && end - offset <= 128);
    const match = /^([a-f0-9]{40}) commit ([1-9][0-9]{0,6})$/u.exec(
      frames.subarray(offset, end).toString("ascii"),
    );
    assert.ok(match && match[1] === oid);
    const size = Number(match[2]);
    assert.ok(size <= 1024 * 1024);
    const raw = frames.subarray(end + 1, end + 1 + size);
    assert.equal(raw.length, size);
    assert.equal(frames[end + 1 + size], 10);
    assert.equal(
      createHash("sha1").update(`commit ${size}\0`).update(raw).digest("hex"),
      oid,
    );
    const boundary = raw.indexOf(Buffer.from("\n\n"));
    assert.ok(boundary > 0);
    const header = raw.subarray(0, boundary).toString("latin1").split("\n");
    assert.match(header[0], /^tree [a-f0-9]{40}$/u);
    const rawParents = header
      .filter((line) => line.startsWith("parent"))
      .map((line) => {
        assert.match(line, /^parent [a-f0-9]{40}$/u);
        return line.slice(7);
      });
    assert.deepEqual(rawParents, parents);
    assert.equal(new Set(parents).size, parents.length);
    assert.ok(
      !plan.mapped.has(oid) || plan.mapped.get(oid) === oid,
      "Old logical ancestry is forbidden even beneath a clean first parent",
    );
    graph.set(oid, parents);
    offset = end + size + 2;
  }
  assert.equal(offset, frames.length);
  for (const parents of graph.values())
    for (const parent of parents) assert.ok(graph.has(parent));
  assert.ok(
    !plan.mapped.has(publicationTip) &&
      !new Set(plan.mapped.values()).has(publicationTip),
  );
  assert.deepEqual(graph.get(publicationTip), [cleanAnchor]);
  const ancestor = (before, after) => {
    assert.ok(graph.has(before) && graph.has(after));
    const pending = [after],
      seen = new Set();
    while (pending.length) {
      const oid = pending.pop();
      if (oid === before) return true;
      if (seen.has(oid)) continue;
      seen.add(oid);
      pending.push(...graph.get(oid));
    }
    return false;
  };
  assert.ok(ancestor(publicationTip, sourceSha));
  if (manualCutover) assert.equal(baseSha, cleanAnchor);
  else assert.ok(ancestor(publicationTip, baseSha));
  return Object.freeze({ commits: graph.size });
}

function boundedFile(path, maxBytes) {
  assert.equal(realpathSync(path), resolve(path));
  const before = lstatSync(path, { bigint: true });
  assert.ok(before.isFile() && !before.isSymbolicLink() && before.nlink === 1n);
  assert.ok(before.size > 0n && before.size <= BigInt(maxBytes));
  const identity = (s) =>
    [s.dev, s.ino, s.nlink, s.size, s.mtimeNs, s.ctimeNs].join(":");
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

function absent(path) {
  try {
    lstatSync(path);
  } catch (error) {
    if (error.code === "ENOENT") return;
    throw error;
  }
  throw new Error("HISTORY_CI_PATH_ALREADY_PRESENT");
}

function sanitizedEnvironment() {
  // Git configuration, alternate object databases and Node injection cannot be
  // inherited from the caller's environment. No credential is sent to Git.
  return {
    PATH: "/usr/bin:/bin",
    HOME: root,
    LANG: "C.UTF-8",
    LC_ALL: "C.UTF-8",
    GIT_CONFIG_NOSYSTEM: "1",
    GIT_CONFIG_GLOBAL: "/dev/null",
    GIT_NO_REPLACE_OBJECTS: "1",
    GIT_TERMINAL_PROMPT: "0",
    GIT_NO_LAZY_FETCH: "1",
  };
}

async function metadata(name, token) {
  const response = await fetch(`https://api.github.com/repos/${name}`, {
    headers: {
      Accept: "application/vnd.github+json",
      Authorization: `Bearer ${token}`,
      "X-GitHub-Api-Version": "2022-11-28",
    },
    signal: AbortSignal.timeout(15000),
    redirect: "error",
  });
  assert.equal(response.status, 200);
  const bytes = Buffer.from(await response.arrayBuffer());
  assert.ok(bytes.length <= 128 * 1024);
  return JSON.parse(bytes.toString("utf8"));
}

async function main() {
  assert.equal(process.argv.length, 2);
  const token = process.env.GH_TOKEN;
  assert.ok(typeof token === "string" && token.length > 0);
  const original = JSON.parse(process.env.HISTORY_CONTEXT ?? "null");
  const definition = JSON.parse(process.env.HISTORY_DEFINITION ?? "null");
  const descriptorBase64 = process.env.HISTORY_DESCRIPTOR_B64 ?? "";
  const candidate = resolve(process.env.GITHUB_WORKSPACE ?? "", "candidate");
  const bundleRoot = resolve(
    dirname(fileURLToPath(import.meta.url)),
    "../bundled-native",
  );
  const bundle = verifyTrustedBundle(bundleRoot);
  const { decodeCIProfile, ciAttestationDirectory, ciCleanGitDirectory } =
    await import("./ci-profile.mjs");
  // The untrusted base field is not used until the complete guard below.
  const profile = decodeCIProfile(original, descriptorBase64, bundle.sha256);
  const baseSha = eventBase(original, profile?.installation);
  const context = verifyHistoryJobContext({ ...original, baseSha }, definition);
  verifyRepositoryMetadata(
    await metadata(context.repository, token),
    context.repository,
    1201945594,
    Number(context.ownerId),
  );
  verifyRepositoryMetadata(
    await metadata("All-projects-Rust/ci-definitions", token),
    "All-projects-Rust/ci-definitions",
    1435776151,
    348736467,
  );
  assert.equal(realpathSync(candidate), candidate);
  absent(root);
  absent(activeDirectory);
  const env = sanitizedEnvironment();
  const git = (cwd, args, maxBuffer = 8 * 1024 * 1024, input) =>
    execFileSync(
      "/usr/bin/git",
      [
        "--no-replace-objects",
        "-c",
        "core.hooksPath=/dev/null",
        "-c",
        "protocol.file.allow=never",
        ...args,
      ],
      {
        cwd,
        env,
        timeout: 180000,
        maxBuffer,
        stdio: [input ? "pipe" : "ignore", "pipe", "pipe"],
        input,
      },
    );
  assert.equal(
    git(candidate, ["rev-parse", "HEAD"]).toString().trim(),
    context.sourceSha,
  );
  assert.equal(
    git(candidate, ["remote", "get-url", "--all", "origin"]).toString().trim(),
    `https://github.com/${context.repository}`,
  );
  assert.equal(
    git(candidate, ["remote", "get-url", "--push", "--all", "origin"])
      .toString()
      .trim(),
    `https://github.com/${context.repository}`,
  );
  // The dedicated job is ephemeral and executes no candidate command. This is
  // its sole privileged operation: creating the fixed trusted installation.
  execFileSync(
    "/usr/bin/sudo",
    [
      "-n",
      "/usr/bin/install",
      "-d",
      "-m",
      "0755",
      "-o",
      String(process.getuid()),
      "-g",
      String(process.getgid()),
      root,
    ],
    { env, stdio: "pipe" },
  );
  mkdirSync(join(root, "empty-hooks"), { mode: 0o755 });
  for (const key of Object.keys(process.env)) delete process.env[key];
  Object.assign(process.env, env, { GH_TOKEN: token, GH_HOST: "github.com" });
  if (profile) {
    const attestationSource = join(candidate, candidateAttestationPath);
    const headerBytes = boundedFile(
      join(attestationSource, "header.json"),
      16 * 1024 * 1024,
    );
    assert.equal(digest(headerBytes), profile.installation.trust.headerSha256);
    const header = JSON.parse(headerBytes.toString("utf8"));
    const pages = {};
    for (const section of sections) {
      assert.ok(
        Array.isArray(header.pages?.[section]) &&
          header.pages[section].length <= 2000,
      );
      pages[section] = header.pages[section].map((_, index) =>
        boundedFile(
          join(attestationSource, section, `${index}.json`),
          1024 * 1024,
        ),
      );
    }
    const { verifyCompactRedaction } =
      await import("../bundled-native/scripts/permission-registry/history-redaction-compact.mjs");
    const format = verifyCompactRedaction({
      headerBytes,
      pages,
      signatureBase64: profile.installation.signatureBase64,
      trust: profile.installation.trust,
    });
    const plan = cleanTransportPlan({
      header,
      pages,
      format,
      sourceSha: context.sourceSha,
      baseSha,
    });
    const quarantine = join(root, "graph-quarantine.git");
    git(root, ["init", "--bare", "--object-format=sha1", quarantine]);
    const url = `https://github.com/${context.repository}`;
    git(quarantine, ["remote", "add", "origin", url]);
    git(quarantine, [
      "-c",
      "fetch.fsckObjects=true",
      "fetch",
      "--filter=blob:none",
      "--no-tags",
      "--no-recurse-submodules",
      "--no-write-fetch-head",
      "--no-auto-maintenance",
      "origin",
      ...new Set([
        context.sourceSha,
        baseSha,
        profile.installation.finalPublicationTip,
      ]),
    ]);
    for (const marker of [
      "shallow",
      "info/grafts",
      "objects/info/alternates",
      "objects/info/http-alternates",
    ])
      absent(join(quarantine, marker));
    assert.equal(
      git(quarantine, ["for-each-ref", "--format=%(refname)", "refs/replace"])
        .length,
      0,
    );
    const listing = git(
      quarantine,
      [
        "rev-list",
        "--parents",
        context.sourceSha,
        baseSha,
        profile.installation.finalPublicationTip,
      ],
      24 * 1024 * 1024,
    );
    const ids = listing
      .toString("utf8")
      .trimEnd()
      .split("\n")
      .map((line) => {
        const oid = line.split(" ")[0];
        assert.match(oid, sha);
        return oid;
      });
    assert.ok(ids.length <= 100000);
    const frames = git(
      quarantine,
      ["cat-file", "--batch"],
      256 * 1024 * 1024,
      Buffer.from(ids.join("\n") + "\n"),
    );
    verifyQuarantineGraph({
      listing,
      frames,
      plan,
      publicationTip: profile.installation.finalPublicationTip,
      cleanAnchor: profile.installation.trust.cleanAnchor,
      sourceSha: context.sourceSha,
      baseSha,
      manualCutover: context.event === "workflow_dispatch",
    });
    // This exact directory was created above in this job's previously absent
    // workspace. Its partial objects never become the authenticated store.
    rmSync(quarantine, { recursive: true });
    mkdirSync(ciAttestationDirectory, { mode: 0o755 });
    writeFileSync(join(ciAttestationDirectory, "header.json"), headerBytes, {
      flag: "wx",
      mode: 0o644,
    });
    for (const section of sections) {
      mkdirSync(join(ciAttestationDirectory, section), { mode: 0o755 });
      pages[section].forEach((bytes, index) =>
        writeFileSync(
          join(ciAttestationDirectory, section, `${index}.json`),
          bytes,
          { flag: "wx", mode: 0o644 },
        ),
      );
    }
    git(root, ["init", "--bare", "--object-format=sha1", ciCleanGitDirectory]);
    git(ciCleanGitDirectory, ["remote", "add", "origin", url]);
    const remoteRefs = parseCleanRetentionRefs(
      git(ciCleanGitDirectory, [
        "ls-remote",
        "--refs",
        "origin",
        `${plan.prefix}*`,
      ]),
      plan,
    );
    const fetchArgs = [
      "-c",
      "fetch.fsckObjects=true",
      "fetch",
      "--no-tags",
      "--no-recurse-submodules",
      "--no-write-fetch-head",
      "--no-auto-maintenance",
      "origin",
    ];
    const wanted = [
      ...plan.roots,
      ...remoteRefs.map(({ ref }) => `${ref}:${ref}`),
    ];
    for (let start = 0; start < wanted.length; start += 64)
      git(ciCleanGitDirectory, [
        ...fetchArgs,
        ...wanted.slice(start, start + 64),
      ]);
    for (const { ref, physical } of remoteRefs)
      assert.equal(
        git(ciCleanGitDirectory, ["rev-parse", "--verify", `${ref}^{commit}`])
          .toString()
          .trim(),
        physical,
      );
    const stagingDescriptor = join(root, "active.json");
    writeFileSync(stagingDescriptor, profile.bytes, {
      flag: "wx",
      mode: 0o600,
    });
    execFileSync(
      "/usr/bin/sudo",
      ["-n", "/usr/bin/install", "-d", "-m", "0755", activeDirectory],
      { env, stdio: "pipe" },
    );
    execFileSync(
      "/usr/bin/sudo",
      [
        "-n",
        "/usr/bin/install",
        "-m",
        "0644",
        "-o",
        "0",
        "-g",
        "0",
        stagingDescriptor,
        `${activeDirectory}/active.json`,
      ],
      { env, stdio: "pipe" },
    );
  }
  const { prepareHistoryGitParents } =
    await import("../bundled-native/scripts/permission-registry/prepare-history-git-parents.mjs");
  const { verifyNativeHistoryRepository } =
    await import("../bundled-native/scripts/permission-registry/surface-gate.mjs");
  process.chdir(candidate);
  const preparation = prepareHistoryGitParents(candidate, [baseSha]);
  await verifyNativeHistoryRepository(candidate, baseSha);
  process.stdout.write(
    JSON.stringify({
      schemaVersion: 1,
      status: "verified",
      phase: context.phase,
      sourceSha: context.sourceSha,
      baseSha,
      definitionSha: context.definitionSha,
      verifierSha256: bundle.sha256,
      descriptorSha256: context.descriptorSha256,
      headerSha256: profile?.installation.trust.headerSha256 ?? null,
      publicationTip: profile?.installation.finalPublicationTip ?? null,
      preparedRevisions: preparation.revisions,
    }) + "\n",
  );
}

if (
  process.argv[1] &&
  pathToFileURL(realpathSync(process.argv[1])).href === import.meta.url
)
  main().catch(() => {
    process.stderr.write("HISTORY_CI_VERIFICATION_REFUSED\n");
    process.exitCode = 1;
  });
