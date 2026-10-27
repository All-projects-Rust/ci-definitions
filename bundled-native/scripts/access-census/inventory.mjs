#!/usr/bin/env node
import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
import {
  readFileSync,
  readdirSync,
  writeFileSync,
  mkdirSync,
  realpathSync,
  existsSync,
} from "node:fs";
import { dirname, join, relative, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";
import { parseSource, sourceLocation, ts } from "./ast.mjs";
import { discoverSurfaces } from "./discovery.mjs";

const isSource = (file) =>
  (/\.[cm]?[jt]sx?$/u.test(file) && !/\.(?:spec|test|d)\.[cm]?[jt]sx?$/u.test(file)) ||
  (/\.py$/u.test(file) && !/^(?:test_.+|.+_test|conftest)\.py$/u.test(file));
const portable = (file) => file.split(sep).join("/");
const DEFAULT_SOURCE_PREFIXES = [
  "apps/api",
  "apps/web",
  "workers",
  "apps/desktop/src",
  "packages/mcp-server",
];
const MANDATORY_SOURCE_PREFIXES = new Set([
  "apps/api",
  "apps/web",
  "workers",
  "packages/mcp-server",
]);
function compareFile(a, b) {
  if (a.file < b.file) return -1;
  if (a.file > b.file) return 1;
  return 0;
}

function excludedTestSpecifier(value) {
  const normalized = value.replaceAll("\\", "/");
  const basename = normalized.slice(normalized.lastIndexOf("/") + 1);
  return (
    /\.(?:spec|test)(?:\.[cm]?[jt]sx?)?$/u.test(basename) ||
    /^(?:test_.+|.+_test|conftest)(?:\.py)?$/u.test(basename)
  );
}

function staticModuleSpecifier(node, constants = new Map(), seen = new Set()) {
  if (!node) return null;
  if (ts.isStringLiteralLike(node) || ts.isNoSubstitutionTemplateLiteral(node)) return node.text;
  if (
    ts.isParenthesizedExpression(node) ||
    ts.isAsExpression(node) ||
    ts.isSatisfiesExpression(node)
  ) {
    return staticModuleSpecifier(node.expression, constants, seen);
  }
  if (ts.isIdentifier(node) && constants.has(node.text) && !seen.has(node.text)) {
    return staticModuleSpecifier(
      constants.get(node.text),
      constants,
      new Set([...seen, node.text]),
    );
  }
  if (ts.isBinaryExpression(node) && node.operatorToken.kind === ts.SyntaxKind.PlusToken) {
    const left = staticModuleSpecifier(node.left, constants, seen);
    const right = staticModuleSpecifier(node.right, constants, seen);
    return left === null || right === null ? null : left + right;
  }
  if (ts.isTemplateExpression(node)) {
    let value = node.head.text;
    for (const span of node.templateSpans) {
      const part = staticModuleSpecifier(span.expression, constants, seen);
      if (part === null) return null;
      value += part + span.literal.text;
    }
    return value;
  }
  return null;
}

function javascriptModuleLoads(input) {
  const source = parseSource(input.file, input.text);
  const loads = [];
  const constants = new Map();
  const duplicateConstants = new Set();
  const requireAliases = new Set(["require"]);
  const collectBindings = (node) => {
    if (
      ts.isVariableDeclaration(node) &&
      ts.isIdentifier(node.name) &&
      node.initializer &&
      ts.isVariableDeclarationList(node.parent) &&
      (node.parent.flags & ts.NodeFlags.Const) !== 0
    ) {
      if (constants.has(node.name.text)) duplicateConstants.add(node.name.text);
      else constants.set(node.name.text, node.initializer);
    }
    ts.forEachChild(node, collectBindings);
  };
  collectBindings(source);
  for (const name of duplicateConstants) constants.delete(name);
  let changed = true;
  while (changed) {
    changed = false;
    for (const [name, initializer] of constants) {
      if (
        ts.isIdentifier(initializer) &&
        requireAliases.has(initializer.text) &&
        !requireAliases.has(name)
      ) {
        requireAliases.add(name);
        changed = true;
      }
    }
  }
  const record = (node, loader, argument) => {
    const specifier = staticModuleSpecifier(argument, constants);
    loads.push({
      specifier,
      loader,
      line: sourceLocation(source, node).line,
      fingerprint: createHash("sha256").update(node.getText(source)).digest("hex"),
    });
  };
  const visit = (node) => {
    if ((ts.isImportDeclaration(node) || ts.isExportDeclaration(node)) && node.moduleSpecifier) {
      record(node, ts.isImportDeclaration(node) ? "import" : "re-export", node.moduleSpecifier);
    }
    if (
      ts.isImportEqualsDeclaration(node) &&
      ts.isExternalModuleReference(node.moduleReference) &&
      node.moduleReference.expression
    ) {
      record(node, "import-equals", node.moduleReference.expression);
    }
    if (
      ts.isCallExpression(node) &&
      node.arguments.length === 1 &&
      ((ts.isIdentifier(node.expression) && requireAliases.has(node.expression.text)) ||
        node.expression.kind === ts.SyntaxKind.ImportKeyword)
    ) {
      record(
        node,
        node.expression.kind === ts.SyntaxKind.ImportKeyword ? "import" : "require",
        node.arguments[0],
      );
    }
    ts.forEachChild(node, visit);
  };
  visit(source);
  return loads;
}

function pythonModuleLoads(input) {
  const loads = [];
  const record = (specifier, loader, offset, expression) => {
    loads.push({
      specifier,
      loader,
      line: input.text.slice(0, offset).split(/\r?\n/u).length,
      fingerprint: createHash("sha256").update(expression).digest("hex"),
    });
  };
  const fromPattern = /^\s*from\s+([.\w]+)\s+import\s*(?:\(([\s\S]*?)\)|([^\n#]+))/gmu;
  for (const match of input.text.matchAll(fromPattern)) {
    const parent = match[1].replaceAll(".", "/");
    record(parent, "python-from", match.index, match[0]);
    for (const item of (match[2] ?? match[3]).split(",")) {
      const importedName = item.trim().split(/\s+as\s+/u)[0];
      if (importedName && importedName !== "*") {
        record(`${parent}/${importedName}`, "python-from", match.index, match[0]);
      }
    }
  }
  const importPattern = /^\s*import\s+([^\n#]+)/gmu;
  for (const match of input.text.matchAll(importPattern)) {
    for (const item of match[1].split(",")) {
      const module = item.trim().split(/\s+as\s+/u)[0];
      if (module) record(module.replaceAll(".", "/"), "python-import", match.index, match[0]);
    }
  }
  const dynamicPattern = /\b(?:importlib\.import_module|__import__)\s*\(([^)]*)\)/gu;
  for (const match of input.text.matchAll(dynamicPattern)) {
    const argument = match[1].trim();
    const literal = /^(?:(["'])([^"']+)\1)$/u.exec(argument)?.[2] ?? null;
    record(literal?.replaceAll(".", "/") ?? null, "python-dynamic", match.index, match[0]);
  }
  return loads;
}

function moduleLoads(input) {
  return input.file.endsWith(".py") ? pythonModuleLoads(input) : javascriptModuleLoads(input);
}

export function discoverOpaqueModuleLoads(inputs) {
  return inputs.flatMap((input) =>
    moduleLoads(input)
      .filter(({ specifier }) => specifier === null)
      .map(({ loader, line, fingerprint }) => ({
        file: input.file,
        loader,
        line,
        fingerprint,
      })),
  );
}

function assertNoProductionTestImports(inputs) {
  for (const input of inputs) {
    const specifiers = moduleLoads(input)
      .map(({ specifier }) => specifier)
      .filter((specifier) => specifier !== null);
    const forbidden = specifiers.find(excludedTestSpecifier);
    if (forbidden) {
      throw new Error(`PRODUCTION_IMPORTS_EXCLUDED_TEST_SOURCE ${input.file} -> ${forbidden}`);
    }
  }
}

function isGeneratedWorkspaceDirectory(repository, directory) {
  const path = portable(relative(repository, directory));
  return (
    path === "apps/web/.next" ||
    path === "apps/api/dist" ||
    // packages/mcp-server's tsc build writes its own hand-written src/ back out as
    // compiled CommonJS under dist/ — scanning both would double-count every tool
    // registration as two unrelated surfaces, and the compiled form's
    // `require(...)`-based imports aren't resolvable by the MCP tool-schema AST
    // matcher (it only recognizes ESM import bindings), so a fresh CI build of this
    // gitignored, non-authoritative output would fail closed on a surface that was
    // already reviewed through its src/ source. See scripts/permission-registry/README.md.
    path === "packages/mcp-server/dist" ||
    /^(?:apps\/(?:api|web)|packages\/mcp-server|workers\/[^/]+)\/(?:node_modules|\.venv|venv)$/u.test(
      path,
    )
  );
}

// The dist exclusion above trusts that nothing gets committed there — check it, so
// force-adding compiled/hand-written code under a path this scanner treats as
// "generated, skip it" can't smuggle an unreviewed surface past the gate. Only
// meaningful inside an actual git checkout (fixtures in tests use plain temp
// directories with no .git at all, where "tracked" doesn't apply).
function assertGeneratedDirectoryUntracked(repository, relativePath) {
  let tracked;
  try {
    tracked = execFileSync("/usr/bin/git", ["ls-files", "--", relativePath], {
      cwd: repository,
      encoding: "utf8",
      timeout: 15_000,
    }).trim();
  } catch (error) {
    if (existsSync(join(repository, ".git"))) {
      throw new Error(`GENERATED_DIRECTORY_TRACKING_CHECK_FAILED ${relativePath}`, {
        cause: error,
      });
    }
    return;
  }
  if (tracked) {
    throw new Error(`TRACKED_FILES_UNDER_EXCLUDED_GENERATED_DIRECTORY ${relativePath}`);
  }
}

// The web build copies the widget bundle into public after the authoritative
// source has already been scanned. Exclude that exact generated output only
// while Git confirms it is untracked. A committed file at the same path stays
// in the inventory, and a non-Git fixture/check fails closed by scanning it.
const GENERATED_UNTRACKED_WORKSPACE_FILES = Object.freeze(["apps/web/public/widget.js"]);

function isConfirmedUntracked(repository, relativePath) {
  try {
    const inside = execFileSync("/usr/bin/git", ["rev-parse", "--is-inside-work-tree"], {
      cwd: repository,
      encoding: "utf8",
      stdio: ["ignore", "pipe", "ignore"],
      timeout: 15_000,
    }).trim();
    if (inside !== "true") return false;
    const tracked = execFileSync("/usr/bin/git", ["ls-files", "--", relativePath], {
      cwd: repository,
      encoding: "utf8",
      stdio: ["ignore", "pipe", "ignore"],
      timeout: 15_000,
    })
      .split(/\r?\n/u)
      .some((file) => portable(file) === relativePath);
    return !tracked;
  } catch {
    return false;
  }
}

/** Reads source files only, never .env, credentials, databases or runtime data. */
export function readSourceInputs(root, prefixes = DEFAULT_SOURCE_PREFIXES) {
  const repository = realpathSync(root);
  assertGeneratedDirectoryUntracked(repository, "packages/mcp-server/dist");
  assertGeneratedDirectoryUntracked(repository, "apps/api/dist");
  const excludedGeneratedFiles = new Set(
    GENERATED_UNTRACKED_WORKSPACE_FILES.filter((file) => isConfirmedUntracked(repository, file)),
  );
  const inputs = [];
  const seen = new Set();
  const walk = (directory) => {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      const full = join(directory, entry.name);
      if (entry.isSymbolicLink()) {
        throw new Error(
          `Source inventory refuses symlink entry: ${portable(relative(repository, full))}`,
        );
      }
      if (entry.isDirectory()) {
        if (!isGeneratedWorkspaceDirectory(repository, full)) walk(full);
      } else if (
        entry.isFile() &&
        isSource(entry.name) &&
        !excludedGeneratedFiles.has(portable(relative(repository, full))) &&
        !seen.has(full)
      ) {
        seen.add(full);
        inputs.push({
          file: portable(relative(repository, full)),
          text: readFileSync(full, "utf8"),
        });
      }
    }
  };
  for (const prefix of prefixes) {
    const directory = resolve(repository, prefix);
    if (!directory.startsWith(`${repository}${sep}`))
      throw new Error("Source prefix must remain inside repository");
    if (!existsSync(directory) && !MANDATORY_SOURCE_PREFIXES.has(prefix)) continue;
    // Reject symlink prefixes, including intermediate segments, before reading source.
    if (existsSync(directory) && realpathSync(directory) !== directory)
      throw new Error("Source prefix must not traverse a symlink");
    walk(directory); // Missing mandatory roots or a raced-away source file must fail visibly.
  }
  inputs.sort(compareFile);
  assertNoProductionTestImports(inputs);
  return inputs;
}

function isGeneratedWorkspaceFile(file) {
  return (
    file.startsWith("apps/web/.next/") ||
    file.startsWith("apps/api/dist/") ||
    file.startsWith("packages/mcp-server/dist/") ||
    /^(?:apps\/(?:api|web)|packages\/mcp-server|workers\/[^/]+)\/(?:node_modules|\.venv|venv)\//u.test(
      file,
    )
  );
}

function readGitBlobs(repository, commit, files) {
  if (files.length === 0) return [];
  const query = `${files.map((file) => `${commit}:${file}`).join("\n")}\n`;
  const output = execFileSync("/usr/bin/git", ["cat-file", "--batch"], {
    cwd: repository,
    input: query,
    maxBuffer: 256 * 1024 * 1024,
  });
  const values = [];
  let offset = 0;
  for (const file of files) {
    const newline = output.indexOf(0x0a, offset);
    if (newline < 0) throw new Error(`Git blob header missing for ${file}`);
    const header = output.subarray(offset, newline).toString("utf8");
    const match = /^[a-f0-9]{40,64} blob (\d+)$/u.exec(header);
    if (!match) throw new Error(`Git source blob missing for ${file}`);
    const size = Number(match[1]);
    const start = newline + 1;
    const end = start + size;
    if (!Number.isSafeInteger(size) || end >= output.length) {
      throw new Error(`Invalid git source blob for ${file}`);
    }
    values.push({ file, text: output.subarray(start, end).toString("utf8") });
    offset = end + 1;
  }
  return values;
}

/** Reads source blobs from an immutable git commit without consulting the worktree. */
export function readSourceInputsAtGitCommit(root, commit, prefixes = DEFAULT_SOURCE_PREFIXES) {
  const repository = realpathSync(root);
  if (!/^[a-f0-9]{40}$/u.test(commit)) throw new Error("Invalid boundary commit");
  const resolved = execFileSync("/usr/bin/git", ["rev-parse", "--verify", `${commit}^{commit}`], {
    cwd: repository,
    encoding: "utf8",
    timeout: 15_000,
  }).trim();
  if (resolved !== commit) throw new Error("Boundary commit must be an exact SHA");
  for (const prefix of prefixes) {
    if (prefix.startsWith("/") || prefix.split("/").includes("..")) {
      throw new Error("Source prefix must remain inside repository");
    }
    if (!MANDATORY_SOURCE_PREFIXES.has(prefix)) continue;
    execFileSync("/usr/bin/git", ["cat-file", "-e", `${commit}:${prefix}`], {
      cwd: repository,
      timeout: 15_000,
    });
  }
  const listing = execFileSync(
    "/usr/bin/git",
    ["ls-tree", "-rz", "--full-tree", commit, "--", ...prefixes],
    { cwd: repository, maxBuffer: 64 * 1024 * 1024 },
  );
  const files = [];
  for (const record of listing.toString("utf8").split("\0")) {
    if (!record) continue;
    const match = /^(\d{6}) (\w+) [a-f0-9]+\t(.+)$/u.exec(record);
    if (!match) throw new Error("Invalid git source tree record");
    const [, mode, type, file] = match;
    if (mode === "120000") throw new Error(`Source inventory refuses symlink entry: ${file}`);
    if (file.startsWith("apps/api/dist/")) {
      throw new Error("TRACKED_FILES_UNDER_EXCLUDED_GENERATED_DIRECTORY apps/api/dist");
    }
    const name = file.slice(file.lastIndexOf("/") + 1);
    if (type === "blob" && isSource(name) && !isGeneratedWorkspaceFile(file)) {
      files.push(file);
    }
  }
  files.sort();
  const inputs = readGitBlobs(repository, commit, [...new Set(files)]);
  assertNoProductionTestImports(inputs);
  return inputs;
}

export function buildInventory(inputs, baseCommit) {
  const discovery = discoverSurfaces(inputs.filter(({ file }) => !file.endsWith(".py")));
  const byKind = Object.create(null);
  for (const surface of discovery.surfaces) byKind[surface.kind] = (byKind[surface.kind] ?? 0) + 1;
  const sourceUnits = inputs
    .filter(({ file }) =>
      /(?:^workers\/|^packages\/mcp-server\/|^apps\/worker-|^apps\/desktop\/|\/modules\/mcp\/|\/management-reports\/|\.(?:worker|processor|scheduler|poller|gateway)\.[jt]s$)/u.test(
        file,
      ),
    )
    .map(({ file }) => ({
      file,
      stage: "INVENTORY",
      classification: null,
      reason:
        "Source unit requires manual review for non-decorator dispatch, reportId, service calls, file/download and machine-principal boundaries",
    }));
  return {
    schemaVersion: 1,
    task: "SIG-669",
    specification: "SIG669-ACC-V1-20260918",
    baseCommit,
    stage: "INVENTORY",
    notice:
      "Source-declared surfaces only. No authorization classification, enforcement, runtime-mount proof or legacy parity is implied.",
    sourceFileCount: inputs.length,
    sourceHash: createHash("sha256")
      .update(
        inputs
          .map(({ file, text }) => `${file}\0${createHash("sha256").update(text).digest("hex")}`)
          .join("\n"),
      )
      .digest("hex"),
    counts: {
      sourceDeclaredSurfaces: discovery.surfaces.length,
      byKind,
      classified: 0,
      enforced: 0,
      discoveryIssues: discovery.issues.length,
      manualSourceUnits: sourceUnits.length,
    },
    discoveryIssues: discovery.issues,
    surfaces: discovery.surfaces.map((surface) => ({
      ...surface,
      stage: "INVENTORY",
      classification: null,
      resource: null,
      action: null,
      scopeContract: null,
      fieldProjection: null,
      acceptanceTests: [],
    })),
    manualSourceUnits: sourceUnits,
    limitations: [
      "Registration in a Nest module, global prefixes and versioning require runtime metadata reconciliation.",
      "Decorator wrappers, inherited Controller metadata without a local Controller decorator, dynamic router factories, direct router registration and non-decorator job dispatch require explicit review.",
      "A Next server-loader candidate may be static; its presence is not proof of a data read.",
      "MCP tool implementations, generic reportId variants, native clients, downloads, stream emission and direct service invocations require semantic inventory beyond route discovery.",
      "Updating this inventory alone does not authorize any endpoint. SIG-909's separate checked surface ledger requires every post-baseline path to be BOUND with runtime-boundary proof or explicitly EXEMPT.",
    ],
  };
}

function main() {
  const root = resolve(dirname(fileURLToPath(import.meta.url)), "../..");
  const output = process.argv[2];
  if (!output) throw new Error("Usage: node scripts/access-census/inventory.mjs <output.json>");
  const destination = resolve(root, output);
  if (!destination.startsWith(`${root}${sep}`))
    throw new Error("Inventory output must remain inside repository");
  const commit = execFileSync("/usr/bin/git", ["rev-parse", "HEAD"], {
    cwd: root,
    encoding: "utf8",
    timeout: 15000,
  }).trim();
  const result = buildInventory(readSourceInputs(root), commit);
  mkdirSync(dirname(destination), { recursive: true });
  writeFileSync(destination, JSON.stringify(result, null, 2) + "\n");
  process.stdout.write(
    JSON.stringify(
      { output: portable(relative(root, destination)), baseCommit: commit, counts: result.counts },
      null,
      2,
    ) + "\n",
  );
  if (result.discoveryIssues.length) process.exitCode = 1;
}

if (process.argv[1] && realpathSync(process.argv[1]) === fileURLToPath(import.meta.url)) main();
