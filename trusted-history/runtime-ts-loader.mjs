import assert from "node:assert/strict";
import { lstatSync, readFileSync, realpathSync } from "node:fs";
import { dirname, resolve as resolvePath } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import ts from "typescript";
import {
  runtimeApiDirectory,
  runtimeClosureNames,
  sandboxCandidate,
  sandboxRuntime,
} from "./runtime-binding-protocol.mjs";

const directory = `${sandboxCandidate}/${runtimeApiDirectory}`;
const allowed = new Set(
  runtimeClosureNames.map((name) => `${directory}/${name}`),
);
const helperFiles = new Set(
  [
    "runtime-binding-child.mjs",
    "runtime-binding-protocol.mjs",
    "runtime-ts-register.mjs",
    "runtime-ts-loader.mjs",
  ].map((name) => `${sandboxRuntime}/${name}`),
);
export function resolveRuntimeImport(specifier, parentURL) {
  const parent = parentURL?.startsWith("file:")
    ? fileURLToPath(parentURL)
    : null;
  if (parent && allowed.has(parent)) {
    if (specifier === "node:crypto")
      return { url: specifier, shortCircuit: true };
    assert.ok(typeof specifier === "string" && /^\.\.?\//u.test(specifier));
    const base = resolvePath(dirname(parent), specifier);
    const matches = [base, `${base}.ts`].filter((file) => allowed.has(file));
    assert.equal(matches.length, 1);
    return { url: pathToFileURL(matches[0]).href, shortCircuit: true };
  }
  if (specifier.startsWith("file:")) {
    const file = fileURLToPath(specifier);
    if (allowed.has(file)) {
      assert.ok(parent && helperFiles.has(parent));
      return { url: specifier, shortCircuit: true };
    }
  }
  return null;
}
export function transpileRuntimeSource(file, bytes) {
  assert.ok(allowed.has(file));
  assert.equal(ts.version, "5.9.3");
  assert.ok(
    Buffer.isBuffer(bytes) && bytes.length > 0 && bytes.length <= 512 * 1024,
  );
  const text = bytes.toString("utf8");
  assert.deepEqual(Buffer.from(text), bytes);
  if (file.endsWith(".json")) {
    JSON.parse(text);
    return `export default JSON.parse(${JSON.stringify(text)});\n`;
  }
  const ast = ts.createSourceFile(
    file,
    text,
    ts.ScriptTarget.Latest,
    true,
    ts.ScriptKind.TS,
  );
  const visit = (node) => {
    if (
      (ts.isImportDeclaration(node) || ts.isExportDeclaration(node)) &&
      node.moduleSpecifier
    ) {
      assert.ok(ts.isStringLiteralLike(node.moduleSpecifier));
      resolveRuntimeImport(node.moduleSpecifier.text, pathToFileURL(file).href);
    }
    if (ts.isImportEqualsDeclaration(node))
      throw new Error("RUNTIME_IMPORT_EQUALS_REFUSED");
    if (
      ts.isCallExpression(node) &&
      (node.expression.kind === ts.SyntaxKind.ImportKeyword ||
        node.expression.getText(ast) === "require")
    )
      throw new Error("RUNTIME_DYNAMIC_MODULE_LOAD_REFUSED");
    ts.forEachChild(node, visit);
  };
  visit(ast);
  const result = ts.transpileModule(text, {
    fileName: file,
    reportDiagnostics: true,
    compilerOptions: {
      target: ts.ScriptTarget.ES2022,
      module: ts.ModuleKind.ESNext,
      verbatimModuleSyntax: false,
    },
  });
  assert.ok(
    !result.diagnostics?.some(
      (d) => d.category === ts.DiagnosticCategory.Error,
    ),
  );
  const javascript = ts.createSourceFile(
    file + ".js",
    result.outputText,
    ts.ScriptTarget.Latest,
    true,
    ts.ScriptKind.JS,
  );
  for (const node of javascript.statements)
    if (
      (ts.isImportDeclaration(node) || ts.isExportDeclaration(node)) &&
      node.moduleSpecifier
    ) {
      assert.ok(ts.isStringLiteralLike(node.moduleSpecifier));
      resolveRuntimeImport(node.moduleSpecifier.text, pathToFileURL(file).href);
    }
  return result.outputText;
}
export function resolve(specifier, context, nextResolve) {
  return (
    resolveRuntimeImport(specifier, context.parentURL) ??
    nextResolve(specifier, context)
  );
}
export function load(url, context, nextLoad) {
  const file = url.startsWith("file:") ? fileURLToPath(url) : null;
  if (!file || !allowed.has(file)) return nextLoad(url, context);
  assert.equal(realpathSync(file), file);
  const stat = lstatSync(file);
  assert.ok(
    stat.isFile() &&
      !stat.isSymbolicLink() &&
      stat.nlink === 1 &&
      stat.size > 0 &&
      stat.size <= 512 * 1024,
  );
  return {
    format: "module",
    source: transpileRuntimeSource(file, readFileSync(file)),
    shortCircuit: true,
  };
}
