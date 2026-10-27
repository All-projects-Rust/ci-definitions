import { ts, hasModifier, hasDirective, importedSymbols, decorators, sourceLocation } from "./ast.mjs";

const HTTP = new Set(["GET", "POST", "PUT", "PATCH", "DELETE", "HEAD", "OPTIONS"]);
const EXPORTED = ts.SyntaxKind.ExportKeyword;
const DEFAULT = ts.SyntaxKind.DefaultKeyword;

function bindingNames(name) {
  if (ts.isIdentifier(name)) return [name.text];
  return name.elements.flatMap((element) => ts.isBindingElement(element) ? bindingNames(element.name) : []);
}

function collectExportDeclaration(statement, source, entries, issues) {
  if (!ts.isExportDeclaration(statement) || statement.isTypeOnly) return false;
  if (!statement.exportClause) {
    issues.push({ ...sourceLocation(source, statement), kind: "export-star", message: "Wildcard re-export requires explicit surface review" });
    return true;
  }
  if (ts.isNamedExports(statement.exportClause)) {
    for (const item of statement.exportClause.elements) {
      if (!item.isTypeOnly) entries.push({ name: item.name.text, node: item });
    }
  }
  return true;
}

function collectModifiedExport(statement, entries) {
  if (!hasModifier(statement, EXPORTED)) return false;
  if (hasModifier(statement, DEFAULT)) {
    entries.push({ name: "default", node: statement });
    return true;
  }
  if (ts.isFunctionDeclaration(statement) && statement.name) {
    entries.push({ name: statement.name.text, node: statement });
    return true;
  }
  if (ts.isVariableStatement(statement)) {
    for (const declaration of statement.declarationList.declarations) {
      for (const name of bindingNames(declaration.name)) entries.push({ name, node: declaration });
    }
  }
  return true;
}

function collectExportAssignment(statement, entries) {
  if (!ts.isExportAssignment(statement) || statement.isExportEquals) return false;
  entries.push({ name: "default", node: statement });
  return true;
}

function exportsFrom(source) {
  const entries = [];
  const issues = [];
  for (const statement of source.statements) {
    if (collectExportDeclaration(statement, source, entries, issues)) continue;
    if (collectModifiedExport(statement, entries)) continue;
    collectExportAssignment(statement, entries);
  }
  return { entries, issues };
}

export function discoverWeb(source) {
  const surfaces = [];
  const routeFile = /(?:^|\/)route\.[jt]sx?$/.test(source.fileName);
  const loaderFile = /(?:^|\/)(page|layout)\.[jt]sx?$/.test(source.fileName);
  const serverModule = hasDirective(source.statements, "use server");
  const clientModule = hasDirective(source.statements, "use client");
  const exported = exportsFrom(source);
  const add = (kind, name, node) => surfaces.push({ id: `${kind}:${source.fileName}#${name}`, kind, handler: name, ...sourceLocation(source, node) });
  for (const { name, node } of exported.entries) {
    if (routeFile && HTTP.has(name)) add("next-route", name, node);
    if (loaderFile && !clientModule && name === "default") add("next-loader-candidate", name, node);
    if (serverModule) add("next-server-action", name, node);
  }
  const visit = (node) => {
    if (ts.isFunctionLike(node) && node.body && ts.isBlock(node.body) && hasDirective(node.body.statements, "use server")) {
      const location = sourceLocation(source, node);
      const name = node.name?.getText(source)
        ?? (ts.isVariableDeclaration(node.parent) ? node.parent.name.getText(source) : `inline@${location.line}`);
      add("next-inline-server-action", name, node);
    }
    ts.forEachChild(node, visit);
  };
  visit(source);
  return { surfaces, issues: routeFile || serverModule ? exported.issues : [] };
}

function triggerDecorators(member, source, symbols) {
  return decorators(member, source, symbols).filter((item) =>
    (item.module === "@nestjs/schedule" && ["Cron", "Interval", "Timeout"].includes(item.name))
    || (["@nestjs/bull", "@nestjs/bullmq"].includes(item.module) && item.name === "Process")
    || (item.module === "@nestjs/websockets" && item.name === "SubscribeMessage"));
}

function classEntrySurfaces(node, source, symbols) {
  if (!ts.isClassDeclaration(node)) return [];
  const className = node.name?.text ?? "anonymous";
  const classDecorators = decorators(node, source, symbols);
  const processor = classDecorators.some((item) =>
    ["@nestjs/bull", "@nestjs/bullmq"].includes(item.module) && item.name === "Processor");
  const surfaces = [];
  for (const member of node.members) {
    if (!ts.isMethodDeclaration(member)) continue;
    const memberName = member.name.getText(source);
    const triggers = triggerDecorators(member, source, symbols);
    if (processor && memberName === "process" && triggers.length === 0) {
      triggers.push({ name: "WorkerHost.process", module: "@nestjs/bullmq" });
    }
    for (const trigger of triggers) {
      const kind = trigger.name === "SubscribeMessage" ? "websocket-event" : "background-entrypoint";
      surfaces.push({
        id: `${kind}:${source.fileName}#${className}.${memberName}:${trigger.name}`,
        kind,
        className,
        handler: memberName,
        trigger: trigger.name,
        ...sourceLocation(source, member),
      });
    }
  }
  return surfaces;
}

/** Non-HTTP entrypoints are candidates, not inferred least-privilege machine policies. */
export function discoverJobsAndStreams(source) {
  const surfaces = [];
  const symbols = importedSymbols(source);
  const visit = (node) => {
    surfaces.push(...classEntrySurfaces(node, source, symbols));
    ts.forEachChild(node, visit);
  };
  visit(source);
  return { surfaces, issues: [] };
}
