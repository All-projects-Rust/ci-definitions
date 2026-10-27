#!/usr/bin/env node
import { createHash } from "node:crypto";
import {
  existsSync,
  mkdirSync,
  readFileSync,
  realpathSync,
  renameSync,
  writeFileSync,
} from "node:fs";
import { dirname, posix, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";
import {
  decorators,
  importedReference,
  importedSymbols,
  parseSource,
  sourceLocation,
  ts,
} from "../access-census/ast.mjs";
import { discoverSurfaces } from "../access-census/discovery.mjs";
import { withParsedInventory } from "../access-census/parsed-inventory.mjs";
import { createFixedRecordReportProof } from "./fixed-record-report-proof.mjs";
import {
  discoverOpaqueModuleLoads,
  readSourceInputs,
  readSourceInputsAtGitCommit,
} from "../access-census/inventory.mjs";

import {
  buildLedgerFromEntries,
  buildLegacyBaselineAnchor,
  surfaceIdentity,
} from "./ledger-format.mjs";
import {
  readSurfaceHistory,
  readEvolutionSurfaceHistory,
  assertEvolutionSurfaceReaderCurrent,
  writeSurfaceFragment,
  getSourceHeadSelections,
  buildClassifiedSourceLedger,
  buildContinuedSourceLedger,
} from "./surface-history.mjs";
export { buildLedgerFromEntries, buildLegacyBaselineAnchor } from "./ledger-format.mjs";

const ACTIONS = new Set([
  "CREATE",
  "READ",
  "UPDATE",
  "DELETE",
  "SEND",
  "EXPORT",
  "ASSIGN",
  "TRANSFER",
  "COMPLETE",
  "APPROVE",
  "MANAGE",
  "IMPERSONATE",
  "OVERRIDE",
  "PUBLISH",
  "SHARE",
  "DOWNLOAD",
  "CORRECT",
]);
const RESOURCE_KEY = /^[a-z][a-z0-9]*(?:[._-][a-z0-9]+)*$/u;
const APPROVED_BOUNDARY_MODULE = "apps/api/src/modules/access-control/permission-runtime-boundary";
const PERMISSION_MANIFEST_MODULE = "apps/api/src/modules/access-control/permission-manifest";
const JWT_AUTH_GUARD_MODULE = "apps/api/src/modules/auth/jwt-auth.guard";
const ORGANIZATION_EXECUTOR_MODULE =
  "apps/api/src/modules/access-control/access-policy.organization-execution";
const INVENTORY_EXECUTOR_MODULE = "apps/api/src/modules/access-control/inventory-policy-execution";
const MCP_SCHEMA_MODULE = "@modelcontextprotocol/sdk/types.js";
const SIG909_BOOTSTRAP_BASE_COMMIT = "096a460784ce3cfb2e82908467fb527cd47b8936";

export function assertSig909BootstrapBase(commit) {
  if (commit !== SIG909_BOOTSTRAP_BASE_COMMIT) {
    throw new Error("BOOTSTRAP_EXACT_BASE_REQUIRED");
  }
}

function compare(a, b) {
  if (a < b) return -1;
  if (a > b) return 1;
  return 0;
}

function stable(value) {
  if (Array.isArray(value)) return `[${value.map(stable).join(",")}]`;
  if (value && typeof value === "object") {
    return `{${Object.entries(value)
      .filter(([, item]) => item !== undefined)
      .sort(([a], [b]) => compare(a, b))
      .map(([key, item]) => `${JSON.stringify(key)}:${stable(item)}`)
      .join(",")}}`;
  }
  return JSON.stringify(value) ?? "null";
}

const digest = (value) => createHash("sha256").update(stable(value)).digest("hex");
const contentDigest = (value) => createHash("sha256").update(value).digest("hex");

function literalProperty(object, name) {
  const property = object.properties.find(
    (item) =>
      ts.isPropertyAssignment(item) &&
      !ts.isComputedPropertyName(item.name) &&
      item.name.getText().replace(/^['"]|['"]$/gu, "") === name,
  );
  return property?.initializer;
}

function propertyName(node, source) {
  if (!node || ts.isComputedPropertyName(node)) return null;
  return node.getText(source).replace(/^['"]|['"]$/gu, "");
}

function toolSurface(input, source, name, node) {
  const handlerLine = sourceLocation(source, node).line;
  return {
    id: `mcp-tool:${input.file}#${name}`,
    kind: "mcp-tool",
    tags: ["mcp"],
    file: input.file,
    handler: name,
    handlerFile: input.file,
    handlerLine,
    line: handlerLine,
  };
}

function bindingContainsName(binding, name) {
  if (ts.isIdentifier(binding)) return binding.text === name;
  if (ts.isObjectBindingPattern(binding) || ts.isArrayBindingPattern(binding)) {
    return binding.elements.some(
      (element) => ts.isBindingElement(element) && bindingContainsName(element.name, name),
    );
  }
  return false;
}

function statementDeclaresName(statement, name) {
  if (ts.isVariableStatement(statement)) {
    return statement.declarationList.declarations.some((declaration) =>
      bindingContainsName(declaration.name, name),
    );
  }
  return Boolean(
    (ts.isFunctionDeclaration(statement) ||
      ts.isClassDeclaration(statement) ||
      ts.isTypeAliasDeclaration(statement) ||
      ts.isInterfaceDeclaration(statement) ||
      ts.isEnumDeclaration(statement)) &&
    statement.name?.text === name,
  );
}

function importedReferenceIsShadowed(node, name) {
  let current = node.parent;
  while (current) {
    if (
      ts.isFunctionLike(current) &&
      current.parameters.some((parameter) => bindingContainsName(parameter.name, name))
    ) {
      return true;
    }
    if (
      (ts.isBlock(current) || ts.isSourceFile(current)) &&
      current.statements.some(
        (statement) => !ts.isImportDeclaration(statement) && statementDeclaresName(statement, name),
      )
    ) {
      return true;
    }
    if (
      (ts.isForStatement(current) ||
        ts.isForInStatement(current) ||
        ts.isForOfStatement(current)) &&
      current.initializer &&
      ts.isVariableDeclarationList(current.initializer) &&
      current.initializer.declarations.some((declaration) =>
        bindingContainsName(declaration.name, name),
      )
    ) {
      return true;
    }
    if (
      ts.isCaseBlock(current) &&
      current.clauses.some((clause) =>
        clause.statements.some((statement) => statementDeclaresName(statement, name)),
      )
    ) {
      return true;
    }
    if (ts.isCatchClause(current) && bindingContainsName(current.variableDeclaration?.name, name)) {
      return true;
    }
    current = current.parent;
  }
  return false;
}

function importedSchemaName(node, symbols) {
  if (!node) return null;
  const imported = ts.isIdentifier(node) ? symbols.get(node.text) : null;
  if (
    !imported ||
    imported.module !== MCP_SCHEMA_MODULE ||
    importedReferenceIsShadowed(node, node.text)
  ) {
    return null;
  }
  return imported.name;
}

function toolsArrayFromListHandler(call, source) {
  const handler = call.arguments[1];
  if (!handler || !ts.isFunctionLike(handler)) {
    throw new Error(`OPAQUE_MCP_REGISTRATION ${source.fileName}`);
  }
  let returned;
  if (ts.isArrowFunction(handler) && !ts.isBlock(handler.body)) {
    returned = unwrapPureExpression(handler.body);
  } else if (handler.body && ts.isBlock(handler.body)) {
    const statements = [...handler.body.statements];
    const terminal = statements.pop();
    const pureDeclarations = statements.every(
      (statement) =>
        ts.isVariableStatement(statement) &&
        statement.declarationList.declarations.every(
          (declaration) =>
            ts.isIdentifier(declaration.name) &&
            declaration.initializer &&
            isStaticMcpErrorValue(declaration.initializer),
        ),
    );
    if (!pureDeclarations || !terminal || !ts.isReturnStatement(terminal) || !terminal.expression) {
      throw new Error(`OPAQUE_MCP_REGISTRATION ${source.fileName}`);
    }
    returned = unwrapPureExpression(terminal.expression);
  }
  if (!returned || !ts.isObjectLiteralExpression(returned) || returned.properties.length !== 1) {
    throw new Error(`OPAQUE_MCP_REGISTRATION ${source.fileName}`);
  }
  const tools = returned.properties[0];
  if (
    !ts.isPropertyAssignment(tools) ||
    propertyName(tools.name, source) !== "tools" ||
    !ts.isArrayLiteralExpression(tools.initializer)
  ) {
    throw new Error(`OPAQUE_MCP_REGISTRATION ${source.fileName}`);
  }
  return tools.initializer;
}

function literalToolsFromArray(input, source, array) {
  const found = [];
  for (const element of array.elements) {
    if (!ts.isObjectLiteralExpression(element)) {
      throw new Error(`OPAQUE_MCP_REGISTRATION ${input.file}`);
    }
    const properties = new Map();
    for (const property of element.properties) {
      if (!ts.isPropertyAssignment(property) || ts.isComputedPropertyName(property.name)) {
        throw new Error(`OPAQUE_MCP_REGISTRATION ${input.file}`);
      }
      const key = propertyName(property.name, source);
      if (!key || properties.has(key)) {
        throw new Error(`OPAQUE_MCP_REGISTRATION ${input.file}`);
      }
      properties.set(key, property.initializer);
    }
    const name = properties.get("name");
    if (!name || !ts.isStringLiteralLike(name)) {
      throw new Error(`OPAQUE_MCP_REGISTRATION ${input.file}`);
    }
    found.push(toolSurface(input, source, name.text, element));
  }
  return found;
}

function directHandlerSwitches(handler) {
  const switches = [];
  const visit = (node) => {
    if (node !== handler && ts.isFunctionLike(node)) return;
    if (ts.isSwitchStatement(node)) switches.push(node);
    ts.forEachChild(node, visit);
  };
  visit(handler);
  return switches;
}

function requestNameAliases(handler, source) {
  const request = handler.parameters?.[0]?.name;
  if (!request || !ts.isIdentifier(request)) return { request: null, aliases: new Set() };
  const aliases = new Set();
  const visit = (node) => {
    if (node !== handler && ts.isFunctionLike(node)) return;
    if (ts.isVariableDeclaration(node) && ts.isObjectBindingPattern(node.name)) {
      const initializer = node.initializer?.getText(source);
      if (initializer === `${request.text}.params`) {
        for (const element of node.name.elements) {
          if (
            ts.isIdentifier(element.name) &&
            (element.propertyName ?? element.name).getText(source) === "name"
          ) {
            aliases.add(element.name.text);
          }
        }
      }
    }
    ts.forEachChild(node, visit);
  };
  visit(handler);
  return { request: request.text, aliases };
}

function isMcpNameReference(node, source, request, aliases) {
  return (
    (ts.isIdentifier(node) && aliases.has(node.text)) ||
    node.getText(source) === `${request}.params.name`
  );
}

function containsMcpNameReference(node, source, request, aliases) {
  let found = false;
  const visit = (candidate) => {
    if (isMcpNameReference(candidate, source, request, aliases)) found = true;
    if (!found) ts.forEachChild(candidate, visit);
  };
  visit(node);
  return found;
}

function isDirectMcpNameComparison(node, source, request, aliases) {
  if (!ts.isBinaryExpression(node)) return false;
  if (
    ![
      ts.SyntaxKind.EqualsEqualsToken,
      ts.SyntaxKind.EqualsEqualsEqualsToken,
      ts.SyntaxKind.ExclamationEqualsToken,
      ts.SyntaxKind.ExclamationEqualsEqualsToken,
    ].includes(node.operatorToken.kind)
  ) {
    return false;
  }
  return (
    isMcpNameReference(node.left, source, request, aliases) ||
    isMcpNameReference(node.right, source, request, aliases)
  );
}

function containsDirectMcpNameComparison(node, source, request, aliases) {
  let found = false;
  const visit = (candidate) => {
    if (isDirectMcpNameComparison(candidate, source, request, aliases)) found = true;
    if (!found) ts.forEachChild(candidate, visit);
  };
  visit(node);
  return found;
}

function isStaticMcpErrorValue(node) {
  const value =
    ts.isAsExpression(node) || ts.isSatisfiesExpression(node) || ts.isParenthesizedExpression(node)
      ? node.expression
      : node;
  if (
    ts.isStringLiteralLike(value) ||
    ts.isNumericLiteral(value) ||
    ts.isNoSubstitutionTemplateLiteral(value) ||
    [ts.SyntaxKind.TrueKeyword, ts.SyntaxKind.FalseKeyword, ts.SyntaxKind.NullKeyword].includes(
      value.kind,
    )
  ) {
    return true;
  }
  if (ts.isArrayLiteralExpression(value)) {
    return value.elements.every(
      (element) => !ts.isSpreadElement(element) && isStaticMcpErrorValue(element),
    );
  }
  if (ts.isObjectLiteralExpression(value)) {
    return value.properties.every(
      (property) =>
        ts.isPropertyAssignment(property) &&
        !ts.isComputedPropertyName(property.name) &&
        isStaticMcpErrorValue(property.initializer),
    );
  }
  return false;
}

function isLiteralStaticMcpSet(identifier, handler, source) {
  const declarations = [];
  let unsafeUse = false;
  const visit = (node) => {
    if (node !== handler && ts.isFunctionLike(node)) return;
    if (
      ts.isVariableDeclaration(node) &&
      ts.isIdentifier(node.name) &&
      node.name.text === identifier
    ) {
      declarations.push(node);
    } else if (ts.isIdentifier(node) && node.text === identifier) {
      const owner = node.parent;
      const declarationName = ts.isVariableDeclaration(owner) && owner.name === node;
      const approvedHas =
        ts.isPropertyAccessExpression(owner) &&
        owner.expression === node &&
        owner.name.text === "has";
      if (!declarationName && !approvedHas) unsafeUse = true;
    }
    ts.forEachChild(node, visit);
  };
  visit(handler);
  if (unsafeUse || declarations.length !== 1) return false;
  const declaration = declarations[0];
  const declarationList = declaration.parent;
  const initializer = declaration.initializer;
  return Boolean(
    ts.isVariableDeclarationList(declarationList) &&
    declarationList.flags & ts.NodeFlags.Const &&
    initializer &&
    ts.isNewExpression(initializer) &&
    ts.isIdentifier(initializer.expression) &&
    initializer.expression.text === "Set" &&
    !importedReferenceIsShadowed(initializer.expression, "Set") &&
    initializer.arguments?.length === 1 &&
    ts.isArrayLiteralExpression(initializer.arguments[0]) &&
    initializer.arguments[0].elements.every((element) => ts.isStringLiteralLike(element)),
  );
}

function isApprovedMcpNameGuardExpression(node, handler, source, request, aliases) {
  if (!containsMcpNameReference(node, source, request, aliases)) {
    return isApprovedMcpScopeGuardExpression(node);
  }
  if (
    ts.isParenthesizedExpression(node) ||
    ts.isAsExpression(node) ||
    ts.isSatisfiesExpression(node) ||
    ts.isNonNullExpression(node)
  ) {
    return isApprovedMcpNameGuardExpression(node.expression, handler, source, request, aliases);
  }
  if (ts.isPrefixUnaryExpression(node) && node.operator === ts.SyntaxKind.ExclamationToken) {
    return isApprovedMcpNameGuardExpression(node.operand, handler, source, request, aliases);
  }
  if (
    ts.isBinaryExpression(node) &&
    [ts.SyntaxKind.AmpersandAmpersandToken, ts.SyntaxKind.BarBarToken].includes(
      node.operatorToken.kind,
    )
  ) {
    return (
      isApprovedMcpNameGuardExpression(node.left, handler, source, request, aliases) &&
      isApprovedMcpNameGuardExpression(node.right, handler, source, request, aliases)
    );
  }
  if (!ts.isCallExpression(node) || !ts.isPropertyAccessExpression(node.expression)) {
    return false;
  }
  const target = node.expression.expression;
  const method = node.expression.name.text;
  if (
    method === "startsWith" &&
    isMcpNameReference(target, source, request, aliases) &&
    node.arguments.length === 1 &&
    ts.isStringLiteralLike(node.arguments[0])
  ) {
    return true;
  }
  return Boolean(
    method === "has" &&
    ts.isIdentifier(target) &&
    isLiteralStaticMcpSet(target.text, handler, source) &&
    node.arguments.length === 1 &&
    isMcpNameReference(node.arguments[0], source, request, aliases),
  );
}

function isApprovedMcpScopeGuardExpression(node) {
  const value = unwrapPureExpression(node);
  if (
    ts.isIdentifier(value) ||
    ts.isStringLiteralLike(value) ||
    [ts.SyntaxKind.TrueKeyword, ts.SyntaxKind.FalseKeyword, ts.SyntaxKind.NullKeyword].includes(
      value.kind,
    )
  ) {
    return true;
  }
  if (ts.isPropertyAccessExpression(value) && !value.questionDotToken) {
    return isApprovedMcpScopeGuardExpression(value.expression);
  }
  if (ts.isPrefixUnaryExpression(value) && value.operator === ts.SyntaxKind.ExclamationToken) {
    return isApprovedMcpScopeGuardExpression(value.operand);
  }
  if (
    ts.isBinaryExpression(value) &&
    [ts.SyntaxKind.AmpersandAmpersandToken, ts.SyntaxKind.BarBarToken].includes(
      value.operatorToken.kind,
    )
  ) {
    return (
      isApprovedMcpScopeGuardExpression(value.left) &&
      isApprovedMcpScopeGuardExpression(value.right)
    );
  }
  return Boolean(
    ts.isCallExpression(value) &&
    ts.isPropertyAccessExpression(value.expression) &&
    value.expression.name.text === "includes" &&
    isApprovedMcpScopeGuardExpression(value.expression.expression) &&
    value.arguments.length === 1 &&
    ts.isStringLiteralLike(value.arguments[0]),
  );
}

function assertSafeMcpGuardBody(statement, source) {
  if (statement.elseStatement) throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
  const statements = ts.isBlock(statement.thenStatement)
    ? [...statement.thenStatement.statements]
    : [statement.thenStatement];
  for (const item of statements) {
    if (ts.isReturnStatement(item) && item.expression && isStaticMcpErrorValue(item.expression)) {
      continue;
    }
    if (
      ts.isExpressionStatement(item) &&
      ts.isCallExpression(item.expression) &&
      ts.isIdentifier(item.expression.expression) &&
      item.expression.expression.text === "logToolAccess" &&
      item.expression.arguments[0]?.kind === ts.SyntaxKind.FalseKeyword &&
      ts.isStringLiteralLike(item.expression.arguments[1])
    ) {
      continue;
    }
    throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
  }
}

function assertSafeMcpNameGuard(statement, handler, source, request, aliases) {
  if (
    statement.elseStatement ||
    containsDirectMcpNameComparison(statement.expression, source, request, aliases) ||
    !isApprovedMcpNameGuardExpression(statement.expression, handler, source, request, aliases)
  ) {
    throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
  }
  assertSafeMcpGuardBody(statement, source);
}

function enclosingNode(node, stop, predicate) {
  let current = node.parent;
  while (current && current !== stop) {
    if (predicate(current)) return current;
    current = current.parent;
  }
  return null;
}

function isIdentifierUse(node) {
  const parent = node.parent;
  if (ts.isPropertyAccessExpression(parent) && parent.name === node) return false;
  if (
    (ts.isPropertyAssignment(parent) || ts.isBindingElement(parent)) &&
    parent.name === node &&
    !ts.isShorthandPropertyAssignment(parent)
  ) {
    return false;
  }
  return true;
}

function isApprovedMcpTelemetryReference(node, handler, source) {
  const declaration = enclosingNode(
    node,
    handler,
    (candidate) =>
      ts.isVariableDeclaration(candidate) &&
      ts.isIdentifier(candidate.name) &&
      candidate.name.text === "logToolAccess",
  );
  if (!declaration) return false;
  const property = enclosingNode(node, declaration, (candidate) =>
    ts.isPropertyAssignment(candidate),
  );
  if (property && propertyName(property.name, source) === "tool") return true;
  const template = enclosingNode(node, declaration, (candidate) => ts.isTemplateSpan(candidate));
  if (!template) return false;
  const call = enclosingNode(template, declaration, (candidate) => ts.isCallExpression(candidate));
  return Boolean(
    call && ts.isPropertyAccessExpression(call.expression) && call.expression.name.text === "warn",
  );
}

function assertMcpNameOwnership(handler, dispatchSwitch, source, request, aliases) {
  const visit = (node) => {
    if (node === dispatchSwitch) return;
    if (
      ts.isElementAccessExpression(node) &&
      (node.expression.getText(source) === `${request}.params` ||
        node.expression.getText(source) === request)
    ) {
      throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
    }
    if (ts.isIdentifier(node) && node.text === request) {
      const parent = node.parent;
      const parameterName = ts.isParameter(parent) && parent.name === node;
      const canonicalParams =
        ts.isPropertyAccessExpression(parent) &&
        parent.expression === node &&
        parent.name.text === "params";
      if (!parameterName && !canonicalParams) {
        throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
      }
    }
    const directRequestName = node.getText(source) === `${request}.params.name`;
    const aliasReference = ts.isIdentifier(node) && aliases.has(node.text) && isIdentifierUse(node);
    if (directRequestName || aliasReference) {
      const guard = enclosingNode(
        node,
        handler,
        (candidate) =>
          ts.isIfStatement(candidate) &&
          candidate.expression.pos <= node.pos &&
          candidate.expression.end >= node.end,
      );
      if (guard) {
        assertSafeMcpNameGuard(guard, handler, source, request, aliases);
        return;
      }
      if (isApprovedMcpTelemetryReference(node, handler, source)) return;
      throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
    }
    ts.forEachChild(node, visit);
  };
  visit(handler);
}

function assertSafeMcpDefault(clause, source) {
  const visit = (node) => {
    if (
      ts.isElementAccessExpression(node) ||
      ts.isAwaitExpression(node) ||
      ts.isTaggedTemplateExpression(node) ||
      (ts.isPrefixUnaryExpression(node) && node.operator === ts.SyntaxKind.DeleteKeyword) ||
      ts.isPostfixUnaryExpression(node)
    ) {
      throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
    }
    if (ts.isCallExpression(node)) {
      const approvedAudit =
        ts.isIdentifier(node.expression) &&
        node.expression.text === "logToolAccess" &&
        node.arguments[0]?.kind === ts.SyntaxKind.FalseKeyword &&
        ts.isStringLiteralLike(node.arguments[1]);
      if (!approvedAudit) throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
    }
    if (
      ts.isNewExpression(node) &&
      (!ts.isIdentifier(node.expression) || node.expression.text !== "Error")
    ) {
      throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
    }
    if (
      ts.isBinaryExpression(node) &&
      (node.operatorToken.kind === ts.SyntaxKind.CommaToken ||
        (node.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
          node.operatorToken.kind <= ts.SyntaxKind.LastAssignment))
    ) {
      throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
    }
    ts.forEachChild(node, visit);
  };
  visit(clause);
}

function dispatchCasesFromCallHandler(call, source) {
  const handler = call.arguments[1];
  if (!handler || !ts.isFunctionLike(handler)) {
    throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
  }
  const { request, aliases } = requestNameAliases(handler, source);
  if (!request) throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
  const candidates = directHandlerSwitches(handler).filter((statement) => {
    const expression = statement.expression.getText(source);
    return expression === `${request}.params.name` || aliases.has(expression);
  });
  if (candidates.length !== 1) throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
  const dispatchSwitch = candidates[0];
  if (!handler.body || !ts.isBlock(handler.body)) {
    throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
  }
  let dispatchContainer = dispatchSwitch;
  while (dispatchContainer.parent && dispatchContainer.parent !== handler.body) {
    dispatchContainer = dispatchContainer.parent;
  }
  if (
    dispatchContainer.parent !== handler.body ||
    handler.body.statements.at(-1) !== dispatchContainer ||
    (!ts.isSwitchStatement(dispatchContainer) && !ts.isTryStatement(dispatchContainer))
  ) {
    throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
  }
  for (const statement of handler.body.statements.slice(0, -1)) {
    if (
      ts.isVariableStatement(statement) ||
      ts.isFunctionDeclaration(statement) ||
      ts.isTypeAliasDeclaration(statement) ||
      ts.isInterfaceDeclaration(statement) ||
      ts.isEmptyStatement(statement)
    ) {
      continue;
    }
    if (
      ts.isIfStatement(statement) &&
      isApprovedMcpNameGuardExpression(statement.expression, handler, source, request, aliases)
    ) {
      assertSafeMcpGuardBody(statement, source);
      continue;
    }
    throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
  }
  const rejectParamsAlias = (node) => {
    if (
      ts.isVariableDeclaration(node) &&
      ts.isIdentifier(node.name) &&
      node.initializer &&
      unwrapPureExpression(node.initializer).getText(source) === `${request}.params`
    ) {
      throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
    }
    if (
      ts.isBinaryExpression(node) &&
      node.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
      unwrapPureExpression(node.right).getText(source) === `${request}.params`
    ) {
      throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
    }
    ts.forEachChild(node, rejectParamsAlias);
  };
  rejectParamsAlias(handler.body);
  let parent = dispatchSwitch.parent;
  while (parent && parent !== handler) {
    if (
      ts.isIfStatement(parent) ||
      ts.isConditionalExpression(parent) ||
      ts.isWhileStatement(parent) ||
      ts.isDoStatement(parent) ||
      ts.isForStatement(parent) ||
      ts.isForInStatement(parent) ||
      ts.isForOfStatement(parent)
    ) {
      throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
    }
    parent = parent.parent;
  }
  assertMcpNameOwnership(handler, dispatchSwitch, source, request, aliases);
  const names = [];
  for (const clause of dispatchSwitch.caseBlock.clauses) {
    if (ts.isDefaultClause(clause)) {
      assertSafeMcpDefault(clause, source);
      continue;
    }
    if (!ts.isStringLiteralLike(clause.expression)) {
      throw new Error(`OPAQUE_MCP_DISPATCH ${source.fileName}`);
    }
    names.push(clause.expression.text);
  }
  return names;
}

function assertMcpDispatchParity(file, listed, dispatched) {
  const expected = [...listed].sort(compare);
  const actual = [...dispatched].sort(compare);
  if (stable(expected) !== stable(actual)) {
    throw new Error(`MCP_TOOL_DISPATCH_MISMATCH ${file}`);
  }
}

function discoverMcpTools(input) {
  if (!/(?:\/modules\/mcp\/|^packages\/mcp-server\/)/u.test(input.file)) return [];
  const source = parseSource(input.file, input.text);
  const symbols = importedSymbols(source);
  const found = [];
  const listed = [];
  const dispatched = [];
  let listHandlers = 0;
  let callHandlers = 0;
  const visit = (node) => {
    if (ts.isCallExpression(node)) {
      if (
        ts.isPropertyAccessExpression(node.expression) &&
        node.expression.name.text === "setRequestHandler"
      ) {
        const schema = importedSchemaName(node.arguments[0], symbols);
        if (schema === "ListToolsRequestSchema") {
          listHandlers += 1;
          const tools = literalToolsFromArray(
            input,
            source,
            toolsArrayFromListHandler(node, source),
          );
          found.push(...tools);
          listed.push(...tools.map((tool) => tool.handler));
        } else if (schema === "CallToolRequestSchema") {
          callHandlers += 1;
          dispatched.push(...dispatchCasesFromCallHandler(node, source));
        } else if (!schema) {
          throw new Error(`OPAQUE_MCP_REGISTRATION ${input.file}`);
        }
      } else if (
        ts.isPropertyAccessExpression(node.expression) &&
        node.expression.name.text === "registerTool"
      ) {
        const name = node.arguments[0];
        if (!name || !ts.isStringLiteralLike(name)) {
          throw new Error(`OPAQUE_MCP_REGISTRATION ${input.file}`);
        }
        found.push(toolSurface(input, source, name.text, node));
      }
    }
    ts.forEachChild(node, visit);
  };
  visit(source);
  if (listHandlers > 0 || callHandlers > 0) {
    if (listHandlers !== 1 || callHandlers !== 1) {
      throw new Error(`MCP_TOOL_DISPATCH_MISMATCH ${input.file}`);
    }
    assertMcpDispatchParity(input.file, listed, dispatched);
  }
  return found;
}

function hasExportModifier(node) {
  return node.modifiers?.some((modifier) => modifier.kind === ts.SyntaxKind.ExportKeyword) ?? false;
}

function workerExportNames(statement, source) {
  if (ts.isFunctionDeclaration(statement) || ts.isClassDeclaration(statement)) {
    if (!hasExportModifier(statement)) return [];
    const isDefault =
      statement.modifiers?.some((modifier) => modifier.kind === ts.SyntaxKind.DefaultKeyword) ??
      false;
    return [isDefault ? "default" : (statement.name?.text ?? "anonymous")];
  }
  if (ts.isVariableStatement(statement) && hasExportModifier(statement)) {
    return statement.declarationList.declarations.flatMap((declaration) =>
      ts.isIdentifier(declaration.name) ? [declaration.name.text] : [],
    );
  }
  if (ts.isExportDeclaration(statement)) {
    if (!statement.exportClause || !ts.isNamedExports(statement.exportClause)) {
      throw new Error(`OPAQUE_WORKER_EXPORT ${source.fileName}`);
    }
    return statement.exportClause.elements
      .filter((element) => !element.isTypeOnly)
      .map((element) => element.name.text);
  }
  if (ts.isExportAssignment(statement)) {
    if (!ts.isObjectLiteralExpression(statement.expression)) return ["default"];
    return statement.expression.properties.map((property) => {
      const name = propertyName(property.name, source);
      if (!name) throw new Error(`OPAQUE_WORKER_EXPORT ${source.fileName}`);
      return `default.${name}`;
    });
  }
  return [];
}

function discoverWorkerEntrypoints(input) {
  const source = parseSource(input.file, input.text);
  const found = [];
  for (const statement of source.statements) {
    if (
      (ts.isFunctionDeclaration(statement) || ts.isClassDeclaration(statement)) &&
      hasExportModifier(statement) &&
      statement.modifiers?.some((modifier) => modifier.kind === ts.SyntaxKind.DefaultKeyword)
    ) {
      throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${input.file}`);
    }
    for (const name of workerExportNames(statement, source)) {
      const handlerLine = sourceLocation(source, statement).line;
      found.push({
        id: `worker-export:${input.file}#${name}`,
        kind: "worker-export",
        tags: ["worker"],
        file: input.file,
        handler: name,
        handlerFile: input.file,
        handlerLine,
      });
    }
  }
  for (const handler of defaultFetchHandlers(source)) {
    const id = `worker-export:${input.file}#default.fetch`;
    if (found.some((surface) => surface.id === id)) continue;
    found.push({
      id,
      kind: "worker-export",
      tags: ["worker"],
      file: input.file,
      handler: "default.fetch",
      handlerFile: input.file,
      handlerLine: sourceLocation(source, handler).line,
    });
  }
  const visit = (node) => {
    if (
      ts.isCallExpression(node) &&
      ts.isIdentifier(node.expression) &&
      node.expression.text === "addEventListener" &&
      ts.isStringLiteralLike(node.arguments[0])
    ) {
      const event = node.arguments[0].text;
      if (event === "fetch") {
        throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${input.file}`);
      }
      const handlerLine = sourceLocation(source, node).line;
      found.push({
        id: `worker-registration:${input.file}#${event}@${handlerLine}`,
        kind: "worker-registration",
        tags: ["worker"],
        file: input.file,
        handler: event,
        handlerFile: input.file,
        handlerLine,
      });
    }
    ts.forEachChild(node, visit);
  };
  visit(source);
  return found;
}

function defaultFetchHandlers(source) {
  const handlers = [];
  const objectBindings = new Map();
  const allBindings = new Map();
  for (const statement of source.statements) {
    if (!ts.isVariableStatement(statement)) continue;
    for (const declaration of statement.declarationList.declarations) {
      if (ts.isIdentifier(declaration.name) && declaration.initializer) {
        allBindings.set(declaration.name.text, declaration.initializer);
      }
      if (
        ts.isIdentifier(declaration.name) &&
        declaration.initializer &&
        ts.isObjectLiteralExpression(declaration.initializer)
      ) {
        objectBindings.set(declaration.name.text, declaration.initializer);
      }
    }
  }
  const containsFetchDefinition = (expression, seen = new Set()) => {
    const value = unwrapPureExpression(expression);
    if (ts.isObjectLiteralExpression(value)) {
      return value.properties.some((property) => propertyName(property.name, source) === "fetch");
    }
    if (ts.isIdentifier(value)) {
      if (seen.has(value.text)) return false;
      seen.add(value.text);
      const initializer = allBindings.get(value.text);
      return Boolean(initializer && containsFetchDefinition(initializer, seen));
    }
    if (ts.isCallExpression(value) || ts.isNewExpression(value)) {
      return Boolean(value.arguments?.some((argument) => containsFetchDefinition(argument, seen)));
    }
    return false;
  };
  const assertInspectableExport = (object, bindingName) => {
    for (const property of object.properties) {
      if (
        ts.isSpreadAssignment(property) ||
        !propertyName(property.name, source) ||
        (!ts.isMethodDeclaration(property) && !ts.isPropertyAssignment(property))
      ) {
        throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
      }
    }
    if (!bindingName) return;
    const visit = (node) => {
      if (ts.isBinaryExpression(node)) {
        const target = unwrapPureExpression(node.left);
        const mutatesBinding =
          (ts.isIdentifier(target) && target.text === bindingName) ||
          ((ts.isPropertyAccessExpression(target) || ts.isElementAccessExpression(target)) &&
            target.expression.getText(source) === bindingName);
        if (mutatesBinding) {
          throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
        }
      }
      if (
        ts.isCallExpression(node) &&
        node.expression.getText(source) === "Object.assign" &&
        node.arguments[0]?.getText(source) === bindingName
      ) {
        throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
      }
      ts.forEachChild(node, visit);
    };
    visit(source);
  };
  for (const statement of source.statements) {
    if (!ts.isExportAssignment(statement)) continue;
    const bindingName = ts.isIdentifier(statement.expression) ? statement.expression.text : null;
    const exported = ts.isObjectLiteralExpression(statement.expression)
      ? statement.expression
      : ts.isIdentifier(statement.expression)
        ? objectBindings.get(statement.expression.text)
        : null;
    if (!exported) {
      // A factory/class/proxy may manufacture fetch without leaving any AST path
      // for the registry to classify. Runtime worker defaults therefore use only
      // a directly inspectable object literal (inline or one local binding).
      // Non-runtime *.config.* files are excluded by isWorkerSource below.
      void containsFetchDefinition(statement.expression);
      throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
    }
    assertInspectableExport(exported, bindingName);
    for (const property of exported.properties) {
      if (propertyName(property.name, source) !== "fetch") continue;
      if (ts.isMethodDeclaration(property)) handlers.push(property);
      else if (
        ts.isPropertyAssignment(property) &&
        (ts.isArrowFunction(property.initializer) || ts.isFunctionExpression(property.initializer))
      ) {
        handlers.push(property.initializer);
      } else {
        throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
      }
    }
  }
  return handlers;
}

function requestRoutingNames(handler, source) {
  const requestParameter = handler.parameters[0]?.name;
  if (!requestParameter || !ts.isIdentifier(requestParameter)) {
    throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
  }
  const urls = new Set();
  const normalizedPaths = new Set();
  const visit = (node) => {
    if (
      ts.isVariableDeclaration(node) &&
      ts.isIdentifier(node.name) &&
      node.initializer &&
      ts.isNewExpression(node.initializer) &&
      node.initializer.expression.getText(source) === "URL" &&
      node.initializer.arguments?.[0]?.getText(source) === `${requestParameter.text}.url`
    ) {
      urls.add(node.name.text);
    }
    if (
      ts.isVariableDeclaration(node) &&
      ts.isIdentifier(node.name) &&
      node.initializer &&
      isCanonicalWorkerPathNormalization(node.initializer, source, {
        request: requestParameter.text,
        urls,
      })
    ) {
      normalizedPaths.add(node.name.text);
    }
    ts.forEachChild(node, visit);
  };
  visit(handler.body);
  return { request: requestParameter.text, urls, normalizedPaths };
}

function isCanonicalWorkerPathNormalization(node, source, names) {
  const value = unwrapPureExpression(node);
  if (
    !ts.isCallExpression(value) ||
    !ts.isIdentifier(value.expression) ||
    value.expression.text !== "decodeURIComponent" ||
    value.arguments.length !== 1
  ) {
    return false;
  }
  const replaceCall = value.arguments[0];
  if (
    !ts.isCallExpression(replaceCall) ||
    !ts.isPropertyAccessExpression(replaceCall.expression) ||
    replaceCall.expression.name.text !== "replace" ||
    replaceCall.arguments.length !== 2 ||
    !ts.isRegularExpressionLiteral(replaceCall.arguments[0]) ||
    replaceCall.arguments[0].getText(source) !== "/^\\/+/" ||
    !ts.isStringLiteralLike(replaceCall.arguments[1]) ||
    replaceCall.arguments[1].text !== ""
  ) {
    return false;
  }
  return routeReference(replaceCall.expression.expression, source, names) === "path";
}

function isCanonicalWorkerPathNormalizationReference(node, source, names) {
  const replaceAccess = node.parent;
  const replaceCall = replaceAccess?.parent;
  const decodeCall = replaceCall?.parent;
  return Boolean(
    ts.isPropertyAccessExpression(replaceAccess) &&
    replaceAccess.expression === node &&
    ts.isCallExpression(replaceCall) &&
    replaceCall.expression === replaceAccess &&
    ts.isCallExpression(decodeCall) &&
    isCanonicalWorkerPathNormalization(decodeCall, source, names),
  );
}

function routeReference(node, source, names) {
  if (!ts.isPropertyAccessExpression(node)) return null;
  const owner = node.expression.getText(source);
  const directUrl =
    ts.isNewExpression(node.expression) &&
    node.expression.expression.getText(source) === "URL" &&
    node.expression.arguments?.[0]?.getText(source) === `${names.request}.url`;
  if (node.name.text === "pathname" && (names.urls.has(owner) || directUrl)) return "path";
  if (node.name.text === "method" && owner === names.request) return "method";
  return null;
}

function opaqueRouteReference(node, source, names) {
  if (!ts.isElementAccessExpression(node)) return false;
  const owner = node.expression.getText(source);
  const field = node.argumentExpression;
  if (!field || !ts.isStringLiteralLike(field)) return false;
  if (field.text === "method" && owner === names.request) return true;
  if (field.text === "url" && owner === names.request) return true;
  if (field.text !== "pathname") return false;
  if (names.urls.has(owner)) return true;
  return Boolean(
    ts.isNewExpression(node.expression) &&
    node.expression.expression.getText(source) === "URL" &&
    node.expression.arguments?.[0]?.getText(source) === `${names.request}.url`,
  );
}

function containsRouteReference(node, source, names) {
  let found = false;
  const visit = (candidate) => {
    if (conditionRouteReference(candidate, source, names)) found = true;
    if (!found) ts.forEachChild(candidate, visit);
  };
  visit(node);
  return found;
}

function conditionRouteReference(node, source, names) {
  const direct = routeReference(node, source, names);
  if (direct) return direct;
  return ts.isIdentifier(node) && names.normalizedPaths.has(node.text) ? "path" : null;
}

function normalizedWorkerCondition(node, source, names) {
  if (ts.isParenthesizedExpression(node)) {
    return `(${normalizedWorkerCondition(node.expression, source, names)})`;
  }
  if (
    ts.isBinaryExpression(node) &&
    [ts.SyntaxKind.AmpersandAmpersandToken, ts.SyntaxKind.BarBarToken].includes(
      node.operatorToken.kind,
    )
  ) {
    const left = normalizedWorkerCondition(node.left, source, names);
    const right = normalizedWorkerCondition(node.right, source, names);
    return `(${left}${node.operatorToken.getText(source)}${right})`;
  }
  if (ts.isBinaryExpression(node)) {
    const operators = new Map([
      [ts.SyntaxKind.EqualsEqualsEqualsToken, "==="],
      [ts.SyntaxKind.ExclamationEqualsEqualsToken, "!=="],
      [ts.SyntaxKind.EqualsEqualsToken, "=="],
      [ts.SyntaxKind.ExclamationEqualsToken, "!="],
    ]);
    const operator = operators.get(node.operatorToken.kind);
    const left = conditionRouteReference(node.left, source, names);
    const right = conditionRouteReference(node.right, source, names);
    const literal = left ? node.right : node.left;
    if (operator && Boolean(left) !== Boolean(right) && ts.isStringLiteralLike(literal)) {
      return `${left ?? right}${operator}${JSON.stringify(literal.text)}`;
    }
  }
  if (containsRouteReference(node, source, names)) {
    throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
  }
  return node.getText(source).replace(/\s+/gu, "");
}

function discoverWorkerRequestBranches(input) {
  const source = parseSource(input.file, input.text);
  const found = [];
  for (const handler of defaultFetchHandlers(source)) {
    const names = requestRoutingNames(handler, source);
    const addBranch = (node, condition, prefix = "") => {
      const handlerLine = sourceLocation(source, node).line;
      found.push({
        id: `worker-request-branch:${input.file}#default.fetch:${prefix}${condition}`,
        kind: "worker-request-branch",
        tags: ["worker"],
        file: input.file,
        handler: "default.fetch",
        handlerFile: input.file,
        handlerLine,
        route: condition,
      });
    };
    if (names.normalizedPaths.size > 0) {
      addBranch(
        handler,
        `normalized-path-handler:${digest(handler.body.getText(source))}`,
        "content:",
      );
    }
    const visit = (node) => {
      if (opaqueRouteReference(node, source, names)) {
        throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
      }
      if (
        routeReference(node, source, names) &&
        !isCanonicalWorkerPathNormalizationReference(node, source, names)
      ) {
        throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
      }
      if (
        ts.isPropertyAccessExpression(node) &&
        node.expression.getText(source) === names.request &&
        node.name.text === "url"
      ) {
        const parent = node.parent;
        const canonicalUrl =
          ts.isNewExpression(parent) &&
          parent.expression.getText(source) === "URL" &&
          parent.arguments?.length === 1 &&
          parent.arguments[0] === node;
        if (!canonicalUrl) {
          throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
        }
      }
      if (
        ts.isCallExpression(node) &&
        node.arguments.some(
          (argument) => ts.isIdentifier(argument) && argument.text === names.request,
        )
      ) {
        throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
      }
      if (ts.isVariableDeclaration(node)) {
        if (node.initializer && routeReference(node.initializer, source, names)) {
          throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
        }
        if (
          ts.isIdentifier(node.name) &&
          node.initializer?.getText(source) === `${names.request}.url`
        ) {
          throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
        }
        if (ts.isIdentifier(node.name) && node.initializer?.getText(source) === names.request) {
          throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
        }
        if (
          ts.isObjectBindingPattern(node.name) &&
          ts.isIdentifier(node.initializer) &&
          (names.urls.has(node.initializer.text) || node.initializer.text === names.request) &&
          node.name.elements.some((element) =>
            ["pathname", "method", "url"].includes(
              (element.propertyName ?? element.name).getText(source),
            ),
          )
        ) {
          throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
        }
      }
      if (
        ts.isBinaryExpression(node) &&
        node.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
        routeReference(node.right, source, names)
      ) {
        throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
      }
      if (
        (ts.isSwitchStatement(node) && containsRouteReference(node.expression, source, names)) ||
        ((ts.isWhileStatement(node) || ts.isDoStatement(node)) &&
          containsRouteReference(node.expression, source, names)) ||
        (ts.isForStatement(node) &&
          node.condition &&
          containsRouteReference(node.condition, source, names)) ||
        ((ts.isForInStatement(node) || ts.isForOfStatement(node)) &&
          containsRouteReference(node.expression, source, names))
      ) {
        throw new Error(`OPAQUE_WORKER_REQUEST_ROUTING ${source.fileName}`);
      }
      if (
        ts.isConditionalExpression(node) &&
        containsRouteReference(node.condition, source, names)
      ) {
        addBranch(node, normalizedWorkerCondition(node.condition, source, names), "ternary:");
        visit(node.whenTrue);
        visit(node.whenFalse);
        return;
      }
      if (ts.isIfStatement(node) && containsRouteReference(node.expression, source, names)) {
        const condition = normalizedWorkerCondition(node.expression, source, names);
        addBranch(node, condition);
        visit(node.thenStatement);
        if (node.elseStatement) visit(node.elseStatement);
        return;
      }
      ts.forEachChild(node, visit);
    };
    visit(handler.body);
  }
  return found;
}

function pythonLine(text, offset) {
  return text.slice(0, offset).split("\n").length;
}

function discoverPythonWorkerEntrypoints(input) {
  const found = [
    {
      id: `python-worker-source:${input.file}`,
      kind: "python-worker-source",
      tags: ["worker"],
      file: input.file,
    },
  ];
  const definitions = new Map();
  const definition = /^(?:async[ \t]+)?def[ \t]+([A-Za-z_]\w*)[ \t]*\(/gmu;
  for (const match of input.text.matchAll(definition)) {
    definitions.set(match[1], match.index);
    found.push({
      id: `python-worker-definition:${input.file}#${match[1]}`,
      kind: "python-worker-definition",
      tags: ["worker"],
      file: input.file,
      handler: match[1],
      handlerFile: input.file,
      handlerLine: pythonLine(input.text, match.index),
    });
  }
  const registration =
    /^[ \t]*runpod\.serverless\.start\(\s*\{\s*(["'])handler\1\s*:\s*([A-Za-z_]\w*)\s*,?\s*\}\s*\)\s*$/gmu;
  const exactOffsets = new Set();
  for (const match of input.text.matchAll(registration)) {
    if (!definitions.has(match[2])) {
      throw new Error(`OPAQUE_PYTHON_WORKER_REGISTRATION ${input.file}`);
    }
    exactOffsets.add(match.index);
    const handlerLine = pythonLine(input.text, match.index);
    found.push({
      id: `python-worker-entrypoint:${input.file}#runpod:${match[2]}`,
      kind: "python-worker-entrypoint",
      tags: ["worker"],
      file: input.file,
      handler: match[2],
      handlerFile: input.file,
      handlerLine,
    });
  }
  const lines = input.text.split("\n");
  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    if (/^[ \t]*#/u.test(line)) continue;
    const lineOffset = lines.slice(0, index).join("\n").length + (index > 0 ? 1 : 0);
    if (exactOffsets.has(lineOffset)) continue;
    if (/^[ \t]*(?:from[ \t]+runpod\b|import[ \t]+runpod[ \t]+as\b)/u.test(line)) {
      throw new Error(`OPAQUE_PYTHON_WORKER_REGISTRATION ${input.file}`);
    }
    if (
      /\bexec[ \t]*\(/u.test(line) ||
      /\bgetattr[ \t]*\([^\n]*(?:runpod|serverless)/u.test(line) ||
      /(?:runpod|serverless)[^\n]*__dict__/u.test(line) ||
      /\bserverless[ \t]*\.[ \t]*start[ \t]*\(/u.test(line)
    ) {
      throw new Error(`OPAQUE_PYTHON_WORKER_REGISTRATION ${input.file}`);
    }
    if (/^[ \t]*[A-Za-z_]\w*[ \t]*=[ \t]*runpod\.serverless\.start[ \t]*$/u.test(line)) {
      throw new Error(`OPAQUE_PYTHON_WORKER_REGISTRATION ${input.file}`);
    }
    if (line.includes("runpod.serverless.start(")) {
      throw new Error(`OPAQUE_PYTHON_WORKER_REGISTRATION ${input.file}`);
    }
    if (/^[ \t]*if\s+__name__\s*==\s*(["'])__main__\1\s*:\s*$/u.test(line)) {
      found.push({
        id: `python-worker-entrypoint:${input.file}#__main__`,
        kind: "python-worker-entrypoint",
        tags: ["worker"],
        file: input.file,
        handler: "__main__",
        handlerFile: input.file,
        handlerLine: index + 1,
      });
    }
  }
  return found;
}

function isWorkerSource(file) {
  if (/(?:^|\/)[^/]+\.config\.[cm]?[jt]sx?$/u.test(file)) return false;
  return (
    file.startsWith("workers/") ||
    /\.(?:worker|processor|scheduler|poller|gateway)\.[cm]?[jt]sx?$/u.test(file)
  );
}

const isPythonSource = (file) => file.endsWith(".py");

function nextRoutePath(file) {
  const match = /(?:^|\/)app\/(.+)\/route\.[cm]?[jt]sx?$/u.exec(file);
  if (!match) return null;
  return `/${match[1]}`
    .replace(/\/\[\[\.\.\.([^\]]+)\]\]/gu, "/:$1*")
    .replace(/\/\[\.\.\.([^\]]+)\]/gu, "/:$1+")
    .replace(/\/\[([^\]]+)\]/gu, "/:$1");
}

function reportSemantics(surface, inputText, fixedRecords) {
  if (surface.kind === "next-route") {
    const path = surface.route ?? nextRoutePath(surface.file) ?? "";
    const dynamicPath = /(?:^|\/):[^/]+/u.test(path);
    const reportPath = /(?:^|\/)reports?(?:\/|$)/iu.test(path);
    const analyticsPath = /(?:^|\/)analytics?(?:\/|$)/iu.test(path);
    const reportSignal =
      /\breport(?:Id|_id)?\b|\/api\/reports?(?:\/|['"`])/iu.test(inputText) ||
      /\b(?:load|get|resolve|dispatch|find)\w*(?:Report|Artifact|Config|Definition)\w*\s*\(/u.test(
        inputText,
      );
    const reportLike = reportPath || (dynamicPath && (analyticsPath || reportSignal));
    return {
      reportLike,
      dynamic: reportLike && dynamicPath,
    };
  }
  if (surface.kind !== "nest-http" && surface.kind !== "nest-sse") {
    return { reportLike: false, dynamic: false };
  }
  const surfaceName =
    `${surface.file} ${surface.path ?? ""} ${surface.controller ?? ""} ${surface.handler ?? ""}`.toLowerCase();
  const reportNamedSurface = /(?:^|[\s/_-])reports?(?:$|[\s/_-])/u.test(surfaceName);
  const analyticsNamedSurface = /(?:^|\/)analytics?(?:$|\/)/u.test(
    (surface.path ?? "").toLowerCase(),
  );
  const dynamicRoute = /(?:^|\/):[^/]+/u.test(surface.path ?? "");
  const reportRouteParameter = /(?:^|\/):[^/]*report[^/]*/iu.test(surface.path ?? "");
  const routeParameters = new Set(
    [...(surface.path ?? "").matchAll(/(?:^|\/):([A-Za-z_]\w*)/gu)].map((match) => match[1]),
  );
  const source = parseSource(surface.handlerFile ?? surface.file, inputText);
  let handler;
  try {
    handler = handlerNode(source, surface);
  } catch {
    return { reportLike: reportRouteParameter, dynamic: reportRouteParameter };
  }
  const symbols = importedSymbols(source);
  let reportParameter = false;
  for (const parameter of handler.parameters ?? []) {
    const name = parameter.name.getText(source);
    const parameterDecorators = decorators(parameter, source, symbols);
    const nestInput = parameterDecorators.find(
      (decorator) =>
        decorator.module === "@nestjs/common" &&
        ["Param", "Query", "Body"].includes(decorator.name),
    );
    const paramArgument = nestInput?.args[0];
    if (
      /report/iu.test(name) ||
      (paramArgument &&
        ts.isStringLiteralLike(paramArgument) &&
        /report/iu.test(paramArgument.text))
    ) {
      reportParameter = true;
    }
  }
  let reportSource = false;
  let ambiguousDynamicLoader = false;
  const visit = (node) => {
    if (
      (ts.isIdentifier(node) && /^(?:report|reportId|report_id)$/iu.test(node.text)) ||
      (ts.isPropertyAccessExpression(node) && /report/iu.test(node.name.text))
    ) {
      reportSource = true;
    }
    if (ts.isCallExpression(node)) {
      const callee = node.expression.getText(source);
      const suspiciousLoader =
        /report/iu.test(callee) ||
        /(?:load|resolve|dispatch).*?(?:artifact|config|definition)/iu.test(callee);
      const consumesRouteParameter = node.arguments.some((argument) => {
        let consumes = false;
        const inspect = (candidate) => {
          if (ts.isIdentifier(candidate) && routeParameters.has(candidate.text)) consumes = true;
          if (!consumes) ts.forEachChild(candidate, inspect);
        };
        inspect(argument);
        return consumes;
      });
      if (suspiciousLoader && consumesRouteParameter) ambiguousDynamicLoader = true;
    }
    ts.forEachChild(node, visit);
  };
  visit(handler);
  const dynamic =
    reportRouteParameter ||
    reportParameter ||
    (dynamicRoute &&
      (reportNamedSurface || analyticsNamedSurface || reportSource || ambiguousDynamicLoader));
  const fixedRecordProof =
    dynamic && !reportRouteParameter && !reportParameter ? fixedRecords?.route(surface) : null;
  return {
    reportLike: reportNamedSurface || dynamic || reportSource,
    dynamic: dynamic && !fixedRecordProof,
    ...(fixedRecordProof ? { fixedRecordReportProofs: [fixedRecordProof] } : {}),
  };
}

function tagsForSurface(surface, inputText, semanticReport) {
  const haystack =
    `${surface.file} ${surface.route ?? ""} ${surface.path ?? ""} ${surface.handler ?? ""}`.toLowerCase();
  const tags = new Set();
  if (surface.kind === "nest-http" || surface.kind === "nest-sse") tags.add("api");
  if (["next-route", "next-server-action", "next-inline-server-action"].includes(surface.kind)) {
    tags.add("proxy");
  }
  if (surface.kind === "background-entrypoint") tags.add("worker");
  if (
    surface.kind === "nest-sse" ||
    surface.kind === "websocket-event" ||
    /(?:^|[\s\/_-])stream(?:$|[\s\/_-])/u.test(haystack) ||
    /text\/event-stream/iu.test(inputText)
  )
    tags.add("stream");
  if (semanticReport.reportLike || /(?:^|[\s\/_-])reports?(?:$|[\s\/_-])/u.test(haystack)) {
    tags.add("report");
  }
  if (
    /(?:^|[\s\/_-])(download|export)(?:$|[\s\/_-])/u.test(haystack) ||
    /content-disposition/iu.test(inputText)
  )
    tags.add("download");
  return [...tags].sort(compare);
}

function normalizedSurface(surface, inputText) {
  const handlerFile = surface.handlerFile ?? (surface.handler ? surface.file : undefined);
  const handlerLine = surface.handlerLine ?? (surface.handler ? surface.line : undefined);
  const route =
    surface.route ?? (surface.kind === "next-route" ? nextRoutePath(surface.file) : null);
  const normalized = route ? { ...surface, route } : surface;
  // Declared route identities retain the historical conservative heuristic.
  // The closed record proof only classifies a fresh source fingerprint; it does
  // not rewrite legacy route history or make a new dynamic route exemptible.
  const semanticReport = reportSemantics(normalized, inputText);
  return Object.freeze({
    id: `declared:${surface.id}`,
    kind: surface.kind,
    tags: Object.freeze(tagsForSurface(normalized, inputText, semanticReport)),
    file: surface.file,
    ...(surface.handler ? { handler: surface.handler } : {}),
    ...(surface.controller ? { controller: surface.controller } : {}),
    ...(handlerFile ? { handlerFile } : {}),
    ...(handlerLine ? { handlerLine } : {}),
    ...(route ? { route } : {}),
    ...(semanticReport.dynamic ? { dynamicReportDispatch: true } : {}),
  });
}

function sourceSentinelFamilies(input, discovered) {
  const families = new Set();
  const kinds = new Set(discovered.map((surface) => surface.kind));
  const mcpSource =
    input.file.startsWith("packages/mcp-server/") ||
    input.file.includes("/modules/mcp/") ||
    /@modelcontextprotocol\/sdk|\b(?:ListTools|CallTool)RequestSchema\b|\.setRequestHandler\b/u.test(
      input.text,
    );
  if (mcpSource) {
    families.add("mcp");
  } else if (
    input.file.startsWith("apps/api/") ||
    /(?:^|\/)[^/]*controller\.[cm]?[jt]sx?$/u.test(input.file) ||
    kinds.has("nest-http") ||
    kinds.has("nest-sse") ||
    (/from\s+["']@nestjs\/common["']/u.test(input.text) && /\bController\b/u.test(input.text))
  ) {
    families.add("nest");
  }
  if (
    input.file.startsWith("apps/web/") ||
    /(?:^|\/)route\.[cm]?[jt]sx?$/u.test(input.file) ||
    kinds.has("next-route") ||
    kinds.has("next-server-action") ||
    kinds.has("next-inline-server-action")
  ) {
    families.add("next");
  }
  if (input.file.startsWith("workers/") || isWorkerSource(input.file)) {
    families.add(isPythonSource(input.file) ? "worker-python" : "worker-js");
  }
  return [...families].sort(compare);
}

function sourceSentinelReportSemantics(input, discovered, fixedRecords) {
  const text = input.text;
  const reportContainer =
    /(?:^|[\/_-])reports?(?:[\/_-]|$)/iu.test(input.file) ||
    /@Controller\s*\(\s*["'][^"']*reports?(?:\/|["'])/iu.test(text);
  const analyticsContainer =
    /(?:^|[\/_-])analytics?(?:[\/_-]|$)/iu.test(input.file) ||
    /@Controller\s*\(\s*["'][^"']*analytics?(?:\/|["'])/iu.test(text);
  const dynamicLiteral = /["'`]\s*:[A-Za-z_]\w*[^"'`]*["'`]/u.test(text);
  const reportSignal =
    /\breport(?:Id|_id)?\b|\/api\/reports?(?:\/|["'`])/iu.test(text) ||
    /\b(?:load|get|resolve|dispatch|find)\w*(?:Report|Artifact|Config|Definition)\w*\s*\(/u.test(
      text,
    );
  const discoveredDynamic = discovered.some((surface) => {
    try {
      return reportSemantics(surface, text, fixedRecords).dynamic;
    } catch {
      return false;
    }
  });
  const fixedRecordReportProofs = !discoveredDynamic && fixedRecords?.source(input, discovered);
  const dynamic =
    discoveredDynamic ||
    (dynamicLiteral &&
      (reportContainer || (analyticsContainer && reportSignal)) &&
      !fixedRecordReportProofs);
  return {
    reportLike: reportContainer || dynamic || reportSignal,
    dynamic,
    ...(fixedRecordReportProofs ? { fixedRecordReportProofs } : {}),
  };
}

function permissionSourceSentinels(input, discovered, fixedRecords) {
  const hash = contentDigest(input.text);
  const report = sourceSentinelReportSemantics(input, discovered, fixedRecords);
  return sourceSentinelFamilies(input, discovered).map((family) => ({
    id: `permission-source-sentinel:${family}:${input.file}#sha256:${hash}`,
    kind: "permission-source-sentinel",
    tags: [
      family === "nest" ? "api" : family === "next" ? "proxy" : family === "mcp" ? "mcp" : "worker",
      ...(report.reportLike ? ["report"] : []),
    ].sort(compare),
    file: input.file,
    handler: family,
    handlerFile: input.file,
    ...(report.dynamic ? { dynamicReportDispatch: true } : {}),
    ...(report.fixedRecordReportProofs
      ? { fixedRecordReportProofs: report.fixedRecordReportProofs }
      : {}),
  }));
}

/**
 * Deterministic source declarations only. This does not claim runtime mount proof or
 * enforcement; the checked ledger forces every new declaration to be bound or exempted.
 */
export function discoverPermissionSurfaces(inputs) {
  const fixedRecords = createFixedRecordReportProof(inputs);
  const textByFile = new Map(inputs.map((input) => [input.file, input.text]));
  const discovery = discoverSurfaces(inputs.filter((input) => !isPythonSource(input.file)));
  if (discovery.issues.length > 0) {
    const first = discovery.issues[0];
    throw new Error(`SOURCE_DISCOVERY_ISSUE ${first.file}:${first.line} ${first.kind}`);
  }
  const surfaces = discovery.surfaces
    .filter((surface) =>
      [
        "nest-http",
        "nest-sse",
        "next-route",
        "next-server-action",
        "next-inline-server-action",
        "background-entrypoint",
        "websocket-event",
      ].includes(surface.kind),
    )
    .map((surface) =>
      normalizedSurface(surface, textByFile.get(surface.handlerFile ?? surface.file) ?? ""),
    );

  for (const load of discoverOpaqueModuleLoads(inputs)) {
    const tag = load.file.startsWith("apps/api/")
      ? "api"
      : load.file.startsWith("apps/web/")
        ? "proxy"
        : load.file.startsWith("packages/mcp-server/")
          ? "mcp"
          : "worker";
    surfaces.push(
      Object.freeze({
        id: `opaque-module-load:${load.file}#${load.loader}@${load.line}:${load.fingerprint}`,
        kind: "opaque-module-load",
        tags: Object.freeze([tag]),
        file: load.file,
        handler: load.loader,
        handlerFile: load.file,
        handlerLine: load.line,
      }),
    );
  }

  for (const input of inputs) {
    const discoveredForFile = discovery.surfaces.filter((surface) => surface.file === input.file);
    surfaces.push(...permissionSourceSentinels(input, discoveredForFile, fixedRecords));
    if (isWorkerSource(input.file)) {
      if (isPythonSource(input.file)) {
        surfaces.push(...discoverPythonWorkerEntrypoints(input));
      } else {
        surfaces.push(
          Object.freeze({
            id: `worker-source:${input.file}`,
            kind: "worker-source",
            tags: Object.freeze(["worker"]),
            file: input.file,
          }),
        );
        surfaces.push(...discoverWorkerEntrypoints(input));
        surfaces.push(...discoverWorkerRequestBranches(input));
      }
    }
    if (!isPythonSource(input.file)) surfaces.push(...discoverMcpTools(input));
  }

  surfaces.sort((a, b) => compare(a.id, b.id));
  const ids = new Set();
  for (const surface of surfaces) {
    if (ids.has(surface.id)) throw new Error(`DUPLICATE_PERMISSION_SURFACE ${surface.id}`);
    ids.add(surface.id);
  }
  return Object.freeze(surfaces);
}

/**
 * `surfaceIdentity()` minus `handlerLine`, for the two places that compare a *stored*
 * identity against a *live* one to decide whether anything security-relevant changed
 * (drift detection, and "does this decision reproduce what's already recorded"). Every
 * classified entry's own file also carries a `permission-source-sentinel` that already
 * fails closed on ANY content change to that file — including a handler's line moving
 * because unrelated code above it grew — so `handlerLine` in these two comparisons only
 * ever catches noise (an ordinary edit elsewhere in the same file), never something the
 * sentinel wouldn't already have caught. `id`/`kind`/`tags`/`route`/`handler` (the fields
 * that actually determine what's being vouched for) are unaffected — a route disappearing,
 * gaining a new tag, or changing its declared route/method still trips this check exactly
 * as before. `handlerLine` itself is untouched in `surfaceIdentity()`/stored entries/the
 * ledger's `surfaceDigest` — it's still recorded and still used (via a live, freshly
 * discovered surface, never the stale ledger value) to disambiguate same-named handlers
 * during BOUND proof verification.
 */
function driftComparableIdentity(surface) {
  const { handlerLine: _handlerLine, ...rest } = surfaceIdentity(surface);
  return {
    ...rest,
    ...(surface.fixedRecordReportProofs
      ? { fixedRecordReportProofs: surface.fixedRecordReportProofs }
      : {}),
  };
}

const SOURCE_SENTINEL_ID = /^permission-source-sentinel:([^:]+):(.+)#sha256:([a-f0-9]{64})$/u;
const WORKER_CONTENT_ID =
  /^(worker-request-branch:.+#default\.fetch:content:normalized-path-handler:)[a-f0-9]{64}$/u;
const SOURCE_TOMBSTONE_ID = /^permission-source-tombstone:([^:]+):(.+)#removed:([a-f0-9]{64})$/u;
const SURFACE_TOMBSTONE_ID = /^permission-surface-tombstone:([a-f0-9]{64})$/u;

export function buildSourceRemovalTombstone(predecessor, { reason, owner, ticket }) {
  const match = SOURCE_SENTINEL_ID.exec(predecessor?.id ?? "");
  if (!match || predecessor.kind !== "permission-source-sentinel") {
    throw new Error("INVALID_SOURCE_TOMBSTONE_PREDECESSOR");
  }
  const [, family, file, hash] = match;
  return {
    id: `permission-source-tombstone:${family}:${file}#removed:${hash}`,
    kind: "permission-source-tombstone",
    tags: [...predecessor.tags],
    file,
    handler: family,
    handlerFile: file,
    disposition: "RETIRED",
    reason,
    owner,
    ticket,
    replaces: predecessor.id,
  };
}

/**
 * Retires a single named surface (route/handler/action) whose *file* is still active —
 * unlike buildSourceRemovalTombstone, which retires an entire content-hash source family.
 * Used when one export is deleted from a file that keeps other live surfaces (e.g. a
 * server action removed from a controller/actions file that still exports others).
 */
export function buildActionRemovalTombstone(predecessor, { reason, owner, ticket }) {
  if (
    !predecessor ||
    typeof predecessor.id !== "string" ||
    replacementFamily(predecessor.id) !== null ||
    SURFACE_TOMBSTONE_ID.test(predecessor.id) ||
    predecessor.kind === "permission-surface-tombstone"
  ) {
    throw new Error("INVALID_SURFACE_TOMBSTONE_PREDECESSOR");
  }
  const hash = createHash("sha256").update(predecessor.id).digest("hex");
  return {
    id: `permission-surface-tombstone:${hash}`,
    kind: "permission-surface-tombstone",
    tags: [...predecessor.tags],
    file: predecessor.file,
    handler: predecessor.handler,
    handlerFile: predecessor.handlerFile ?? predecessor.file,
    disposition: "RETIRED",
    reason,
    owner,
    ticket,
    replaces: predecessor.id,
  };
}

export function decisionFor(surface, decision, legacyBoundaryCommit, allowLegacyBaseline) {
  const identity = surfaceIdentity(surface);
  if (!decision) {
    if (!allowLegacyBaseline) {
      throw new Error(`UNCLASSIFIED_NEW_SURFACE ${surface.tags.join(",")} ${surface.id}`);
    }
    return {
      ...identity,
      disposition: "LEGACY_BASELINE",
      introducedAtOrBefore: legacyBoundaryCommit,
      reason:
        "Checked SIG-909 legacy baseline; presence is not evidence of permission enforcement.",
    };
  }
  if (decision.disposition === "BOUND") {
    if (surface.kind === "opaque-module-load") {
      throw new Error(`OPAQUE_MODULE_LOAD_CANNOT_BE_BOUND ${surface.id}`);
    }
    if (surface.kind === "permission-source-sentinel") {
      throw new Error(`SOURCE_SENTINEL_CANNOT_BE_BOUND ${surface.id}`);
    }
    return {
      ...identity,
      disposition: "BOUND",
      resourceKey: decision.resourceKey,
      action: decision.action,
      bindingProof: decision.bindingProof,
      ...(decision.replaces ? { replaces: decision.replaces } : {}),
      ...(decision.codeDefinedReportId
        ? { codeDefinedReportId: decision.codeDefinedReportId }
        : {}),
    };
  }
  if (decision.disposition === "EXEMPT") {
    if (surface.kind === "opaque-module-load") {
      throw new Error(`OPAQUE_PRODUCTION_MODULE_LOAD ${surface.id}`);
    }
    if (surface.dynamicReportDispatch) {
      throw new Error(`DYNAMIC_REPORT_REQUIRES_BINDING ${surface.id}`);
    }
    return {
      ...identity,
      disposition: "EXEMPT",
      ...(surface.fixedRecordReportProofs
        ? { fixedRecordReportProofs: surface.fixedRecordReportProofs }
        : {}),
      reason: decision.reason,
      owner: decision.owner,
      ticket: decision.ticket,
      ...(decision.replaces ? { replaces: decision.replaces } : {}),
    };
  }
  throw new Error(`INVALID_SURFACE_DISPOSITION ${surface.id}`);
}

export function buildSurfaceLedger(
  surfaces,
  {
    legacyBoundaryCommit,
    decisions = new Map(),
    allowLegacyBaseline = false,
    retainedEntries = [],
  },
) {
  if (!/^[a-f0-9]{40}$/u.test(legacyBoundaryCommit))
    throw new Error("INVALID_LEGACY_BOUNDARY_COMMIT");
  const entries = [
    ...surfaces.map((surface) =>
      decisionFor(surface, decisions.get(surface.id), legacyBoundaryCommit, allowLegacyBaseline),
    ),
    ...retainedEntries.map((entry) => structuredClone(entry)),
  ].sort((left, right) => compare(left.id, right.id));
  if (new Set(entries.map((entry) => entry.id)).size !== entries.length) {
    throw new Error("DUPLICATE_SURFACE_LEDGER_ENTRY");
  }
  return buildLedgerFromEntries(entries, legacyBoundaryCommit);
}

/**
 * One-time migration helper. Only surfaces that exist in the immutable boundary tree
 * become legacy; current-tree deltas always need an explicit reviewed decision.
 */
export function buildBootstrapLedger(
  boundarySurfaces,
  currentSurfaces,
  { legacyBoundaryCommit, decisions = new Map() },
) {
  if (!/^[a-f0-9]{40}$/u.test(legacyBoundaryCommit)) {
    throw new Error("INVALID_LEGACY_BOUNDARY_COMMIT");
  }
  const boundary = buildSurfaceLedger(boundarySurfaces, {
    legacyBoundaryCommit,
    allowLegacyBaseline: true,
  });
  const boundaryById = new Map(boundary.entries.map((entry) => [entry.id, entry]));
  const currentById = new Map(currentSurfaces.map((surface) => [surface.id, surface]));
  const currentByFamily = new Map();
  const usedDecisions = new Set();
  const retirementsByFile = new Map();
  for (const surface of currentSurfaces) {
    const family = replacementFamily(surface.id);
    if (!family) continue;
    const familySurfaces = currentByFamily.get(family) ?? [];
    familySurfaces.push(surface);
    currentByFamily.set(family, familySurfaces);
  }
  for (const legacy of boundary.entries) {
    const retirement = decisions.get(legacy.id);
    if (
      currentById.has(legacy.id) ||
      legacy.kind !== "permission-source-sentinel" ||
      retirement?.disposition !== "RETIRED"
    ) {
      continue;
    }
    usedDecisions.add(legacy.id);
    const tombstone = buildSourceRemovalTombstone(legacy, retirement);
    const fileRetirements = retirementsByFile.get(legacy.file) ?? [];
    fileRetirements.push({ predecessor: legacy, tombstone });
    retirementsByFile.set(legacy.file, fileRetirements);
  }

  const entries = [];
  for (const surface of currentSurfaces) {
    const legacy = boundaryById.get(surface.id);
    if (legacy) {
      entries.push({
        ...surfaceIdentity(surface),
        disposition: "LEGACY_BASELINE",
        introducedAtOrBefore: legacyBoundaryCommit,
        reason:
          "Checked SIG-909 legacy baseline; presence is not evidence of permission enforcement.",
      });
      continue;
    }
    const decision = decisions.get(surface.id);
    if (decision) usedDecisions.add(surface.id);
    if (decision?.disposition === "EXEMPT" && surface.kind !== "permission-source-sentinel") {
      throw new Error(`BOOTSTRAP_ENDPOINT_REQUIRES_BOUND ${surface.id}`);
    }
    entries.push(decisionFor(surface, decision, legacyBoundaryCommit, false));
  }

  for (const legacy of boundary.entries) {
    if (currentById.has(legacy.id)) continue;
    const family = replacementFamily(legacy.id);
    const replacements = family ? (currentByFamily.get(family) ?? []) : [];
    const replacement = replacements.find(
      (candidate) => decisions.get(candidate.id)?.replaces === legacy.id,
    );
    if (replacement) {
      if (replacements.length !== 1) {
        throw new Error(`AMBIGUOUS_BOOTSTRAP_REPLACEMENT ${legacy.id}`);
      }
      entries.push({ ...legacy, replacedBy: replacement.id });
      continue;
    }
    const sourceRetirement = (retirementsByFile.get(legacy.file) ?? []).find(
      ({ predecessor }) => predecessor.id === legacy.id,
    );
    if (sourceRetirement) {
      const { tombstone } = sourceRetirement;
      entries.push({ ...legacy, replacedBy: tombstone.id }, tombstone);
      continue;
    }
    const fileRetirement = (retirementsByFile.get(legacy.handlerFile ?? legacy.file) ?? [])[0];
    if (fileRetirement) {
      entries.push({ ...legacy, retiredBy: fileRetirement.tombstone.id });
      continue;
    }
    throw new Error(`BOOTSTRAP_REMOVED_BOUNDARY_SURFACE ${legacy.id}`);
  }

  for (const id of decisions.keys()) {
    if (!usedDecisions.has(id)) throw new Error(`UNUSED_BOOTSTRAP_DECISION ${id}`);
  }

  entries.sort((left, right) => compare(left.id, right.id));
  if (new Set(entries.map((entry) => entry.id)).size !== entries.length) {
    throw new Error("DUPLICATE_SURFACE_LEDGER_ENTRY");
  }
  const ledger = buildLedgerFromEntries(entries, legacyBoundaryCommit);
  return { ledger, baseline: buildLegacyBaselineAnchor(ledger) };
}

function validateBaselineAnchor(baseline, ledger) {
  if (
    !baseline ||
    baseline.schemaVersion !== 1 ||
    baseline.task !== "SIG-909" ||
    !Array.isArray(baseline.retirements)
  ) {
    throw new Error("LEGACY_BASELINE_ANCHOR_MISMATCH");
  }
  const { contentHash, ...content } = baseline;
  if (contentHash !== digest(content)) throw new Error("LEGACY_BASELINE_ANCHOR_MISMATCH");
  if (baseline.legacyBoundaryCommit !== ledger.legacyBoundaryCommit) {
    throw new Error("LEGACY_BASELINE_ANCHOR_MISMATCH");
  }
  const retirements = ledger.entries.filter((entry) => entry.disposition === "RETIRED");
  const byId = (left, right) => compare(left.id, right.id);
  if (stable([...baseline.retirements].sort(byId)) !== stable([...retirements].sort(byId))) {
    throw new Error("LEGACY_BASELINE_RETIREMENT_MISMATCH");
  }
}

function validateDisposition(entry, ledger) {
  if (
    (entry.kind === "permission-source-tombstone" ||
      entry.kind === "permission-surface-tombstone") &&
    entry.disposition !== "RETIRED"
  ) {
    throw new Error(`SOURCE_TOMBSTONE_CANNOT_BE_BOUND ${entry.id}`);
  }
  if (entry.disposition === "LEGACY_BASELINE") {
    if (
      entry.introducedAtOrBefore !== ledger.legacyBoundaryCommit ||
      entry.reason !==
        "Checked SIG-909 legacy baseline; presence is not evidence of permission enforcement."
    )
      throw new Error(`INVALID_LEGACY_BASELINE ${entry.id}`);
    return "legacy";
  }
  if (entry.disposition === "BOUND") {
    if (entry.kind === "permission-source-sentinel") {
      throw new Error(`SOURCE_SENTINEL_CANNOT_BE_BOUND ${entry.id}`);
    }
    if (!RESOURCE_KEY.test(entry.resourceKey ?? "") || !ACTIONS.has(entry.action)) {
      throw new Error(`INVALID_BOUND_SURFACE ${entry.id}`);
    }
    const proof = entry.bindingProof;
    if (
      !proof ||
      ![
        "ORGANIZATION_EXECUTOR_WRAPPER",
        "INVENTORY_EXECUTOR_WRAPPER",
        "CODE_DEFINED_REPORT_EXECUTOR_WRAPPER",
      ].includes(proof.kind) ||
      !RESOURCE_KEY.test(proof.enforcementAdapter ?? "")
    ) {
      throw new Error(`INVALID_BOUND_SURFACE_PROOF ${entry.id}`);
    }
    if (entry.tags.includes("report")) {
      if (
        proof.kind !== "CODE_DEFINED_REPORT_EXECUTOR_WRAPPER" ||
        typeof entry.codeDefinedReportId !== "string" ||
        !RESOURCE_KEY.test(entry.codeDefinedReportId)
      ) {
        throw new Error(`INVALID_CODE_DEFINED_REPORT_BOUNDARY ${entry.id}`);
      }
    }
    return "bound";
  }
  if (entry.disposition === "EXEMPT") {
    if (entry.dynamicReportDispatch) {
      throw new Error(`DYNAMIC_REPORT_REQUIRES_BINDING ${entry.id}`);
    }
    if (
      typeof entry.reason !== "string" ||
      entry.reason.trim().length < 12 ||
      typeof entry.owner !== "string" ||
      entry.owner.trim().length < 2 ||
      typeof entry.ticket !== "string" ||
      entry.ticket.trim().length < 3
    )
      throw new Error(`INVALID_EXEMPTION ${entry.id}`);
    return "exempt";
  }
  if (entry.disposition === "RETIRED") {
    if (entry.kind === "permission-source-tombstone") {
      const match = SOURCE_TOMBSTONE_ID.exec(entry.id ?? "");
      if (
        !match ||
        entry.file !== match[2] ||
        entry.handler !== match[1] ||
        entry.handlerFile !== match[2] ||
        typeof entry.replaces !== "string" ||
        entry.replacedBy ||
        typeof entry.reason !== "string" ||
        entry.reason.trim().length < 12 ||
        typeof entry.owner !== "string" ||
        entry.owner.trim().length < 2 ||
        typeof entry.ticket !== "string" ||
        entry.ticket.trim().length < 3 ||
        entry.resourceKey !== undefined ||
        entry.action !== undefined ||
        entry.bindingProof !== undefined ||
        entry.codeDefinedReportId !== undefined
      ) {
        throw new Error(`INVALID_SOURCE_TOMBSTONE ${entry.id}`);
      }
      return "retired";
    }
    if (entry.kind === "permission-surface-tombstone") {
      const match = SURFACE_TOMBSTONE_ID.exec(entry.id ?? "");
      if (
        !match ||
        typeof entry.replaces !== "string" ||
        replacementFamily(entry.replaces) !== null ||
        entry.replacedBy ||
        typeof entry.reason !== "string" ||
        entry.reason.trim().length < 12 ||
        typeof entry.owner !== "string" ||
        entry.owner.trim().length < 2 ||
        typeof entry.ticket !== "string" ||
        entry.ticket.trim().length < 3 ||
        entry.resourceKey !== undefined ||
        entry.action !== undefined ||
        entry.bindingProof !== undefined ||
        entry.codeDefinedReportId !== undefined
      ) {
        throw new Error(`INVALID_SURFACE_TOMBSTONE ${entry.id}`);
      }
      return "retired";
    }
    throw new Error(`INVALID_SOURCE_TOMBSTONE ${entry.id}`);
  }
  throw new Error(`INVALID_SURFACE_DISPOSITION ${entry.id}`);
}

function replacementFamily(id) {
  const worker = WORKER_CONTENT_ID.exec(id);
  if (worker) return worker[1];
  const sentinel = SOURCE_SENTINEL_ID.exec(id);
  if (sentinel) return `permission-source:${sentinel[1]}:${sentinel[2]}`;
  const tombstone = SOURCE_TOMBSTONE_ID.exec(id);
  return tombstone ? `permission-source:${tombstone[1]}:${tombstone[2]}` : null;
}

function validateReplacementGraph(entries, current, selections = []) {
  const selected = new Map(selections.map((r) => [r.family, r]));
  const selectedFor = (id) => selected.get(id.slice(0, id.lastIndexOf("#sha256:")));
  for (const r of selections) {
    if (!current.has(r.head) || r.lineage.some((ref) => ref.id !== r.head && current.has(ref.id)))
      throw new Error("SOURCE_HEAD_SELECTION_CURRENT_SOURCE_MISMATCH");
  }
  const recorded = new Map(entries.map((entry) => [entry.id, entry]));
  for (const entry of entries) {
    const active = current.has(entry.id);
    const family = replacementFamily(entry.id);
    if (entry.disposition === "RETIRED" && entry.kind === "permission-source-tombstone") {
      const tombstone = SOURCE_TOMBSTONE_ID.exec(entry.id);
      const predecessor = SOURCE_SENTINEL_ID.exec(entry.replaces ?? "");
      if (!tombstone || !predecessor || tombstone[3] !== predecessor[3]) {
        throw new Error(`INVALID_SOURCE_TOMBSTONE ${entry.id}`);
      }
    }
    if (entry.disposition === "RETIRED" && entry.kind === "permission-surface-tombstone") {
      const tombstone = SURFACE_TOMBSTONE_ID.exec(entry.id);
      const predecessorEntry = recorded.get(entry.replaces);
      if (
        !tombstone ||
        !predecessorEntry ||
        predecessorEntry.retiredBy !== entry.id ||
        replacementFamily(predecessorEntry.id) !== null ||
        tombstone[1] !== createHash("sha256").update(entry.replaces).digest("hex")
      ) {
        throw new Error(`INVALID_SURFACE_TOMBSTONE ${entry.id}`);
      }
    }
    if (active && entry.replacedBy && selectedFor(entry.id)?.head !== entry.id) {
      throw new Error(`ACTIVE_SURFACE_MARKED_REPLACED ${entry.id}`);
    }
    if (active && entry.retiredBy) {
      throw new Error(`ACTIVE_SURFACE_MARKED_RETIRED ${entry.id}`);
    }
    if (
      !active &&
      !entry.replacedBy &&
      !entry.retiredBy &&
      entry.disposition !== "RETIRED" &&
      !selectedFor(entry.id)
    ) {
      throw new Error(`STALE_SURFACE_LEDGER_ENTRY ${entry.id}`);
    }
    if (entry.retiredBy) {
      const retirement = recorded.get(entry.retiredBy);
      if (
        entry.replacedBy ||
        entry.replaces ||
        !retirement ||
        (retirement.kind !== "permission-source-tombstone" &&
          retirement.kind !== "permission-surface-tombstone") ||
        retirement.disposition !== "RETIRED" ||
        retirement.file !== (entry.handlerFile ?? entry.file) ||
        // permission-surface-tombstone retires exactly one named surface, so unlike
        // permission-source-tombstone (legitimately many-to-one across every handler
        // in a retired file), its `replaces` must name this exact predecessor —
        // otherwise an unrelated removal could piggyback on one hash-bound tombstone's
        // reason/owner/ticket without its own accountable retirement record.
        (retirement.kind === "permission-surface-tombstone" && retirement.replaces !== entry.id)
      ) {
        throw new Error(`INVALID_SOURCE_RETIREMENT ${entry.id}`);
      }
      continue;
    }
    if (entry.kind === "permission-surface-tombstone") continue;
    if (entry.kind === "opaque-module-load" && entry.disposition === "BOUND") {
      throw new Error(`OPAQUE_MODULE_LOAD_CANNOT_BE_BOUND ${entry.id}`);
    }
    if (!entry.replacedBy && !entry.replaces) continue;
    if (!family) throw new Error(`INVALID_SURFACE_REPLACEMENT ${entry.id}`);
    if (entry.replacedBy) {
      const replacement = recorded.get(entry.replacedBy);
      if (
        !replacement ||
        replacement.replaces !== entry.id ||
        replacementFamily(replacement.id) !== family
      ) {
        throw new Error(`INVALID_SURFACE_REPLACEMENT ${entry.id}`);
      }
    }
    if (entry.replaces) {
      const predecessor = recorded.get(entry.replaces);
      if (
        !predecessor ||
        predecessor.replacedBy !== entry.id ||
        replacementFamily(predecessor.id) !== family ||
        entry.disposition === "LEGACY_BASELINE"
      ) {
        throw new Error(`INVALID_SURFACE_REPLACEMENT ${entry.id}`);
      }
    }
  }
  for (const entry of entries) {
    if (!entry.replacedBy) continue;
    const seen = new Set([entry.id]);
    let cursor = entry;
    while (cursor.replacedBy) {
      if (seen.has(cursor.replacedBy)) {
        throw new Error(`SURFACE_REPLACEMENT_CYCLE ${entry.id}`);
      }
      seen.add(cursor.replacedBy);
      cursor = recorded.get(cursor.replacedBy);
      if (!cursor) throw new Error(`INVALID_SURFACE_REPLACEMENT ${entry.id}`);
    }
    if (!current.has(cursor.id) && cursor.disposition !== "RETIRED" && !selectedFor(cursor.id)) {
      throw new Error(`SURFACE_REPLACEMENT_WITHOUT_ACTIVE_HEAD ${entry.id}`);
    }
  }
}

function rejectRetiredSourceReuse(entries, current) {
  const activeFamilies = new Set([...current.keys()].map(replacementFamily).filter(Boolean));
  for (const entry of entries) {
    const family = replacementFamily(entry.id);
    if (entry.disposition === "RETIRED" && family && activeFamilies.has(family)) {
      throw new Error(`RETIRED_SOURCE_FAMILY_REUSED ${entry.id}`);
    }
  }
}

export function verifySurfaceLedger(surfaces, ledger, baseline) {
  if (
    !ledger ||
    ledger.schemaVersion !== 1 ||
    ledger.task !== "SIG-909" ||
    !Array.isArray(ledger.entries)
  ) {
    throw new Error("UNSUPPORTED_SURFACE_LEDGER");
  }
  const { contentHash, ...content } = ledger;
  if (contentHash !== digest(content)) throw new Error("LEDGER_CONTENT_HASH_MISMATCH");
  if (new Set(ledger.entries.map((entry) => entry.id)).size !== ledger.entries.length) {
    throw new Error("DUPLICATE_SURFACE_LEDGER_ENTRY");
  }
  validateBaselineAnchor(baseline, ledger);
  const current = new Map(surfaces.map((surface) => [surface.id, surface]));
  const recorded = new Map(ledger.entries.map((entry) => [entry.id, entry]));
  const counts = { checked: ledger.entries.length, bound: 0, exempt: 0, legacy: 0, retired: 0 };
  for (const entry of ledger.entries) counts[validateDisposition(entry, ledger)] += 1;
  rejectRetiredSourceReuse(ledger.entries, current);
  for (const surface of surfaces) {
    if (!recorded.has(surface.id)) {
      throw new Error(`UNCLASSIFIED_NEW_SURFACE ${surface.tags.join(",")} ${surface.id}`);
    }
  }
  validateReplacementGraph(ledger.entries, current, getSourceHeadSelections(ledger));
  for (const entry of ledger.entries) {
    const surface = current.get(entry.id);
    if (!surface) continue;
    if (stable(driftComparableIdentity(surface)) !== stable(driftComparableIdentity(entry))) {
      throw new Error(`SURFACE_CLASSIFICATION_DRIFT ${entry.id}`);
    }
  }
  if (ledger.surfaceDigest !== digest(ledger.entries.map(surfaceIdentity))) {
    throw new Error("SURFACE_DIGEST_MISMATCH");
  }
  const legacyIds = ledger.entries
    .filter((entry) => entry.disposition === "LEGACY_BASELINE")
    .map((entry) => entry.id);
  if (ledger.legacyIdsDigest !== digest(legacyIds))
    throw new Error("LEGACY_BOUNDARY_HASH_MISMATCH");
  if (
    baseline.legacyCount !== legacyIds.length ||
    baseline.legacyIdsDigest !== ledger.legacyIdsDigest
  ) {
    throw new Error("LEGACY_BASELINE_ANCHOR_MISMATCH");
  }
  if (counts.retired === 0) delete counts.retired;
  return counts;
}

/** Required-suite parity: tuple, adapter and code-defined report must all agree. */
export function verifySurfaceLedgerBindings(ledger, context) {
  const readonlyMap = (value) =>
    value &&
    typeof value.get === "function" &&
    typeof value.has === "function" &&
    typeof value.entries === "function" &&
    typeof value[Symbol.iterator] === "function";
  const readonlySet = (value) =>
    value &&
    typeof value.has === "function" &&
    typeof value.values === "function" &&
    typeof value[Symbol.iterator] === "function";
  if (
    !ledger ||
    !Array.isArray(ledger.entries) ||
    !readonlySet(context?.knownPermissions) ||
    !readonlyMap(context.adapterBindings) ||
    !readonlyMap(context.codeDefinedReports)
  ) {
    throw new Error("INVALID_SURFACE_BINDING_INPUT");
  }
  let bound = 0;
  for (const entry of ledger.entries) {
    if (entry.fixedRecordReportProofs) {
      if (
        entry.disposition !== "EXEMPT" ||
        entry.kind !== "permission-source-sentinel" ||
        entry.dynamicReportDispatch ||
        !Array.isArray(entry.fixedRecordReportProofs) ||
        !entry.fixedRecordReportProofs.length
      ) {
        throw new Error(`INVALID_FIXED_RECORD_REPORT_PROOF ${entry.id}`);
      }
      for (const proof of entry.fixedRecordReportProofs) {
        if (
          proof.version !== 1 ||
          !context.knownPermissions.has(`${proof.resourceKey}:${proof.action}`)
        ) {
          throw new Error(`UNKNOWN_FIXED_RECORD_REPORT_PERMISSION ${entry.id}`);
        }
      }
    }
    if (
      entry.kind === "permission-source-tombstone" ||
      entry.kind === "permission-surface-tombstone"
    ) {
      if (entry.disposition === "BOUND") {
        throw new Error(`SOURCE_TOMBSTONE_CANNOT_BE_BOUND ${entry.id}`);
      }
      continue;
    }
    if (entry.disposition !== "BOUND" || entry.replacedBy) continue;
    const permission = `${entry.resourceKey}:${entry.action}`;
    if (!context.knownPermissions.has(permission)) {
      throw new Error(`UNKNOWN_BOUND_PERMISSION ${entry.id} ${permission}`);
    }
    const adapter = context.adapterBindings.get(entry.bindingProof?.enforcementAdapter);
    if (!adapter) throw new Error(`UNKNOWN_BOUND_ADAPTER ${entry.id}`);
    if (!adapter.has(permission)) throw new Error(`ADAPTER_TUPLE_MISMATCH ${entry.id}`);
    if (entry.tags.includes("report")) {
      const reportPermission = context.codeDefinedReports.get(entry.codeDefinedReportId);
      if (!reportPermission) throw new Error(`MISSING_CODE_DEFINED_REPORT_BINDING ${entry.id}`);
      if (reportPermission !== permission)
        throw new Error(`REPORT_PERMISSION_MISMATCH ${entry.id}`);
    }
    bound += 1;
  }
  return bound;
}

function enclosingClassName(node) {
  let current = node.parent;
  while (current) {
    if (ts.isClassDeclaration(current)) return current.name?.text ?? null;
    current = current.parent;
  }
  return null;
}

function handlerNode(source, surface) {
  const found = [];
  const visit = (node) => {
    if (
      (ts.isMethodDeclaration(node) || ts.isFunctionDeclaration(node)) &&
      node.name?.getText(source) === surface.handler
    ) {
      found.push(node);
    }
    if (ts.isVariableDeclaration(node) && node.name.getText(source) === surface.handler) {
      found.push(node);
    }
    ts.forEachChild(node, visit);
  };
  visit(source);
  const exact = found.filter((node) => {
    if (surface.handlerLine && sourceLocation(source, node).line !== surface.handlerLine) {
      return false;
    }
    if (
      surface.controller &&
      surface.handlerFile === surface.file &&
      ts.isMethodDeclaration(node) &&
      enclosingClassName(node) !== surface.controller
    ) {
      return false;
    }
    return true;
  });
  if (exact.length !== 1) throw new Error(`BOUND_HANDLER_IDENTITY_MISMATCH ${surface.id}`);
  return exact[0];
}

function unwrapCall(expression) {
  let current = expression;
  while (ts.isAwaitExpression(current) || ts.isParenthesizedExpression(current)) {
    current = current.expression;
  }
  return ts.isCallExpression(current) ? current : null;
}

function directReturnCalls(handler) {
  const calls = [];
  const body = ts.isVariableDeclaration(handler) ? handler.initializer : handler.body;
  if (!body) return calls;
  if (ts.isArrowFunction(body) && !ts.isBlock(body.body)) {
    calls.push(unwrapCall(body.body));
    return calls;
  }
  const root = ts.isArrowFunction(body) ? body.body : body;
  const visit = (node) => {
    if (node !== root && ts.isFunctionLike(node)) return;
    if (ts.isReturnStatement(node) && node.expression) {
      calls.push(unwrapCall(node.expression));
      return;
    }
    ts.forEachChild(node, visit);
  };
  visit(root);
  return calls;
}

function harmlessDeclarationValue(node) {
  if (!node) return true;
  if (
    ts.isArrowFunction(node) ||
    ts.isFunctionExpression(node) ||
    ts.isStringLiteralLike(node) ||
    ts.isNumericLiteral(node) ||
    [
      ts.SyntaxKind.TrueKeyword,
      ts.SyntaxKind.FalseKeyword,
      ts.SyntaxKind.NullKeyword,
      ts.SyntaxKind.UndefinedKeyword,
    ].includes(node.kind)
  ) {
    return true;
  }
  if (
    ts.isParenthesizedExpression(node) ||
    ts.isAsExpression(node) ||
    ts.isSatisfiesExpression(node)
  ) {
    return harmlessDeclarationValue(node.expression);
  }
  if (ts.isArrayLiteralExpression(node)) {
    return node.elements.every(
      (element) => !ts.isSpreadElement(element) && harmlessDeclarationValue(element),
    );
  }
  if (ts.isObjectLiteralExpression(node)) {
    return node.properties.every(
      (property) =>
        ts.isPropertyAssignment(property) &&
        !ts.isComputedPropertyName(property.name) &&
        harmlessDeclarationValue(property.initializer),
    );
  }
  return false;
}

function harmlessHandlerDeclaration(statement) {
  if (
    ts.isFunctionDeclaration(statement) ||
    ts.isTypeAliasDeclaration(statement) ||
    ts.isInterfaceDeclaration(statement) ||
    ts.isEmptyStatement(statement)
  ) {
    return true;
  }
  if (!ts.isVariableStatement(statement)) return false;
  return statement.declarationList.declarations.every(
    (declaration) =>
      ts.isIdentifier(declaration.name) && harmlessDeclarationValue(declaration.initializer),
  );
}

function assertThinHandler(handler, entry) {
  const body = ts.isVariableDeclaration(handler) ? handler.initializer : handler.body;
  if (!body) throw new Error(`PRE_BOUNDARY_EXECUTION ${entry.id}`);
  if (ts.isArrowFunction(body) && !ts.isBlock(body.body)) return;
  const block = ts.isArrowFunction(body) ? body.body : body;
  if (!ts.isBlock(block) || block.statements.length === 0) {
    throw new Error(`PRE_BOUNDARY_EXECUTION ${entry.id}`);
  }
  const terminal = block.statements.at(-1);
  if (!ts.isReturnStatement(terminal) || !terminal.expression) {
    throw new Error(`PRE_BOUNDARY_EXECUTION ${entry.id}`);
  }
  if (!block.statements.slice(0, -1).every(harmlessHandlerDeclaration)) {
    throw new Error(`PRE_BOUNDARY_EXECUTION ${entry.id}`);
  }
}

function resolvedImport(file, specifier) {
  if (!specifier.startsWith(".")) return specifier;
  return posix
    .normalize(posix.join(posix.dirname(file), specifier))
    .replace(/\.(?:[cm]?[jt]sx?)$/u, "");
}

const PROOF_BOUNDARIES = Object.freeze({
  ORGANIZATION_EXECUTOR_WRAPPER: Object.freeze({
    name: "executeOrganizationPermission",
    adapter: "access-policy-runtime-v1",
    arity: 4,
    permissionIndex: 2,
    callbackIndex: 3,
    executorIndex: 0,
    actorIndex: 1,
    executorType: "AccessPolicyOrganizationExecutionService",
    executorModule: ORGANIZATION_EXECUTOR_MODULE,
  }),
  INVENTORY_EXECUTOR_WRAPPER: Object.freeze({
    name: "executeInventoryPermission",
    adapter: "inventory-policy-execution-v1",
    arity: 5,
    permissionIndex: 2,
    callbackIndex: 4,
    executorIndex: 0,
    actorIndex: 1,
    executorType: "InventoryPolicyExecutionService",
    executorModule: INVENTORY_EXECUTOR_MODULE,
  }),
  CODE_DEFINED_REPORT_EXECUTOR_WRAPPER: Object.freeze({
    name: "executeCodeDefinedReport",
    adapter: "access-policy-runtime-v1",
    arity: 4,
    manifestIndex: 2,
    reportIdIndex: 3,
    executorIndex: 0,
    actorIndex: 1,
    executorType: "AccessPolicyOrganizationExecutionService",
    executorModule: ORGANIZATION_EXECUTOR_MODULE,
  }),
});

function unwrapPureExpression(node) {
  let current = node;
  while (
    ts.isParenthesizedExpression(current) ||
    ts.isAsExpression(current) ||
    ts.isSatisfiesExpression(current) ||
    ts.isNonNullExpression(current)
  ) {
    current = current.expression;
  }
  return current;
}

function enclosingClass(node) {
  let current = node.parent;
  while (current && !ts.isClassLike(current)) current = current.parent;
  return current ?? null;
}

function directFieldReference(node, name) {
  const value = unwrapPureExpression(node);
  return Boolean(
    ts.isPropertyAccessExpression(value) &&
    value.expression.kind === ts.SyntaxKind.ThisKeyword &&
    value.name.text === name,
  );
}

function containsNode(node, predicate) {
  let found = false;
  const visit = (candidate) => {
    if (found) return;
    if (predicate(candidate)) {
      found = true;
      return;
    }
    ts.forEachChild(candidate, visit);
  };
  visit(node);
  return found;
}

function fieldRootedReference(node, name) {
  let current = unwrapPureExpression(node);
  while (ts.isPropertyAccessExpression(current) || ts.isElementAccessExpression(current)) {
    if (directFieldReference(current, name)) return true;
    current = unwrapPureExpression(current.expression);
  }
  return directFieldReference(current, name);
}

function expressionRootedAtThis(node) {
  let current = unwrapPureExpression(node);
  while (ts.isPropertyAccessExpression(current) || ts.isElementAccessExpression(current)) {
    current = unwrapPureExpression(current.expression);
  }
  return current.kind === ts.SyntaxKind.ThisKeyword;
}

function nodeBelongsTo(node, ancestor) {
  let current = node;
  while (current) {
    if (current === ancestor) return true;
    current = current.parent;
  }
  return false;
}

function isApprovedExecutorUse(call, handler, name) {
  return Boolean(
    nodeBelongsTo(call, handler) &&
    ts.isIdentifier(call.expression) &&
    Object.values(PROOF_BOUNDARIES).some((proof) => proof.name === call.expression.text) &&
    call.arguments[0] &&
    directFieldReference(call.arguments[0], name),
  );
}

function isApprovedExecutorReference(node, handler, name) {
  let current = node;
  while (
    current.parent &&
    (ts.isParenthesizedExpression(current.parent) ||
      ts.isAsExpression(current.parent) ||
      ts.isSatisfiesExpression(current.parent) ||
      ts.isNonNullExpression(current.parent))
  ) {
    current = current.parent;
  }
  return Boolean(
    ts.isCallExpression(current.parent) &&
    current.parent.arguments[0] === current &&
    isApprovedExecutorUse(current.parent, handler, name),
  );
}

function parameterProperty(owner, name) {
  const conflictingAccessor = owner.members.some((member) => {
    if (!ts.isGetAccessorDeclaration(member) && !ts.isSetAccessorDeclaration(member)) {
      return false;
    }
    const memberName = ts.isIdentifier(member.name)
      ? member.name.text
      : ts.isStringLiteralLike(member.name)
        ? member.name.text
        : null;
    return memberName === name;
  });
  if (conflictingAccessor) return null;
  const constructors = owner.members.filter((member) => ts.isConstructorDeclaration(member));
  if (constructors.length !== 1) return null;
  return constructors[0].parameters.find(
    (candidate) => ts.isIdentifier(candidate.name) && candidate.name.text === name,
  );
}

function stableParameterModifiers(parameter) {
  if (
    !parameter ||
    !ts.isIdentifier(parameter.name) ||
    parameter.initializer ||
    parameter.questionToken ||
    parameter.dotDotDotToken
  ) {
    return false;
  }
  const modifiers = new Set(parameter.modifiers?.map((modifier) => modifier.kind) ?? []);
  const hasAccessModifier = [
    ts.SyntaxKind.PrivateKeyword,
    ts.SyntaxKind.ProtectedKeyword,
    ts.SyntaxKind.PublicKeyword,
  ].some((kind) => modifiers.has(kind));
  return hasAccessModifier && modifiers.has(ts.SyntaxKind.ReadonlyKeyword);
}

function fieldHasUnsafeUse(owner, handler, name) {
  let unsafe = false;
  const referencesOwnerOrField = (node) =>
    containsNode(node, (candidate) => {
      if (directFieldReference(candidate, name)) return true;
      if (candidate.kind !== ts.SyntaxKind.ThisKeyword) return false;
      return !(
        (ts.isPropertyAccessExpression(candidate.parent) ||
          ts.isElementAccessExpression(candidate.parent)) &&
        candidate.parent.expression === candidate
      );
    });
  const visit = (node) => {
    if (unsafe) return;
    if (ts.isElementAccessExpression(node) && expressionRootedAtThis(node)) {
      unsafe = true;
      return;
    }
    if (directFieldReference(node, name) && !isApprovedExecutorReference(node, handler, name)) {
      unsafe = true;
      return;
    }
    if (
      node.kind === ts.SyntaxKind.ThisKeyword &&
      !(
        (ts.isPropertyAccessExpression(node.parent) || ts.isElementAccessExpression(node.parent)) &&
        node.parent.expression === node
      )
    ) {
      unsafe = true;
      return;
    }
    if (
      ts.isVariableDeclaration(node) &&
      node.initializer &&
      referencesOwnerOrField(node.initializer)
    ) {
      unsafe = true;
      return;
    }
    if (
      ts.isBinaryExpression(node) &&
      node.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
      node.operatorToken.kind <= ts.SyntaxKind.LastAssignment &&
      fieldRootedReference(node.left, name)
    ) {
      unsafe = true;
      return;
    }
    if (
      (ts.isPrefixUnaryExpression(node) || ts.isPostfixUnaryExpression(node)) &&
      [ts.SyntaxKind.PlusPlusToken, ts.SyntaxKind.MinusMinusToken].includes(node.operator) &&
      fieldRootedReference(node.operand, name)
    ) {
      unsafe = true;
      return;
    }
    if (ts.isDeleteExpression(node) && fieldRootedReference(node.expression, name)) {
      unsafe = true;
      return;
    }
    if (ts.isCallExpression(node) || ts.isNewExpression(node)) {
      const fieldReceiver =
        ts.isCallExpression(node) && fieldRootedReference(node.expression, name);
      const escaped = (node.arguments ?? []).some(referencesOwnerOrField);
      if (
        (fieldReceiver || escaped) &&
        (!ts.isCallExpression(node) || !isApprovedExecutorUse(node, handler, name))
      ) {
        unsafe = true;
        return;
      }
    }
    ts.forEachChild(node, visit);
  };
  visit(owner);
  return unsafe;
}

function isConstructorParameterField(name, handler) {
  const owner = enclosingClass(handler);
  if (!owner) return false;
  const parameter = parameterProperty(owner, name);
  return stableParameterModifiers(parameter) && !fieldHasUnsafeUse(owner, handler, name);
}

function actorFactoryShape(node) {
  const value = unwrapPureExpression(node);
  return Boolean(
    ts.isCallExpression(value) &&
    ts.isIdentifier(value.expression) &&
    value.arguments.length === 1 &&
    ts.isIdentifier(value.arguments[0]),
  );
}

function isEvaluationPure(node, handler) {
  const value = unwrapPureExpression(node);
  if (
    ts.isIdentifier(value) ||
    ts.isStringLiteralLike(value) ||
    ts.isNumericLiteral(value) ||
    ts.isRegularExpressionLiteral(value) ||
    value.kind === ts.SyntaxKind.ThisKeyword ||
    [ts.SyntaxKind.TrueKeyword, ts.SyntaxKind.FalseKeyword, ts.SyntaxKind.NullKeyword].includes(
      value.kind,
    )
  ) {
    return true;
  }
  if (ts.isNoSubstitutionTemplateLiteral(value)) return true;
  if (ts.isPropertyAccessExpression(value) && value.expression.kind === ts.SyntaxKind.ThisKeyword) {
    return isConstructorParameterField(value.name.text, handler);
  }
  if (ts.isTemplateExpression(value)) {
    return value.templateSpans.every((span) => isEvaluationPure(span.expression, handler));
  }
  if (ts.isPrefixUnaryExpression(value)) {
    return (
      value.operator !== ts.SyntaxKind.DeleteKeyword &&
      value.operator !== ts.SyntaxKind.PlusPlusToken &&
      value.operator !== ts.SyntaxKind.MinusMinusToken &&
      isEvaluationPure(value.operand, handler)
    );
  }
  if (ts.isArrayLiteralExpression(value)) {
    return value.elements.every(
      (element) => !ts.isSpreadElement(element) && isEvaluationPure(element, handler),
    );
  }
  if (ts.isObjectLiteralExpression(value)) {
    return value.properties.every((property) => {
      if (ts.isShorthandPropertyAssignment(property)) return true;
      return (
        ts.isPropertyAssignment(property) &&
        !ts.isComputedPropertyName(property.name) &&
        isEvaluationPure(property.initializer, handler)
      );
    });
  }
  return false;
}

function isPureCallbackArgument(node) {
  const callback = unwrapPureExpression(node);
  return (
    ts.isIdentifier(callback) || ts.isArrowFunction(callback) || ts.isFunctionExpression(callback)
  );
}

function assertPureBoundaryArguments(call, proof, entry, handler) {
  if (call.arguments.length !== proof.arity) {
    throw new Error(`IMPURE_BOUNDARY_ARGUMENT ${entry.id}`);
  }
  for (let index = 0; index < call.arguments.length; index += 1) {
    const argument = call.arguments[index];
    const pure =
      proof.callbackIndex !== undefined && index === proof.callbackIndex
        ? isPureCallbackArgument(argument)
        : index === proof.actorIndex
          ? actorFactoryShape(argument) || isEvaluationPure(argument, handler)
          : isEvaluationPure(argument, handler);
    if (!pure) throw new Error(`IMPURE_BOUNDARY_ARGUMENT ${entry.id}`);
  }
}

function matchesImportedSymbol(node, source, input, name, module) {
  if (!ts.isIdentifier(node)) return false;
  const imported = importedSymbols(source).get(node.text);
  return Boolean(
    imported &&
    imported.name === name &&
    resolvedImport(input.file, imported.module) === module &&
    !importedReferenceIsShadowed(node, node.text),
  );
}

function exactCanonicalInjection(parameter, proof, source, input) {
  const parameterDecorators = decorators(parameter, source, importedSymbols(source));
  if (parameterDecorators.length === 0) return true;
  if (parameterDecorators.length !== 1 || parameterDecorators[0].args.length !== 1) return false;
  const injection = parameterDecorators[0];
  const expression = injection.node.expression;
  const target = ts.isCallExpression(expression) ? expression.expression : expression;
  return Boolean(
    matchesImportedSymbol(target, source, input, "Inject", "@nestjs/common") &&
    matchesImportedSymbol(
      injection.args[0],
      source,
      input,
      proof.executorType,
      proof.executorModule,
    ),
  );
}

function trustedExecutorArgument(call, proof, handler, source, input) {
  const argument = call.arguments[proof.executorIndex];
  const value = argument && unwrapPureExpression(argument);
  if (
    !value ||
    !ts.isPropertyAccessExpression(value) ||
    value.expression.kind !== ts.SyntaxKind.ThisKeyword ||
    !isConstructorParameterField(value.name.text, handler)
  ) {
    return false;
  }
  const owner = enclosingClass(handler);
  const parameter = owner && parameterProperty(owner, value.name.text);
  const type = parameter?.type;
  return Boolean(
    parameter &&
    type &&
    ts.isTypeReferenceNode(type) &&
    ts.isIdentifier(type.typeName) &&
    !type.typeArguments?.length &&
    matchesImportedSymbol(type.typeName, source, input, proof.executorType, proof.executorModule) &&
    exactCanonicalInjection(parameter, proof, source, input),
  );
}

const NEST_ROUTE_DECORATORS = new Set([
  "All",
  "Delete",
  "Get",
  "Head",
  "Options",
  "Patch",
  "Post",
  "Put",
  "RequestMapping",
  "Search",
  "Sse",
]);

function staticRouteMetadata(node) {
  const value = unwrapPureExpression(node);
  if (ts.isStringLiteralLike(value) || ts.isNoSubstitutionTemplateLiteral(value)) return true;
  return (
    ts.isArrayLiteralExpression(value) &&
    value.elements.every((element) => !ts.isSpreadElement(element) && staticRouteMetadata(element))
  );
}

function canonicalGuardDecorator(decorator, source, input) {
  return (
    decorator.module === "@nestjs/common" &&
    decorator.name === "UseGuards" &&
    decorator.args.length === 1 &&
    matchesImportedSymbol(decorator.args[0], source, input, "JwtAuthGuard", JWT_AUTH_GUARD_MODULE)
  );
}

function canonicalExecutionDecorators(handler, source, input) {
  const symbols = importedSymbols(source);
  const owner = enclosingClass(handler);
  if (!owner) return false;
  const ownerDecorators = decorators(owner, source, symbols);
  const handlerDecorators = decorators(handler, source, symbols);
  const controllers = ownerDecorators.filter(
    (decorator) => decorator.module === "@nestjs/common" && decorator.name === "Controller",
  );
  const routes = handlerDecorators.filter(
    (decorator) =>
      decorator.module === "@nestjs/common" && NEST_ROUTE_DECORATORS.has(decorator.name),
  );
  if (
    controllers.length !== 1 ||
    controllers[0].args.length > 1 ||
    controllers[0].args.some((argument) => !staticRouteMetadata(argument)) ||
    routes.length !== 1 ||
    routes[0].args.length > 1 ||
    routes[0].args.some((argument) => !staticRouteMetadata(argument))
  ) {
    return false;
  }
  const allowedOwner = ownerDecorators.every(
    (decorator) =>
      decorator === controllers[0] || canonicalGuardDecorator(decorator, source, input),
  );
  const allowedHandler = handlerDecorators.every(
    (decorator) => decorator === routes[0] || canonicalGuardDecorator(decorator, source, input),
  );
  return (
    allowedOwner &&
    allowedHandler &&
    [...ownerDecorators, ...handlerDecorators].some((decorator) =>
      canonicalGuardDecorator(decorator, source, input),
    )
  );
}

const NEST_BOUND_INPUT_DECORATORS = new Set([
  "Body",
  "Headers",
  "HostParam",
  "Ip",
  "Param",
  "Query",
  "Session",
]);

function literalNestInputSelector(node) {
  const value = unwrapPureExpression(node);
  return Boolean(
    ts.isStringLiteralLike(value) ||
    ts.isNumericLiteral(value) ||
    value.kind === ts.SyntaxKind.TrueKeyword ||
    value.kind === ts.SyntaxKind.FalseKeyword,
  );
}

function stableBoundHandlerParameters(handler, source) {
  const symbols = importedSymbols(source);
  return handler.parameters.every((parameter) => {
    if (
      !ts.isIdentifier(parameter.name) ||
      parameter.initializer ||
      parameter.questionToken ||
      parameter.dotDotDotToken
    ) {
      return false;
    }
    const parameterDecorators = decorators(parameter, source, symbols);
    if (parameterDecorators.length === 0) return true;
    if (parameterDecorators.length !== 1 || parameterDecorators[0].module !== "@nestjs/common") {
      return false;
    }
    const decorator = parameterDecorators[0];
    if (decorator.name === "Req") return decorator.args.length === 0;
    return (
      NEST_BOUND_INPUT_DECORATORS.has(decorator.name) &&
      decorator.args.length <= 1 &&
      decorator.args.every(literalNestInputSelector)
    );
  });
}

function identifierIsImportBinding(node) {
  let current = node.parent;
  while (current && !ts.isSourceFile(current)) {
    if (ts.isImportDeclaration(current)) return true;
    current = current.parent;
  }
  return false;
}

function directModuleMetadataArrayReference(node, property, source, input) {
  const array = node.parent;
  if (!ts.isArrayLiteralExpression(array) || !array.elements.includes(node)) return false;
  const assignment = array.parent;
  if (
    !ts.isPropertyAssignment(assignment) ||
    assignment.initializer !== array ||
    propertyName(assignment.name, source) !== property
  ) {
    return false;
  }
  const metadata = assignment.parent;
  const call = metadata.parent;
  return Boolean(
    ts.isObjectLiteralExpression(metadata) &&
    ts.isCallExpression(call) &&
    call.arguments[0] === metadata &&
    ts.isDecorator(call.parent) &&
    matchesImportedSymbol(call.expression, source, input, "Module", "@nestjs/common"),
  );
}

function moduleWithoutExtension(file) {
  return file.replace(/\.(?:[cm]?[jt]sx?)$/u, "");
}

function boundClassExportGraph(ownerModule, className, inputs) {
  const exportsByModule = new Map([[ownerModule, new Set([className])]]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const candidateInput of inputs) {
      if (!/\.[cm]?[jt]sx?$/u.test(candidateInput.file)) continue;
      const candidate = parseSource(candidateInput.file, candidateInput.text);
      const currentModule = moduleWithoutExtension(candidateInput.file);
      for (const statement of candidate.statements) {
        if (
          !ts.isExportDeclaration(statement) ||
          !statement.exportClause ||
          !ts.isNamedExports(statement.exportClause)
        ) {
          continue;
        }
        const sourceModule = statement.moduleSpecifier
          ? resolvedImport(candidateInput.file, statement.moduleSpecifier.text)
          : currentModule;
        const sourceExports = exportsByModule.get(sourceModule);
        if (!sourceExports) continue;
        for (const element of statement.exportClause.elements) {
          const importedName = (element.propertyName ?? element.name).text;
          if (!sourceExports.has(importedName)) continue;
          const currentExports = exportsByModule.get(currentModule) ?? new Set();
          const size = currentExports.size;
          currentExports.add(element.name.text);
          exportsByModule.set(currentModule, currentExports);
          if (currentExports.size !== size) changed = true;
        }
      }
    }
  }
  return exportsByModule;
}

function requireCallModule(node, file, requireAliases = new Set(["require"])) {
  const value = unwrapPureExpression(node);
  if (
    !ts.isCallExpression(value) ||
    !ts.isIdentifier(value.expression) ||
    !requireAliases.has(value.expression.text) ||
    value.arguments.length !== 1
  ) {
    return null;
  }
  const specifier = staticModuleText(value.arguments[0]);
  return specifier === null ? null : resolvedImport(file, specifier);
}

function ownerThisMutation(owner) {
  const aliases = new Set();
  const mutatorAliases = new Map();
  const canonicalMutator = (node) => {
    const value = unwrapPureExpression(node);
    if (ts.isIdentifier(value)) return mutatorAliases.get(value.text) ?? null;
    if (ts.isPropertyAccessExpression(value) && ts.isIdentifier(value.expression)) {
      return `${value.expression.text}.${value.name.text}`;
    }
    if (
      ts.isElementAccessExpression(value) &&
      ts.isIdentifier(value.expression) &&
      value.argumentExpression &&
      ts.isStringLiteralLike(value.argumentExpression)
    ) {
      return `${value.expression.text}.${value.argumentExpression.text}`;
    }
    return null;
  };
  let changed = true;
  const rootIsOwner = (node) => {
    let value = unwrapPureExpression(node);
    while (ts.isPropertyAccessExpression(value) || ts.isElementAccessExpression(value)) {
      value = unwrapPureExpression(value.expression);
    }
    return (
      value.kind === ts.SyntaxKind.ThisKeyword ||
      (ts.isIdentifier(value) && aliases.has(value.text))
    );
  };
  while (changed) {
    changed = false;
    const collect = (node) => {
      if (
        ts.isVariableDeclaration(node) &&
        ts.isIdentifier(node.name) &&
        node.initializer &&
        rootIsOwner(node.initializer) &&
        !aliases.has(node.name.text)
      ) {
        aliases.add(node.name.text);
        changed = true;
      }
      if (ts.isVariableDeclaration(node) && ts.isIdentifier(node.name) && node.initializer) {
        const mutator = canonicalMutator(node.initializer);
        if (mutator && !mutatorAliases.has(node.name.text)) {
          mutatorAliases.set(node.name.text, mutator);
          changed = true;
        }
      }
      ts.forEachChild(node, collect);
    };
    collect(owner);
  }
  const mutators = new Set([
    "Object.assign",
    "Object.defineProperties",
    "Object.defineProperty",
    "Object.setPrototypeOf",
    "Reflect.defineProperty",
    "Reflect.deleteProperty",
    "Reflect.set",
    "Reflect.setPrototypeOf",
  ]);
  let unsafe = false;
  const visit = (node) => {
    if (unsafe) return;
    if (
      ts.isBinaryExpression(node) &&
      node.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
      node.operatorToken.kind <= ts.SyntaxKind.LastAssignment &&
      rootIsOwner(node.left)
    ) {
      unsafe = true;
      return;
    }
    if (
      (ts.isPrefixUnaryExpression(node) || ts.isPostfixUnaryExpression(node)) &&
      [ts.SyntaxKind.PlusPlusToken, ts.SyntaxKind.MinusMinusToken].includes(node.operator) &&
      rootIsOwner(node.operand)
    ) {
      unsafe = true;
      return;
    }
    if (ts.isDeleteExpression(node) && rootIsOwner(node.expression)) {
      unsafe = true;
      return;
    }
    if (
      ts.isCallExpression(node) &&
      mutators.has(canonicalMutator(node.expression)) &&
      node.arguments[0] &&
      rootIsOwner(node.arguments[0])
    ) {
      unsafe = true;
      return;
    }
    ts.forEachChild(node, visit);
  };
  visit(owner);
  return unsafe;
}

function assertNoBoundClassRuntimeMutation(handler, source, input, inputs) {
  const owner = enclosingClass(handler);
  if (!owner?.name || !ts.isIdentifier(owner.name)) {
    throw new Error("BOUND_CLASS_RUNTIME_MUTATION anonymous-bound-class");
  }
  const className = owner.name.text;
  const ownerModule = moduleWithoutExtension(input.file);
  if (ownerThisMutation(owner)) {
    throw new Error(`BOUND_CLASS_RUNTIME_MUTATION ${input.file}#${className}`);
  }
  const exportsByModule = boundClassExportGraph(ownerModule, className, inputs);
  for (const candidateInput of inputs) {
    if (!/\.[cm]?[jt]sx?$/u.test(candidateInput.file)) continue;
    const candidate =
      candidateInput.file === input.file
        ? source
        : parseSource(candidateInput.file, candidateInput.text);
    const aliases = new Set();
    const namespaces = new Map();
    if (candidateInput.file === input.file) aliases.add(className);
    for (const [local, imported] of importedSymbols(candidate)) {
      const importedModule = resolvedImport(candidateInput.file, imported.module);
      const exportedNames = exportsByModule.get(importedModule);
      if (imported.name === "*" && exportedNames) {
        namespaces.set(local, exportedNames);
      } else if (exportedNames?.has(imported.name)) {
        aliases.add(local);
      }
    }
    const requireAliases = new Set(["require"]);
    let aliasesChanged = true;
    while (aliasesChanged) {
      aliasesChanged = false;
      const collectRequireAliases = (node) => {
        if (
          ts.isVariableDeclaration(node) &&
          ts.isIdentifier(node.name) &&
          node.initializer &&
          ts.isIdentifier(unwrapPureExpression(node.initializer)) &&
          requireAliases.has(unwrapPureExpression(node.initializer).text) &&
          !requireAliases.has(node.name.text)
        ) {
          requireAliases.add(node.name.text);
          aliasesChanged = true;
        }
        ts.forEachChild(node, collectRequireAliases);
      };
      collectRequireAliases(candidate);
    }
    const collectRequires = (node) => {
      if (!ts.isVariableDeclaration(node) || !node.initializer) {
        ts.forEachChild(node, collectRequires);
        return;
      }
      const initializer = unwrapPureExpression(node.initializer);
      const directModule = requireCallModule(initializer, candidateInput.file, requireAliases);
      const propertyModule = ts.isPropertyAccessExpression(initializer)
        ? requireCallModule(initializer.expression, candidateInput.file, requireAliases)
        : null;
      if (directModule && exportsByModule.has(directModule)) {
        const exportedNames = exportsByModule.get(directModule);
        if (ts.isIdentifier(node.name)) namespaces.set(node.name.text, exportedNames);
        if (ts.isObjectBindingPattern(node.name)) {
          for (const element of node.name.elements) {
            const exportedName = (element.propertyName ?? element.name).getText(candidate);
            if (exportedNames.has(exportedName) && ts.isIdentifier(element.name)) {
              aliases.add(element.name.text);
            }
          }
        }
      }
      if (
        propertyModule &&
        exportsByModule.get(propertyModule)?.has(initializer.name.text) &&
        ts.isIdentifier(node.name)
      ) {
        aliases.add(node.name.text);
      }
      ts.forEachChild(node, collectRequires);
    };
    collectRequires(candidate);
    if (aliases.size === 0 && namespaces.size === 0) continue;
    let unsafe = false;
    const visit = (node) => {
      if (unsafe) return;
      if (
        ts.isPropertyAccessExpression(node) &&
        ts.isIdentifier(node.expression) &&
        namespaces.get(node.expression.text)?.has(node.name.text) &&
        !directModuleMetadataArrayReference(node, "controllers", candidate, candidateInput)
      ) {
        unsafe = true;
        return;
      }
      if (ts.isIdentifier(node) && aliases.has(node.text)) {
        const declarationName = candidateInput.file === input.file && owner.name === node;
        if (
          !declarationName &&
          !identifierIsImportBinding(node) &&
          !directModuleMetadataArrayReference(node, "controllers", candidate, candidateInput)
        ) {
          unsafe = true;
          return;
        }
      }
      ts.forEachChild(node, visit);
    };
    visit(candidate);
    if (unsafe) {
      throw new Error(`BOUND_CLASS_RUNTIME_MUTATION ${input.file}#${className}`);
    }
  }
}

const CANONICAL_PROVIDER_TOKENS = Object.freeze([
  Object.freeze({
    name: "AccessPolicyOrganizationExecutionService",
    module: ORGANIZATION_EXECUTOR_MODULE,
    directProvider: true,
  }),
  Object.freeze({
    name: "InventoryPolicyExecutionService",
    module: INVENTORY_EXECUTOR_MODULE,
    directProvider: true,
  }),
  Object.freeze({ name: "JwtAuthGuard", module: JWT_AUTH_GUARD_MODULE, directProvider: true }),
  Object.freeze({
    name: "ORGANIZATION_POLICY_REGISTRY",
    module: ORGANIZATION_EXECUTOR_MODULE,
    directProvider: false,
  }),
  Object.freeze({
    name: "INVENTORY_POLICY_REGISTRY",
    module: INVENTORY_EXECUTOR_MODULE,
    directProvider: false,
  }),
]);

function exactCanonicalInjectReference(node, token, source, input) {
  const call = node.parent;
  const decorator = ts.isCallExpression(call) ? call.parent : null;
  const parameter = decorator && ts.isDecorator(decorator) ? decorator.parent : null;
  if (
    !ts.isCallExpression(call) ||
    call.arguments.length !== 1 ||
    call.arguments[0] !== node ||
    !ts.isDecorator(decorator) ||
    !ts.isParameter(parameter) ||
    !stableParameterModifiers(parameter) ||
    !matchesImportedSymbol(call.expression, source, input, "Inject", "@nestjs/common")
  ) {
    return false;
  }
  const type = parameter.type;
  return Boolean(
    type &&
    ts.isTypeReferenceNode(type) &&
    ts.isIdentifier(type.typeName) &&
    matchesImportedSymbol(type.typeName, source, input, token.name, token.module),
  );
}

function exactCanonicalGuardReference(node, token, source, input) {
  if (token.name !== "JwtAuthGuard") return false;
  const call = node.parent;
  return Boolean(
    ts.isCallExpression(call) &&
    call.arguments.includes(node) &&
    ts.isDecorator(call.parent) &&
    matchesImportedSymbol(call.expression, source, input, "UseGuards", "@nestjs/common"),
  );
}

function exactCanonicalRegistryInjection(node, token, source, input) {
  if (token.directProvider) return false;
  const call = node.parent;
  return Boolean(
    ts.isCallExpression(call) &&
    call.arguments.length === 1 &&
    call.arguments[0] === node &&
    ts.isDecorator(call.parent) &&
    ts.isParameter(call.parent.parent) &&
    matchesImportedSymbol(call.expression, source, input, "Inject", "@nestjs/common"),
  );
}

function allowedCanonicalProviderReference(node, token, source, input) {
  if (identifierIsImportBinding(node)) return true;
  if (ts.isTypeReferenceNode(node.parent) && node.parent.typeName === node) return true;
  if (exactCanonicalInjectReference(node, token, source, input)) return true;
  if (exactCanonicalRegistryInjection(node, token, source, input)) return true;
  if (exactCanonicalGuardReference(node, token, source, input)) return true;
  return Boolean(
    token.directProvider &&
    (directModuleMetadataArrayReference(node, "providers", source, input) ||
      directModuleMetadataArrayReference(node, "exports", source, input)),
  );
}

function staticModuleText(node, constants = new Map(), seen = new Set()) {
  const value = unwrapPureExpression(node);
  if (ts.isStringLiteralLike(value) || ts.isNoSubstitutionTemplateLiteral(value)) {
    return value.text;
  }
  if (ts.isBinaryExpression(value) && value.operatorToken.kind === ts.SyntaxKind.PlusToken) {
    const left = staticModuleText(value.left, constants, seen);
    const right = staticModuleText(value.right, constants, seen);
    return left === null || right === null ? null : left + right;
  }
  if (ts.isIdentifier(value) && constants.has(value.text) && !seen.has(value.text)) {
    return staticModuleText(constants.get(value.text), constants, new Set([...seen, value.text]));
  }
  if (ts.isTemplateExpression(value)) {
    let result = value.head.text;
    for (const span of value.templateSpans) {
      const part = staticModuleText(span.expression, constants, seen);
      if (part === null) return null;
      result += part + span.literal.text;
    }
    return result;
  }
  return null;
}

function dynamicModuleLoad(node, constants) {
  if (!ts.isCallExpression(node) || node.arguments.length !== 1) return null;
  if (
    (ts.isIdentifier(node.expression) && node.expression.text === "require") ||
    node.expression.kind === ts.SyntaxKind.ImportKeyword
  ) {
    return { specifier: staticModuleText(node.arguments[0], constants) };
  }
  return null;
}

function assertNoCanonicalProviderOverrides(inputs) {
  const canonicalModules = new Set(CANONICAL_PROVIDER_TOKENS.map((token) => token.module));
  for (const input of inputs) {
    if (!/\.[cm]?[jt]sx?$/u.test(input.file)) continue;
    const source = parseSource(input.file, input.text);
    const symbols = importedSymbols(source);
    const constants = new Map();
    for (const statement of source.statements) {
      if (
        !ts.isVariableStatement(statement) ||
        (statement.declarationList.flags & ts.NodeFlags.Const) === 0
      ) {
        continue;
      }
      for (const declaration of statement.declarationList.declarations) {
        if (ts.isIdentifier(declaration.name) && declaration.initializer) {
          constants.set(declaration.name.text, declaration.initializer);
        }
      }
    }
    let unsafe = false;
    const visit = (node) => {
      if (unsafe) return;
      const moduleLoad = dynamicModuleLoad(node, constants);
      if (
        moduleLoad &&
        moduleLoad.specifier !== null &&
        canonicalModules.has(resolvedImport(input.file, moduleLoad.specifier))
      ) {
        unsafe = true;
        return;
      }
      const reference = importedReference(node, symbols);
      const token = reference
        ? CANONICAL_PROVIDER_TOKENS.find(
            (candidate) =>
              reference.name === candidate.name &&
              resolvedImport(input.file, reference.module) === candidate.module,
          )
        : null;
      if (token && !allowedCanonicalProviderReference(node, token, source, input)) {
        unsafe = true;
        return;
      }
      ts.forEachChild(node, visit);
    };
    visit(source);
    if (unsafe) throw new Error(`CANONICAL_PERMISSION_PROVIDER_OVERRIDE ${input.file}`);
  }
}

function identifierIsStaticPropertyName(node) {
  const parent = node.parent;
  return Boolean(
    (ts.isPropertyAccessExpression(parent) && parent.name === node) ||
    ((ts.isPropertyAssignment(parent) ||
      ts.isMethodDeclaration(parent) ||
      ts.isPropertyDeclaration(parent) ||
      ts.isGetAccessorDeclaration(parent) ||
      ts.isSetAccessorDeclaration(parent)) &&
      parent.name === node &&
      !ts.isComputedPropertyName(parent.name)),
  );
}

function requestParameterIsStable(handler, parameter, approvedReference) {
  if (
    !handler.body ||
    !ts.isIdentifier(parameter.name) ||
    parameter.initializer ||
    parameter.dotDotDotToken ||
    parameter.questionToken
  ) {
    return false;
  }
  const requestName = parameter.name.text;
  const matchingParameters = handler.parameters.filter((candidate) =>
    bindingContainsName(candidate.name, requestName),
  );
  if (matchingParameters.length !== 1) return false;

  let stable = true;
  const visit = (node) => {
    if (!stable) return;
    if (
      ts.isIdentifier(node) &&
      node.text === requestName &&
      node !== approvedReference &&
      !identifierIsStaticPropertyName(node)
    ) {
      stable = false;
      return;
    }
    ts.forEachChild(node, visit);
  };
  visit(handler.body);
  return stable;
}

function trustedActorArgument(call, proof, handler, source, input) {
  const actor = unwrapPureExpression(call.arguments[proof.actorIndex]);
  if (
    !ts.isCallExpression(actor) ||
    !matchesImportedSymbol(
      actor.expression,
      source,
      input,
      "permissionActorFromRequest",
      APPROVED_BOUNDARY_MODULE,
    ) ||
    actor.arguments.length !== 1 ||
    !ts.isIdentifier(actor.arguments[0]) ||
    !canonicalExecutionDecorators(handler, source, input)
  ) {
    return false;
  }
  const requestName = actor.arguments[0].text;
  const parameter = handler.parameters?.find(
    (candidate) => ts.isIdentifier(candidate.name) && candidate.name.text === requestName,
  );
  if (!parameter) return false;
  const symbols = importedSymbols(source);
  const parameterDecorators = decorators(parameter, source, symbols);
  const requestParameters = handler.parameters.filter((candidate) =>
    decorators(candidate, source, symbols).some(
      (decorator) => decorator.module === "@nestjs/common" && decorator.name === "Req",
    ),
  );
  return Boolean(
    requestParameters.length === 1 &&
    requestParameters[0] === parameter &&
    parameterDecorators.length === 1 &&
    parameterDecorators[0].module === "@nestjs/common" &&
    parameterDecorators[0].name === "Req" &&
    parameterDecorators[0].args.length === 0 &&
    requestParameterIsStable(handler, parameter, actor.arguments[0]),
  );
}

function approvedBoundaryCall(call, source, input, proof) {
  return matchesImportedSymbol(
    call.expression,
    source,
    input,
    proof.name,
    APPROVED_BOUNDARY_MODULE,
  );
}

function exactPermissionArgument(call, entry, index) {
  const permission = call.arguments[index];
  if (!permission || !ts.isObjectLiteralExpression(permission)) return false;
  if (permission.properties.length !== 2) return false;
  const properties = new Map();
  for (const property of permission.properties) {
    if (!ts.isPropertyAssignment(property) || ts.isComputedPropertyName(property.name))
      return false;
    const name = ts.isIdentifier(property.name)
      ? property.name.text
      : ts.isStringLiteralLike(property.name)
        ? property.name.text
        : null;
    if (!name || properties.has(name)) return false;
    properties.set(name, property.initializer);
  }
  if ([...properties.keys()].some((name) => !["resourceKey", "action"].includes(name))) {
    return false;
  }
  const resource = properties.get("resourceKey");
  const action = properties.get("action");
  return Boolean(
    resource &&
    ts.isStringLiteralLike(resource) &&
    resource.text === entry.resourceKey &&
    action &&
    ts.isStringLiteralLike(action) &&
    action.text === entry.action,
  );
}

function verifyOneBindingProof(entry, surface, input, inputs) {
  const source = parseSource(input.file, input.text);
  const handler = surface.handler && handlerNode(source, surface);
  if (!handler) throw new Error(`MISSING_BOUND_HANDLER ${entry.id}`);
  if (!stableBoundHandlerParameters(handler, source)) {
    throw new Error(`UNSAFE_BOUND_HANDLER_PARAMETER ${entry.id}`);
  }
  assertNoBoundClassRuntimeMutation(handler, source, input, inputs);
  assertThinHandler(handler, entry);
  const proof = PROOF_BOUNDARIES[entry.bindingProof.kind];
  if (!proof || proof.adapter !== entry.bindingProof.enforcementAdapter) {
    throw new Error(`MISSING_APPROVED_RUNTIME_BOUNDARY ${entry.id}`);
  }
  const calls = directReturnCalls(handler);
  if (
    calls.length === 0 ||
    calls.some((call) => !call || !approvedBoundaryCall(call, source, input, proof))
  ) {
    throw new Error(`MISSING_APPROVED_RUNTIME_BOUNDARY ${entry.id}`);
  }
  for (const call of calls) {
    assertPureBoundaryArguments(call, proof, entry, handler);
    if (!canonicalExecutionDecorators(handler, source, input)) {
      throw new Error(`UNSAFE_BOUND_DECORATOR ${entry.id}`);
    }
    if (proof.permissionIndex !== undefined) {
      if (!exactPermissionArgument(call, entry, proof.permissionIndex)) {
        throw new Error(`MISSING_BOUND_PERMISSION_ARGUMENT ${entry.id}`);
      }
    } else {
      if (
        !matchesImportedSymbol(
          call.arguments[proof.manifestIndex],
          source,
          input,
          "SIGNALO_PERMISSION_MANIFEST",
          PERMISSION_MANIFEST_MODULE,
        )
      ) {
        throw new Error(`MISSING_CODE_DEFINED_REPORT_MANIFEST ${entry.id}`);
      }
      const reportId = call.arguments[proof.reportIdIndex];
      if (
        !reportId ||
        !ts.isStringLiteralLike(reportId) ||
        reportId.text !== entry.codeDefinedReportId
      ) {
        throw new Error(`DYNAMIC_OR_MISSING_REPORT_ID ${entry.id}`);
      }
      if (surface.dynamicReportDispatch && handler.parameters.length !== 1) {
        throw new Error(`DYNAMIC_REPORT_INPUT_CAPTURE ${entry.id}`);
      }
    }
    if (!trustedExecutorArgument(call, proof, handler, source, input)) {
      throw new Error(`IMPURE_BOUNDARY_ARGUMENT ${entry.id}`);
    }
    if (!trustedActorArgument(call, proof, handler, source, input)) {
      throw new Error(`UNTRUSTED_PERMISSION_ACTOR ${entry.id}`);
    }
  }
}

/** Static source proof only; it does not claim runtime mount or guard execution. */
export function verifySurfaceBindingProofs(surfaces, ledger, inputs) {
  const surfaceById = new Map(surfaces.map((surface) => [surface.id, surface]));
  const inputByFile = new Map(inputs.map((input) => [input.file, input]));
  const fixedRecords = createFixedRecordReportProof(inputs);
  const freshReports = new Map();
  for (const entry of ledger.entries) {
    if (
      entry.disposition !== "EXEMPT" ||
      entry.replacedBy ||
      (!entry.tags.includes("report") && !entry.fixedRecordReportProofs)
    )
      continue;
    const input = inputByFile.get(entry.file);
    if (!input) {
      if (entry.fixedRecordReportProofs)
        throw new Error(`MISSING_FIXED_RECORD_REPORT_SOURCE ${entry.id}`);
      continue;
    }
    if (!freshReports.has(entry.file)) {
      const discovery = discoverSurfaces([input]);
      if (discovery.issues.length) throw new Error(`SOURCE_DISCOVERY_ISSUE ${entry.file}`);
      freshReports.set(entry.file, [
        ...discovery.surfaces.map((surface) => normalizedSurface(surface, input.text)),
        ...permissionSourceSentinels(input, discovery.surfaces, fixedRecords),
      ]);
    }
    const fresh = freshReports.get(entry.file).find((surface) => surface.id === entry.id);
    if (!fresh || fresh.dynamicReportDispatch)
      throw new Error(`DYNAMIC_REPORT_REQUIRES_BINDING ${entry.id}`);
    if (stable(fresh.fixedRecordReportProofs) !== stable(entry.fixedRecordReportProofs)) {
      throw new Error(`FIXED_RECORD_REPORT_PROOF_DRIFT ${entry.id}`);
    }
  }
  let bound = 0;
  if (ledger.entries.some((entry) => entry.disposition === "BOUND" && !entry.replacedBy)) {
    assertNoCanonicalProviderOverrides(inputs);
  }
  for (const entry of ledger.entries) {
    if (
      entry.kind === "permission-source-tombstone" ||
      entry.kind === "permission-surface-tombstone"
    ) {
      if (entry.disposition === "BOUND") {
        throw new Error(`SOURCE_TOMBSTONE_CANNOT_BE_BOUND ${entry.id}`);
      }
      continue;
    }
    if (entry.disposition !== "BOUND" || entry.replacedBy) continue;
    if (entry.kind === "permission-source-sentinel") {
      throw new Error(`SOURCE_SENTINEL_CANNOT_BE_BOUND ${entry.id}`);
    }
    const surface = surfaceById.get(entry.id);
    if (!surface) throw new Error(`UNKNOWN_BOUND_SURFACE ${entry.id}`);
    const input = inputByFile.get(surface.handlerFile ?? surface.file);
    if (!input) throw new Error(`MISSING_BOUND_SOURCE ${entry.id}`);
    verifyOneBindingProof(entry, surface, input, inputs);
    bound += 1;
  }
  return bound;
}

function repositoryRoot() {
  return resolve(dirname(fileURLToPath(import.meta.url)), "../..");
}

function boundedPath(root, value) {
  const path = resolve(root, value);
  if (!path.startsWith(`${root}${sep}`)) throw new Error("LEDGER_PATH_OUTSIDE_REPOSITORY");
  return path;
}

function writeFileAtomic(path, contents) {
  const tmp = `${path}.${process.pid}.tmp`;
  writeFileSync(tmp, contents);
  return tmp;
}

/**
 * The only array field these JSON files ever hold is a short `tags` string
 * array, and the repo's prettier config (printWidth 100) always collapses it
 * onto one line — but `JSON.stringify(value, null, 2)` always spreads it
 * across lines. Without reconciling that, every `--classify`/`--bootstrap`
 * write gets silently reformatted whole-file by the next pre-commit prettier
 * pass (a one-array-per-line diff turning into a many-thousand-line diff),
 * which both hides the real change from reviewers and guarantees any two
 * concurrent classify runs conflict on lines neither of them touched. This
 * reproduces prettier's own collapsing for exactly that shape so the file
 * already matches what pre-commit would produce.
 */
export function formatLedgerJson(value) {
  const raw = `${JSON.stringify(value, null, 2)}\n`;
  return raw.replace(/"tags": \[\n(\s+"[^"]*"(?:,\n\s+"[^"]*")*)\n\s*\]/gu, (match, body) => {
    const items = body.split(/,\n\s*/u).map((item) => item.trim());
    return `"tags": [${items.join(", ")}]`;
  });
}

const CLASSIFY_DECISION_FIELDS = {
  BOUND: new Set([
    "id",
    "disposition",
    "resourceKey",
    "action",
    "bindingProof",
    "codeDefinedReportId",
    "replaces",
  ]),
  EXEMPT: new Set(["id", "disposition", "reason", "owner", "ticket", "replaces"]),
  RETIRED: new Set(["id", "disposition", "reason", "owner", "ticket"]),
};

function isSentinelId(id) {
  return SOURCE_SENTINEL_ID.test(id ?? "");
}

function isReplaceableFingerprintId(id) {
  return isSentinelId(id) || WORKER_CONTENT_ID.test(id ?? "");
}

/**
 * Read-only survey of every gap the gate would currently reject, collected in one pass
 * instead of the single-error-at-a-time failure `verifySurfaceLedger` throws — so a
 * developer (or this audit) can see the whole `--classify decisions.json` they need to
 * write before running anything, instead of discovering gaps one CI run at a time.
 * Splits unclassified surfaces into genuinely new entry points (routes/handlers/actions)
 * versus mere content-hash fingerprint changes, and for each fingerprint, names the
 * removable predecessor in the same file/family so its `replaces` value is copy-pasteable.
 */
export function surfaceLedgerGaps(surfaces, ledger) {
  const recorded = new Map(ledger.entries.map((entry) => [entry.id, entry]));
  const current = new Map(surfaces.map((surface) => [surface.id, surface]));
  const removable = ledger.entries.filter(
    (entry) =>
      !current.has(entry.id) &&
      !entry.replacedBy &&
      !entry.retiredBy &&
      entry.disposition !== "RETIRED",
  );
  const removableSentinelsByFamily = new Map();
  for (const entry of removable) {
    if (!isSentinelId(entry.id)) continue;
    removableSentinelsByFamily.set(replacementFamily(entry.id), entry.id);
  }
  const newEntryPoints = [];
  const newFingerprints = [];
  for (const surface of surfaces) {
    if (recorded.has(surface.id)) continue;
    if (isSentinelId(surface.id)) {
      newFingerprints.push({
        id: surface.id,
        replaces: removableSentinelsByFamily.get(replacementFamily(surface.id)) ?? null,
      });
    } else {
      newEntryPoints.push(surface.id);
    }
  }
  return {
    newEntryPoints,
    newFingerprints,
    removable: removable.map((entry) => entry.id),
  };
}

/**
 * True when `entry` already reflects exactly what re-applying `decision` against the
 * live `surface`/`predecessor` state would produce — a `--classify` re-run (e.g. a CI
 * retry after a transient failure) must be able to see the exact same decisions file
 * twice and succeed the second time as a no-op, not fail as though the ids were already
 * "taken" by someone else's unrelated change.
 */
function decisionAlreadyApplied(entry, expected) {
  if (!entry) return false;
  // Same reasoning as `driftComparableIdentity`: `handlerLine` can legitimately differ
  // between the stored entry and a freshly recomputed `expected` (an unrelated edit
  // elsewhere in the file shifted it again since the first apply) without the retried
  // decision actually being any different — that must still count as the same decision,
  // not a conflict.
  const { handlerLine: _entryLine, ...entryRest } = entry;
  if (!expected) return stable(entryRest) === stable(expected);
  const { handlerLine: _expectedLine, ...expectedRest } = expected;
  return stable(entryRest) === stable(expectedRest);
}

/**
 * Applies a small, explicit batch of reviewed decisions to the existing ledger/baseline
 * without rebuilding either from scratch. Every decision must resolve exactly one gate
 * gap that already exists on disk:
 *   - a newly discovered, not-yet-classified surface (BOUND/EXEMPT);
 *   - a real entry point (route/handler/action) that disappeared from discovery
 *     (RETIRED, via a per-action tombstone);
 *   - a whole file's content-hash sentinel that disappeared from discovery because the
 *     file itself was deleted (RETIRED on the sentinel id, via a whole-file tombstone —
 *     every other now-gone surface that belonged to that same file is retired under the
 *     same tombstone automatically, since that follows mechanically from "the file is
 *     gone," not from a separate judgment call);
 *   - a whole file's content-hash sentinel that disappeared because the file's content
 *     changed in place (EXEMPT with `replaces` pointing at the old sentinel id) — this
 *     and the content-addressed normalized Worker parser family already supported
 *     by the verifier. These are the ONLY cases `replaces` is accepted for, and
 *     neither carries forward the old `reason`/`owner`/`ticket`: the decision must state its own, explicit,
 *     freshly reviewed justification for the new content, because "the file used to be
 *     fine" is not evidence the new content still is.
 * This is what keeps the tool from ever being able to auto-classify EXEMPT/LEGACY on
 * its own, silently touch an already-classified id's meaning, or erase/downgrade
 * anything already recorded. A decision that exactly reproduces an already-applied
 * change (same predecessor, same successor content) is treated as a no-op, not an
 * error, so retrying the same decisions file is safe; a decision that targets an id
 * already resolved DIFFERENTLY is rejected as a conflict, never silently overwritten.
 * The incoming ledger/baseline are checked for self-consistency first (so a
 * hand-tampered on-disk file can't be silently re-sealed with a fresh hash), and full
 * verifySurfaceLedger/verifySurfaceBindingProofs validation runs on the result before
 * any write.
 */
export function classifySurfaceLedger({
  surfaces,
  inputs,
  ledger,
  baseline,
  decisionDocument,
  continuation,
}) {
  const { contentHash: incomingHash, ...incomingContent } = ledger ?? {};
  if (!ledger || incomingHash !== digest(incomingContent)) {
    throw new Error("LEDGER_CONTENT_HASH_MISMATCH");
  }
  if (new Set(ledger.entries.map((entry) => entry.id)).size !== ledger.entries.length) {
    throw new Error("DUPLICATE_SURFACE_LEDGER_ENTRY");
  }
  validateBaselineAnchor(baseline, ledger);

  if (!decisionDocument || !Array.isArray(decisionDocument.entries)) {
    throw new Error("INVALID_CLASSIFY_DECISIONS");
  }
  if (
    decisionDocument.entries.some(
      (decision) => !decision || typeof decision !== "object" || Array.isArray(decision),
    )
  ) {
    throw new Error("MALFORMED_CLASSIFY_DECISION");
  }
  const decisionIds = decisionDocument.entries.map((entry) => entry.id);
  if (decisionIds.some((id) => typeof id !== "string" || id.length === 0)) {
    throw new Error("MALFORMED_CLASSIFY_DECISION_ID");
  }
  if (new Set(decisionIds).size !== decisionIds.length) {
    throw new Error("DUPLICATE_CLASSIFY_DECISION");
  }

  const recorded = new Map(ledger.entries.map((entry) => [entry.id, entry]));
  const current = new Map(surfaces.map((surface) => [surface.id, surface]));
  const unclassifiedIds = new Set(
    surfaces.filter((surface) => !recorded.has(surface.id)).map((surface) => surface.id),
  );
  const removableIds = new Set(
    ledger.entries
      .filter(
        (entry) =>
          !current.has(entry.id) &&
          !entry.replacedBy &&
          !entry.retiredBy &&
          entry.disposition !== "RETIRED",
      )
      .map((entry) => entry.id),
  );

  const additions = [];
  const retiredByUpdates = new Map();
  const replacedByUpdates = new Map();
  const newEntryPoints = [];
  const newFingerprints = [];
  const alreadyApplied = [];

  for (const decision of decisionDocument.entries) {
    const { id, disposition } = decision;
    const allowedFields = CLASSIFY_DECISION_FIELDS[disposition];
    if (!allowedFields) throw new Error(`INVALID_CLASSIFY_DISPOSITION ${id}`);
    for (const key of Object.keys(decision)) {
      if (!allowedFields.has(key))
        throw new Error(`UNEXPECTED_CLASSIFY_DECISION_FIELD ${id}:${key}`);
    }

    if (disposition === "RETIRED") {
      const existing = recorded.get(id);
      if (existing?.kind === "permission-source-sentinel" && existing.replacedBy) {
        const [, family, file, hash] = SOURCE_SENTINEL_ID.exec(id) ?? [];
        const expectedTombstoneId = `permission-source-tombstone:${family}:${file}#removed:${hash}`;
        if (existing.replacedBy !== expectedTombstoneId) {
          throw new Error(`CLASSIFY_DECISION_CONFLICTS_WITH_EXISTING_STATE ${id}`);
        }
        // Same tombstone id — but id equality alone doesn't prove it's the SAME
        // decision: this id encodes only family/file/hash, never reason/owner/ticket,
        // so a resubmitted RETIRED with a materially different reason must still be
        // rejected as a conflict, not silently dropped as a no-op.
        const recordedTombstone = recorded.get(expectedTombstoneId);
        const freshTombstone = buildSourceRemovalTombstone(existing, {
          reason: decision.reason,
          owner: decision.owner,
          ticket: decision.ticket,
        });
        if (!decisionAlreadyApplied(recordedTombstone, freshTombstone)) {
          throw new Error(`CLASSIFY_DECISION_CONFLICTS_WITH_EXISTING_STATE ${id}`);
        }
        alreadyApplied.push(id);
        continue;
      } else if (existing?.retiredBy) {
        const expectedTombstoneId = `permission-surface-tombstone:${createHash("sha256").update(id).digest("hex")}`;
        if (existing.retiredBy !== expectedTombstoneId) {
          throw new Error(`CLASSIFY_DECISION_CONFLICTS_WITH_EXISTING_STATE ${id}`);
        }
        const recordedTombstone = recorded.get(expectedTombstoneId);
        const freshTombstone = buildActionRemovalTombstone(existing, {
          reason: decision.reason,
          owner: decision.owner,
          ticket: decision.ticket,
        });
        if (!decisionAlreadyApplied(recordedTombstone, freshTombstone)) {
          throw new Error(`CLASSIFY_DECISION_CONFLICTS_WITH_EXISTING_STATE ${id}`);
        }
        alreadyApplied.push(id);
        continue;
      }
      if (!removableIds.has(id)) throw new Error(`UNKNOWN_CLASSIFY_RETIRE_TARGET ${id}`);
      const predecessor = recorded.get(id);
      if (predecessor.kind === "permission-source-sentinel") {
        // Whole file deleted: every other surface that belonged to it is gone for the
        // exact same mechanical reason, so it's retired under the same tombstone —
        // that's a fact about the file, not a separate per-surface judgment call.
        const tombstone = buildSourceRemovalTombstone(predecessor, {
          reason: decision.reason,
          owner: decision.owner,
          ticket: decision.ticket,
        });
        replacedByUpdates.set(id, tombstone.id);
        additions.push(tombstone);
        for (const other of ledger.entries) {
          if (other.id === id) continue;
          if ((other.handlerFile ?? other.file) !== predecessor.file) continue;
          if (!removableIds.has(other.id)) continue;
          retiredByUpdates.set(other.id, tombstone.id);
        }
      } else {
        const tombstone = buildActionRemovalTombstone(predecessor, {
          reason: decision.reason,
          owner: decision.owner,
          ticket: decision.ticket,
        });
        retiredByUpdates.set(id, tombstone.id);
        additions.push(tombstone);
      }
      continue;
    }

    // BOUND / EXEMPT.
    if (decision.replaces) {
      if (!isReplaceableFingerprintId(id))
        throw new Error(`CLASSIFY_REPLACEMENT_UNSUPPORTED ${id}`);
      const predecessor = recorded.get(decision.replaces);
      if (!predecessor || !isReplaceableFingerprintId(predecessor.id)) {
        throw new Error(`INVALID_SENTINEL_REPLACEMENT_PREDECESSOR ${id}`);
      }
      if (replacementFamily(predecessor.id) !== replacementFamily(id)) {
        throw new Error(`SENTINEL_REPLACEMENT_FAMILY_MISMATCH ${id}`);
      }
      const surface = current.get(id);
      const expected =
        surface && decisionFor(surface, decision, ledger.legacyBoundaryCommit, false);
      if (predecessor.replacedBy === id && decisionAlreadyApplied(recorded.get(id), expected)) {
        alreadyApplied.push(id);
        continue;
      }
      if (predecessor.replacedBy && predecessor.replacedBy !== id) {
        throw new Error(`CLASSIFY_DECISION_CONFLICTS_WITH_EXISTING_STATE ${decision.replaces}`);
      }
      if (!removableIds.has(decision.replaces)) {
        throw new Error(`UNKNOWN_CLASSIFY_RETIRE_TARGET ${decision.replaces}`);
      }
      if (!surface || !unclassifiedIds.has(id)) throw new Error(`UNKNOWN_CLASSIFY_TARGET ${id}`);
      replacedByUpdates.set(decision.replaces, id);
      additions.push(expected);
      newFingerprints.push(id);
      continue;
    }
    const existing = recorded.get(id);
    if (existing) {
      const surface = current.get(id);
      const expected =
        surface && decisionFor(surface, decision, ledger.legacyBoundaryCommit, false);
      if (decisionAlreadyApplied(existing, expected)) {
        alreadyApplied.push(id);
        continue;
      }
      throw new Error(`CLASSIFY_DECISION_CONFLICTS_WITH_EXISTING_STATE ${id}`);
    }
    if (!unclassifiedIds.has(id)) throw new Error(`UNKNOWN_CLASSIFY_TARGET ${id}`);
    const entry = decisionFor(current.get(id), decision, ledger.legacyBoundaryCommit, false);
    additions.push(entry);
    (isSentinelId(id) ? newFingerprints : newEntryPoints).push(id);
  }

  const entries = [
    ...ledger.entries.map((entry) => {
      if (retiredByUpdates.has(entry.id))
        return { ...entry, retiredBy: retiredByUpdates.get(entry.id) };
      if (replacedByUpdates.has(entry.id))
        return { ...entry, replacedBy: replacedByUpdates.get(entry.id) };
      return entry;
    }),
    ...additions,
  ].sort((left, right) => compare(left.id, right.id));
  if (new Set(entries.map((entry) => entry.id)).size !== entries.length) {
    throw new Error("DUPLICATE_SURFACE_LEDGER_ENTRY");
  }

  const continued = continuation
    ? buildContinuedSourceLedger(continuation.root, ledger, entries, continuation.document)
    : null;
  const nextLedger = continued?.ledger ?? buildClassifiedSourceLedger(ledger, entries);
  const nextBaseline = buildLegacyBaselineAnchor(nextLedger, baseline);
  verifySurfaceLedger(surfaces, nextLedger, nextBaseline);
  verifySurfaceBindingProofs(surfaces, nextLedger, inputs);
  return {
    ledger: nextLedger,
    baseline: nextBaseline,
    ...(continued ? { continuationFragment: continued.fragment } : {}),
    newEntryPoints,
    newFingerprints,
    retired: [...retiredByUpdates.keys(), ...replacedByUpdates.keys()],
    alreadyApplied,
  };
}

async function verifyOwningHistory(root, evolutionBase, inputs, surfaces, owning) {
  const result = verifySurfaceLedger(surfaces, owning.ledger, owning.baseline);
  const sourceProofs = verifySurfaceBindingProofs(surfaces, owning.ledger, inputs);
  const { verifyPermissionRegistryEvolution } = await import("./evolution-gate.mjs");
  verifyPermissionRegistryEvolution(root, evolutionBase, owning);
  if (digest(readSourceInputs(root)) !== digest(inputs))
    throw new Error("PERMISSION_REGISTRY_PREFLIGHT_SOURCE_CHANGED");
  assertEvolutionSurfaceReaderCurrent(root, owning);
  return { sourceProofs, ...result };
}

// A separately pinned verifier may execute its own code against candidate DATA.
// No imports, hooks, configuration or dependencies are loaded from this root.
// The same owning validation and exact-base evolution are used by the CLI below.
export async function verifyNativeHistoryRepository(repositoryRoot, physicalBase) {
  const root = realpathSync(repositoryRoot);
  if (!/^[a-f0-9]{40}$/u.test(physicalBase)) throw new Error("INVALID_PERMISSION_REGISTRY_BASE");
  return withParsedInventory(async () => {
    const inputs = readSourceInputs(root);
    const surfaces = discoverPermissionSurfaces(inputs);
    const owning = readEvolutionSurfaceHistory(root);
    return Object.freeze(await verifyOwningHistory(root, physicalBase, inputs, surfaces, owning));
  });
}

async function main() {
  const root = repositoryRoot();
  const evolutionIndex = process.argv.indexOf("--evolution-base");
  const evolutionBase = evolutionIndex >= 0 ? process.argv[evolutionIndex + 1] : null;
  if (
    evolutionIndex >= 0 &&
    (!/^[a-f0-9]{40}$/u.test(evolutionBase ?? "") ||
      process.argv.slice(2).length !== 3 ||
      process.argv.slice(2).filter((arg) => arg === "--assemble").length !== 1 ||
      process.argv.slice(2).filter((arg) => arg === "--evolution-base").length !== 1)
  )
    throw new Error("INVALID_PERMISSION_REGISTRY_PREFLIGHT_ARGUMENTS");
  const defaultLedger = "scripts/permission-registry/permission-surface-ledger.json";
  const defaultBaseline = "scripts/permission-registry/permission-surface-baseline.json";
  const bootstrapIndex = process.argv.indexOf("--bootstrap-legacy");
  const classifyIndex = process.argv.indexOf("--classify");
  const inputs = readSourceInputs(root);
  const surfaces = discoverPermissionSurfaces(inputs);
  if (classifyIndex >= 0) {
    const decisionsPath = boundedPath(root, process.argv[classifyIndex + 1] ?? "");
    const ledgerArgIndex = process.argv.indexOf("--ledger");
    const baselineArgIndex = process.argv.indexOf("--baseline");
    const destination = boundedPath(
      root,
      ledgerArgIndex >= 0 ? process.argv[ledgerArgIndex + 1] : defaultLedger,
    );
    const baselineDestination = boundedPath(
      root,
      baselineArgIndex >= 0 ? process.argv[baselineArgIndex + 1] : defaultBaseline,
    );
    const dryRun = process.argv.includes("--dry-run");
    const showDiff = process.argv.includes("--diff");
    const useHistory = ledgerArgIndex < 0 && baselineArgIndex < 0;
    const continuationIndex = process.argv.indexOf("--source-head-continuations");
    const paired = continuationIndex >= 0;
    if (paired && !useHistory)
      throw new Error("SOURCE_HEAD_CONTINUATION_AUTHENTIC_READER_REQUIRED");
    // The paired publisher owns its initial fresh read and private transaction memo.
    // Avoid a discarded independent read before starting that transaction.
    const { ledger, baseline } = paired
      ? {}
      : useHistory
        ? readSurfaceHistory(root)
        : {
            ledger: JSON.parse(readFileSync(destination, "utf8")),
            baseline: JSON.parse(readFileSync(baselineDestination, "utf8")),
          };
    const decisionDocument = JSON.parse(readFileSync(decisionsPath, "utf8"));
    const continuationPath = paired
      ? boundedPath(root, process.argv[continuationIndex + 1] ?? "")
      : null;
    const publisher = paired ? await import("./source-head-publisher.mjs") : null;
    const result = paired
      ? publisher.preparePairedSourceClassification(root, decisionsPath, continuationPath)
      : classifySurfaceLedger({ surfaces, inputs, ledger, baseline, decisionDocument });
    const summary = {
      newEntryPoints: result.newEntryPoints,
      newFingerprints: result.newFingerprints,
      retired: result.retired,
      alreadyApplied: result.alreadyApplied,
    };
    if (showDiff || dryRun) {
      process.stdout.write(`${JSON.stringify({ ...summary, dryRun }, null, 2)}\n`);
    }
    if (!dryRun) {
      const fragment = paired
        ? publisher.publishPairedSourceClassification(root, result, {
            exclusiveWriter: process.argv.includes("--exclusive-source-history-writer"),
          })
        : useHistory
          ? writeSurfaceFragment(root, ledger, result.ledger)
          : null;
      if (!useHistory) {
        const ledgerTmp = writeFileAtomic(destination, formatLedgerJson(result.ledger));
        const baselineTmp = writeFileAtomic(baselineDestination, formatLedgerJson(result.baseline));
        renameSync(ledgerTmp, destination);
        renameSync(baselineTmp, baselineDestination);
      }
      process.stdout.write(
        `${JSON.stringify({
          ...(useHistory ? { fragment } : { ledger: destination, baseline: baselineDestination }),
          ...summary,
          contentHash: result.ledger.contentHash,
        })}\n`,
      );
    }
    return;
  }
  if (bootstrapIndex >= 0) {
    const destination = boundedPath(root, process.argv[bootstrapIndex + 1] ?? defaultLedger);
    const baselineDestination = boundedPath(
      root,
      process.argv[bootstrapIndex + 2] ?? defaultBaseline,
    );
    if (existsSync(destination) || existsSync(baselineDestination)) {
      throw new Error("LEGACY_LEDGER_ALREADY_EXISTS");
    }
    const decisionsPath = boundedPath(
      root,
      process.argv[bootstrapIndex + 3] ??
        "scripts/permission-registry/permission-surface-bootstrap-decisions.json",
    );
    const baseIndex = process.argv.indexOf("--base");
    const commit = process.argv[baseIndex + 1];
    if (baseIndex < 0) throw new Error("BOOTSTRAP_EXACT_BASE_REQUIRED");
    assertSig909BootstrapBase(commit);
    const decisionDocument = JSON.parse(readFileSync(decisionsPath, "utf8"));
    const { contentHash: decisionHash, ...decisionContent } = decisionDocument;
    if (
      decisionDocument.schemaVersion !== 1 ||
      decisionDocument.task !== "SIG-909" ||
      decisionDocument.legacyBoundaryCommit !== commit ||
      !Array.isArray(decisionDocument.entries) ||
      decisionHash !== digest(decisionContent) ||
      new Set(decisionDocument.entries.map((entry) => entry.id)).size !==
        decisionDocument.entries.length
    ) {
      throw new Error("INVALID_BOOTSTRAP_DECISIONS");
    }
    const decisions = new Map(
      decisionDocument.entries.map(({ id, ...decision }) => [id, decision]),
    );
    const boundaryInputs = readSourceInputsAtGitCommit(root, commit);
    const boundarySurfaces = discoverPermissionSurfaces(boundaryInputs);
    const { ledger, baseline } = buildBootstrapLedger(boundarySurfaces, surfaces, {
      legacyBoundaryCommit: commit,
      decisions,
    });
    verifySurfaceLedger(surfaces, ledger, baseline);
    verifySurfaceBindingProofs(surfaces, ledger, inputs);
    mkdirSync(dirname(destination), { recursive: true });
    writeFileSync(destination, formatLedgerJson(ledger));
    writeFileSync(baselineDestination, formatLedgerJson(baseline));
    process.stdout.write(
      `${JSON.stringify({ ledger: destination, baseline: baselineDestination, bootstrapDecisions: decisionsPath, baselineAnchorHash: baseline.contentHash, contentHash: ledger.contentHash, checked: ledger.entries.length })}\n`,
    );
    return;
  }
  if (process.argv.includes("--gaps")) {
    const { ledger } = readSurfaceHistory(root);
    process.stdout.write(`${JSON.stringify(surfaceLedgerGaps(surfaces, ledger), null, 2)}\n`);
    return;
  }
  const assemble = process.argv.includes("--assemble");
  const useHistory = !process.argv[2] || assemble;
  const destination = boundedPath(root, useHistory ? defaultLedger : process.argv[2]);
  const baselineDestination = boundedPath(
    root,
    useHistory ? defaultBaseline : (process.argv[3] ?? defaultBaseline),
  );
  const owning = useHistory
    ? evolutionBase
      ? readEvolutionSurfaceHistory(root)
      : readSurfaceHistory(root)
    : null;
  const { ledger, baseline } = owning ?? {
    ledger: JSON.parse(readFileSync(destination, "utf8")),
    baseline: JSON.parse(readFileSync(baselineDestination, "utf8")),
  };
  const result = evolutionBase
    ? await verifyOwningHistory(root, evolutionBase, inputs, surfaces, owning)
    : {
        ...verifySurfaceLedger(surfaces, ledger, baseline),
        sourceProofs: verifySurfaceBindingProofs(surfaces, ledger, inputs),
      };
  if (assemble) {
    const ledgerTmp = writeFileAtomic(destination, formatLedgerJson(ledger));
    const baselineTmp = writeFileAtomic(baselineDestination, formatLedgerJson(baseline));
    renameSync(ledgerTmp, destination);
    renameSync(baselineTmp, baselineDestination);
  }
  process.stdout.write(
    `${JSON.stringify({ ledger: destination, baseline: baselineDestination, ...result })}\n`,
  );
  if (evolutionBase)
    process.stdout.write(`permission registry evolution valid from ${evolutionBase}\n`);
}

if (process.argv[1] && realpathSync(process.argv[1]) === fileURLToPath(import.meta.url))
  withParsedInventory(main).catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
