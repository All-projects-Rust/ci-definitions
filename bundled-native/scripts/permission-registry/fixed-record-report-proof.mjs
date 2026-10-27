/**
 * A deliberately closed proof of a route parameter's record-value use. This is
 * classification evidence, never permission enforcement or a BOUND adapter.
 * Unknown syntax, injection or value escape leaves the old dynamic gate closed.
 */
import { createHash } from "node:crypto";
import { posix } from "node:path";
import {
  decorators,
  importedSymbols,
  parseSource,
  staticValue,
  ts,
} from "../access-census/ast.mjs";

const CANONICAL = Object.freeze({
  permission: [
    "ShadowAccessPermission",
    "apps/api/src/modules/access-control/access-policy.shadow-guard",
  ],
  jwt: ["JwtAuthGuard", "apps/api/src/modules/auth/jwt-auth.guard"],
  guard: ["DomainPolicyGuard", "apps/api/src/medical/data/access-policy/domain-policy.guard"],
  interceptor: [
    "DomainPolicyInterceptor",
    "apps/api/src/medical/data/access-policy/domain-policy.interceptor",
  ],
  boundary: [
    "AccessPolicyRecordQueryService",
    "apps/api/src/modules/access-control/access-policy.record-query",
  ],
});
const stripExtension = (file) => file.replace(/\.[cm]?[jt]sx?$/u, "");
const moduleOf = (file, specifier) =>
  specifier.startsWith(".")
    ? stripExtension(posix.normalize(posix.join(posix.dirname(file), specifier)))
    : stripExtension(specifier);
const hash = (text) => createHash("sha256").update(text).digest("hex");
const fail = () => {
  throw new Error("UNPROVEN_FIXED_RECORD_REPORT");
};
const requireProof = (value) => {
  if (!value) fail();
  return value;
};
const visit = (node, fn) => {
  fn(node);
  ts.forEachChild(node, (child) => visit(child, fn));
};
const mods = (node, kind) =>
  (ts.getModifiers(node) ?? []).some((modifier) => modifier.kind === kind);
const literal = (node) => (node && ts.isStringLiteral(node) ? node.text : null);
const named = (node) => (node?.name && ts.isIdentifier(node.name) ? node.name.text : null);
const thisProperty = (node) =>
  ts.isPropertyAccessExpression(node) && node.expression.kind === ts.SyntaxKind.ThisKeyword
    ? node.name.text
    : null;
const property = (node, name) => ts.isPropertyAccessExpression(node) && node.name.text === name;
const call = (node) => node && ts.isCallExpression(node);
const unparen = (node) => (ts.isParenthesizedExpression(node) ? unparen(node.expression) : node);
const oneReturn = (node) =>
  node?.body &&
  ts.isBlock(node.body) &&
  node.body.statements.length === 1 &&
  ts.isReturnStatement(node.body.statements[0])
    ? node.body.statements[0].expression
    : null;
const references = (root, name) => {
  const found = [];
  visit(root, (node) => {
    if (!ts.isIdentifier(node) || node.text !== name) return;
    const parent = node.parent;
    if (
      (ts.isPropertyAccessExpression(parent) && parent.name === node) ||
      ((ts.isPropertyAssignment(parent) || ts.isMethodDeclaration(parent)) && parent.name === node)
    )
      return;
    found.push(node);
  });
  return found;
};

function unshadowed(root, names, allowedDeclaration = null) {
  const binding = (name) => {
    if (ts.isIdentifier(name)) {
      if (names.has(name.text)) fail();
      return;
    }
    for (const element of name.elements ?? [])
      if (ts.isBindingElement(element)) binding(element.name);
  };
  visit(root, (node) => {
    if (node === allowedDeclaration) return;
    if (
      (ts.isVariableDeclaration(node) ||
        ts.isParameter(node) ||
        ts.isFunctionDeclaration(node) ||
        ts.isClassDeclaration(node) ||
        ts.isBindingElement(node)) &&
      node.name
    ) {
      binding(node.name);
    }
  });
}

// Runtime lexical bindings, indexed once per supplied AST. A nested declaration
// shadows only its lexical scope; static member names and erased types do not
// reference the imported value. Ambiguous bindings remain unsupported.
const lexicalIndexes = new WeakMap();
function lexicalIndex(root) {
  if (lexicalIndexes.has(root)) return lexicalIndexes.get(root);
  const scopes = new Map();
  const scope = (node, functionOnly = false) => {
    for (let current = node; current; current = current.parent)
      if (
        ts.isSourceFile(current) ||
        ts.isFunctionLike(current) ||
        (!functionOnly &&
          (ts.isBlock(current) ||
            ts.isCaseBlock(current) ||
            ts.isForStatement(current) ||
            ts.isForInStatement(current) ||
            ts.isForOfStatement(current) ||
            ts.isCatchClause(current) ||
            ts.isClassLike(current) ||
            ts.isModuleBlock(current)))
      )
        return current;
    fail();
  };
  const bind = (owner, name) => {
    if (!name) return;
    if (!ts.isIdentifier(name)) {
      for (const item of name.elements ?? []) if (ts.isBindingElement(item)) bind(owner, item.name);
      return;
    }
    if (!scopes.has(owner)) scopes.set(owner, new Map());
    const names = scopes.get(owner);
    names.set(name.text, names.has(name.text) && names.get(name.text) !== name ? false : name);
  };
  visit(root, (node) => {
    if (ts.isImportClause(node)) bind(root, node.name);
    if (
      ts.isImportSpecifier(node) ||
      ts.isNamespaceImport(node) ||
      ts.isImportEqualsDeclaration(node)
    )
      bind(root, node.name);
    if (ts.isVariableDeclaration(node)) {
      if (ts.isCatchClause(node.parent)) bind(node.parent, node.name);
      else if (ts.isVariableDeclarationList(node.parent))
        bind(scope(node.parent.parent, !(node.parent.flags & ts.NodeFlags.BlockScoped)), node.name);
    }
    if (ts.isParameter(node)) bind(node.parent, node.name);
    if (
      ts.isFunctionDeclaration(node) ||
      ts.isClassDeclaration(node) ||
      ts.isEnumDeclaration(node) ||
      ts.isModuleDeclaration(node)
    )
      bind(scope(node.parent), node.name);
    if (ts.isFunctionExpression(node) || ts.isClassLike(node)) bind(node, node.name);
  });
  const result = (ref) => {
    for (let current = ref; current; current = current.parent) {
      const names = scopes.get(current);
      if (names?.has(ref.text)) return requireProof(names.get(ref.text));
    }
    return undefined;
  };
  lexicalIndexes.set(root, result);
  return result;
}
function erasedReference(node) {
  for (let current = node; current; current = current.parent) {
    if (
      ts.isTypeNode(current) ||
      ts.isInterfaceDeclaration(current) ||
      ts.isTypeAliasDeclaration(current)
    )
      return true;
    if (ts.isStatement(current) || ts.isFunctionLike(current)) break;
  }
  return false;
}
function valueReference(node) {
  const parent = node.parent;
  return !(
    (ts.isJsxAttribute(parent) && parent.name === node) ||
    (ts.isPropertyAccessExpression(parent) && parent.name === node) ||
    ((ts.isPropertyAssignment(parent) ||
      ts.isPropertyDeclaration(parent) ||
      ts.isPropertySignature(parent) ||
      ts.isMethodDeclaration(parent) ||
      ts.isMethodSignature(parent) ||
      ts.isBindingElement(parent)) &&
      parent.name === node &&
      !ts.isBindingElement(parent)) ||
    (ts.isBindingElement(parent) && parent.propertyName === node) ||
    ts.isImportSpecifier(parent) ||
    ts.isImportClause(parent) ||
    ts.isNamespaceImport(parent)
  );
}
function importedBinding(input, name) {
  const result = [];
  for (const statement of input.ast.statements) {
    if (!ts.isImportDeclaration(statement)) continue;
    const clause = statement.importClause;
    if (clause?.name?.text === name) result.push(clause.name);
    const bindings = clause?.namedBindings;
    if (bindings && ts.isNamespaceImport(bindings) && bindings.name.text === name)
      result.push(bindings.name);
    if (bindings && ts.isNamedImports(bindings))
      for (const entry of bindings.elements) if (entry.name.text === name) result.push(entry.name);
  }
  return requireProof(result.length === 1 && result[0]);
}
function importedReference(node, input) {
  return (
    ts.isIdentifier(node) &&
    input.symbols.has(node.text) &&
    lexicalIndex(input.ast)(node) === importedBinding(input, node.text)
  );
}

/** Explicit finite runtime boundary; no ambient Nest/global mutation guarantee. */
export function createFixedRecordReportProof(inputs) {
  const raw = new Map();
  for (const input of inputs) {
    requireProof(!raw.has(input.file));
    raw.set(input.file, input);
  }
  const parsed = new Map(),
    cache = new Map();
  function source(file) {
    if (!parsed.has(file)) {
      const input = requireProof(raw.get(file));
      const ast = parseSource(file, input.text);
      requireProof(!ast.parseDiagnostics.length);
      parsed.set(file, { ...input, ast, symbols: importedSymbols(ast) });
    }
    return parsed.get(file);
  }
  function reference(node, input) {
    if (!node || !ts.isIdentifier(node)) return null; // no namespace/computed/alias proof
    const ref = input.symbols.get(node.text);
    if (!ref || ref.name !== node.text || ref.name === "*" || !importedReference(node, input))
      return null;
    return { name: ref.name, module: moduleOf(input.file, ref.module) };
  }
  function canonical(node, input, tuple) {
    const ref = reference(node, input);
    return ref?.name === tuple[0] && ref.module === tuple[1];
  }
  function resolved(node, input, kind) {
    const ref = requireProof(reference(node, input));
    const candidates = [...raw.keys()].filter((file) => stripExtension(file) === ref.module);
    requireProof(candidates.length === 1);
    const target = source(candidates[0]);
    const declarations = target.ast.statements.filter(
      (item) => kind(item) && named(item) === ref.name,
    );
    requireProof(declarations.length === 1 && mods(declarations[0], ts.SyntaxKind.ExportKeyword));
    return { input: target, node: declarations[0] };
  }
  function member(owner, name, kind = ts.isMethodDeclaration) {
    const found = owner.members.filter((item) => kind(item) && named(item) === name);
    return requireProof(found.length === 1 && found[0].body && !found[0].asteriskToken && found[0]);
  }
  function metadata(owner, method, input) {
    const own = decorators(owner, input.ast, input.symbols);
    const methodDecorators = decorators(method, input.ast, input.symbols);
    const by = (list, name, module) =>
      list.filter(
        (dec) =>
          dec.name === name &&
          dec.module &&
          moduleOf(input.file, dec.module) === module &&
          ts.isCallExpression(dec.node.expression) &&
          canonical(dec.node.expression.expression, input, [name, module]),
      );
    const controllers = by(own, "Controller", "@nestjs/common");
    requireProof(
      controllers.length === 1 &&
        controllers[0].args.length === 1 &&
        literal(controllers[0].args[0]) !== null,
    );
    const guards = requireProof(by(own, "UseGuards", "@nestjs/common")[0]);
    const interceptors = requireProof(by(own, "UseInterceptors", "@nestjs/common")[0]);
    requireProof(
      guards.args.some((arg) => canonical(arg, input, CANONICAL.jwt)) &&
        guards.args.some((arg) => canonical(arg, input, CANONICAL.guard)) &&
        guards.args.length === 3 &&
        new Set(guards.args.map((arg) => arg.getText(input.ast))).size === 3 &&
        guards.args.every(
          (arg) =>
            canonical(arg, input, CANONICAL.jwt) ||
            canonical(arg, input, CANONICAL.guard) ||
            canonical(arg, input, [
              "BlockCleanDoctorGuard",
              "apps/api/src/medical/clinic-analytics/block-clean-doctor.guard",
            ]),
        ) &&
        interceptors.args.length === 1 &&
        canonical(interceptors.args[0], input, CANONICAL.interceptor),
    );
    requireProof(own.length === 3); // no metadata-overriding class decorator
    const permission = by(methodDecorators, ...CANONICAL.permission);
    requireProof(permission.length === 1 && permission[0].args.length === 2);
    const resourceKey = literal(permission[0].args[0]);
    const action = literal(permission[0].args[1]);
    requireProof(/^reports?\.[a-z][a-z0-9._-]*$/u.test(resourceKey ?? "") && action === "READ");
    for (const dec of methodDecorators) {
      requireProof(
        (dec.module === "@nestjs/common" && ["Get", "Post", "Header"].includes(dec.name)) ||
          (dec.module === "@nestjs/throttler" && dec.name === "Throttle") ||
          dec === permission[0],
      );
      if (dec !== permission[0]) for (const argument of dec.args) staticValue(argument);
      requireProof(
        ts.isCallExpression(dec.node.expression) &&
          canonical(dec.node.expression.expression, input, [
            dec.name,
            moduleOf(input.file, dec.module),
          ]),
      );
    }
    return { resourceKey, action };
  }

  // A query function may be used only by direct named calls in its code-owned
  // graph. External mutation is outside this runtime primitive's assurance;
  // exported containers, callbacks and opaque local value transport are not.
  function closedReferences(target, kind, deps) {
    deps.add(target.input.file);
    requireProof(kind === "function" && ts.isFunctionDeclaration(target.node));
    for (const ref of references(target.input.ast, named(target.node))) {
      if (ref === target.node.name || erasedReference(ref)) continue;
      requireProof(call(ref.parent) && ref.parent.expression === ref);
    }
  }
  // Evaluate only immutable literal construction. Runtime parameters may bind
  // SQL values, but may never produce raw identifiers/tables/functions.
  function staticSqlArgument(expression, input) {
    const declarations = new Map();
    visit(input.ast, (node) => {
      if (ts.isVariableDeclaration(node) && named(node)) {
        const entries = declarations.get(named(node)) ?? [];
        entries.push(node);
        declarations.set(named(node), entries);
      }
    });
    const bindings = new Map();
    const used = new Set();
    function evaluate(node, values = new Map(), active = new Set()) {
      used.add(node);
      if (ts.isStringLiteralLike(node)) return node.text;
      if (ts.isNumericLiteral(node)) return Number(node.text);
      if (node.kind === ts.SyntaxKind.TrueKeyword) return true;
      if (node.kind === ts.SyntaxKind.FalseKeyword) return false;
      if (node.kind === ts.SyntaxKind.NullKeyword) return null;
      if (
        ts.isParenthesizedExpression(node) ||
        ts.isAsExpression(node) ||
        ts.isSatisfiesExpression(node)
      )
        return evaluate(node.expression, values, active);
      if (ts.isIdentifier(node)) {
        if (values.has(node.text)) return values.get(node.text);
        requireProof(!active.has(node.text));
        const candidates = declarations.get(node.text) ?? [];
        const decl = requireProof(candidates.length === 1 && candidates[0]);
        requireProof(
          decl.initializer &&
            ts.isVariableDeclarationList(decl.parent) &&
            decl.parent.flags & ts.NodeFlags.Const,
        );
        bindings.set(node.text, decl);
        return evaluate(decl.initializer, values, new Set([...active, node.text]));
      }
      if (ts.isArrayLiteralExpression(node))
        return node.elements.map((item) => evaluate(item, values, active));
      if (ts.isObjectLiteralExpression(node)) {
        const result = Object.create(null);
        for (const prop of node.properties) {
          requireProof(
            ts.isPropertyAssignment(prop) && named(prop) && !Object.hasOwn(result, named(prop)),
          );
          result[named(prop)] = evaluate(prop.initializer, values, active);
        }
        return result;
      }
      if (ts.isPropertyAccessExpression(node)) {
        const object = evaluate(node.expression, values, active);
        requireProof(
          object &&
            typeof object === "object" &&
            !Array.isArray(object) &&
            Object.hasOwn(object, node.name.text),
        );
        return object[node.name.text];
      }
      if (ts.isTemplateExpression(node)) {
        return (
          node.head.text +
          node.templateSpans
            .map((span) => {
              const value = evaluate(span.expression, values, active);
              requireProof(["string", "number", "boolean"].includes(typeof value));
              return String(value) + span.literal.text;
            })
            .join("")
        );
      }
      if (call(node) && ts.isPropertyAccessExpression(node.expression)) {
        const array = evaluate(node.expression.expression, values, active);
        requireProof(Array.isArray(array));
        if (node.expression.name.text === "join") {
          requireProof(
            node.arguments.length === 1 &&
              array.every((item) => ["string", "number", "boolean"].includes(typeof item)),
          );
          const separator = evaluate(node.arguments[0], values, active);
          requireProof(typeof separator === "string");
          return array.join(separator);
        }
        const mapper = node.arguments[0];
        requireProof(
          node.expression.name.text === "map" &&
            node.arguments.length === 1 &&
            ts.isArrowFunction(mapper) &&
            mapper.parameters.length === 1 &&
            named(mapper.parameters[0]) &&
            !mapper.parameters[0].initializer &&
            !mapper.parameters[0].dotDotDotToken &&
            !ts.isBlock(mapper.body) &&
            array.length > 0,
        );
        return array.map((item) =>
          evaluate(mapper.body, new Map([...values, [named(mapper.parameters[0]), item]]), active),
        );
      }
      fail();
    }
    const result = evaluate(expression);
    // const does not freeze an array/object. Every other reference must also be
    // consumed by this closed literal evaluator, never by a mutator or escape.
    const checked = new Set();
    while ([...bindings.keys()].some((name) => !checked.has(name))) {
      for (const [name, declaration] of bindings) {
        if (checked.has(name)) continue;
        checked.add(name);
        // const/ReadonlyArray do not freeze runtime containers. An export opens
        // consumers outside this local evaluator; no importer interpretation is
        // attempted. Alias/default export references also fail below as escapes.
        requireProof(
          !ts.isVariableStatement(declaration.parent.parent) ||
            !mods(declaration.parent.parent, ts.SyntaxKind.ExportKeyword),
        );
        for (const ref of references(input.ast, name)) {
          if (ref === declaration.name || used.has(ref)) continue;
          let root = ref;
          while (
            root.parent &&
            !ts.isVariableDeclaration(root.parent) &&
            !ts.isExpressionStatement(root.parent) &&
            !ts.isReturnStatement(root.parent) &&
            !(
              call(root.parent) &&
              canonical(root.parent.expression, input, ["Prisma", "@prisma/client"])
            )
          ) {
            if (
              call(root.parent) &&
              ts.isPropertyAccessExpression(root.parent.expression) &&
              ["raw", "join"].includes(root.parent.expression.name.text) &&
              canonical(root.parent.expression.expression, input, ["Prisma", "@prisma/client"])
            )
              break;
            root = root.parent;
          }
          if (ts.isVariableDeclaration(root.parent) && root.parent.initializer === root) {
            const next = root.parent;
            requireProof(named(next) && next.parent.flags & ts.NodeFlags.Const);
            evaluate(root);
            bindings.set(named(next), next);
          } else {
            // A literal value returned, exported or passed elsewhere can expose
            // the original container. Only a raw/join argument is a terminal
            // consumer; evaluating the value alone does not prove no escape.
            requireProof(
              call(root.parent) &&
                root.parent.arguments.includes(root) &&
                ts.isPropertyAccessExpression(root.parent.expression) &&
                ["raw", "join"].includes(root.parent.expression.name.text) &&
                canonical(root.parent.expression.expression, input, ["Prisma", "@prisma/client"]),
            );
            evaluate(root);
          }
        }
      }
    }
    return result;
  }
  const checkedSqlModules = new WeakMap();
  function sqlModule(input, deps) {
    const status = checkedSqlModules.get(input.ast);
    requireProof(status !== false);
    if (status) return;
    checkedSqlModules.set(input.ast, "checking");
    try {
      pinImports(input, deps);
      for (const statement of input.ast.statements) {
        if (
          ts.isImportDeclaration(statement) ||
          ts.isTypeAliasDeclaration(statement) ||
          ts.isInterfaceDeclaration(statement)
        )
          continue;
        if (ts.isFunctionDeclaration(statement)) {
          closedSqlConstruction({ input, node: statement }, deps);
          continue;
        }
        requireProof(
          ts.isVariableStatement(statement) && statement.declarationList.flags & ts.NodeFlags.Const,
        );
        for (const declaration of statement.declarationList.declarations) {
          requireProof(named(declaration) && declaration.initializer);
          const value = staticSqlArgument(declaration.initializer, input);
          requireProof(
            !mods(statement, ts.SyntaxKind.ExportKeyword) ||
              value === null ||
              ["string", "number", "boolean"].includes(typeof value),
          );
        }
      }
      checkedSqlModules.set(input.ast, true);
    } catch (error) {
      checkedSqlModules.set(input.ast, false);
      throw error;
    }
  }
  function closedSqlConstruction(target, deps, active = new Set()) {
    sqlModule(target.input, deps);
    const key = `${target.input.file}#${named(target.node)}`;
    requireProof(!active.has(key));
    active = new Set([...active, key]);
    deps.add(target.input.file);
    closedReferences(target, "function", deps);
    const fn = target.node;
    requireProof(
      fn.parameters.every(
        (parameter) =>
          named(parameter) &&
          !parameter.dotDotDotToken &&
          (!parameter.initializer ||
            ts.isNumericLiteral(parameter.initializer) ||
            (property(parameter.initializer, "empty") &&
              canonical(parameter.initializer.expression, target.input, [
                "Prisma",
                "@prisma/client",
              ]))),
      ),
    );
    requireProof(
      fn.body && fn.body.statements.length > 0 && ts.isReturnStatement(fn.body.statements.at(-1)),
    );
    const terminal = fn.body.statements.at(-1).expression;
    requireProof(
      (ts.isTaggedTemplateExpression(terminal) &&
        property(terminal.tag, "sql") &&
        canonical(terminal.tag.expression, target.input, ["Prisma", "@prisma/client"])) ||
        (call(terminal) && ts.isIdentifier(terminal.expression)),
    );
    requireProof(
      fn.body.statements
        .slice(0, -1)
        .every(
          (statement) =>
            ts.isVariableStatement(statement) &&
            statement.declarationList.flags & ts.NodeFlags.Const,
        ),
    );
    const locals = new Set(fn.parameters.map(named));
    visit(fn.body, (node) => {
      if (ts.isVariableDeclaration(node) || ts.isParameter(node)) {
        requireProof(named(node));
        locals.add(named(node));
      }
    });
    const constant = (name) => {
      const declarations = target.input.ast.statements
        .filter(ts.isVariableStatement)
        .filter((statement) => statement.declarationList.flags & ts.NodeFlags.Const)
        .flatMap((statement) => [...statement.declarationList.declarations])
        .filter((decl) => named(decl) === name);
      if (declarations.length !== 1 || !declarations[0].initializer) return false;
      try {
        staticValue(declarations[0].initializer);
        return true;
      } catch {
        return false;
      }
    };
    function inspect(node) {
      if (ts.isTypeNode(node)) return;
      requireProof(
        !ts.isElementAccessExpression(node) &&
          !ts.isNewExpression(node) &&
          !ts.isAwaitExpression(node) &&
          !ts.isDeleteExpression(node) &&
          node.kind !== ts.SyntaxKind.ThisKeyword,
      );
      if (ts.isBinaryExpression(node))
        requireProof(
          node.operatorToken.kind < ts.SyntaxKind.FirstAssignment ||
            node.operatorToken.kind > ts.SyntaxKind.LastAssignment,
        );
      if (ts.isTaggedTemplateExpression(node))
        requireProof(
          property(node.tag, "sql") &&
            canonical(node.tag.expression, target.input, ["Prisma", "@prisma/client"]),
        );
      if (call(node)) {
        if (ts.isIdentifier(node.expression)) {
          const local = target.input.ast.statements.filter(
            (item) => ts.isFunctionDeclaration(item) && named(item) === node.expression.text,
          );
          const next =
            local.length === 1
              ? { input: target.input, node: local[0] }
              : resolved(node.expression, target.input, ts.isFunctionDeclaration);
          closedSqlConstruction(next, deps, active);
        } else {
          requireProof(
            ts.isPropertyAccessExpression(node.expression) &&
              ((canonical(node.expression.expression, target.input, ["Prisma", "@prisma/client"]) &&
                ["raw", "join"].includes(node.expression.name.text)) ||
                ["map", "join", "toISOString", "slice"].includes(node.expression.name.text)),
          );
          if (canonical(node.expression.expression, target.input, ["Prisma", "@prisma/client"])) {
            requireProof(node.arguments.length > 0);
            const value = staticSqlArgument(node.arguments[0], target.input);
            requireProof(
              node.expression.name.text === "raw"
                ? typeof value === "string"
                : Array.isArray(value),
            );
            for (const argument of node.arguments.slice(1))
              staticSqlArgument(argument, target.input);
          }
        }
      }
      if (ts.isIdentifier(node)) {
        const parent = node.parent;
        const staticName =
          (ts.isPropertyAccessExpression(parent) && parent.name === node) ||
          (ts.isPropertyAssignment(parent) && parent.name === node);
        if (!staticName && !locals.has(node.text) && !constant(node.text)) {
          requireProof(
            (canonical(node, target.input, ["Prisma", "@prisma/client"]) &&
              ts.isPropertyAccessExpression(parent) &&
              parent.expression === node) ||
              (call(parent) && parent.expression === node),
          );
        }
      }
      ts.forEachChild(node, inspect);
    }
    inspect(fn.body);
  }
  function sqlFunction(target, position, mode, deps, active = new Set()) {
    closedSqlConstruction(target, deps);
    const key = `${target.input.file}#${named(target.node)}:${position}:${mode}`;
    requireProof(!active.has(key));
    active = new Set([...active, key]);
    deps.add(target.input.file);
    closedReferences(target, "function", deps);
    const fn = target.node;
    const parameter = fn.parameters[position];
    requireProof(
      fn.body &&
        parameter &&
        ts.isIdentifier(parameter.name) &&
        !parameter.initializer &&
        !parameter.dotDotDotToken,
    );
    unshadowed(fn.body, new Set([...target.input.symbols.keys(), ...fn.parameters.map(named)]));
    const env = new Map([[parameter.name.text, mode]]);
    let bound = 0;
    let uses = 0;
    let recordAlias = null;
    let tenantBound = false;
    // A fragment or value cannot be interpolated inside an SQL quote/comment.
    function sqlState(text, state = "code") {
      for (let index = 0; index < text.length; index += 1) {
        const char = text[index],
          next = text[index + 1];
        if (state === "line") {
          if (char === "\n") state = "code";
          continue;
        }
        if (state === "block") {
          if (char === "*" && next === "/") {
            state = "code";
            index += 1;
          }
          continue;
        }
        if (state === "single" || state === "double") {
          const quote = state === "single" ? "'" : '"';
          if (char === quote) {
            if (next === quote) index += 1;
            else state = "code";
          }
          requireProof(char !== "\\");
          continue;
        }
        if (char === "-" && next === "-") {
          state = "line";
          index += 1;
        } else if (char === "/" && next === "*") {
          state = "block";
          index += 1;
        } else if (char === "'") state = "single";
        else if (char === '"') state = "double";
        else requireProof(char !== "$" || !/^\$(?:[a-zA-Z_]\w*)?\$/u.test(text.slice(index)));
      }
      return state;
    }
    function evaluate(node) {
      if (ts.isIdentifier(node)) {
        if (env.has(node.text)) {
          uses += 1;
          return env.get(node.text);
        }
        return null;
      }
      if (ts.isTaggedTemplateExpression(node)) {
        const tag = node.tag;
        requireProof(
          property(tag, "sql") &&
            canonical(tag.expression, target.input, ["Prisma", "@prisma/client"]),
        );
        if (ts.isNoSubstitutionTemplateLiteral(node.template)) return null;
        let tainted = false;
        let before = node.template.head.text;
        let state = sqlState(before);
        for (const span of node.template.templateSpans) {
          const value = evaluate(span.expression);
          if (value) requireProof(state === "code");
          if (
            state === "code" &&
            ts.isIdentifier(span.expression) &&
            span.expression.text === named(fn.parameters[0]) &&
            /\b[a-zA-Z_]\w*\."organizationId"\s*=\s*$/u.test(before)
          )
            tenantBound = true;
          if (value === "id") {
            // This exact grammar admits a bound record predicate, never raw SQL,
            // an identifier, a selector expression, or a quoted/commented value.
            const predicate = /^AND\s+([a-zA-Z_]\w*)\."id"\s*=\s*$/u.exec(before.trim());
            const spans = node.template.templateSpans;
            requireProof(
              predicate &&
                spans.length === 2 &&
                spans[0] === span &&
                /^\s+$/u.test(span.literal.text) &&
                ts.isIdentifier(spans[1].expression) &&
                spans[1].expression.text === named(fn.parameters[2]) &&
                /^\s*$/u.test(spans[1].literal.text),
            );
            recordAlias = predicate[1];
            bound += 1;
          }
          if (
            value === "sql" &&
            ts.isIdentifier(span.expression) &&
            span.expression.text === parameter.name.text
          ) {
            // A predicate fragment may only extend this complete WHERE clause;
            // OR/UNION/suffix expressions cannot neutralize the fixed ID test.
            requireProof(
              mode === "sql" &&
                /\bWHERE\s+1\s*=\s*1\s*$/u.test(before) &&
                /^\s*\)/u.test(span.literal.text),
            );
          }
          tainted ||= Boolean(value);
          before = span.literal.text;
          state = sqlState(before, state);
        }
        requireProof(state === "code" || state === "line");
        return tainted ? "sql" : null;
      }
      if (call(node)) {
        for (const name of env.keys()) requireProof(references(node.expression, name).length === 0);
        const values = node.arguments.map(evaluate);
        const tainted = values.flatMap((value, index) => (value ? [index] : []));
        if (!tainted.length) return null;
        requireProof(
          tainted.length === 1 && values[tainted[0]] === "sql" && ts.isIdentifier(node.expression),
        );
        let next;
        const local = target.input.ast.statements.filter(
          (item) => ts.isFunctionDeclaration(item) && named(item) === node.expression.text,
        );
        if (local.length === 1) next = { input: target.input, node: local[0] };
        else next = resolved(node.expression, target.input, ts.isFunctionDeclaration);
        sqlFunction(next, tainted[0], "sql", deps, active);
        return "sql";
      }
      // Non-tainted subexpressions may not capture the parameter in an alias,
      // closure, property, conditional, raw call, mutation or computed dispatch.
      let tainted = false;
      visit(node, (child) => {
        if (ts.isIdentifier(child) && env.has(child.text)) tainted = true;
      });
      requireProof(!tainted);
      return null;
    }
    const statements = [...fn.body.statements];
    requireProof(statements.length > 0 && ts.isReturnStatement(statements.at(-1)));
    for (const statement of statements.slice(0, -1)) {
      requireProof(
        ts.isVariableStatement(statement) && statement.declarationList.flags & ts.NodeFlags.Const,
      );
      for (const declaration of statement.declarationList.declarations) {
        requireProof(ts.isIdentifier(declaration.name) && declaration.initializer);
        const value = evaluate(declaration.initializer);
        requireProof(value !== "id"); // no record-value alias outside its bound slot
        if (value) env.set(declaration.name.text, value);
      }
    }
    requireProof(
      evaluate(statements.at(-1).expression) === "sql" &&
        uses > 0 &&
        (mode !== "sql" || uses === 1) &&
        (mode !== "id" || (bound === 1 && tenantBound)),
    );
    // Require all original parameter references to be consumed by the evaluator.
    requireProof(references(fn.body, parameter.name.text).length > 0);
    return recordAlias;
  }

  function pinImports(input, deps) {
    deps.add(input.file);
    for (const statement of input.ast.statements) {
      if (!ts.isImportDeclaration(statement)) continue;
      const spec = literal(statement.moduleSpecifier);
      requireProof(
        spec &&
          statement.importClause &&
          !statement.importClause.name &&
          statement.importClause.namedBindings &&
          ts.isNamedImports(statement.importClause.namedBindings),
      );
      if (!spec.startsWith(".")) continue;
      const files = [...raw.keys()].filter(
        (file) => stripExtension(file) === moduleOf(input.file, spec),
      );
      requireProof(files.length === 1);
      deps.add(files[0]);
    }
  }
  const dataMethods = new Set([
    "map",
    "filter",
    "some",
    "every",
    "flatMap",
    "includes",
    "trim",
    "toISOString",
    "getTime",
    "slice",
    "split",
    "join",
    "toString",
  ]);
  const globals = new Map([
    ["Number", new Set(["isSafeInteger", "isInteger", "isNaN"])],
    ["Math", new Set(["min", "max", "floor"])],
    ["Array", new Set(["isArray"])],
    ["Date", new Set(["UTC"])],
    ["Buffer", new Set(["from"])],
    ["JSON", new Set(["parse", "stringify"])],
  ]);
  function queryGraph(target, deps) {
    const input = target.input,
      owner = target.node;
    pinImports(input, deps);
    requireProof(
      !owner.heritageClauses && decorators(owner, input.ast, input.symbols).length === 0,
    );
    requireProof(
      input.ast.statements.every(
        (s) =>
          ts.isImportDeclaration(s) ||
          ts.isInterfaceDeclaration(s) ||
          ts.isTypeAliasDeclaration(s) ||
          s === owner,
      ),
    );
    const ctor = owner.members.filter(ts.isConstructorDeclaration);
    requireProof(
      ctor.length === 1 && ctor[0].parameters.length === 2 && ctor[0].body.statements.length === 0,
    );
    for (const p of ctor[0].parameters)
      requireProof(
        named(p) &&
          mods(p, ts.SyntaxKind.PrivateKeyword) &&
          mods(p, ts.SyntaxKind.ReadonlyKeyword) &&
          !p.initializer &&
          !p.dotDotDotToken &&
          decorators(p, input.ast, input.symbols).length === 0,
      );
    const txName = named(ctor[0].parameters[0]),
      ownName = named(ctor[0].parameters[1]);
    const methods = owner.members.filter(ts.isMethodDeclaration);
    requireProof(methods.length > 1 && new Set(methods.map(named)).size === methods.length);
    const localNames = new Set(methods.map(named)),
      fields = new Map(owner.members.filter(ts.isPropertyDeclaration).map((m) => [named(m), m]));
    const externalCalls = new Set();
    for (const statement of input.ast.statements.filter(ts.isImportDeclaration)) {
      const spec = literal(statement.moduleSpecifier);
      for (const binding of statement.importClause.namedBindings.elements) {
        const name = (binding.propertyName ?? binding.name).text;
        if (statement.importClause.isTypeOnly || binding.isTypeOnly) continue;
        if (spec === "@nestjs/common")
          requireProof(
            ["BadRequestException", "InternalServerErrorException", "NotFoundException"].includes(
              name,
            ),
          );
        else if (spec === "@prisma/client") requireProof(name === "Prisma");
        else if (spec === "node:crypto") requireProof(name === "createHash");
        else {
          const resolvedFunction = resolved(binding.name, input, ts.isFunctionDeclaration);
          closedSqlConstruction(resolvedFunction, deps);
          externalCalls.add(binding.name.text);
        }
      }
    }
    for (const field of owner.members.filter(ts.isPropertyDeclaration)) {
      requireProof(
        named(field) &&
          mods(field, ts.SyntaxKind.StaticKeyword) &&
          mods(field, ts.SyntaxKind.ReadonlyKeyword) &&
          field.initializer,
      );
      const value = field.initializer;
      if (ts.isNewExpression(value))
        requireProof(
          ts.isIdentifier(value.expression) &&
            value.expression.text === "Set" &&
            !lexicalIndex(input.ast)(value.expression) &&
            value.arguments.length === 1 &&
            ts.isArrayLiteralExpression(value.arguments[0]) &&
            value.arguments[0].elements.every((e) => literal(e) !== null),
        );
      else
        requireProof(
          value.kind === ts.SyntaxKind.RegularExpressionLiteral || ts.isNumericLiteral(value),
        );
    }
    requireProof(
      owner.members.every(
        (m) =>
          ts.isMethodDeclaration(m) ||
          ts.isPropertyDeclaration(m) ||
          ts.isConstructorDeclaration(m),
      ),
    );
    let rawQueries = 0;
    // Only simple DATA parameters belong to this finite subset. Defaults run
    // before a method body, so they cannot be inferred safe from its inspection.
    const dataParameter = (p) =>
      named(p) &&
      !p.initializer &&
      !p.dotDotDotToken &&
      decorators(p, input.ast, input.symbols).length === 0;
    // Prove receivers from lexical value origins, never from a method name or
    // an asserted TS type. Owner/transaction/SQL capabilities are not DATA.
    const bindingOf = lexicalIndex(input.ast);
    function valueKind(value, seen = new Set()) {
      if (!value || seen.has(value)) return null;
      seen = new Set(seen).add(value);
      if (
        ts.isParenthesizedExpression(value) ||
        ts.isAsExpression(value) ||
        ts.isTypeAssertionExpression(value) ||
        ts.isNonNullExpression(value) ||
        ts.isAwaitExpression(value)
      )
        return valueKind(value.expression, seen);
      if (ts.isIdentifier(value)) {
        const binding = bindingOf(value);
        if (!binding) return value.text === "undefined" ? "data" : null;
        let declaration = binding.parent;
        if (ts.isParameter(declaration))
          return methods.includes(declaration.parent) || ts.isArrowFunction(declaration.parent)
            ? "data"
            : null;
        if (ts.isBindingElement(declaration)) {
          while (ts.isBindingElement(declaration) || ts.isBindingPattern(declaration))
            declaration = declaration.parent;
          const origin = ts.isVariableDeclaration(declaration) ? declaration.initializer : null;
          return valueKind(origin, seen) === "data" ? "data" : null;
        }
        if (!ts.isVariableDeclaration(declaration)) return null;
        const origin = declaration.initializer;
        if (!origin) {
          const loop = declaration.parent.parent;
          if (ts.isForOfStatement(loop))
            return valueKind(loop.expression, seen) === "data" ? "data" : null;
          // Uninitialized mutable locals may only hold DATA. Every write is
          // checked below; they cannot acquire a branded builtin capability.
          return "data";
        }
        const kind = valueKind(origin, seen);
        return kind === "data" || declaration.parent.flags & ts.NodeFlags.Const ? kind : null;
      }
      if (ts.isPropertyAccessExpression(value)) {
        if (ts.isIdentifier(value.expression) && bindingOf(value.expression) === owner.name) {
          const field = fields.get(value.name.text);
          if (!field) return null;
          return ts.isNewExpression(field.initializer)
            ? "set"
            : field.initializer.kind === ts.SyntaxKind.RegularExpressionLiteral
              ? "regexp"
              : "data";
        }
        return valueKind(value.expression, seen) === "data" ? "data" : null;
      }
      if (ts.isElementAccessExpression(value))
        return valueKind(value.expression, seen) === "data" ? "data" : null;
      if (
        ts.isNewExpression(value) &&
        ts.isIdentifier(value.expression) &&
        !bindingOf(value.expression)
      )
        return value.expression.text === "Set"
          ? "set"
          : value.expression.text === "Date"
            ? "data"
            : null;
      if (call(value)) {
        const expr = value.expression;
        if (ts.isIdentifier(expr)) {
          const ref = reference(expr, input);
          if (ref?.module === "node:crypto" && ref.name === "createHash") return "hash";
          return !bindingOf(expr) && ["String", "Number"].includes(expr.text) ? "data" : null;
        }
        if (!ts.isPropertyAccessExpression(expr)) return null;
        if (thisProperty(expr.expression) === txName && expr.name.text === "$queryRaw")
          return "data";
        if (expr.expression.kind === ts.SyntaxKind.ThisKeyword && localNames.has(expr.name.text))
          return "data";
        if (
          ts.isIdentifier(expr.expression) &&
          !bindingOf(expr.expression) &&
          globals.get(expr.expression.text)?.has(expr.name.text)
        )
          return expr.expression.text === "Buffer" ? "buffer" : "data";
        const receiver = valueKind(expr.expression, seen);
        if (receiver === "hash" && expr.name.text === "update") return "hash";
        if (
          (receiver === "hash" && expr.name.text === "digest") ||
          (receiver === "buffer" && expr.name.text === "toString") ||
          (receiver === "data" && dataMethods.has(expr.name.text)) ||
          (receiver === "set" && expr.name.text === "has") ||
          (receiver === "regexp" && expr.name.text === "test")
        )
          return "data";
        return null;
      }
      if (ts.isConditionalExpression(value))
        return valueKind(value.whenTrue, seen) === "data" &&
          valueKind(value.whenFalse, seen) === "data"
          ? "data"
          : null;
      if (ts.isArrayLiteralExpression(value))
        return value.elements.every(
          (e) => valueKind(ts.isSpreadElement(e) ? e.expression : e, seen) === "data",
        )
          ? "data"
          : null;
      if (ts.isObjectLiteralExpression(value))
        return value.properties.every(
          (p) =>
            (ts.isPropertyAssignment(p) && valueKind(p.initializer, seen) === "data") ||
            (ts.isShorthandPropertyAssignment(p) && valueKind(p.name, seen) === "data") ||
            (ts.isSpreadAssignment(p) && valueKind(p.expression, seen) === "data"),
        )
          ? "data"
          : null;
      if (value.kind === ts.SyntaxKind.RegularExpressionLiteral) return "regexp";
      if (
        ts.isLiteralExpression(value) ||
        ts.isTemplateExpression(value) ||
        ts.isBinaryExpression(value) ||
        ts.isPrefixUnaryExpression(value) ||
        [ts.SyntaxKind.TrueKeyword, ts.SyntaxKind.FalseKeyword, ts.SyntaxKind.NullKeyword].includes(
          value.kind,
        )
      )
        return "data";
      return null;
    }
    function inspect(node, method) {
      if (ts.isTypeNode(node)) return;
      if (node.kind === ts.SyntaxKind.ThisKeyword)
        requireProof(ts.isPropertyAccessExpression(node.parent) && node.parent.expression === node);
      if (ts.isParameter(node)) requireProof(dataParameter(node));
      if (ts.isBindingElement(node))
        requireProof(
          !node.initializer &&
            !node.dotDotDotToken &&
            (!node.propertyName || !ts.isComputedPropertyName(node.propertyName)),
        );
      requireProof(
        !ts.isDeleteExpression(node) &&
          !ts.isYieldExpression(node) &&
          !ts.isClassExpression(node) &&
          !ts.isFunctionExpression(node) &&
          !ts.isFunctionDeclaration(node) &&
          (!ts.isMethodDeclaration(node) || node === method),
      );
      if (ts.isArrowFunction(node))
        requireProof(
          call(node.parent) &&
            node.parent.arguments[0] === node &&
            ts.isPropertyAccessExpression(node.parent.expression) &&
            ["map", "filter", "flatMap", "some", "every"].includes(
              node.parent.expression.name.text,
            ),
        );
      if (ts.isIdentifier(node) && valueReference(node) && !erasedReference(node)) {
        if (
          [
            "eval",
            "require",
            "globalThis",
            "Reflect",
            "Function",
            "process",
            "module",
            "exports",
          ].includes(node.text)
        )
          fail();
        if (!lexicalIndex(input.ast)(node))
          requireProof(
            globals.has(node.text) ||
              ["String", "Number", "Set", "Date", "Error", "undefined"].includes(node.text),
          );
        if (node.text === named(owner) && lexicalIndex(input.ast)(node) === owner.name) {
          const access = node.parent;
          requireProof(
            ts.isPropertyAccessExpression(access) &&
              access.expression === node &&
              fields.has(access.name.text),
          );
          const field = fields.get(access.name.text);
          if (!ts.isNumericLiteral(field.initializer))
            requireProof(
              ts.isPropertyAccessExpression(access.parent) &&
                [
                  field.initializer.kind === ts.SyntaxKind.RegularExpressionLiteral
                    ? "test"
                    : "has",
                ].includes(access.parent.name.text) &&
                call(access.parent.parent) &&
                access.parent.parent.expression === access.parent,
            );
        }
        if (input.symbols.has(node.text)) {
          const ref = reference(node, input);
          requireProof(ref);
          const p = node.parent;
          requireProof(
            (call(p) && p.expression === node) ||
              (ts.isNewExpression(p) && p.expression === node) ||
              (ts.isPropertyAccessExpression(p) && p.expression === node && ref.name === "Prisma"),
          );
        }
      }
      if (ts.isElementAccessExpression(node)) {
        // Dynamic values may index data, never code, a capability or this.
        let base = node.expression;
        while (ts.isPropertyAccessExpression(base) || ts.isElementAccessExpression(base))
          base = base.expression;
        requireProof(
          base.kind !== ts.SyntaxKind.ThisKeyword &&
            !(call(node.parent) && node.parent.expression === node),
        );
      }
      if (ts.isPropertyAccessExpression(node)) {
        requireProof(
          !["constructor", "prototype", "__proto__", "call", "apply", "bind"].includes(
            node.name.text,
          ),
        );
        if (node.expression.kind === ts.SyntaxKind.ThisKeyword)
          requireProof([txName, ownName, ...localNames].includes(node.name.text));
        if (thisProperty(node) === txName)
          requireProof(
            ts.isPropertyAccessExpression(node.parent) &&
              node.parent.name.text === "$queryRaw" &&
              call(node.parent.parent) &&
              node.parent.parent.expression === node.parent,
          );
        if (thisProperty(node) === ownName)
          requireProof(
            call(node.parent) &&
              node.parent.arguments.at(-1) === node &&
              ts.isIdentifier(node.parent.expression) &&
              externalCalls.has(node.parent.expression.text) &&
              call(node.parent.parent) &&
              thisProperty(node.parent.parent.expression.expression) === txName,
          );
        if (node.expression.kind === ts.SyntaxKind.ThisKeyword && localNames.has(node.name.text))
          requireProof(call(node.parent) && node.parent.expression === node);
      }
      if (
        ts.isBinaryExpression(node) &&
        node.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
        node.operatorToken.kind <= ts.SyntaxKind.LastAssignment
      )
        requireProof(
          ts.isIdentifier(node.left) &&
            valueKind(node.right) === "data" &&
            ts.isVariableDeclaration(bindingOf(node.left)?.parent),
        );
      if (ts.isNewExpression(node)) {
        requireProof(ts.isIdentifier(node.expression));
        const ref = reference(node.expression, input);
        requireProof(
          ref?.module === "@nestjs/common" ||
            (!lexicalIndex(input.ast)(node.expression) &&
              ["Set", "Date", "Error"].includes(node.expression.text)),
        );
      }
      if (call(node)) {
        const expr = node.expression;
        if (
          ts.isPropertyAccessExpression(expr) &&
          ["map", "filter", "flatMap", "some", "every"].includes(expr.name.text)
        )
          requireProof(
            node.arguments.length === 1 &&
              (ts.isArrowFunction(node.arguments[0]) ||
                (ts.isIdentifier(node.arguments[0]) &&
                  node.arguments[0].text === "Number" &&
                  !lexicalIndex(input.ast)(node.arguments[0]))),
          );
        if (
          ts.isPropertyAccessExpression(expr) &&
          ts.isIdentifier(expr.expression) &&
          expr.expression.text === "JSON"
        )
          requireProof(node.arguments.length === 1);
        if (ts.isIdentifier(expr)) {
          const ref = reference(expr, input);
          requireProof(
            (ref?.module === "node:crypto" && ref.name === "createHash") ||
              (ref &&
                externalCalls.has(expr.text) &&
                call(node.parent) &&
                node.parent.arguments[0] === node &&
                thisProperty(node.parent.expression.expression) === txName) ||
              (!lexicalIndex(input.ast)(expr) && ["String", "Number"].includes(expr.text)),
          );
        } else {
          requireProof(ts.isPropertyAccessExpression(expr));
          if (thisProperty(expr.expression) === txName) {
            requireProof(
              expr.name.text === "$queryRaw" &&
                node.arguments.length === 1 &&
                call(node.arguments[0]) &&
                ts.isIdentifier(node.arguments[0].expression) &&
                externalCalls.has(node.arguments[0].expression.text),
            );
            rawQueries++;
            const fn = resolved(node.arguments[0].expression, input, ts.isFunctionDeclaration);
            requireProof(
              node.arguments[0].arguments.length === fn.node.parameters.length &&
                node.arguments[0].arguments.at(-1).getText(input.ast) === `this.${ownName}`,
            );
            if (method.name.text === "detail") sqlFunction(fn, 1, "id", deps);
          } else if (expr.expression.kind === ts.SyntaxKind.ThisKeyword)
            requireProof(
              localNames.has(expr.name.text) &&
                node.arguments.every((arg) => valueKind(arg) === "data"),
            );
          else if (ts.isIdentifier(expr.expression) && globals.has(expr.expression.text))
            requireProof(
              !lexicalIndex(input.ast)(expr.expression) &&
                globals.get(expr.expression.text).has(expr.name.text),
            );
          else {
            const receiver = valueKind(expr.expression);
            requireProof(
              (receiver === "data" && dataMethods.has(expr.name.text)) ||
                (receiver === "hash" && ["update", "digest"].includes(expr.name.text)) ||
                (receiver === "buffer" && expr.name.text === "toString") ||
                (receiver === "set" && ["has", "add"].includes(expr.name.text)) ||
                (receiver === "regexp" && expr.name.text === "test"),
            );
          }
        }
      }
      ts.forEachChild(node, (child) => inspect(child, method));
    }
    for (const m of methods) {
      requireProof(
        named(m) &&
          !mods(m, ts.SyntaxKind.StaticKeyword) &&
          decorators(m, input.ast, input.symbols).length === 0 &&
          m.parameters.every(dataParameter),
      );
      requireProof(m.body && !m.asteriskToken);
      inspect(m.body, m);
    }
    requireProof(
      rawQueries === 2 &&
        methods
          .filter((m) => !mods(m, ts.SyntaxKind.PrivateKeyword))
          .map(named)
          .sort()
          .join(",") === "detail,list",
    );
  }
  function boundaryGraph(deps) {
    const files = [...raw.keys()].filter((file) => stripExtension(file) === CANONICAL.boundary[1]);
    requireProof(files.length === 1);
    const input = source(files[0]);
    pinImports(input, deps);
    const owners = input.ast.statements.filter(
      (s) => ts.isClassDeclaration(s) && named(s) === CANONICAL.boundary[0],
    );
    requireProof(owners.length === 1);
    const owner = owners[0];
    const query = member(owner, "query");
    requireProof(query.parameters.length === 4 && query.body.statements.length === 4);
    const binding = query.body.statements[0];
    requireProof(
      ts.isVariableStatement(binding) &&
        binding.declarationList.flags & ts.NodeFlags.Const &&
        binding.declarationList.declarations.length === 1,
    );
    const decl = binding.declarationList.declarations[0],
      construct = decl.initializer;
    requireProof(
      named(decl) && construct && ts.isNewExpression(construct) && construct.arguments.length === 2,
    );
    requireProof(
      ts.isIdentifier(construct.arguments[0]) &&
        construct.arguments[0].text === named(query.parameters[0]),
    );
    const scope = construct.arguments[1];
    requireProof(
      call(scope) &&
        scope.arguments.length === 2 &&
        canonical(scope.expression, input, [
          "domainOwnDoctorSql",
          "apps/api/src/medical/data/access-policy/domain-scope",
        ]) &&
        literal(scope.arguments[0]) === "report.doctors",
    );
    const column = scope.arguments[1];
    requireProof(
      ts.isTaggedTemplateExpression(column) &&
        property(column.tag, "sql") &&
        canonical(column.tag.expression, input, ["Prisma", "@prisma/client"]) &&
        ts.isNoSubstitutionTemplateLiteral(column.template) &&
        column.template.text === 'f."identStaffId"',
    );
    const target = resolved(construct.expression, input, ts.isClassDeclaration);
    queryGraph(target, deps);
    const routes = new Map();
    for (const branch of query.body.statements.slice(1, 3)) {
      requireProof(
        ts.isIfStatement(branch) && !branch.elseStatement && ts.isBlock(branch.thenStatement),
      );
      const condition =
        ts.isBinaryExpression(branch.expression) &&
        branch.expression.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken
          ? branch.expression.left
          : branch.expression;
      requireProof(
        ts.isBinaryExpression(condition) &&
          condition.operatorToken.kind === ts.SyntaxKind.EqualsEqualsEqualsToken &&
          ts.isIdentifier(condition.left) &&
          condition.left.text === named(query.parameters[2]),
      );
      const operation = literal(condition.right);
      requireProof(operation && !routes.has(operation));
      if (condition !== branch.expression)
        requireProof(
          ts.isBinaryExpression(branch.expression.right) &&
            branch.expression.right.operatorToken.kind === ts.SyntaxKind.EqualsEqualsEqualsToken &&
            ts.isTypeOfExpression(branch.expression.right.left) &&
            ts.isIdentifier(branch.expression.right.left.expression) &&
            branch.expression.right.left.expression.text === named(query.parameters[3]) &&
            literal(branch.expression.right.right) === "string",
        );
      const statements = branch.thenStatement.statements;
      requireProof(
        statements.length === 2 &&
          ts.isVariableStatement(statements[0]) &&
          ts.isReturnStatement(statements[1]),
      );
      requireProof(
        statements[0].declarationList.flags & ts.NodeFlags.Const &&
          statements[0].declarationList.declarations.length === 1,
      );
      const result = statements[0].declarationList.declarations[0];
      requireProof(named(result) && ts.isAwaitExpression(result.initializer));
      const invoke = result.initializer.expression;
      requireProof(
        call(invoke) &&
          ts.isPropertyAccessExpression(invoke.expression) &&
          ts.isIdentifier(invoke.expression.expression) &&
          invoke.expression.expression.text === named(decl) &&
          invoke.arguments.length === 2,
      );
      requireProof(
        invoke.arguments[0].getText(input.ast) === `${named(query.parameters[1])}.organizationId`,
      );
      let data = invoke.arguments[1];
      if (ts.isAsExpression(data)) data = data.expression;
      requireProof(ts.isIdentifier(data) && data.text === named(query.parameters[3]));
      requireProof(
        ts.isIdentifier(statements[1].expression) &&
          statements[1].expression.text === named(result),
      );
      const method = invoke.expression.name.text;
      requireProof(["list", "detail"].includes(method));
      routes.set(operation, { method, kind: method === "detail" ? "Param" : "Body" });
    }
    requireProof(
      routes.size === 2 && new Set([...routes.values()].map((x) => x.method)).size === 2,
    );
    const rejection = query.body.statements[3];
    requireProof(
      ts.isThrowStatement(rejection) &&
        ts.isNewExpression(rejection.expression) &&
        canonical(rejection.expression.expression, input, [
          "OrganizationPolicyError",
          "apps/api/src/modules/access-control/access-policy.organization-execution",
        ]) &&
        rejection.expression.arguments.length === 1 &&
        literal(rejection.expression.arguments[0]) === "ACCESS_DENIED",
    );
    return { routes, input };
  }
  function controllerProof(surface, deps, graph) {
    const input = source(surface.file);
    pinImports(input, deps);
    const classes = input.ast.statements.filter(ts.isClassDeclaration);
    requireProof(
      classes.length === 1 &&
        !classes[0].heritageClauses &&
        named(classes[0]) === surface.controller,
    );
    requireProof(
      input.ast.statements.every(
        (s) => ts.isImportDeclaration(s) || ts.isInterfaceDeclaration(s) || s === classes[0],
      ),
    );
    const owner = classes[0],
      handler = member(owner, surface.handler);
    requireProof(
      !mods(handler, ts.SyntaxKind.StaticKeyword) &&
        !mods(handler, ts.SyntaxKind.PrivateKeyword) &&
        !mods(handler, ts.SyntaxKind.ProtectedKeyword),
    );
    const tuple = metadata(owner, handler, input);
    requireProof(tuple.resourceKey === "report.doctors" && tuple.action === "READ");
    const ctor = owner.members.filter(ts.isConstructorDeclaration);
    requireProof(
      ctor.length === 1 && ctor[0].parameters.length === 1 && ctor[0].body.statements.length === 0,
    );
    const p = ctor[0].parameters[0];
    requireProof(
      decorators(p, input.ast, input.symbols).length === 0 &&
        named(p) &&
        !p.initializer &&
        mods(p, ts.SyntaxKind.PrivateKeyword) &&
        mods(p, ts.SyntaxKind.ReadonlyKeyword) &&
        ts.isTypeReferenceNode(p.type) &&
        canonical(p.type.typeName, input, CANONICAL.boundary),
    );
    requireProof(owner.members.every((m) => ts.isMethodDeclaration(m) || m === ctor[0]));
    const terminal = oneReturn(handler);
    requireProof(
      call(terminal) &&
        ts.isPropertyAccessExpression(terminal.expression) &&
        thisProperty(terminal.expression.expression) === named(p) &&
        terminal.expression.name.text === "read" &&
        terminal.arguments.length === 5,
    );
    const req = handler.parameters[0],
      data = handler.parameters[1];
    requireProof(
      handler.parameters.length === 2 &&
        named(req) &&
        named(data) &&
        !req.initializer &&
        !data.initializer &&
        !req.dotDotDotToken &&
        !data.dotDotDotToken,
    );
    const rd = decorators(req, input.ast, input.symbols),
      dd = decorators(data, input.ast, input.symbols);
    requireProof(
      rd.length === 1 &&
        rd[0].name === "Req" &&
        rd[0].module === "@nestjs/common" &&
        rd[0].args.length === 0 &&
        canonical(rd[0].node.expression.expression, input, ["Req", "@nestjs/common"]),
    );
    const operation = literal(terminal.arguments[3]),
      mapping = graph.routes.get(operation);
    requireProof(mapping);
    requireProof(
      dd.length === 1 &&
        dd[0].name === mapping.kind &&
        dd[0].module === "@nestjs/common" &&
        canonical(dd[0].node.expression.expression, input, [mapping.kind, "@nestjs/common"]),
    );
    const path = decorators(handler, input.ast, input.symbols).filter(
      (x) => x.module === "@nestjs/common" && ["Get", "Post"].includes(x.name),
    );
    requireProof(path.length === 1);
    if (mapping.kind === "Param")
      requireProof(
        path[0].name === "Get" &&
          path[0].args.length === 1 &&
          literal(path[0].args[0]) === `:${named(data)}` &&
          dd[0].args.length === 1 &&
          literal(dd[0].args[0]) === named(data) &&
          !/report/iu.test(named(data)),
      );
    else
      requireProof(
        path[0].name === "Post" &&
          dd[0].args.length === 0 &&
          !/:/u.test(literal(path[0].args[0]) ?? ":"),
      );
    requireProof(
      terminal.arguments[0].getText(input.ast) === `${named(req)}.user` &&
        literal(terminal.arguments[1]) === tuple.resourceKey &&
        literal(terminal.arguments[2]) === tuple.action &&
        ts.isIdentifier(terminal.arguments[4]) &&
        terminal.arguments[4].text === named(data),
    );
    return { tuple, operation };
  }
  function moduleWiring(controller, controllerName, deps) {
    let installed = 0,
      exported = 0,
      provided = 0;
    for (const rawInput of raw.values()) {
      // Only canonical static imports introduce this trusted runtime primitive.
      // This is a finite DI boundary check, not a root-token/ambient JS proof.
      if (!rawInput.text.includes(CANONICAL.boundary[0]) && !rawInput.text.includes(controllerName))
        continue;
      const input = source(rawInput.file);
      for (const [local, ref] of input.symbols) {
        const module = moduleOf(input.file, ref.module);
        const boundary = module === CANONICAL.boundary[1] && ref.name === CANONICAL.boundary[0];
        const route = module === stripExtension(controller.file) && ref.name === controllerName;
        if (!boundary && !route) continue;
        for (const id of references(input.ast, local)) {
          if (erasedReference(id) || id === importedBinding(input, local)) continue;
          const array = id.parent,
            prop = array?.parent,
            object = prop?.parent,
            invoke = object?.parent;
          requireProof(
            ts.isArrayLiteralExpression(array) &&
              array.elements.includes(id) &&
              ts.isPropertyAssignment(prop) &&
              ["controllers", "providers", "exports"].includes(named(prop)) &&
              ts.isObjectLiteralExpression(object) &&
              call(invoke) &&
              invoke.arguments.length === 1 &&
              canonical(invoke.expression, input, ["Module", "@nestjs/common"]) &&
              ts.isDecorator(invoke.parent),
          );
          requireProof(
            (route && named(prop) === "controllers") ||
              (boundary && ["providers", "exports"].includes(named(prop))),
          );
          const moduleClass = invoke.parent.parent;
          requireProof(
            ts.isClassDeclaration(moduleClass) &&
              !moduleClass.heritageClauses &&
              moduleClass.members.length === 0 &&
              decorators(moduleClass, input.ast, input.symbols).length === 1,
          );
          requireProof(new Set(object.properties.map(named)).size === object.properties.length);
          for (const item of object.properties)
            requireProof(
              ts.isPropertyAssignment(item) &&
                named(item) &&
                ts.isArrayLiteralExpression(item.initializer) &&
                item.initializer.elements.every(ts.isIdentifier),
            );
          if (route) {
            installed++;
            const imports = object.properties.find((p) => named(p) === "imports");
            requireProof(
              imports &&
                imports.initializer.elements.some((n) =>
                  canonical(n, input, [
                    "AccessPolicyModule",
                    "apps/api/src/modules/access-control/access-policy.module",
                  ]),
                ),
            );
          } else if (named(prop) === "exports") exported++;
          else if (named(prop) === "providers") provided++;
          pinImports(input, deps);
        }
      }
    }
    requireProof(installed === 1 && exported === 1 && provided === 1);
  }
  function prove(surface) {
    if (cache.has(surface.id)) return cache.get(surface.id);
    let result = null;
    try {
      requireProof(surface.kind === "nest-http");
      const deps = new Set(),
        graph = boundaryGraph(deps);
      const { tuple, operation } = controllerProof(surface, deps, graph);
      moduleWiring(source(surface.file), surface.controller, deps);
      const dependencies = [...deps]
        .sort()
        .map((file) => ({ file, sha256: hash(raw.get(file).text) }));
      result = Object.freeze({
        version: 1,
        route: surface.id,
        ...tuple,
        operation,
        boundary: "RECORD_QUERY_V1",
        dependencies,
        digest: hash(JSON.stringify(dependencies)),
      });
    } catch {
      /* Unknown shape retains the dynamic report gate. */
    }
    cache.set(surface.id, result);
    return result;
  }
  return Object.freeze({
    route: prove,
    source(input, discovered) {
      try {
        requireProof(
          discovered.length > 0 && discovered.every((s) => s.file === input.file && prove(s)),
        );
        const ast = source(input.file),
          owners = ast.ast.statements.filter(ts.isClassDeclaration);
        const methods = owners.flatMap((owner) => owner.members.filter(ts.isMethodDeclaration));
        requireProof(
          methods.length === discovered.length &&
            methods.every((m) => discovered.filter((s) => s.handler === named(m)).length === 1),
        );
        requireProof(discovered.some((s) => /(?:^|\/):[^/]+/u.test(s.path ?? "")));
        return discovered.map(prove);
      } catch {
        return null;
      }
    },
  });
}
