/** Source discovery only. Nothing in this module decides whether access is allowed. */
import ts from "typescript";

export { ts };
export { parseSource } from "./parsed-inventory.mjs";

export function importedSymbols(source) {
  const symbols = new Map();
  for (const statement of source.statements) {
    if (!ts.isImportDeclaration(statement) || !ts.isStringLiteral(statement.moduleSpecifier))
      continue;
    const module = statement.moduleSpecifier.text;
    const clause = statement.importClause;
    if (clause?.name) symbols.set(clause.name.text, { module, name: "default" });
    const bindings = clause?.namedBindings;
    if (bindings && ts.isNamespaceImport(bindings)) {
      symbols.set(bindings.name.text, { module, name: "*" });
    } else if (bindings && ts.isNamedImports(bindings)) {
      for (const binding of bindings.elements) {
        symbols.set(binding.name.text, {
          module,
          name: (binding.propertyName ?? binding.name).text,
        });
      }
    }
  }
  return symbols;
}

export function importedReference(expression, symbols) {
  if (ts.isIdentifier(expression)) return symbols.get(expression.text) ?? null;
  if (ts.isPropertyAccessExpression(expression) && ts.isIdentifier(expression.expression)) {
    const namespace = symbols.get(expression.expression.text);
    if (namespace?.name === "*") return { module: namespace.module, name: expression.name.text };
  }
  return null;
}

export function decorators(node, source, symbols) {
  return (ts.canHaveDecorators(node) ? (ts.getDecorators(node) ?? []) : []).map((decorator) => {
    const expression = decorator.expression;
    const call = ts.isCallExpression(expression) ? expression : null;
    const target = call?.expression ?? expression;
    const ref = importedReference(target, symbols);
    return {
      name: ref?.name ?? target.getText(source),
      module: ref?.module ?? null,
      args: [...(call?.arguments ?? [])],
      expression: expression.getText(source),
      node: decorator,
    };
  });
}

export function constantExpressions(source) {
  const values = new Map();
  for (const statement of source.statements) {
    if (
      !ts.isVariableStatement(statement) ||
      statement.declarationList.flags !== ts.NodeFlags.Const
    )
      continue;
    for (const declaration of statement.declarationList.declarations) {
      if (ts.isIdentifier(declaration.name) && declaration.initializer) {
        values.set(declaration.name.text, declaration.initializer);
      }
    }
  }
  return values;
}

function staticArray(node, constants, seen) {
  return node.elements.flatMap((element) => {
    if (!ts.isSpreadElement(element)) return [staticValue(element, constants, seen)];
    const value = staticValue(element.expression, constants, seen);
    if (!Array.isArray(value)) throw new Error("Non-array spread in route metadata");
    return value;
  });
}

function staticObject(node, constants, seen) {
  const result = Object.create(null);
  for (const property of node.properties) {
    if (ts.isSpreadAssignment(property)) {
      const spread = staticValue(property.expression, constants, seen);
      if (!spread || typeof spread !== "object" || Array.isArray(spread)) {
        throw new Error("Non-object metadata spread");
      }
      Object.assign(result, spread);
      continue;
    }
    if (ts.isShorthandPropertyAssignment(property)) {
      result[property.name.text] = staticValue(property.name, constants, seen);
      continue;
    }
    if (!ts.isPropertyAssignment(property) || ts.isComputedPropertyName(property.name)) {
      throw new Error("Computed route metadata property");
    }
    result[property.name.text] = staticValue(property.initializer, constants, seen);
  }
  return result;
}

function staticBinary(node, constants, seen) {
  if (node.operatorToken.kind !== ts.SyntaxKind.PlusToken) return undefined;
  const left = staticValue(node.left, constants, seen);
  const right = staticValue(node.right, constants, seen);
  if (typeof left === "string" && typeof right === "string") return left + right;
  return undefined;
}

function staticTemplate(node, constants, seen) {
  let text = node.head.text;
  for (const span of node.templateSpans) {
    const value = staticValue(span.expression, constants, seen);
    if (typeof value !== "string" && typeof value !== "number")
      throw new Error("Dynamic route template");
    text += String(value) + span.literal.text;
  }
  return text;
}

/** Deliberately not eval: unsupported computed metadata is a visible discovery error. */
export function staticValue(node, constants = new Map(), seen = new Set()) {
  if (!node) return undefined;
  if (ts.isStringLiteralLike(node)) return node.text;
  if (ts.isNumericLiteral(node)) return Number(node.text);
  if (node.kind === ts.SyntaxKind.TrueKeyword) return true;
  if (node.kind === ts.SyntaxKind.FalseKeyword) return false;
  if (node.kind === ts.SyntaxKind.NullKeyword) return null;
  if (
    ts.isParenthesizedExpression(node) ||
    ts.isAsExpression(node) ||
    ts.isSatisfiesExpression(node)
  ) {
    return staticValue(node.expression, constants, seen);
  }
  if (ts.isIdentifier(node) && constants.has(node.text) && !seen.has(node.text)) {
    return staticValue(constants.get(node.text), constants, new Set([...seen, node.text]));
  }
  if (ts.isArrayLiteralExpression(node)) return staticArray(node, constants, seen);
  if (ts.isObjectLiteralExpression(node)) return staticObject(node, constants, seen);
  if (ts.isBinaryExpression(node)) {
    const value = staticBinary(node, constants, seen);
    if (value !== undefined) return value;
  }
  if (ts.isTemplateExpression(node)) return staticTemplate(node, constants, seen);
  throw new Error(`Unresolved static metadata: ${node.getText().slice(0, 120)}`);
}

export function stringVariants(value, fallback = "") {
  if (value === undefined) return [fallback];
  const variants = Array.isArray(value) ? value : [value];
  if (!variants.length || variants.some((part) => typeof part !== "string")) {
    throw new Error("Expected a non-empty list of literal route paths");
  }
  return [...new Set(variants)];
}

export function sourceLocation(source, node) {
  return {
    file: source.fileName,
    line: source.getLineAndCharacterOfPosition(node.getStart(source)).line + 1,
  };
}

export function hasModifier(node, kind) {
  return (ts.canHaveModifiers(node) ? (ts.getModifiers(node) ?? []) : []).some(
    (modifier) => modifier.kind === kind,
  );
}

export function hasDirective(statements, directive) {
  for (const statement of statements) {
    if (!ts.isExpressionStatement(statement) || !ts.isStringLiteral(statement.expression))
      return false;
    if (statement.expression.text === directive) return true;
  }
  return false;
}
