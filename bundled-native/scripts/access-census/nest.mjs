import { posix } from "node:path";
import {
  ts, importedSymbols, importedReference, decorators, constantExpressions,
  staticValue, stringVariants, sourceLocation,
} from "./ast.mjs";

const HTTP = new Map([
  ["Get", "GET"], ["Post", "POST"], ["Put", "PUT"], ["Patch", "PATCH"],
  ["Delete", "DELETE"], ["Head", "HEAD"], ["Options", "OPTIONS"],
  ["All", "ALL"], ["Sse", "SSE"],
]);
const isNest = (decorator, name) => decorator.module === "@nestjs/common" && decorator.name === name;

function trimSlashes(value) {
  let start = 0;
  let end = value.length;
  while (start < end && value[start] === "/") start += 1;
  while (end > start && value[end - 1] === "/") end -= 1;
  return value.slice(start, end);
}

const joinRoute = (...parts) => parts.map(trimSlashes).filter(Boolean).join("/");
const trimEvidence = (items) => items.map(({ name, module, expression }) => ({ name, module, expression }));

function controllerPaths(decorator, constants) {
  const argument = decorator.args[0];
  if (argument && ts.isObjectLiteralExpression(argument)) {
    const pathProperty = argument.properties.find((property) =>
      ts.isPropertyAssignment(property) && property.name.getText() === "path");
    return stringVariants(pathProperty ? staticValue(pathProperty.initializer, constants) : undefined);
  }
  const value = staticValue(argument, constants);
  const pathValue = value && typeof value === "object" && !Array.isArray(value) ? value.path : value;
  return stringVariants(pathValue);
}

function relativeSource(file, specifier, sources) {
  if (!specifier.startsWith(".")) return null;
  const stem = posix.normalize(posix.join(posix.dirname(file), specifier));
  return [stem, `${stem}.ts`, `${stem}.tsx`, `${stem}/index.ts`]
    .find((candidate) => sources.has(candidate)) ?? null;
}

function baseClass(entry, classes, sources) {
  const clause = entry.node.heritageClauses?.find((item) => item.token === ts.SyntaxKind.ExtendsKeyword);
  if (!clause) return null;
  const expression = clause.types[0]?.expression;
  if (!expression || !ts.isIdentifier(expression)) throw new Error("Unsupported computed controller inheritance");
  const own = classes.get(`${entry.source.fileName}#${expression.text}`);
  if (own) return own;
  const ref = importedReference(expression, entry.symbols);
  const file = ref ? relativeSource(entry.source.fileName, ref.module, sources) : null;
  const parent = file ? classes.get(`${file}#${ref.name}`) : null;
  if (!parent) throw new Error(`Unresolved controller base ${expression.text}`);
  return parent;
}

function effectiveMethods(entry, classes, sources, visiting = new Set()) {
  if (visiting.has(entry)) throw new Error("Cyclic controller inheritance");
  const next = new Set([...visiting, entry]);
  const parent = baseClass(entry, classes, sources);
  const methods = parent ? effectiveMethods(parent, classes, sources, next) : new Map();
  for (const member of entry.node.members) {
    if (!member.name || ts.isComputedPropertyName(member.name)) continue;
    const raw = member.name.getText(entry.source);
    const name = raw.startsWith('"') || raw.startsWith("'") ? raw.slice(1, -1) : raw;
    methods.set(name, { member, entry });
  }
  return methods;
}

function mappedRoute(decorator, constants, symbols) {
  const argument = decorator.args[0];
  if (!argument || !ts.isObjectLiteralExpression(argument)) throw new Error("RequestMapping needs a literal options object");
  const properties = new Map(argument.properties.filter(ts.isPropertyAssignment).map((item) => [item.name.getText(), item.initializer]));
  const method = properties.get("method");
  let verb = "GET";
  if (method) {
    if (!ts.isPropertyAccessExpression(method)) throw new Error("RequestMapping method must be an explicit RequestMethod member");
    const ref = importedReference(method.expression, symbols);
    if (ref?.module !== "@nestjs/common" || ref?.name !== "RequestMethod") throw new Error("Unresolved RequestMethod binding");
    verb = method.name.text;
    if (![...HTTP.values()].includes(verb)) throw new Error("Unsupported RequestMapping method");
  }
  return { verb, paths: stringVariants(staticValue(properties.get("path"), constants)) };
}

function collectClasses(sources) {
  const classes = new Map();
  for (const source of sources.values()) {
    const symbols = importedSymbols(source);
    const constants = constantExpressions(source);
    const visit = (node) => {
      if (ts.isClassDeclaration(node) && node.name) {
        const entry = { source, node, symbols, constants };
        classes.set(`${source.fileName}#${node.name.text}`, entry);
        const isDefault = node.modifiers?.some((modifier) => modifier.kind === ts.SyntaxKind.DefaultKeyword);
        if (isDefault) classes.set(`${source.fileName}#default`, entry);
      }
      ts.forEachChild(node, visit);
    };
    visit(source);
  }
  return classes;
}

function routeMetadata(routeDecorator, owner) {
  if (routeDecorator.name === "RequestMapping") {
    return mappedRoute(routeDecorator, owner.constants, owner.symbols);
  }
  return {
    verb: HTTP.get(routeDecorator.name),
    paths: stringVariants(staticValue(routeDecorator.args[0], owner.constants)),
  };
}

function addRouteSurfaces(
  surfaces,
  controllerEntry,
  owner,
  member,
  memberName,
  prefixes,
  route,
  classDecorators,
  methodDecorators,
) {
  for (const prefix of prefixes) {
    for (const suffix of route.paths) {
      const fullPath = joinRoute(prefix, suffix);
      const controllerName = controllerEntry.node.name.text;
      surfaces.push({
        id: `nest:${controllerEntry.source.fileName}#${controllerName}.${memberName}:${route.verb} ${fullPath}`,
        kind: route.verb === "SSE" ? "nest-sse" : "nest-http",
        verb: route.verb,
        route: `${route.verb} ${fullPath}`,
        path: fullPath,
        prefix,
        controller: controllerName,
        handler: memberName,
        ...sourceLocation(controllerEntry.source, controllerEntry.node),
        handlerFile: owner.source.fileName,
        handlerLine: sourceLocation(owner.source, member).line,
        inherited: owner !== controllerEntry,
        classDecorators: trimEvidence(classDecorators),
        methodDecorators: trimEvidence(methodDecorators),
        inheritedClassDecorators: owner === controllerEntry
          ? []
          : trimEvidence(decorators(owner.node, owner.source, owner.symbols)),
      });
    }
  }
}

function discoverMethodRoutes(context) {
  const {
    entry, owner, member, memberName, prefixes, classDecorators, surfaces, issues,
  } = context;
  const methodDecorators = decorators(member, owner.source, owner.symbols);
  const routeDecorators = methodDecorators.filter((item) =>
    item.module === "@nestjs/common" && (HTTP.has(item.name) || item.name === "RequestMapping"));
  for (const routeDecorator of routeDecorators) {
    try {
      if (!ts.isMethodDeclaration(member)) throw new Error("Route decorator on a non-method member");
      const route = routeMetadata(routeDecorator, owner);
      addRouteSurfaces(
        surfaces, entry, owner, member, memberName, prefixes, route, classDecorators, methodDecorators,
      );
    } catch (error) {
      issues.push({ ...sourceLocation(owner.source, member), kind: "nest-discovery", message: error.message });
    }
  }
}

function discoverController(entry, classes, sources, surfaces, issues) {
  const classDecorators = decorators(entry.node, entry.source, entry.symbols);
  const controller = classDecorators.find((item) => isNest(item, "Controller"));
  if (!controller) return;
  let prefixes;
  let methods;
  try {
    prefixes = controllerPaths(controller, entry.constants);
    methods = effectiveMethods(entry, classes, sources);
  } catch (error) {
    issues.push({ ...sourceLocation(entry.source, entry.node), kind: "nest-discovery", message: error.message });
    return;
  }
  for (const [memberName, { member, entry: owner }] of methods) {
    discoverMethodRoutes({
      entry, owner, member, memberName, prefixes, classDecorators, surfaces, issues,
    });
  }
}

/** The output is declared source routes, NOT runtime mount or permission certification. */
export function discoverNest(sources) {
  const classes = collectClasses(sources);
  const issues = [];
  const surfaces = [];
  for (const entry of new Set(classes.values())) {
    discoverController(entry, classes, sources, surfaces, issues);
  }
  surfaces.sort((a, b) => a.id.localeCompare(b.id));
  return { surfaces, issues };
}
