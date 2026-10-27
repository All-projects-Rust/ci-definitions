import { ts, parseSource } from "./ast.mjs";
import { discoverNest } from "./nest.mjs";
import { discoverWeb, discoverJobsAndStreams } from "./entries.mjs";
import { discoverSourceSnapshot } from "./parsed-inventory.mjs";

export function discoverSurfaces(files) {
  return discoverSourceSnapshot(files, discoverUncachedSurfaces);
}

function discoverUncachedSurfaces(files) {
  const sources = new Map(files.map(({ file, text }) => [file, parseSource(file, text)]));
  const result = discoverNest(sources);
  for (const source of sources.values()) {
    for (const diagnostic of source.parseDiagnostics) {
      const offset = diagnostic.start ?? 0;
      result.issues.push({
        file: source.fileName,
        line: source.getLineAndCharacterOfPosition(offset).line + 1,
        kind: "parse-error",
        message: ts.flattenDiagnosticMessageText(diagnostic.messageText, " "),
      });
    }
  }
  for (const source of sources.values()) {
    if (source.fileName.startsWith("apps/web/")) {
      const found = discoverWeb(source);
      result.surfaces.push(...found.surfaces);
      result.issues.push(...found.issues);
    }
    const found = discoverJobsAndStreams(source);
    result.surfaces.push(...found.surfaces);
    result.issues.push(...found.issues);
  }
  result.surfaces.sort((a, b) => a.id.localeCompare(b.id));
  const ids = new Set();
  for (const surface of result.surfaces) {
    if (ids.has(surface.id))
      result.issues.push({
        file: surface.file,
        line: surface.line,
        kind: "duplicate-id",
        message: surface.id,
      });
    ids.add(surface.id);
  }
  return result;
}
