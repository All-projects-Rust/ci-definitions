import { createHash } from "node:crypto";

export function compare(a, b) {
  if (a < b) return -1;
  if (a > b) return 1;
  return 0;
}

export function stable(value) {
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

export const digest = (value) => createHash("sha256").update(stable(value)).digest("hex");
export function surfaceIdentity(surface) {
  return {
    id: surface.id,
    kind: surface.kind,
    tags: [...surface.tags],
    file: surface.file,
    ...(surface.handler ? { handler: surface.handler } : {}),
    ...(surface.controller ? { controller: surface.controller } : {}),
    ...(surface.handlerFile ? { handlerFile: surface.handlerFile } : {}),
    ...(surface.handlerLine ? { handlerLine: surface.handlerLine } : {}),
    ...(surface.route ? { route: surface.route } : {}),
    ...(surface.dynamicReportDispatch ? { dynamicReportDispatch: true } : {}),
  };
}

export function buildLedgerFromEntries(entries, legacyBoundaryCommit) {
  const legacyIds = entries
    .filter((entry) => entry.disposition === "LEGACY_BASELINE")
    .map((entry) => entry.id);
  const ledger = {
    schemaVersion: 1,
    task: "SIG-909",
    legacyBoundaryCommit,
    surfaceDigest: digest(entries.map(surfaceIdentity)),
    legacyIdsDigest: digest(legacyIds),
    entries,
  };
  return { ...ledger, contentHash: digest(ledger) };
}

export function buildLegacyBaselineAnchor(ledger, previousBaseline) {
  const legacyIds = ledger.entries
    .filter((entry) => entry.disposition === "LEGACY_BASELINE")
    .map((entry) => entry.id);
  const currentRetirements = new Map(
    ledger.entries
      .filter((entry) => entry.disposition === "RETIRED")
      .map((entry) => [entry.id, entry]),
  );
  const retirements = [];
  for (const previous of previousBaseline?.retirements ?? []) {
    const current = currentRetirements.get(previous.id);
    if (!current || stable(current) !== stable(previous)) {
      throw new Error(`PERMISSION_SURFACE_RETIREMENTS_NOT_APPEND_ONLY ${previous.id}`);
    }
    retirements.push(structuredClone(previous));
    currentRetirements.delete(previous.id);
  }
  retirements.push(
    ...[...currentRetirements.values()]
      .sort((left, right) => compare(left.id, right.id))
      .map((entry) => structuredClone(entry)),
  );
  const anchor = {
    schemaVersion: 1,
    task: "SIG-909",
    legacyBoundaryCommit: ledger.legacyBoundaryCommit,
    legacyCount: legacyIds.length,
    legacyIdsDigest: digest(legacyIds),
    retirements,
  };
  return { ...anchor, contentHash: digest(anchor) };
}
