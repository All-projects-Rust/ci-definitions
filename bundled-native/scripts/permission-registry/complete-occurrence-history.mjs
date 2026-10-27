import { digest, stable } from "./ledger-format.mjs";
import { types } from "node:util";

const trustedViews = new WeakMap();
export function hasPlainRegistryContainers(value, active = new WeakSet()) {
  if (value === null || typeof value !== "object") return typeof value !== "function";
  if (types.isProxy(value)) return false;
  if (active.has(value)) return false;
  active.add(value);
  const prototype = Object.getPrototypeOf(value),
    descriptors = Object.getOwnPropertyDescriptors(value);
  let valid;
  if (prototype === Map.prototype || prototype === Set.prototype) {
    valid =
      Reflect.ownKeys(descriptors).length === 0 &&
      [...value].every((item) => hasPlainRegistryContainers(item, active));
  } else if (prototype === Array.prototype) {
    valid = Reflect.ownKeys(descriptors).every(
      (key) =>
        key === "length" ||
        (typeof key === "string" &&
          /^(0|[1-9][0-9]*)$/u.test(key) &&
          Object.hasOwn(descriptors[key], "value") &&
          hasPlainRegistryContainers(descriptors[key].value, active)),
    );
  } else {
    valid =
      (prototype === Object.prototype || prototype === null) &&
      Reflect.ownKeys(descriptors).every(
        (key) =>
          typeof key === "string" &&
          descriptors[key].enumerable &&
          Object.hasOwn(descriptors[key], "value") &&
          hasPlainRegistryContainers(descriptors[key].value, active),
      );
  }
  active.delete(value);
  return valid;
}
const viewSnapshot = (v) =>
  stable({
    catalog: { entries: [...v.catalog.entries], edges: [...v.catalog.edges] },
    entries: [...v.entries],
    edgeKeys: [...v.edgeKeys],
    owners: [...v.owners],
    bindings: [...v.bindings],
    provenance: v.provenance,
  });
export function assertCompleteOccurrenceView(view) {
  if (
    !trustedViews.has(view) ||
    !hasPlainRegistryContainers(view) ||
    trustedViews.get(view) !== viewSnapshot(view)
  )
    throw new Error("INVALID_PERMISSION_SURFACE_COMPLETE_OCCURRENCE_RECONCILIATION");
}

const fail = () => {
  throw new Error("INVALID_PERMISSION_SURFACE_COMPLETE_OCCURRENCE_RECONCILIATION");
};
const keys = (v, expected) =>
  v && typeof v === "object" && !Array.isArray(v) && Object.keys(v).sort().join(",") === expected;
const hash = (v) => typeof v === "string" && /^[a-f0-9]{64}$/u.test(v);
const metadata = (r) =>
  [r?.reason, r?.owner, r?.ticket].every((v) => typeof v === "string" && v.trim()) &&
  r.reason.trim().length >= 12 &&
  r.owner.trim().length >= 2 &&
  r.ticket.trim().length >= 3;
export const occurrenceFamily = (id) =>
  typeof id === "string" && /^permission-source-sentinel:[^:]+:.+#sha256:[a-f0-9]{64}$/u.test(id)
    ? id.slice(0, id.lastIndexOf("#sha256:"))
    : null;
const free = ({ reason, owner, ticket, ...rest }) => rest;
const reference = (f, e) => ({ fragment: digest(f), attestation: digest(e) });
const sameSet = (a, b) =>
  Array.isArray(a) &&
  a.length === b.length &&
  new Set(a.map(stable)).size === a.length &&
  a.every((x) => b.some((y) => stable(x) === stable(y)));
export function occurrenceCatalog(fragments) {
  const entries = new Map(),
    edges = new Map();
  for (const f of fragments) {
    for (const entry of f.entries) {
      if (!entries.has(entry.id)) entries.set(entry.id, []);
      entries.get(entry.id).push({ ...reference(f, entry), entry });
    }
    for (const edge of f.transitions) {
      const k = stable(edge);
      if (!edges.has(k)) edges.set(k, []);
      edges.get(k).push({ ...reference(f, edge), edge });
    }
  }
  return { entries, edges };
}
const match = (refs, originals) => {
  if (
    !Array.isArray(refs) ||
    refs.length < 2 ||
    !originals ||
    refs.length !== originals.length ||
    refs.some(
      (r) => !keys(r, "attestation,fragment") || !hash(r.fragment) || !hash(r.attestation),
    ) ||
    new Set(refs.map((r) => r.fragment)).size !== refs.length ||
    !sameSet(
      refs,
      originals.map(({ fragment, attestation }) => ({ fragment, attestation })),
    )
  )
    fail();
};
const sentinelKeys = [
  "id",
  "kind",
  "tags",
  "file",
  "handler",
  "handlerFile",
  "dynamicReportDispatch",
  "disposition",
  "reason",
  "owner",
  "ticket",
  "replaces",
];
const routeKeys = [
  "id",
  "kind",
  "tags",
  "file",
  "handler",
  "handlerFile",
  "handlerLine",
  "route",
  "disposition",
  "reason",
  "owner",
  "ticket",
];
const routes = new Map([
  [
    "apps/web/app/api/wazzup/dialogs/[dialogId]/head/route.ts",
    "/api/wazzup/dialogs/:dialogId/head",
  ],
  ["apps/web/app/api/wazzup/dialogs/rows/route.ts", "/api/wazzup/dialogs/rows"],
  ["apps/web/app/api/wazzup/dialogs/value/route.ts", "/api/wazzup/dialogs/value"],
]);
function valid(entry) {
  if (
    !metadata(entry) ||
    entry.disposition !== "EXEMPT" ||
    !Array.isArray(entry.tags) ||
    !entry.tags.length ||
    entry.tags.some((t) => typeof t !== "string" || !t) ||
    new Set(entry.tags).size !== entry.tags.length
  )
    fail();
  if (entry.kind === "permission-source-sentinel") {
    const family = occurrenceFamily(entry.id),
      m = family && /^permission-source-sentinel:([^:]+):(.+)$/u.exec(family);
    if (
      !m ||
      entry.handler !== m[1] ||
      entry.file !== m[2] ||
      (Object.hasOwn(entry, "handlerFile") && entry.handlerFile !== entry.file) ||
      Object.keys(entry).some((k) => !sentinelKeys.includes(k))
    )
      fail();
  } else if (entry.kind === "next-route") {
    if (
      !routes.has(entry.file) ||
      entry.id !== `declared:next-route:${entry.file}#POST` ||
      entry.handler !== "POST" ||
      entry.handlerFile !== entry.file ||
      entry.route !== routes.get(entry.file) ||
      !Number.isSafeInteger(entry.handlerLine) ||
      entry.handlerLine < 1 ||
      Object.keys(entry).some((k) => !routeKeys.includes(k))
    )
      fail();
  } else fail();
}

/** Complete N proof. The returned view is internal data, never inherited authority. */
export function prepareCompleteOccurrences(seed, fragments, receipts) {
  const catalog = occurrenceCatalog(fragments),
    entries = new Map(),
    edgeKeys = new Set(),
    owners = new Map(),
    bindings = new Map(),
    provenance = [];
  for (const receipt of receipts) {
    if (
      !keys(receipt, "entries,owner,reason,rootBindings,ticket,transitions") ||
      !metadata(receipt) ||
      !Array.isArray(receipt.entries) ||
      !receipt.entries.length ||
      !Array.isArray(receipt.transitions) ||
      !Array.isArray(receipt.rootBindings)
    )
      fail();
    const reference = digest({ schemaVersion: 10, receipt }),
      owned = new Set();
    const proof = {
      reference,
      receipt: structuredClone(receipt),
      entries: [],
      transitions: [],
      rootBindings: [],
    };
    for (const decision of receipt.entries) {
      const originals = catalog.entries.get(decision?.id),
        route = originals?.[0]?.entry.kind === "next-route";
      if (
        !keys(
          decision,
          route
            ? "effectiveMetadata,id,occurrences,sourceBinding"
            : "effectiveMetadata,id,occurrences",
        ) ||
        !keys(decision.effectiveMetadata, "owner,reason,ticket") ||
        !metadata(decision.effectiveMetadata) ||
        entries.has(decision.id) ||
        seed.entries.some((e) => e.id === decision.id)
      )
        fail();
      match(decision.occurrences, originals);
      originals.forEach(({ entry }) => valid(entry));
      if (originals.some(({ entry }) => stable(free(entry)) !== stable(free(originals[0].entry))))
        fail();
      entries.set(decision.id, {
        ...structuredClone(originals[0].entry),
        ...decision.effectiveMetadata,
      });
      owners.set(decision.id, { reference, decision, originals });
      owned.add(decision.id);
      proof.entries.push({
        id: decision.id,
        occurrences: structuredClone(originals).sort((a, b) => stable(a).localeCompare(stable(b))),
      });
    }
    for (const decision of receipt.entries) {
      const entry = entries.get(decision.id);
      if (entry.kind !== "next-route") continue;
      const binding = decision.sourceBinding,
        paired = receipt.entries.find((d) => d.id === binding?.id),
        sentinel = entries.get(binding?.id);
      if (
        !keys(binding, "file,fingerprint,id,occurrences") ||
        !paired ||
        !sentinel ||
        sentinel.kind !== "permission-source-sentinel" ||
        sentinel.disposition !== "EXEMPT" ||
        binding.file !== entry.file ||
        sentinel.file !== entry.file ||
        sentinel.handler !== "next" ||
        binding.id !==
          `permission-source-sentinel:next:${entry.file}#sha256:${binding.fingerprint}` ||
        !hash(binding.fingerprint) ||
        !sameSet(binding.occurrences, paired.occurrences)
      )
        fail();
      for (const original of catalog.entries.get(entry.id))
        if (
          !catalog.entries
            .get(sentinel.id)
            .some(
              (o) =>
                o.fragment === original.fragment &&
                binding.occurrences.some(
                  (r) => r.fragment === o.fragment && r.attestation === o.attestation,
                ),
            )
        )
          fail();
    }
    for (const decision of receipt.transitions) {
      if (
        !keys(decision, "field,id,occurrences,target") ||
        decision.field !== "replacedBy" ||
        !owned.has(decision.target) ||
        entries.get(decision.target).kind !== "permission-source-sentinel" ||
        entries.get(decision.target).replaces !== decision.id ||
        occurrenceFamily(decision.id) !== occurrenceFamily(decision.target)
      )
        fail();
      const edge = { id: decision.id, field: decision.field, target: decision.target },
        k = stable(edge);
      if (edgeKeys.has(k)) fail();
      match(decision.occurrences, catalog.edges.get(k));
      edgeKeys.add(k);
      proof.transitions.push({
        ...edge,
        occurrences: structuredClone(catalog.edges.get(k)).sort((a, b) =>
          stable(a).localeCompare(stable(b)),
        ),
      });
    }
    for (const [k, all] of catalog.edges)
      if (all.length > 1 && owned.has(all[0].edge.target) && !edgeKeys.has(k)) fail();
    for (const binding of receipt.rootBindings) {
      if (
        !keys(binding, "entryIds,family,rootReceipt,rootReceiptFragment,rootRefs") ||
        !hash(binding.rootReceipt) ||
        !hash(binding.rootReceiptFragment) ||
        bindings.has(binding.family) ||
        !Array.isArray(binding.entryIds) ||
        !binding.entryIds.length ||
        !Array.isArray(binding.rootRefs)
      )
        fail();
      const rootFragment = fragments.find(
          (f) => digest(f) === binding.rootReceiptFragment && f.schemaVersion === 8,
        ),
        root = rootFragment?.rootReconciliations?.find(
          (r) => digest({ schemaVersion: 8, receipt: r }) === binding.rootReceipt,
        );
      const expected = [...owned].filter((id) => occurrenceFamily(id) === binding.family).sort();
      if (
        !root ||
        root.family !== binding.family ||
        !sameSet(binding.rootRefs, root.roots) ||
        stable(binding.rootRefs) !== stable(root.roots) ||
        !sameSet(binding.entryIds, expected) ||
        !expected.length
      )
        fail();
      for (const r of root.roots) {
        const originals = catalog.entries.get(r.id);
        if (!originals?.some((o) => o.fragment === r.fragment && o.attestation === r.attestation))
          fail();
      }
      bindings.set(binding.family, { ...structuredClone(binding), owner: reference });
      proof.rootBindings.push(structuredClone(binding));
    }
    provenance.push(proof);
  }
  // Any duplicated family claimed by schema8 requires an explicit composition claim.
  for (const f of fragments)
    for (const root of f.rootReconciliations ?? []) {
      const affected = [...owners.keys()].filter((id) => occurrenceFamily(id) === root.family);
      if (affected.length && !bindings.has(root.family)) fail();
    }
  const result = {
    catalog,
    entries,
    edgeKeys,
    owners,
    bindings,
    provenance: provenance.sort((a, b) => a.reference.localeCompare(b.reference)),
  };
  trustedViews.set(result, viewSnapshot(result));
  return result;
}

/** Exact historical subsets, before constructing a unique map. Never inject nodes. */
export function projectOccurrenceSubset(
  seed,
  localFragments,
  fullFragments,
  effectiveEntries,
  decisions,
  { historical = false, requireHistorical = false } = {},
) {
  if (requireHistorical && !historical) fail();
  const full = occurrenceCatalog(fullFragments),
    local = occurrenceCatalog(localFragments),
    entries = new Map(),
    edges = new Set();
  const files = new Set(decisions.map((d) => full.entries.get(d.id)?.[0]?.entry.file)),
    families = new Set(decisions.map((d) => occurrenceFamily(d.id)).filter(Boolean));
  for (const f of localFragments) {
    for (const e of f.entries)
      if (
        files.has(e.file) &&
        (e.kind === "permission-source-sentinel" || e.kind === "next-route") &&
        !full.entries
          .get(e.id)
          ?.some((o) => o.fragment === digest(f) && o.attestation === digest(e))
      )
        fail();
    for (const edge of f.transitions)
      if (
        families.has(occurrenceFamily(edge.id)) ||
        families.has(occurrenceFamily(edge.target)) ||
        decisions.some((d) => d.id === edge.id || d.id === edge.target)
      ) {
        if (
          !full.edges
            .get(stable(edge))
            ?.some((o) => o.fragment === digest(f) && o.attestation === digest(edge))
        )
          fail();
      }
  }
  for (const decision of decisions) {
    const originals = full.entries.get(decision.id),
      present = local.entries.get(decision.id),
      effective = effectiveEntries.get(decision.id);
    if (!originals || !effective) fail();
    if (!present) {
      const sample = originals[0].entry,
        family = occurrenceFamily(sample.id);
      const relevant = (e) =>
        e.id === sample.id ||
        ((e.kind === "permission-source-sentinel" || e.kind === "next-route") &&
          e.file === sample.file);
      const unknown =
        seed.entries.some((e) => e.id === sample.id) ||
        localFragments.some((f) =>
          f.entries.some(
            (e) =>
              relevant(e) &&
              !full.entries
                .get(e.id)
                ?.some((o) => o.fragment === digest(f) && o.attestation === digest(e)),
          ),
        );
      const touching = localFragments.some((f) =>
        f.transitions.some((e) => e.id === sample.id || e.target === sample.id),
      );
      if (!historical || unknown || touching) fail();
      continue;
    }
    for (const occurrence of present)
      if (
        !originals.some(
          (o) =>
            o.fragment === occurrence.fragment &&
            o.attestation === occurrence.attestation &&
            stable(o.entry) === stable(occurrence.entry),
        )
      )
        fail();
    entries.set(decision.id, {
      ...structuredClone(present[0].entry),
      reason: effective.reason,
      owner: effective.owner,
      ticket: effective.ticket,
    });
    for (const [k, all] of local.edges)
      if (all.length > 1 && all[0].edge.target === decision.id) {
        const proven = full.edges.get(k);
        if (
          !proven ||
          all.some(
            (o) =>
              !proven.some((p) => p.fragment === o.fragment && p.attestation === o.attestation),
          )
        )
          fail();
        edges.add(k);
      }
  }
  return { entries, edges };
}
