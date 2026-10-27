import { assertCompleteOccurrenceView } from "./complete-occurrence-history.mjs";
import { digest, stable } from "./ledger-format.mjs";

const failure = () => {
  throw new Error("INVALID_PERMISSION_SURFACE_ROOT_RECONCILIATION");
};
const familyOf = (id) =>
  typeof id === "string" && /^permission-source-sentinel:[^:]+:.+#sha256:[a-f0-9]{64}$/u.test(id)
    ? id.slice(0, id.lastIndexOf("#sha256:"))
    : null;
const exactKeys = (value, keys) =>
  value &&
  typeof value === "object" &&
  !Array.isArray(value) &&
  Object.keys(value).sort().join(",") === keys;
const metadata = (r) =>
  [r?.reason, r?.owner, r?.ticket].every((v) => typeof v === "string" && v.trim()) &&
  r.reason.trim().length >= 12 &&
  r.owner.trim().length >= 2 &&
  r.ticket.trim().length >= 3;
const exactSet = (a, b) =>
  Array.isArray(a) &&
  a.length === b.length &&
  new Set(a).size === a.length &&
  new Set(b).size === b.length &&
  a.every((id) => b.includes(id));
const refOf = (fragment, entry) => ({ fragment: digest(fragment), attestation: digest(entry) });
const identity = (entry) => {
  const { id, reason, owner, ticket, replaces, ...rest } = entry;
  return rest;
};

/** Complete raw family validation. This function creates no history links. */
function validateFamily(seedLedger, fragments, receipt, occurrenceView) {
  if (occurrenceView) assertCompleteOccurrenceView(occurrenceView);
  if (
    !exactKeys(receipt, "family,lineage,owner,reason,roots,ticket") ||
    !metadata(receipt) ||
    typeof receipt.family !== "string" ||
    !Array.isArray(receipt.roots) ||
    receipt.roots.length < 2 ||
    !Array.isArray(receipt.lineage)
  )
    failure();
  const match = /^permission-source-sentinel:([^:]+):(.+)$/u.exec(receipt.family);
  if (!match) failure();
  const [, handler, file] = match;
  if (
    seedLedger.entries.some(
      (e) =>
        familyOf(e.id) === receipt.family ||
        (e.kind === "permission-source-sentinel" && e.file === file),
    )
  )
    failure();
  const nodes = new Map(),
    edgeRefs = [],
    outgoing = new Map(),
    incoming = new Map();
  for (const fragment of fragments) {
    for (const entry of fragment.entries) {
      if (
        familyOf(entry.id) !== receipt.family &&
        !(entry.kind === "permission-source-sentinel" && entry.file === file)
      )
        continue;
      if (
        familyOf(entry.id) !== receipt.family ||
        (nodes.has(entry.id) && !occurrenceView?.bindings.has(receipt.family)) ||
        entry.kind !== "permission-source-sentinel" ||
        entry.disposition !== "EXEMPT" ||
        Object.keys(entry).some(
          (key) =>
            ![
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
            ].includes(key),
        ) ||
        !Array.isArray(entry.tags) ||
        !entry.tags.length ||
        entry.tags.some((tag) => typeof tag !== "string" || !tag) ||
        new Set(entry.tags).size !== entry.tags.length ||
        !metadata(entry) ||
        entry.file !== file ||
        entry.handler !== handler ||
        (Object.hasOwn(entry, "handlerFile") && entry.handlerFile !== file) ||
        Object.hasOwn(entry, "replacedBy") ||
        Object.hasOwn(entry, "retiredBy") ||
        ["resourceKey", "action", "bindingProof", "codeDefinedReportId"].some((key) =>
          Object.hasOwn(entry, key),
        )
      )
        failure();
      const claim = occurrenceView?.owners.get(entry.id);
      const binding = occurrenceView?.bindings.get(receipt.family);
      if (nodes.has(entry.id) && (!claim || !binding?.entryIds.includes(entry.id))) failure();
      if (
        claim &&
        (!binding ||
          !claim.originals.some(
            (o) => o.fragment === digest(fragment) && o.attestation === digest(entry),
          ))
      )
        failure();
      const node = nodes.get(entry.id) ?? {
        id: entry.id,
        ...refOf(fragment, entry),
        entry: claim ? structuredClone(occurrenceView.entries.get(entry.id)) : entry,
        originals: [],
      };
      node.originals.push({ ...refOf(fragment, entry), entry });
      nodes.set(entry.id, node);
    }
    for (const old of [
      fragment.reconciliations,
      fragment.spliceReconciliations,
      fragment.compositionReconciliations,
      fragment.compositionExtensions,
      fragment.compositionSupersessions,
      fragment.occurrenceReconciliations,
    ].flatMap((x) => x ?? [])) {
      if (
        familyOf(old.predecessor) === receipt.family ||
        old.entries?.some((e) => familyOf(e.id) === receipt.family)
      )
        failure();
    }
  }
  if (!nodes.size) failure();
  for (const fragment of fragments)
    for (const edge of fragment.transitions) {
      if (familyOf(edge.id) !== receipt.family && familyOf(edge.target) !== receipt.family)
        continue;
      if (
        !exactKeys(edge, "field,id,target") ||
        edge.field !== "replacedBy" ||
        !nodes.has(edge.id) ||
        !nodes.has(edge.target) ||
        (outgoing.has(edge.id) &&
          !(
            occurrenceView?.bindings.has(receipt.family) &&
            occurrenceView.edgeKeys.has(stable(edge)) &&
            outgoing.get(edge.id) === edge.target
          )) ||
        (incoming.has(edge.target) &&
          !(
            occurrenceView?.bindings.has(receipt.family) &&
            occurrenceView.edgeKeys.has(stable(edge)) &&
            incoming.get(edge.target) === edge.id
          ))
      )
        failure();
      outgoing.set(edge.id, edge.target);
      incoming.set(edge.target, edge.id);
      edgeRefs.push({ ...refOf(fragment, edge), edge });
    }
  const roots = [...nodes.values()].filter(
    ({ entry }) => !Object.hasOwn(entry, "replaces") && !incoming.has(entry.id),
  );
  if (
    !exactSet(
      receipt.roots.map((r) => r?.id),
      roots.map((r) => r.id),
    ) ||
    !exactSet(
      receipt.lineage,
      roots.map((r) => r.id),
    )
  )
    failure();
  for (const ref of receipt.roots) {
    if (
      !exactKeys(ref, "attestation,fragment,id") ||
      !/^[a-f0-9]{64}$/u.test(ref.fragment) ||
      !/^[a-f0-9]{64}$/u.test(ref.attestation)
    )
      failure();
    const occurrence = nodes.get(ref.id);
    if (
      !occurrence.originals.some(
        (original) =>
          ref.fragment === original.fragment && ref.attestation === original.attestation,
      )
    )
      failure();
  }
  const first = nodes.get(receipt.lineage[0]).entry;
  for (const { entry } of nodes.values()) {
    if (stable(identity(entry)) !== stable(identity(first))) failure();
    if (Object.hasOwn(entry, "replaces") && incoming.get(entry.id) !== entry.replaces) failure();
    if (!Object.hasOwn(entry, "replaces") && incoming.has(entry.id)) failure();
  }
  const rootIds = new Set(receipt.lineage);
  for (const id of receipt.lineage.slice(0, -1)) if (outgoing.has(id)) failure();
  const lineage = [...receipt.lineage],
    visited = new Set(lineage);
  let tail = lineage.at(-1);
  while (outgoing.has(tail)) {
    const next = outgoing.get(tail);
    if (visited.has(next) || rootIds.has(next) || nodes.get(next).entry.replaces !== tail)
      failure();
    lineage.push(next);
    visited.add(next);
    tail = next;
  }
  if (!exactSet(lineage, [...nodes.keys()])) failure();
  const effective = new Map(
    [...nodes].map(([id, occurrence]) => [id, structuredClone(occurrence.entry)]),
  );
  const joins = [];
  for (let i = 1; i < receipt.lineage.length; i++) {
    const id = receipt.lineage[i - 1],
      target = receipt.lineage[i];
    effective.get(id).replacedBy = target;
    effective.get(target).replaces = id;
    joins.push({ id, target, kind: "derived-root-join" });
  }
  for (const [id, target] of outgoing) effective.get(id).replacedBy = target;
  return { nodes, edgeRefs, effective, joins, lineage };
}

/** Apply only reviewed virtual root joins, keeping the original raw fragments intact. */
export function reconcileRootFamilies(
  seedLedger,
  fragments,
  entries,
  groups,
  receipts,
  inheritedEvidence,
  historicalProjection,
  occurrenceView,
) {
  const families = new Set(),
    projected = new Map(),
    provenance = [],
    referenceHashes = new Set();
  for (const receipt of receipts) {
    if (families.has(receipt?.family)) failure();
    families.add(receipt?.family);
    let localView = occurrenceView;
    if (historicalProjection && !localView?.bindings.has(receipt.family)) {
      // An unchanged local root receipt may use its issuing union's complete
      // metadata proof. validateFamily still inventories only local raw bytes.
      const views = new Set(
        inheritedEvidence
          .filter(
            (evidence) =>
              evidence.occurrenceView?.bindings.has(receipt.family) &&
              evidence.rootReconciliations.some((r) => stable(r) === stable(receipt)),
          )
          .map((evidence) => evidence.occurrenceView),
      );
      if (views.size > 1) failure();
      if (views.size === 1) localView = [...views][0];
    }
    const proof = validateFamily(seedLedger, fragments, receipt, localView);
    for (const [id, entry] of proof.effective) {
      const derived = structuredClone(entry);
      delete derived.replacedBy;
      entries.set(id, derived);
      projected.set(id, stable(entry));
    }
    for (const { id, target } of proof.joins) groups.set(id, [{ id, field: "replacedBy", target }]);
    for (const ref of [...proof.nodes.values(), ...proof.edgeRefs])
      referenceHashes.add(ref.fragment);
    provenance.push({
      reference: digest({ schemaVersion: 8, receipt }),
      receipt: structuredClone(receipt),
      originals: structuredClone([...proof.nodes.values()]).sort((a, b) =>
        a.id.localeCompare(b.id),
      ),
      joins: proof.joins,
      lineage: proof.lineage,
      ...(localView?.bindings.has(receipt.family)
        ? { occurrenceBinding: structuredClone(localView.bindings.get(receipt.family)) }
        : {}),
    });
  }
  for (const evidence of inheritedEvidence) {
    if (!historicalProjection) failure();
    for (const receipt of evidence.rootReconciliations) {
      const proof = validateFamily(
        seedLedger,
        evidence.fragments,
        receipt,
        evidence.occurrenceView,
      );
      const localNodes = fragments
        .flatMap((f) => f.entries.map((entry) => ({ ...refOf(f, entry), entry })))
        .filter(
          ({ entry }) =>
            familyOf(entry.id) === receipt.family ||
            (entry.kind === "permission-source-sentinel" &&
              entry.file === proof.nodes.values().next().value.entry.file),
        );
      if (!localNodes.length) {
        const file = proof.nodes.values().next().value.entry.file;
        const existing = [...entries.values()].some(
          (entry) =>
            familyOf(entry.id) === receipt.family ||
            (entry.kind === "permission-source-sentinel" && entry.file === file),
        );
        const touchingEdge = fragments.some((fragment) =>
          fragment.transitions.some(
            (edge) =>
              familyOf(edge.id) === receipt.family || familyOf(edge.target) === receipt.family,
          ),
        );
        if (existing || touchingEdge) failure();
        // Full trusted evidence was validated above. This family is a future
        // addition; historical comparison must not inject entries or joins.
        continue;
      }
      if (!localNodes.some(({ entry }) => receipt.lineage.includes(entry.id))) failure();
      for (const local of localNodes) {
        const original = proof.nodes.get(local.entry.id);
        const entry = structuredClone(
          evidence.occurrenceView?.entries.get(local.entry.id) ?? local.entry,
        );
        // Project only reviewed root joins, never a future raw tail edge absent
        // from this historical snapshot. Ordinary evolution must check that tail.
        for (const join of proof.joins) {
          if (join.id === entry.id) entry.replacedBy = join.target;
          if (join.target === entry.id) entry.replaces = join.id;
        }
        const localOutgoing = groups.get(entry.id);
        if (localOutgoing) {
          if (localOutgoing.length !== 1 || localOutgoing[0].field !== "replacedBy") failure();
          entry.replacedBy = localOutgoing[0].target;
        }
        if (
          !original ||
          !original.originals.some(
            (o) =>
              local.fragment === o.fragment &&
              local.attestation === o.attestation &&
              stable(local.entry) === stable(o.entry),
          )
        )
          failure();
        if (projected.has(local.entry.id) && projected.get(local.entry.id) !== stable(entry))
          failure();
        const derived = structuredClone(entry);
        if (groups.has(local.entry.id)) delete derived.replacedBy;
        entries.set(local.entry.id, derived);
        projected.set(local.entry.id, stable(entry));
      }
      for (const fragment of fragments)
        for (const edge of fragment.transitions) {
          if (familyOf(edge.id) !== receipt.family && familyOf(edge.target) !== receipt.family)
            continue;
          if (
            !proof.edgeRefs.some(
              (ref) => ref.fragment === digest(fragment) && ref.attestation === digest(edge),
            )
          )
            failure();
        }
      // Comparison view only: absent peer nodes/edges are never loaded into the base.
      provenance.push({
        reference: digest({ schemaVersion: 8, receipt }),
        receipt: structuredClone(receipt),
        historicalProjection: true,
        localIds: localNodes.map(({ entry }) => entry.id).sort(),
      });
    }
  }
  const evidence = receipts.length
    ? {
        rootEvidence: true,
        rootReconciliations: structuredClone(receipts).sort((a, b) =>
          digest(a).localeCompare(digest(b)),
        ),
        fragments: structuredClone(fragments.filter((f) => referenceHashes.has(digest(f)))).sort(
          (a, b) => digest(a).localeCompare(digest(b)),
        ),
      }
    : null;
  return {
    provenance: [...new Map(provenance.map((proof) => [digest(proof), proof])).values()].sort(
      (a, b) => a.reference.localeCompare(b.reference),
    ),
    evidence,
  };
}
