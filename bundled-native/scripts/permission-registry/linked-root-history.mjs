import { digest, stable } from "./ledger-format.mjs";

const fail = () => {
  throw new Error("INVALID_PERMISSION_SURFACE_LINKED_ROOT_RECONCILIATION");
};
const familyOf = (id) =>
  typeof id === "string" && /^permission-source-sentinel:[^:]+:.+#sha256:[a-f0-9]{64}$/u.test(id)
    ? id.slice(0, id.lastIndexOf("#sha256:"))
    : null;
const keys = (value, expected) =>
  value &&
  typeof value === "object" &&
  !Array.isArray(value) &&
  Object.keys(value).sort().join(",") === expected;
const metadata = (value) =>
  [value?.reason, value?.owner, value?.ticket].every((v) => typeof v === "string" && v.trim()) &&
  value.reason.trim().length >= 12 &&
  value.owner.trim().length >= 2 &&
  value.ticket.trim().length >= 3;
const hash = (value) => typeof value === "string" && /^[a-f0-9]{64}$/u.test(value);
const ref = (fragment, entry) => ({ fragment: digest(fragment), attestation: digest(entry) });
const identity = ({ id, reason, owner, ticket, replaces, ...rest }) => rest;
const mentions = (value, family) =>
  typeof value === "string"
    ? familyOf(value) === family || value === family
    : Array.isArray(value)
      ? value.some((v) => mentions(v, family))
      : value && typeof value === "object"
        ? Object.values(value).some((v) => mentions(v, family))
        : false;

/** Full raw proof; no linked/root exception exists without these exact attestations. */
function validate(seed, fragments, receipt) {
  if (
    !keys(receipt, "entry,owner,predecessor,reason,ticket,transition") ||
    !metadata(receipt) ||
    !keys(receipt.entry, "effectiveMetadata,id,occurrences") ||
    !keys(receipt.entry.effectiveMetadata, "owner,reason,ticket") ||
    !metadata(receipt.entry.effectiveMetadata) ||
    !Array.isArray(receipt.entry.occurrences) ||
    receipt.entry.occurrences.length !== 2 ||
    !keys(receipt.predecessor, "attestation,fragment,id") ||
    !keys(receipt.transition, "attestation,field,fragment,id,target")
  )
    fail();
  const family = familyOf(receipt.entry.id),
    P = receipt.predecessor.id,
    S = receipt.entry.id;
  if (
    !family ||
    P === S ||
    familyOf(P) !== family ||
    receipt.transition.id !== P ||
    receipt.transition.target !== S ||
    receipt.transition.field !== "replacedBy"
  )
    fail();
  const [, handler, file] = /^permission-source-sentinel:([^:]+):(.+)$/u.exec(family);
  const belongs = (entry) =>
    familyOf(entry.id) === family ||
    (entry.kind === "permission-source-sentinel" && entry.file === file);
  if (seed.entries.some(belongs)) fail();
  const nodes = new Map(),
    edges = [],
    outgoing = new Map(),
    incoming = new Map();
  let ownReceipts = 0;
  for (const fragment of fragments) {
    for (const entry of fragment.entries) {
      if (!belongs(entry)) continue;
      if (
        familyOf(entry.id) !== family ||
        entry.kind !== "permission-source-sentinel" ||
        entry.disposition !== "EXEMPT" ||
        !metadata(entry) ||
        entry.file !== file ||
        entry.handler !== handler ||
        (Object.hasOwn(entry, "handlerFile") && entry.handlerFile !== file) ||
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
        new Set(entry.tags).size !== entry.tags.length
      )
        fail();
      if (!nodes.has(entry.id)) nodes.set(entry.id, []);
      nodes.get(entry.id).push({ id: entry.id, ...ref(fragment, entry), entry });
    }
    for (const field of [
      "reconciliations",
      "spliceReconciliations",
      "compositionReconciliations",
      "compositionExtensions",
      "compositionSupersessions",
      "occurrenceReconciliations",
      "rootReconciliations",
      "completeOccurrenceReconciliations",
    ])
      for (const old of fragment[field] ?? []) if (mentions(old, family)) fail();
    for (const old of fragment.linkedRootReconciliations ?? []) {
      if (!mentions(old, family)) continue;
      if (stable(old) !== stable(receipt) || ++ownReceipts > 1) fail();
    }
  }
  if (
    nodes.get(S)?.length !== 2 ||
    nodes.get(P)?.length !== 1 ||
    [...nodes].some(([id, all]) => id !== S && all.length !== 1)
  )
    fail();
  const originals = nodes.get(S);
  if (
    receipt.entry.occurrences.some(
      (r) => !keys(r, "attestation,fragment") || !hash(r.fragment) || !hash(r.attestation),
    ) ||
    new Set(receipt.entry.occurrences.map(stable)).size !== 2 ||
    !originals.every((o) =>
      receipt.entry.occurrences.some(
        (r) => r.fragment === o.fragment && r.attestation === o.attestation,
      ),
    )
  )
    fail();
  const predecessor = nodes.get(P)[0];
  if (
    !hash(receipt.predecessor.fragment) ||
    !hash(receipt.predecessor.attestation) ||
    receipt.predecessor.fragment !== predecessor.fragment ||
    receipt.predecessor.attestation !== predecessor.attestation ||
    Object.hasOwn(predecessor.entry, "replaces")
  )
    fail();
  const linked = originals.filter((o) => Object.hasOwn(o.entry, "replaces")),
    roots = originals.filter((o) => !Object.hasOwn(o.entry, "replaces"));
  if (
    linked.length !== 1 ||
    roots.length !== 1 ||
    linked[0].entry.replaces !== P ||
    stable(identity(linked[0].entry)) !== stable(identity(roots[0].entry))
  )
    fail();
  for (const all of nodes.values())
    for (const { entry } of all)
      if (stable(identity(entry)) !== stable(identity(linked[0].entry))) fail();
  for (const fragment of fragments)
    for (const edge of fragment.transitions) {
      if (familyOf(edge.id) !== family && familyOf(edge.target) !== family) continue;
      if (
        !keys(edge, "field,id,target") ||
        edge.field !== "replacedBy" ||
        !nodes.has(edge.id) ||
        !nodes.has(edge.target) ||
        outgoing.has(edge.id) ||
        incoming.has(edge.target)
      )
        fail();
      outgoing.set(edge.id, edge.target);
      incoming.set(edge.target, edge.id);
      edges.push({ ...ref(fragment, edge), edge });
    }
  const provenEdge = edges.find(({ edge }) => edge.id === P && edge.target === S);
  if (
    !provenEdge ||
    incoming.has(P) ||
    incoming.get(S) !== P ||
    outgoing.get(P) !== S ||
    !hash(receipt.transition.fragment) ||
    !hash(receipt.transition.attestation) ||
    receipt.transition.fragment !== provenEdge.fragment ||
    receipt.transition.attestation !== provenEdge.attestation
  )
    fail();
  const lineage = [P, S],
    visited = new Set(lineage);
  let last = S;
  while (outgoing.has(last)) {
    const next = outgoing.get(last);
    if (
      visited.has(next) ||
      nodes.get(next).length !== 1 ||
      nodes.get(next)[0].entry.replaces !== last
    )
      fail();
    lineage.push(next);
    visited.add(next);
    last = next;
  }
  if (visited.size !== nodes.size || edges.length !== lineage.length - 1) fail();
  const canonical = { ...structuredClone(linked[0].entry), ...receipt.entry.effectiveMetadata };
  return {
    family,
    file,
    belongs,
    P,
    S,
    nodes,
    edges,
    outgoing,
    incoming,
    lineage,
    canonical,
    predecessor,
    originals,
    provenEdge,
  };
}

/** Prepare only internally validated exceptions before the normal unique-entry collector. */
export function prepareLinkedRootHistory(
  seed,
  fragments,
  receipts,
  inherited,
  historical,
  foreignInherited = [],
) {
  const canonicalEntries = new Map(),
    comparisonIncomingEdges = new Set(),
    projected = new Map(),
    projections = [],
    provenance = [],
    hashes = new Set(),
    families = new Set();
  for (const receipt of receipts) {
    const proof = validate(seed, fragments, receipt);
    if (
      foreignInherited.some((candidate) =>
        mentions(
          candidate?.occurrenceReconciliations ??
            candidate?.rootReconciliations ??
            candidate?.completeOccurrenceReconciliations ??
            candidate,
          proof.family,
        ),
      )
    )
      fail();
    if (families.has(proof.family)) fail();
    families.add(proof.family);
    canonicalEntries.set(proof.S, proof.canonical);
    for (const [id, all] of proof.nodes) {
      const entry = structuredClone(id === proof.S ? proof.canonical : all[0].entry);
      if (proof.outgoing.has(id)) entry.replacedBy = proof.outgoing.get(id);
      projected.set(id, stable(entry));
      for (const o of all) hashes.add(o.fragment);
    }
    for (const edge of proof.edges) hashes.add(edge.fragment);
    provenance.push({
      reference: digest({ schemaVersion: 9, receipt }),
      receipt: structuredClone(receipt),
      originals: structuredClone(proof.originals).sort((a, b) =>
        stable(a).localeCompare(stable(b)),
      ),
      predecessor: structuredClone(proof.predecessor),
      transition: structuredClone(proof.provenEdge),
      derived: {
        id: proof.S,
        replaces: proof.P,
        effectiveMetadata: structuredClone(receipt.entry.effectiveMetadata),
      },
    });
  }
  for (const evidence of inherited) {
    if (!historical) fail();
    for (const receipt of evidence.linkedRootReconciliations) {
      const proof = validate(seed, evidence.fragments, receipt);
      if (
        foreignInherited.some((candidate) =>
          mentions(
            candidate?.occurrenceReconciliations ??
              candidate?.rootReconciliations ??
              candidate?.completeOccurrenceReconciliations ??
              candidate,
            proof.family,
          ),
        )
      )
        fail();
      // Current raw receipt ownership remains authoritative even during historical reads.
      for (const fragment of fragments)
        for (const field of [
          "reconciliations",
          "spliceReconciliations",
          "compositionReconciliations",
          "compositionExtensions",
          "compositionSupersessions",
          "occurrenceReconciliations",
          "rootReconciliations",
          "completeOccurrenceReconciliations",
          "linkedRootReconciliations",
        ])
          for (const old of fragment[field] ?? [])
            if (
              mentions(old, proof.family) &&
              !(field === "linkedRootReconciliations" && stable(old) === stable(receipt))
            )
              fail();
      if (receipts.some((own) => stable(own) === stable(receipt))) continue;
      const locals = fragments.flatMap((fragment) =>
        fragment.entries
          .filter(proof.belongs)
          .map((entry) => ({ id: entry.id, ...ref(fragment, entry), entry })),
      );
      const localEdges = fragments.flatMap((fragment) =>
        fragment.transitions
          .filter(
            (edge) => familyOf(edge.id) === proof.family || familyOf(edge.target) === proof.family,
          )
          .map((edge) => ({ ...ref(fragment, edge), edge })),
      );
      if (!locals.length) {
        if (seed.entries.some(proof.belongs) || localEdges.length) fail();
        projections.push({ proof, entries: new Map(), absent: true });
        continue;
      }
      const localNodes = new Map();
      for (const local of locals) {
        if (
          localNodes.has(local.id) ||
          !proof.nodes
            .get(local.id)
            ?.some(
              (o) =>
                o.fragment === local.fragment &&
                o.attestation === local.attestation &&
                stable(o.entry) === stable(local.entry),
            )
        )
          fail();
        localNodes.set(local.id, local.entry);
      }
      const outgoing = new Map(),
        incoming = new Map();
      for (const local of localEdges) {
        const missingPredecessorLink =
          !localNodes.has(proof.P) &&
          !seed.entries.some((entry) => entry.id === proof.P) &&
          localNodes.get(proof.S)?.replaces === proof.P &&
          local.edge.field === "replacedBy" &&
          local.edge.id === proof.P &&
          local.edge.target === proof.S &&
          local.fragment === proof.provenEdge.fragment &&
          local.attestation === proof.provenEdge.attestation &&
          local.fragment === receipt.transition.fragment &&
          local.attestation === receipt.transition.attestation;
        if (
          !proof.edges.some(
            (o) => o.fragment === local.fragment && o.attestation === local.attestation,
          ) ||
          (!localNodes.has(local.edge.id) && !missingPredecessorLink) ||
          !localNodes.has(local.edge.target) ||
          outgoing.has(local.edge.id) ||
          incoming.has(local.edge.target)
        )
          fail();
        outgoing.set(local.edge.id, local.edge.target);
        incoming.set(local.edge.target, local.edge.id);
        if (missingPredecessorLink) comparisonIncomingEdges.add(stable(local.edge));
      }
      if (!localNodes.has(proof.S)) {
        if (localNodes.size !== 1 || !localNodes.has(proof.P) || localEdges.length) fail();
        projections.push({ proof, entries: new Map(), predecessorOnly: true });
        continue;
      }
      const S = localNodes.get(proof.S),
        hasP = localNodes.has(proof.P);
      if (
        Object.hasOwn(S, "replaces") &&
        (incoming.get(proof.S) !== proof.P ||
          (!hasP && !comparisonIncomingEdges.has(stable(proof.provenEdge.edge))))
      )
        fail();
      if (outgoing.has(proof.P) && outgoing.get(proof.P) !== proof.S) fail();
      const visited = new Set([proof.S, ...(hasP ? [proof.P] : [])]);
      let tail = proof.S;
      while (outgoing.has(tail)) {
        const next = outgoing.get(tail);
        if (visited.has(next) || localNodes.get(next)?.replaces !== tail) fail();
        visited.add(next);
        tail = next;
      }
      if (visited.size !== localNodes.size) fail();
      const values = new Map();
      values.set(proof.S, {
        ...structuredClone(S),
        ...receipt.entry.effectiveMetadata,
        replaces: proof.P,
      });
      if (hasP)
        values.set(proof.P, { ...structuredClone(localNodes.get(proof.P)), replacedBy: proof.S });
      // Compare the full effective view, including real LOCAL outgoing transitions.
      for (const [id, value] of values) {
        const view = structuredClone(value);
        if (outgoing.has(id)) view.replacedBy = outgoing.get(id);
        if (projected.has(id) && projected.get(id) !== stable(view)) fail();
        projected.set(id, stable(view));
      }
      projections.push({ proof, entries: values });
      provenance.push({
        reference: digest({ schemaVersion: 9, receipt }),
        receipt: structuredClone(receipt),
        historicalProjection: true,
        localIds: [...localNodes.keys()].sort(),
        comparisonFields: [...values].map(([id]) => ({
          id,
          fields: id === proof.S ? ["reason", "owner", "ticket", "replaces"] : ["replacedBy"],
        })),
        ...(!hasP && comparisonIncomingEdges.has(stable(proof.provenEdge.edge))
          ? { comparisonIncomingTransition: structuredClone(proof.provenEdge) }
          : {}),
      });
    }
  }
  const evidence = receipts.length
    ? {
        linkedRootEvidence: true,
        linkedRootReconciliations: structuredClone(receipts).sort((a, b) =>
          digest(a).localeCompare(digest(b)),
        ),
        fragments: structuredClone(fragments.filter((f) => hashes.has(digest(f)))).sort((a, b) =>
          digest(a).localeCompare(digest(b)),
        ),
      }
    : null;
  return {
    canonicalEntries,
    comparisonIncomingEdges,
    projections,
    evidence,
    provenance: [...new Map(provenance.map((p) => [digest(p), p])).values()].sort((a, b) =>
      a.reference.localeCompare(b.reference),
    ),
  };
}

/** Historical comparison fields never create transition groups or new entries. */
export function applyLinkedRootHistory(result, entries, groups) {
  for (const projection of result.projections) {
    if (projection.absent) {
      if ([...entries.values()].some(projection.proof.belongs)) fail();
      continue;
    }
    for (const [id, value] of projection.entries) {
      if (!entries.has(id)) fail();
      const raw = projection.proof.nodes.get(id)?.map((o) => o.entry) ?? [];
      const current = entries.get(id);
      if (
        !raw.some((original) => stable(original) === stable(current)) &&
        stable(current) !== stable(value) &&
        stable(current) !== stable((({ replacedBy, ...rest }) => rest)(value))
      )
        fail();
      const entry = structuredClone(value);
      // Ordinary local transitions still run and preserve their exact raw origin.
      if (groups.has(id)) delete entry.replacedBy;
      entries.set(id, entry);
    }
  }
}
