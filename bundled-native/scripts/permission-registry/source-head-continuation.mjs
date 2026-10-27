import { digest, stable } from "./ledger-format.mjs";
import { sourceHeadFamily, validateSourceHeadSelections } from "./source-head-selection.mjs";

export const SOURCE_HEAD_CONTINUATION_FAMILIES = Object.freeze([
  "permission-source-sentinel:next:apps/web/app/app/crm/crm-board.tsx",
  "permission-source-sentinel:next:apps/web/app/lib/crm-freshness/cache.ts",
  "permission-source-sentinel:next:apps/web/app/app/crm/crm-board-window.ts",
]);
const fail = () => {
  throw new Error("INVALID_PERMISSION_SOURCE_HEAD_CONTINUATION");
};
const keys = (o, expected) =>
  o && typeof o === "object" && !Array.isArray(o) && Object.keys(o).sort().join(",") === expected;
const hash = (x) => typeof x === "string" && /^[a-f0-9]{64}$/u.test(x);
export const sourceHeadReceiptReference = (schemaVersion, receipt) =>
  digest({ schemaVersion, receipt });
export const sourceHeadClassificationDigest = (fragment) =>
  digest({
    schemaVersion: 1,
    entries: fragment.entries,
    transitions: fragment.transitions,
  });

function validateEnvelope(f) {
  if (
    !keys(f, "entries,schemaVersion,sourceHeadContinuations,transitions") ||
    f.schemaVersion !== 12 ||
    !Array.isArray(f.entries) ||
    !Array.isArray(f.transitions) ||
    !Array.isArray(f.sourceHeadContinuations) ||
    !f.sourceHeadContinuations.length ||
    f.sourceHeadContinuations.length > SOURCE_HEAD_CONTINUATION_FAMILIES.length
  )
    fail();
  const families = new Set();
  for (const r of f.sourceHeadContinuations) {
    if (
      !keys(r, "classification,family,head,lineage,owner,previous,reason,ticket") ||
      !SOURCE_HEAD_CONTINUATION_FAMILIES.includes(r.family) ||
      families.has(r.family) ||
      !keys(r.previous, "fragment,receipt") ||
      !hash(r.previous.fragment) ||
      !hash(r.previous.receipt) ||
      !hash(r.classification) ||
      r.classification !== sourceHeadClassificationDigest(f) ||
      ![r.reason, r.owner, r.ticket].every((x) => typeof x === "string" && x.trim()) ||
      r.reason.trim().length < 12 ||
      r.owner.trim().length < 2 ||
      r.ticket.trim().length < 3 ||
      !Array.isArray(r.lineage) ||
      r.lineage.length < 3 ||
      sourceHeadFamily(r.head) !== r.family
    )
      fail();
    families.add(r.family);
  }
}

/** Pure validation only. Neither raw fragments nor its return value confer authority. */
export function validateSourceHeadContinuations(fragments, ledger) {
  return validateContinuations(fragments, ledger);
}

/** Pure validation of a reader-authenticated origin. This function issues no capability. */
export function validateStructuralSourceHeadContinuations(fragments, ledger, origin) {
  return validateContinuations(fragments, ledger, origin);
}

function validateContinuations(fragments, ledger, structuralOrigin) {
  const continuationFragments = fragments.filter((f) => f.schemaVersion === 12);
  if (!continuationFragments.length && !structuralOrigin)
    return validateSourceHeadSelections(fragments, ledger);
  const catalog = new Map();
  const origins = new Map();
  const records = [];
  for (const f of fragments) {
    if (f.schemaVersion === 12) validateEnvelope(f);
    const receipts =
      f.schemaVersion === 11
        ? f.sourceHeadSelections
        : f.schemaVersion === 12
          ? f.sourceHeadContinuations
          : [];
    if (!Array.isArray(receipts)) fail();
    for (const receipt of receipts) {
      // Exact whole parent fragments and their old chain were independently validated
      // by the owning history reader. A post-merge continuation must start at the authenticated structural anchor.
      if (
        structuralOrigin &&
        receipt.family === structuralOrigin.family &&
        structuralOrigin.parentHashes.has(digest(f))
      )
        continue;
      const record = { fragment: f, receipt, schemaVersion: f.schemaVersion };
      const ref = stable({
        fragment: digest(f),
        receipt: sourceHeadReceiptReference(f.schemaVersion, receipt),
      });
      if (catalog.has(ref)) fail();
      catalog.set(ref, record);
      if (f.schemaVersion === 11) {
        if (origins.has(receipt.family)) fail();
        origins.set(receipt.family, record);
      } else records.push(record);
    }
  }
  if (structuralOrigin) {
    const record = {
      receipt: structuralOrigin.selection,
      schemaVersion: structuralOrigin.schemaVersion ?? 13,
    };
    if (origins.has(structuralOrigin.family) || catalog.has(stable(structuralOrigin.anchor)))
      fail();
    origins.set(structuralOrigin.family, record);
    catalog.set(stable(structuralOrigin.anchor), record);
  }
  const successors = new Map();
  for (const record of records) {
    const previous = catalog.get(stable(record.receipt.previous));
    if (
      !previous ||
      previous === record ||
      previous.receipt.family !== record.receipt.family ||
      successors.has(previous)
    )
      fail();
    successors.set(previous, record);
  }
  const used = new Set();
  const originalEntries = structuredClone(ledger.entries);
  const effective = new Map();
  for (const [family, origin] of origins) {
    const chain = [origin];
    while (successors.has(chain.at(-1))) {
      const next = successors.get(chain.at(-1));
      if (used.has(next) || chain.includes(next)) fail();
      used.add(next);
      chain.push(next);
    }
    if (chain.length === 1) continue;
    let current = ledger.entries
      .filter((e) => sourceHeadFamily(e.id) === family)
      .map((e) => structuredClone(e));
    for (let i = chain.length - 1; i > 0; i--) {
      const { receipt: r, fragment: f } = chain[i];
      const previous = chain[i - 1].receipt;
      if (
        r.lineage.length !== previous.lineage.length + 1 ||
        current.length !== r.lineage.length ||
        r.head !== r.lineage.at(-1)?.id
      )
        fail();
      const seen = new Set(),
        byid = new Map(current.map((e) => [e.id, e]));
      for (let j = 0; j < r.lineage.length; j++) {
        const ref = r.lineage[j],
          e = byid.get(ref?.id);
        if (
          !keys(ref, "attestation,id") ||
          !e ||
          seen.has(e.id) ||
          !hash(ref.attestation) ||
          ref.attestation !== digest(e) ||
          sourceHeadFamily(e.id) !== family ||
          e.replaces !== r.lineage[j - 1]?.id ||
          e.replacedBy !== r.lineage[j + 1]?.id
        )
          fail();
        seen.add(e.id);
      }
      if (previous.lineage.some((ref, j) => ref.id !== r.lineage[j]?.id)) fail();
      const tail = byid.get(r.head),
        terminalId = previous.lineage.at(-1).id;
      const terminal = byid.get(terminalId);
      const allowed = [
        "id",
        "kind",
        "tags",
        "file",
        "handler",
        "handlerFile",
        "disposition",
        "reason",
        "owner",
        "ticket",
        "replaces",
        "replacedBy",
      ];
      if (
        !tail ||
        tail.kind !== "permission-source-sentinel" ||
        tail.disposition !== "EXEMPT" ||
        Object.keys(tail).some((k) => !allowed.includes(k)) ||
        tail.replaces !== terminalId ||
        tail.replacedBy !== undefined ||
        terminal?.replacedBy !== tail.id
      )
        fail();
      const additions = f.entries.filter((e) => sourceHeadFamily(e.id) === family);
      const edges = f.transitions.filter(
        (e) => sourceHeadFamily(e.id) === family || sourceHeadFamily(e.target) === family,
      );
      if (
        additions.length !== 1 ||
        stable(additions[0]) !== stable(tail) ||
        edges.length !== 1 ||
        !keys(edges[0], "field,id,target") ||
        edges[0].id !== terminalId ||
        edges[0].field !== "replacedBy" ||
        edges[0].target !== tail.id
      )
        fail();
      current = current.filter((e) => e.id !== tail.id);
      delete current.find((e) => e.id === terminalId).replacedBy;
      const old = new Map(current.map((e) => [e.id, e]));
      if (previous.lineage.some((ref) => digest(old.get(ref.id)) !== ref.attestation)) fail();
    }
    const restored = new Map(current.map((e) => [e.id, e]));
    for (let i = originalEntries.length - 1; i >= 0; i--) {
      if (sourceHeadFamily(originalEntries[i].id) !== family) continue;
      if (restored.has(originalEntries[i].id))
        originalEntries[i] = restored.get(originalEntries[i].id);
      else originalEntries.splice(i, 1);
    }
    const last = chain.at(-1).receipt;
    effective.set(family, {
      family,
      head: last.head,
      lineage: structuredClone(last.lineage),
      reason: last.reason,
      owner: last.owner,
      ticket: last.ticket,
    });
  }
  if (used.size !== records.length) fail();
  // The original validator remains unchanged; only precisely proven tails were peeled.
  // This projection is only for the unchanged selection validator, never for
  // fragment hashes, receipt references, assembly or whole-file validation.
  const originalFragments = fragments
    .filter((f) => f.schemaVersion !== 12)
    .flatMap((f) => {
      if (!structuralOrigin || f.schemaVersion !== 11) return [f];
      const remaining = f.sourceHeadSelections.filter((r) => r.family !== structuralOrigin.family);
      return remaining.length ? [{ ...f, sourceHeadSelections: remaining }] : [];
    });
  const originals = validateSourceHeadSelections(originalFragments, {
    ...ledger,
    entries: originalEntries,
  });
  if (structuralOrigin) {
    const restored = originalEntries.filter(
      (e) => sourceHeadFamily(e.id) === structuralOrigin.family,
    );
    const byid = new Map(restored.map((e) => [e.id, e]));
    if (
      restored.length !== structuralOrigin.selection.lineage.length ||
      structuralOrigin.selection.lineage.some(
        (ref) => !byid.has(ref.id) || digest(byid.get(ref.id)) !== ref.attestation,
      )
    )
      fail();
    // Rebased attestations do not replace the original selector semantics.
    // This validation-only projection checks the head, disposition suffix,
    // legacy prefix and complete entry-key whitelist with the same validator.
    const rebased = validateSourceHeadSelections(
      [
        ...originalFragments.filter((f) => f.schemaVersion !== 11),
        {
          schemaVersion: 11,
          entries: [],
          transitions: [],
          sourceHeadSelections: [structuralOrigin.selection],
        },
      ],
      { ...ledger, entries: originalEntries },
    );
    originals.push(...rebased);
  }
  return originals.map((r) => effective.get(r.family) ?? r);
}
