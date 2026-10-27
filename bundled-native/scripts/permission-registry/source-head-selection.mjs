import { digest } from "./ledger-format.mjs";

const fail = () => {
  throw new Error("INVALID_PERMISSION_SOURCE_HEAD_SELECTION");
};
export const sourceHeadFamily = (id) =>
  /^permission-source-sentinel:[^:]+:.+#sha256:[a-f0-9]{64}$/u.test(id ?? "")
    ? id.slice(0, id.lastIndexOf("#sha256:"))
    : null;

/** Validate against already fully assembled, unchanged historical entries. No issuance here. */
export function validateSourceHeadSelections(fragments, ledger) {
  const selections = [];
  const families = new Set();
  const structural = fragments.flatMap((f) => [
    ...(f.reconciliations ?? []),
    ...(f.spliceReconciliations ?? []),
    ...(f.compositionReconciliations ?? []),
    ...(f.compositionExtensions ?? []),
    ...(f.compositionSupersessions ?? []),
  ]);
  for (const f of fragments.filter((f) => f.schemaVersion === 11)) {
    if (
      f.entries.length ||
      f.transitions.length ||
      !Array.isArray(f.sourceHeadSelections) ||
      !f.sourceHeadSelections.length
    )
      fail();
    for (const r of f.sourceHeadSelections) {
      if (
        !r ||
        Object.keys(r).sort().join(",") !== "family,head,lineage,owner,reason,ticket" ||
        ![r.reason, r.owner, r.ticket].every((v) => typeof v === "string" && v.trim()) ||
        r.reason.trim().length < 12 ||
        r.owner.trim().length < 2 ||
        r.ticket.trim().length < 3 ||
        typeof r.family !== "string" ||
        families.has(r.family) ||
        !Array.isArray(r.lineage) ||
        r.lineage.length < 2
      )
        fail();
      const entries = ledger.entries.filter((e) => sourceHeadFamily(e.id) === r.family);
      const recorded = new Map(entries.map((e) => [e.id, e]));
      if (
        entries.length !== r.lineage.length ||
        !structural.some((s) => sourceHeadFamily(s.predecessor) === r.family)
      )
        fail();
      const seen = new Set();
      const headIndex = r.lineage.findIndex((ref) => ref?.id === r.head);
      if (headIndex < 0 || !r.family.startsWith("permission-source-sentinel:next:")) fail();
      for (let i = 0; i < r.lineage.length; i++) {
        const ref = r.lineage[i],
          e = recorded.get(ref?.id);
        if (
          !ref ||
          Object.keys(ref).sort().join(",") !== "attestation,id" ||
          !e ||
          seen.has(e.id) ||
          e.kind !== "permission-source-sentinel" ||
          (e.disposition !== "EXEMPT" && !(i < headIndex && e.disposition === "LEGACY_BASELINE")) ||
          e.retiredBy ||
          Object.keys(e).some(
            (k) =>
              ![
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
                "introducedAtOrBefore",
              ].includes(k),
          ) ||
          ref.attestation !== digest(e) ||
          e.replaces !== r.lineage[i - 1]?.id ||
          e.replacedBy !== r.lineage[i + 1]?.id
        )
          fail();
        seen.add(e.id);
      }
      if (!seen.has(r.head) || r.head === r.lineage.at(-1).id) fail();
      families.add(r.family);
      selections.push(structuredClone(r));
    }
  }
  return selections;
}
