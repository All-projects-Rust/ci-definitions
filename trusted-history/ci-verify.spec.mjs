import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";
import { test } from "node:test";
import {
  cleanTransportPlan,
  eventBase,
  parseCleanRetentionRefs,
  verifyQuarantineGraph,
} from "./ci-verify.mjs";
const logical = "a".repeat(40),
  physical = "b".repeat(40),
  source = "c".repeat(40),
  base = "d".repeat(40);
const installation = {
  finalPublicationTip: source,
  trust: { cleanAnchor: physical },
};

test("base is intrinsic to the event; manual cutover is exact active publication only", () => {
  for (const event of ["pull_request", "merge_group"])
    assert.equal(eventBase({ event, eventBaseSha: base }, null), base);
  assert.equal(
    eventBase(
      {
        event: "workflow_dispatch",
        phase: "active",
        sourceSha: source,
        eventBaseSha: "",
      },
      installation,
    ),
    physical,
  );
  for (const context of [
    { event: "push", eventBaseSha: base },
    { event: "pull_request", eventBaseSha: "main" },
    {
      event: "workflow_dispatch",
      phase: "legacy",
      sourceSha: source,
      eventBaseSha: "",
    },
    {
      event: "workflow_dispatch",
      phase: "active",
      sourceSha: base,
      eventBaseSha: "",
    },
    {
      event: "workflow_dispatch",
      phase: "active",
      sourceSha: source,
      eventBaseSha: base,
    },
  ])
    assert.throws(() => eventBase(context, installation));
  assert.throws(() =>
    eventBase(
      {
        event: "workflow_dispatch",
        phase: "active",
        sourceSha: source,
        eventBaseSha: "",
      },
      null,
    ),
  );
});

function fixture() {
  const pairs = new Map([[logical, physical]]);
  return {
    header: { cleanAnchor: physical, migrationId: "synthetic-migration" },
    pages: {
      refs: [Buffer.from(JSON.stringify([["e".repeat(64), "h", logical]]))],
      dependencies: [Buffer.from(JSON.stringify([logical]))],
    },
    format: {
      resolveMapped(id) {
        assert.ok(pairs.has(id));
        return pairs.get(id);
      },
      mappedRevisionPairs() {
        return [...pairs];
      },
    },
    sourceSha: source,
    baseSha: base,
  };
}

test("clean transport uses authenticated mapped roots, never old logical IDs", () => {
  const plan = cleanTransportPlan(fixture());
  assert.deepEqual(plan.roots, [physical, source, base].sort());
  assert.equal(plan.roots.includes(logical), false);
  assert.equal(
    plan.prefix,
    "refs/tags/signalo-permission-clean/synthetic-migration/",
  );
  const bad = fixture();
  bad.pages.dependencies = [Buffer.from(JSON.stringify([source]))];
  assert.throws(() => cleanTransportPlan(bad));
  assert.throws(() =>
    cleanTransportPlan({ ...fixture(), sourceSha: "refs/heads/main" }),
  );
  assert.throws(() => cleanTransportPlan({ ...fixture(), sourceSha: logical }));
  assert.throws(() => cleanTransportPlan({ ...fixture(), baseSha: logical }));
});

test("retention advertisements must bind exact canonical logical suffix to mapped physical SHA", () => {
  const plan = cleanTransportPlan(fixture());
  const ref = plan.prefix + logical;
  assert.deepEqual(
    parseCleanRetentionRefs(Buffer.from(`${physical}\t${ref}\n`), plan),
    [{ ref, physical }],
  );
  assert.deepEqual(parseCleanRetentionRefs(Buffer.alloc(0), plan), []);
  for (const text of [
    `${logical}\t${ref}\n`,
    `${physical}\trefs/tags/signalo-permission-history/${logical}\n`,
    `${physical}\t${plan.prefix}${source}\n`,
    `${physical}\t${plan.prefix}${logical}/nested\n`,
    `${physical}\t${ref}^{}\n`,
    `${physical}\t${ref}\n${physical}\t${ref}\n`,
    `--upload-pack=anything\t${ref}\n`,
    `${physical}\t${ref}\r\n`,
  ])
    assert.throws(() => parseCleanRetentionRefs(Buffer.from(text), plan));
  assert.throws(() => parseCleanRetentionRefs(Buffer.from([0xff]), plan));
});

test("CLI fails generically before filesystem installation for missing or malformed administrative context", () => {
  const command = fileURLToPath(new URL("./ci-verify.mjs", import.meta.url));
  for (const patch of [
    {},
    { GH_TOKEN: "synthetic-token", HISTORY_CONTEXT: "null" },
    {
      GH_TOKEN: "synthetic-token",
      HISTORY_CONTEXT: JSON.stringify({
        phase: "active",
        descriptorSha256: "d".repeat(64),
      }),
      HISTORY_DESCRIPTOR_B64: "bad",
    },
  ]) {
    const run = spawnSync(process.execPath, [command], {
      env: { PATH: "/usr/bin:/bin", ...patch },
      encoding: "utf8",
    });
    assert.equal(run.status, 1);
    assert.equal(run.stdout, "");
    assert.equal(run.stderr, "HISTORY_CI_VERIFICATION_REFUSED\n");
  }
});

function graphFixture(mixed = false) {
  function commit(parents, message) {
    const bytes = Buffer.from(
      `tree ${"f".repeat(40)}\n${parents.map((p) => `parent ${p.oid}\n`).join("")}author Synthetic <fixture@example.invalid> 0 +0000\ncommitter Synthetic <fixture@example.invalid> 0 +0000\n\n${message}\n`,
    );
    return {
      bytes,
      parents: parents.map((p) => p.oid),
      oid: createHash("sha1")
        .update(`commit ${bytes.length}\0`)
        .update(bytes)
        .digest("hex"),
    };
  }
  const clean = commit([], "clean anchor"),
    old = commit([], "old logical root");
  const publication = commit([clean], "publication"),
    next = commit(mixed ? [publication, old] : [publication], "new descendant");
  const rows = mixed
    ? [next, publication, old, clean]
    : [next, publication, clean];
  return {
    clean,
    old,
    publication,
    next,
    rows,
    input: {
      plan: { mapped: new Map([[old.oid, clean.oid]]) },
      publicationTip: publication.oid,
      cleanAnchor: clean.oid,
      sourceSha: next.oid,
      baseSha: publication.oid,
      manualCutover: false,
      listing: Buffer.from(
        rows.map((r) => [r.oid, ...r.parents].join(" ")).join("\n") + "\n",
      ),
      frames: Buffer.concat(
        rows.flatMap((r) => [
          Buffer.from(`${r.oid} commit ${r.bytes.length}\n`),
          r.bytes,
          Buffer.from("\n"),
        ]),
      ),
    },
  };
}

test("quarantine authenticates raw commit SHA1 and ordered parents before clean-only transport", () => {
  const { input, clean, publication } = graphFixture();
  assert.deepEqual(verifyQuarantineGraph(input), { commits: 3 });
  assert.deepEqual(
    verifyQuarantineGraph({
      ...input,
      sourceSha: publication.oid,
      baseSha: clean.oid,
      manualCutover: true,
    }),
    { commits: 3 },
  );
  const altered = Buffer.from(input.frames);
  altered[altered.length - 3] ^= 1;
  assert.throws(() => verifyQuarantineGraph({ ...input, frames: altered }));
  assert.throws(() =>
    verifyQuarantineGraph({
      ...input,
      frames: Buffer.concat([input.frames, Buffer.from("extra")]),
    }),
  );
  assert.throws(() =>
    verifyQuarantineGraph({ ...input, sourceSha: clean.oid }),
  );
  assert.throws(() => verifyQuarantineGraph({ ...input, baseSha: clean.oid }));
  assert.throws(() =>
    verifyQuarantineGraph({ ...input, publicationTip: input.sourceSha }),
  );
});

test("a clean descendant with merged old ancestry is rejected across the entire graph", () => {
  const { input, rows } = graphFixture(true);
  assert.equal(rows[0].parents[0], input.publicationTip);
  assert.throws(() => verifyQuarantineGraph(input), /Old logical ancestry/u);
  // Parent order reported by Git cannot disagree with authenticated raw bytes.
  const noOldIdentity = { ...input, plan: { mapped: new Map() } };
  const reordered = Buffer.from(
    rows
      .map((r, i) =>
        [r.oid, ...(i === 0 ? [...r.parents].reverse() : r.parents)].join(" "),
      )
      .join("\n") + "\n",
  );
  assert.throws(() =>
    verifyQuarantineGraph({ ...noOldIdentity, listing: reordered }),
  );
});
