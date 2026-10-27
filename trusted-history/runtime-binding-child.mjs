import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
  completeRuntimeResponse,
  exactKeys,
  runtimeApiDirectory,
  sandboxCandidate,
} from "./runtime-binding-protocol.mjs";

async function main() {
  assert.equal(process.argv.length, 2);
  assert.equal(process.getuid(), 65534);
  assert.equal(process.getgid(), 65534);
  const status = readFileSync("/proc/self/status", "utf8");
  assert.match(status, /^CapEff:\s*0+$/mu);
  assert.match(status, /^NoNewPrivs:\s*1$/mu);
  assert.equal(process.env.GH_TOKEN, undefined);
  assert.equal(process.env.GITHUB_TOKEN, undefined);
  let size = 0;
  const chunks = [];
  for await (const chunk of process.stdin) {
    size += chunk.length;
    assert.ok(size <= 1024);
    chunks.push(chunk);
  }
  const request = JSON.parse(Buffer.concat(chunks).toString("utf8"));
  exactKeys(request, ["schemaVersion", "nonce"]);
  assert.equal(request.schemaVersion, 1);
  assert.match(request.nonce, /^[a-f0-9]{64}$/u);
  const manifest = await import(
    `${sandboxCandidate}/${runtimeApiDirectory}/permission-manifest.ts`
  );
  const adapters = await import(
    `${sandboxCandidate}/${runtimeApiDirectory}/permission-adapter.contracts.ts`
  );
  assert.ok(Array.isArray(manifest.CODE_DEFINED_REPORT_BINDINGS));
  assert.equal(
    typeof adapters.permissionRuntimeSurfaceBindingContext,
    "function",
  );
  const context = adapters.permissionRuntimeSurfaceBindingContext(
    manifest.CODE_DEFINED_REPORT_BINDINGS,
  );
  const data = {
    knownPermissions: Array.from(context.knownPermissions),
    adapterBindings: Array.from(context.adapterBindings, ([name, values]) => [
      name,
      Array.from(values),
    ]),
    codeDefinedReports: Array.from(
      context.codeDefinedReports,
      ([name, value]) => [name, value],
    ),
  };
  process.stdout.write(completeRuntimeResponse(data, request.nonce));
}
main().catch(() => {
  process.stderr.write("RUNTIME_BINDING_CHILD_REFUSED\n");
  process.exitCode = 1;
});
