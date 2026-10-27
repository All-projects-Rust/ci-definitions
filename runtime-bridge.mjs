// Stable installed entry point: /usr/local/libexec/signalo-history/runtime-bridge.mjs.
// All authority and data resolution remain in the fixed administrator reader.
import { runtimeBridgeMain } from "./trusted-history/runtime-bridge.mjs";

runtimeBridgeMain().catch(() => {
  process.stderr.write("HISTORY_RUNTIME_BRIDGE_REFUSED\n");
  process.exitCode = 1;
});
