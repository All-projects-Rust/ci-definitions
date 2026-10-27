import { register } from "node:module";
register(new URL("./runtime-ts-loader.mjs", import.meta.url), {
  parentURL: import.meta.url,
});
