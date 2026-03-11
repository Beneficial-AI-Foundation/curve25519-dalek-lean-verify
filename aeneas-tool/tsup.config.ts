import { defineConfig } from "tsup";
import module from "node:module";

const nodeBuiltins = module.builtinModules.flatMap((m) => [m, `node:${m}`]);

export default defineConfig({
  entry: ["src/index.ts"],
  format: ["esm"],
  target: "node20",
  clean: true,
  bundle: true,
  noExternal: [/.*/],
  external: nodeBuiltins,
  banner: { js: "#!/usr/bin/env node\nimport{createRequire}from'module';const require=createRequire(import.meta.url);" },
  shims: true,
});
