// Bundle the portal drive layer (the browser UI + the published @dregg/sdk +
// @noble) into a single self-contained ESM file the static portal loads — no
// runtime import map, no CDN, edge-servable as a flat asset.
import { build } from "esbuild";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const here = dirname(fileURLToPath(import.meta.url));

await build({
  entryPoints: [join(here, "src/drive-ui.mjs")],
  outfile: join(here, "dist/drive.bundle.js"),
  bundle: true,
  format: "esm",
  platform: "browser",
  target: ["es2020"],
  minify: true,
  sourcemap: false,
  legalComments: "none",
});

console.log("built portal/dist/drive.bundle.js (drive-ui + @dregg/sdk/browser + @noble, inlined)");
