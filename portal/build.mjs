// Build the portal's two shipped artifacts into dist/:
//
//  1. dist/drive.bundle.js — the drive layer (the browser UI + the published
//     @dregg/sdk + @noble) bundled into a single self-contained ESM file the
//     static portal loads — no runtime import map, no CDN, edge-servable as a
//     flat asset.
//
//  2. dist/pkg/ — the wasm light-client engine (the FULL wasm-pack output:
//     dregg_wasm.js + dregg_wasm_bg.wasm + snippets/ + package.json), staged
//     wholesale from ../wasm/pkg. index.html/portal.js and cell.html
//     dynamically `import("./pkg/dregg_wasm.js")`, and that module in turn
//     imports its `./snippets/…` (the biscuit-auth wasm shim) — so a partial
//     copy (bare dregg_wasm* files, no snippets/) CANNOT instantiate. The pkg
//     is build output, kept out of git (wasm/pkg/.gitignore + the repo-wide
//     *.wasm ignore); build it first (from the repo root):
//
//       RUSTFLAGS="-C link-arg=-zstack-size=33554432" \
//         wasm-pack build wasm --target web --out-dir pkg --release
//
//     (the enlarged stack gives the in-tab recursion verify headroom — the same
//     flags scripts/build-pages-dist.sh uses for the site's /cards/pkg build).
import { build } from "esbuild";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";
import { cpSync, existsSync, readFileSync, rmSync } from "node:fs";

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

// Stage the wasm light-client pkg (FULL wasm-pack output, snippets/ included).
const wasmPkg = join(here, "../wasm/pkg");
const distPkg = join(here, "dist/pkg");
if (!existsSync(join(wasmPkg, "dregg_wasm_bg.wasm")) || !existsSync(join(wasmPkg, "snippets"))) {
  console.error(
    "ERROR: ../wasm/pkg is missing or incomplete (need dregg_wasm_bg.wasm AND snippets/) — " +
      "the portal's in-tab proof engine cannot ship.\n" +
      "Build it first (from the repo root):\n" +
      '  RUSTFLAGS="-C link-arg=-zstack-size=33554432" wasm-pack build wasm --target web --out-dir pkg --release\n' +
      "then re-run node portal/build.mjs. (Green-or-bust: we never ship a portal without its engine.)",
  );
  process.exit(1);
}
rmSync(distPkg, { recursive: true, force: true });
cpSync(wasmPkg, distPkg, { recursive: true });
console.log("staged portal/dist/pkg/ from wasm/pkg (full wasm-bindgen output incl. snippets/)");

// Stage the pre-folded whole-history demo aggregate (the wire envelope + config
// VK anchor) the engine verifies in-tab. Produced ONCE, off the verifier, by the
// heavy native prover (folding in-tab is out of reach on wasm32 — >4 GiB):
//   cargo run --release -p dregg-lightclient --bin produce_history_envelope --features prover -- 3 7 \
//     > site/light-client/history.json
const historySrc = join(here, "../site/light-client/history.json");
const historyDst = join(here, "dist/history.json");
cpSync(historySrc, historyDst);

// FRESHNESS TOOTH (green-or-bust): the staged aggregate must ATTEST under the
// staged engine — a circuit/VK epoch that obsoletes the baked artifact fails the
// build loudly instead of shipping a demo the tab will refuse.
const m = await import(distPkg + "/dregg_wasm.js");
await m.default({ module_or_path: readFileSync(join(distPkg, "dregg_wasm_bg.wasm")) });
const baked = JSON.parse(readFileSync(historyDst, "utf8"));
let verdict;
try {
  verdict = m.verify_devnet_history(JSON.stringify(baked.envelope), baked.anchor_hex);
} catch (e) {
  verdict = { attested: false, named_floor: String(e && e.message || e) };
}
if (!verdict.attested) {
  console.error(
    "ERROR: the baked history.json does NOT attest under the just-staged wasm engine —\n" +
    "the circuit/VK moved since the artifact was folded. Regenerate it (repo root):\n" +
    "  cargo run --release -p dregg-lightclient --bin produce_history_envelope --features prover -- 3 7 \\\n" +
    "    > site/light-client/history.json\n" +
    "then re-run node portal/build.mjs. Refusal detail: " + verdict.named_floor,
  );
  process.exit(1);
}
console.log("staged portal/dist/history.json — attests under the staged engine (" + verdict.num_turns + " turns)");
