# dregg-portal — the DreggNet portal (`portal.dregg.studio`)

The read-only trustless network view plus the interactive drive layer (connect
an identity, fire real cap-gated turns), built on the published `@dregg/sdk`.
The in-tab proof engine is the `dregg-wasm` recursive-STARK light client:
`index.html`/`portal.js` and `cell.html` dynamically
`import("./pkg/dregg_wasm.js")`.

## Build (everything into `dist/`)

```sh
# 1. the wasm light-client engine (once per circuit change; ~6 min warm)
npm run build:wasm      # = RUSTFLAGS="-C link-arg=-zstack-size=33554432" \
                        #   wasm-pack build ../wasm --target web --out-dir pkg --release

# 2. the drive bundle + stage the FULL pkg (snippets/ included) into dist/pkg
npm run build           # = node build.mjs  (fails loudly if ../wasm/pkg is incomplete)

# 3. tests
npm test                # = node --test test/*.test.mjs
```

`dist/pkg/` is build output, kept out of git (wasm-pack's `pkg/.gitignore` +
the repo-wide `*.wasm` ignore) — a fresh checkout must run the two build steps
above before `dist/` is servable. A partial pkg copy (bare `dregg_wasm*` files
without `snippets/`) canNOT instantiate: `dregg_wasm.js` imports its
`./snippets/…` (the biscuit-auth wasm shim).

The wasm build [patch]es the plonky3-recursion fork via the sibling checkout
`../../plonky3-recursion` — see `wasm/Cargo.toml` §THE FORK SEAM for the pinned
rev discipline (the sibling rev IS the circuit/VK).

## Headless smoke (no browser)

```sh
node --input-type=module -e '
import { readFileSync } from "node:fs";
const m = await import("./dist/pkg/dregg_wasm.js");
await m.default({ module_or_path: readFileSync("./dist/pkg/dregg_wasm_bg.wasm") });
console.log("engine instantiates OK");'
```

## Publish

`dist/` is a flat static site (no server code). It ships to
`portal.dregg.studio` via the DreggNet staging deploy, which stages the static
files and re-copies the FULL `wasm/pkg` at stage time:
`dreggnet/deploy/staging/deploy.sh` (`build` → `ship`). The publish itself is
human-go — nothing here pushes.
