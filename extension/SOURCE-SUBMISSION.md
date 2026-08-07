# Source-Code Submission & Reproducible Build — Dragon's Egg Cipherclerk

This document is for the **Mozilla AMO** and **Chrome Web Store** human
reviewers. The submitted package contains two machine-generated artifacts —
a WebAssembly binary (`dregg_wasm_bg.wasm`, ~17 MB) and bundled JavaScript
(`dist/*.js`) — that are **not** the human-authored source. Per AMO's
[source-code submission policy](https://extensionworkshop.com/documentation/publish/source-code-submission/),
this document gives the exact source locations, the pinned toolchain, and the
exact commands a reviewer (or anyone) runs to reproduce every shipped artifact
byte-for-byte from source.

Nothing in the package is downloaded or evaluated at runtime. Both generated
artifacts are produced **at build time** from source that ships in the
submission and is published at the repository below.

- **Public source repository:** the `dregg` monorepo. The extension lives in
  `extension/`; the WebAssembly crypto core lives in `wasm/`.
- **License:** AGPL-3.0-or-later (see `wasm/Cargo.toml`).
- **Top-level build entry point:** `extension/build.sh`.

---

## 1. Toolchain (pin these exact versions to reproduce)

| Tool | Version used | How it is pinned / where to get it |
|------|--------------|------------------------------------|
| Rust (rustc / cargo) | `nightly` (built with `1.98.0-nightly (91fe22da8 2026-06-21)`) | `rust-toolchain.toml` at the repo root pins `channel = "nightly"`. Install via `rustup`. |
| Rust target | `wasm32-unknown-unknown` | `rustup target add wasm32-unknown-unknown` |
| `wasm-bindgen-cli` | `0.2.125` | Must match the `wasm-bindgen` crate version locked in `wasm/Cargo.lock`. `cargo install wasm-bindgen-cli --version 0.2.125` |
| `wasm-opt` (Binaryen) | `version 130` | size optimizer. `brew install binaryen` (macOS) or distro package. The build installs it automatically via Homebrew if missing. |
| Node.js | `v26.4.0` (any current LTS works) | for the esbuild JS bundle step |
| esbuild | `0.21.5` | dev-dependency, pinned in `extension/package-lock.json` (`^0.21.0`) |
| TypeScript | `5.9.3` | dev-dependency, pinned in `extension/package-lock.json` (`^5.5.0`); used for `npm run typecheck` |
| `zip` | system | packaging the `.zip` / `.xpi` |

> The exact dependency graph for the WebAssembly crate is locked in
> `wasm/Cargo.lock`; the JS toolchain is locked in `extension/package-lock.json`.
> Both lockfiles are committed, so a reviewer building from the published source
> gets the same dependency versions.

---

## 2. One-command reproduction

From the repository root:

```bash
cd extension
npm ci          # installs esbuild + typescript from package-lock.json
./build.sh      # builds wasm, runs wasm-bindgen + wasm-opt, bundles JS, packages
```

`./build.sh` runs four stages (see the script for the exact, commented
commands). The stages are reproduced individually below so a reviewer can follow
each artifact back to its source.

---

## 3. Stage-by-stage: how each shipped file is generated

### 3a. The WebAssembly binary — `dregg_wasm_bg.wasm` + glue `dregg_wasm.js`

**Source:** the `dregg-wasm` Rust crate at `wasm/` (entry `wasm/src/lib.rs`,
crypto in `wasm/src/privacy.rs`). It is a standalone cargo workspace (its
`Cargo.toml` declares an empty `[workspace]`), so it builds into `wasm/target/`.

```bash
# (1) compile the crate to wasm (release).
#     BOTH RUSTFLAGS, ALWAYS — they are one pair and they travel together:
#       --cfg getrandom_backend="wasm_js"    getrandom 0.3/0.4 will not compile for
#                                            wasm32 without a backend selection
#       -C link-arg=-zstack-size=33554432    32 MiB of linear-memory stack; the
#                                            recursion verifier overflows the 1 MiB default
#     The repo keeps ONE definition of them, in `scripts/wasm-build-flags.sh`; the command
#     below is that definition written out, and `scripts/wasm-build-flags.sh` printed will
#     reproduce it exactly. Note that cargo does NOT merge the RUSTFLAGS environment
#     variable with `.cargo/config.toml` — env wins outright — so passing only one of the
#     two silently deletes the other.
RUSTFLAGS='--cfg getrandom_backend="wasm_js" -C link-arg=-zstack-size=33554432' \
cargo build \
  --manifest-path wasm/Cargo.toml \
  -p dregg-wasm \
  --target wasm32-unknown-unknown \
  --release
# -> wasm/target/wasm32-unknown-unknown/release/dregg_wasm.wasm

# (2) generate the JS glue + the browser-ready wasm with wasm-bindgen 0.2.125.
#     --target no-modules: emits a classic-script global initializer (required
#     because an MV3 service worker / classic worker has no ESM import), NOT a
#     remote/dynamic loader.
wasm-bindgen wasm/target/wasm32-unknown-unknown/release/dregg_wasm.wasm \
  --out-dir extension \
  --target no-modules \
  --no-typescript \
  --omit-default-module-path
# -> extension/dregg_wasm.js  (hand-readable glue)
# -> extension/dregg_wasm_bg.wasm

# (3) inline any wasm-bindgen `inline_js` snippets into the glue so the bundle is
#     flat and self-contained (no runtime `require(...)` of a snippets dir, which
#     does not exist in a service worker). Deterministic source transform:
node extension/inline-snippets.mjs extension/dregg_wasm.js extension/snippets
rm -rf extension/snippets

# (4) shrink the blob for size (MV3 re-instantiates wasm on every worker wake):
wasm-opt -Oz extension/dregg_wasm_bg.wasm -o extension/dregg_wasm_bg.wasm
# 27.16 MB -> 17.57 MB
```

`./extension/build.sh wasm` runs exactly these four steps and nothing else, and
then (5) writes `extension/dregg-wasm-provenance.json` — the sha256 of the glue,
the sha256 of the blob, and a fingerprint of the whole wasm32 source closure they
were built from — and re-checks all three with
`scripts/check-wasm-freshness.sh`. `./extension/build.sh package` puts that record
INSIDE the .zip/.xpi and refuses to leave a package the check calls stale, so the
correspondence between the shipped binary and this repository is machine-checkable
from the package alone.

Of the two outputs, only `extension/dregg_wasm.js` is committed; the `.wasm` blob
is a build product and is not in the repository (the repo-root `.gitignore`
excludes `*.wasm`). Both are produced by the steps above. The glue is standard
wasm-bindgen output and is human-readable; the `.wasm` is the compiled,
size-optimized form of the `wasm/` Rust source.

> Note on `wasm-opt`: `-Oz` is a size optimization, not an obfuscation. The
> unoptimized blob built by step (1)+(2) is functionally identical; a reviewer
> who wants the un-stripped artifact for inspection can simply **skip step (4)**
> and load the larger blob — the extension runs the same.

### 3b. The bundled extension JavaScript — `dist/*.js`

**Source:** the TypeScript in `extension/src/`. esbuild concatenates each entry
point and its local imports into one IIFE per output (no minification of names
in production beyond bundling; **no** transform that hides logic):

```bash
cd extension && npm run build   # runs `node build.mjs` (esbuild)
```

`extension/build.mjs` is the full, readable build config. It produces:

| Shipped file | Built from (esbuild entry + its `src/` imports) | Role |
|---|---|---|
| `dist/background.js` | `src/background.ts` | MV3 service worker (keys, signing, node I/O) |
| `dist/content.js` | `src/content.ts` | content script (injects the page provider) |
| `dist/page.js` | `src/page.ts` | the `window.dregg` provider injected into pages |
| `dist/popup-script.js` | `src/popup-script.ts` | toolbar popup logic |

esbuild settings (from `build.mjs`): `format: 'iife'`, `target: ['es2022']`,
`bundle: true`, and **sourcemaps only in dev/watch** — production ships no
sourcemap. There is no minify/mangle pass; the output is a straightforward
bundle of the `src/*.ts` files.

### 3c. Hand-written files shipped as-is (no build step)

These ship verbatim from `extension/` and are already source — no
reverse-engineering needed:

- Static UI pages: `popup.html`, `settings.html`, `provision.html`,
  `recovery.html`, `confirm-intent.html`, `disclosure-picker.html`,
  `origin-permission.html`, `share-capability.html`.
- Their dedicated, hand-authored scripts: `settings-script.js`, `provision.js`,
  `recovery.js`, `confirm-intent-script.js`, `disclosure-picker.js`,
  `origin-permission-script.js`, `share-capability.js`.
- `bip39_english.txt` (the standard BIP-39 English wordlist).
- `icons/icon-{16,32,48,128}.png` (from `icons/icon.svg`).
- `manifest.json` (Chrome) / `manifest-firefox.json` (Firefox, renamed to
  `manifest.json` inside the `.xpi`).

### 3d. Packaging

`./build.sh package` rebuilds the TS bundle (so a stale `dist/` can never be
shipped), re-optimizes the wasm idempotently, and zips the explicit file list
(see `BASE_FILES` in `build.sh`) into:

- `dist/dregg-cipherclerk-chrome.zip` (uses `manifest.json`)
- `dist/dregg-cipherclerk-firefox.xpi` (uses `manifest-firefox.json` as
  `manifest.json`)

Both packages are ~4.1 MB (the wasm compresses well inside the zip).

---

## 4. What to verify

1. Build artifacts are deterministic given the pinned toolchain above. Building
   from the published `wasm/` source reproduces `dregg_wasm_bg.wasm`; building
   from `extension/src/` reproduces `dist/*.js`.
2. **No artifact is fetched or generated at runtime.** The wasm and all scripts
   are loaded only via `chrome.runtime.getURL(...)` from inside the package (see
   `REVIEWER-AUDIT.md` §2). The `'wasm-unsafe-eval'` in the CSP is solely for
   the browser to instantiate the **bundled** `.wasm`; it does not permit remote
   code.
3. The crypto is real and inspectable in `wasm/src/privacy.rs`
   (`ed25519_dalek`-backed signing, `blake3` key derivation), not a stub.

Questions: dregg-cipherclerk@fg-goose.online
