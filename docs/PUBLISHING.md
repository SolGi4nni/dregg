# Publishing the dregg client artifacts

How each shippable artifact publishes, what credential it needs, and the exact
commands. Three artifacts ship to public registries/stores:

| Artifact | Registry | Package | Credential | Workflow |
|---|---|---|---|---|
| TypeScript SDK | npm | `@dregg/sdk` | `NPM_TOKEN` (npm automation token, `@dregg` scope) | `.github/workflows/publish-sdk-ts.yml` |
| Python SDK | PyPI | `dregg` | PyPI Trusted Publishing **or** `PYPI_API_TOKEN` | `.github/workflows/publish-sdk-py.yml` |
| Browser extension | Chrome Web Store + Firefox AMO | Dragon's Egg Cipherclerk | a developer-account login (manual) | `.github/workflows/extension.yml` (builds the zips) |

The CI workflows build + verify on every tag/dispatch. The actual **publish**
needs ember's credentials (set the repo secrets, or run the local commands
below with a token in the environment). The two store uploads are manual.

---

## Prerequisite: the plonky3-recursion fork pin

The standalone `wasm/` workspace `[patch]`es the four `p3-*` crates onto a
sibling checkout of `emberian/plonky3-recursion`. cargo forbids re-pointing a
git source to a different rev of the same URL via `[patch]`, so the override is
a **path patch** onto `../../plonky3-recursion`, pinned (in CI + dev) at the
pushed `update-plonky3-rev` tip:

```
rev 993efecd724261fff3fd894c06cc2525b5532e28
```

This rev is referenced in lockstep by: `wasm/Cargo.toml` (the `[patch]` comment),
`.github/workflows/pages.yml`, `.github/workflows/extension.yml`, and
`.github/workflows/publish-sdk-ts.yml`. To build the wasm locally:

```sh
git clone https://github.com/emberian/plonky3-recursion ../plonky3-recursion
git -C ../plonky3-recursion checkout 993efecd724261fff3fd894c06cc2525b5532e28
cd wasm && RUSTFLAGS="-C link-arg=-zstack-size=33554432" \
  wasm-pack build . --target web --out-dir pkg --release
```

(The root workspace pins the same four crates at an EARLIER ancestor rev for the
native lanes; those revs are circuit/VK-sensitive and are bumped separately.)

---

## 1. `@dregg/sdk` → npm

**Package:** `@dregg/sdk` (currently `0.3.0`, scoped, public). The wasm runtime
is an **optional peer dependency** (`dregg-wasm`), published separately — the
SDK tarball ships only `dist/ src/ README.md LICENSE` (~300 kB), not the 15 MB
wasm. The `.d.ts` build still needs the `dregg-wasm` types at `../wasm/pkg`
(the `@dregg/sdk/wasm` face declares `typeof import("dregg-wasm")`).

**Build + verify locally:**

```sh
# (build wasm/pkg first — see prerequisite above)
cd sdk-ts
npm ci
npm run build
npm pack --dry-run     # inspect file list + size
```

**Credential:** repo secret `NPM_TOKEN` — an npm *automation* token with
publish rights on the `@dregg` scope (npmjs.com → Access Tokens → Generate →
Automation). For org scopes you must also have publish rights on `@dregg`.

**Publish via CI (preferred):** push a tag `sdk-ts-v0.3.0` (or run the workflow
manually). With `NPM_TOKEN` set, the `publish-sdk-ts.yml` job builds wasm +
SDK, verifies the pack, and runs `npm publish --access public`. Without the
secret it builds + verifies and no-ops the publish with a warning.

**Publish manually (exact command):**

```sh
cd sdk-ts
npm run build
NPM_TOKEN=<token> npm publish --access public
# or, classic auth:
npm config set //registry.npmjs.org/:_authToken <token>
npm publish --access public
```

Bump `version` in `sdk-ts/package.json` before re-publishing (npm rejects a
duplicate version).

---

## 2. `dregg` → PyPI

**Package:** `dregg` (currently `0.3.0`). The published wheel is the **default
LIGHT, kernel-free client** (`default = ["light"]`): pure-Rust executor at
parity with the Lean spec, Ed25519 + wire-codec + HTTP — no Lean toolchain, no
`libleanshared`. pyo3 `abi3-py310`, so **one stable-ABI wheel per platform**
covers Python 3.10+. The heavy embedded-kernel wheel (`dregg[kernel]`) is a
separate build and is NOT published by this workflow.

**Build + verify locally:**

```sh
cd sdk-py
maturin build --release            # default features = light; writes target/wheels/*.whl
# inspect:
python -m zipfile -l target/wheels/dregg-0.3.0-*.whl
pip install target/wheels/dregg-0.3.0-*.whl && python -c "import dregg; print(dregg.kernel())"
# expect build="light", executor="rust"
```

**Credential — two paths, in order of preference:**

1. **Trusted Publishing (OIDC, no token):** on PyPI, configure a trusted
   publisher for project `dregg` → GitHub → repo `emberian/dregg`, workflow
   `publish-sdk-py.yml`. The workflow already grants `id-token: write`.
2. **API token:** create a PyPI project-scoped token and store it as the repo
   secret `PYPI_API_TOKEN`. The publish step uses it when trusted publishing is
   not configured.

**Publish via CI:** push a tag `sdk-py-v0.3.0` (or dispatch). The workflow
builds wheels (linux x86_64/aarch64, macOS arm64/x86_64) + an sdist and uploads
via `pypa/gh-action-pypi-publish`.

**Publish manually (exact commands):**

```sh
cd sdk-py
maturin build --release --out dist
# with trusted publishing not available, twine + a token:
pip install twine
TWINE_USERNAME=__token__ TWINE_PASSWORD=<pypi-token> twine upload dist/*
# or maturin's own uploader:
MATURIN_PYPI_TOKEN=<pypi-token> maturin publish --release
```

Bump `version` in `sdk-py/Cargo.toml` before re-publishing (PyPI rejects a
duplicate version; there is no delete-and-reupload).

---

## 3. Browser extension → Chrome Web Store + Firefox AMO

**Artifacts (already built, current):**

```
extension/dist/dregg-cipherclerk-chrome.zip   (Chrome Web Store)
extension/dist/dregg-cipherclerk-firefox.xpi  (Firefox AMO)
```

Rebuild any time with: `cd extension && ./build.sh package` (or `./build.sh`
to rebuild the wasm core first — that needs the plonky3 sibling, see
prerequisite). CI builds them on `gh workflow run Extension --ref main`
(the `package` job, dispatch-only) and uploads them as run artifacts.

**Listing metadata (both stores):**

- **Name:** Dragon's Egg Cipherclerk
- **Summary/description:** Capability-based cipherclerk for dregg: manages
  signing keys, authorization tokens, and capability handles with
  zero-knowledge proofs. Holds named signing identities, shows exactly what a
  turn does before it signs, submits signed turns to a node, and tails the
  node's receipt stream.
- **Category:** Developer tools / Productivity
- **Version:** 0.1.0 (from `manifest.json` / `manifest-firefox.json`)

**Permission justifications (for store review):**

- `storage` — persist encrypted identity profiles, recovery state, and the
  receipt outbox at rest (PBKDF2 + AES-256-GCM).
- `activeTab` — read the active tab's origin only when the user invokes a
  capability/provision flow, to bind a token to the requesting site.
- `contextMenus` — the right-click "sign with dregg / provision capability"
  entry points.
- `alarms` — schedule auto-lock after inactivity and receipt-stream reconnect
  backoff.
- `host_permissions` (`https://devnet.dregg.fg-goose.online/*`,
  `http(s)://localhost:8420/*`, `ws://localhost:8420/*`, and the `127.0.0.1`
  equivalents) — submit signed turns and tail the receipt SSE stream from the
  user's dregg node (the public devnet and a local node).
- content script on `<all_urls>` — expose the page-side `window.dregg`
  provider so any site can *request* (never silently obtain) a signature or a
  capability token; all signing is gated behind an explicit, nonce-bound
  confirmation popup.

**Manual upload steps (ember, interactive — needs the dev accounts):**

Chrome Web Store:
1. Go to the Developer Dashboard: https://chrome.google.com/webstore/devconsole
2. Select the item (or "New item") → upload `extension/dist/dregg-cipherclerk-chrome.zip`.
3. Fill the store listing (name/description/category/icons/screenshots), the
   privacy tab (justify each permission as above; declare no remote code), then
   "Submit for review."

Firefox AMO:
1. Go to: https://addons.mozilla.org/developers/addon/submit/
2. Upload `extension/dist/dregg-cipherclerk-firefox.xpi` (the gecko id
   `dregg-cipherclerk@fg-goose.online` is baked into the manifest).
3. Choose "On this site" (listed) or self-distribution, fill the listing +
   permission notes, submit. AMO may request the source (the extension bundles
   a wasm blob built from this repo's `wasm/` + `extension/build.sh`).

---

## What ember must do

- **npm:** set repo secret `NPM_TOKEN`, then tag `sdk-ts-v0.3.0` (or run the
  manual `npm publish` command above).
- **PyPI:** configure Trusted Publishing for `dregg` **or** set repo secret
  `PYPI_API_TOKEN`, then tag `sdk-py-v0.3.0` (or run the manual `twine upload`).
- **Chrome Web Store:** upload `dregg-cipherclerk-chrome.zip` via the developer
  dashboard (manual, interactive — needs the Chrome dev account).
- **Firefox AMO:** upload `dregg-cipherclerk-firefox.xpi` via the AMO developer
  hub (manual, interactive — needs the AMO dev account).
