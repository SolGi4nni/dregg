# Web content-creation & demoing tooling

The web is a content-creation and demoing surface for three things dregg already
ships: **the games** (the verified 3-game portfolio), **the launchpad** (verified
token deploys), and **the verified-edge-for-agents** story. This
document designs a small suite of browser tools that turn those into things a
community member can *make with* and *show off with* — riffing on spwashi's
direction: an 8-bit shader, a preloader, an asset-production process, and "what
other web tools we could offer for content-creation and demoing."

The suite's first tool — the **8-bit shader** — is built and running
(`web-studio/eightbit/`). The rest are designed here with honest have-vs-build.

## The ethos these tools inherit

Every existing web surface holds one line, and these tools hold it too:

- **Self-contained, no CDN.** The DrEX v2 frontend is Preact + htm + signals bundled
  by esbuild into one file — "the whole build toolchain is one dependency, not a
  300-package tree … at runtime the page makes ZERO external requests"
  (`drex-web-v2/build.mjs`, `README.md`). New tools ship the same way.
- **A single designed look.** Dark-first tokens (`drex-web-v2/styles.css`:
  `--bg #0d1117`, `--accent #58a6ff`, …) and the board's navy accent
  (`assets/games/README.md`: `#0b1020` / `#5cc9ff` / `#dfe8fb`). Tools reuse them.
- **The game renders as SVG + glyphs, not raster.** `dreggnet-sprite` is a pure
  `AssetId → 128×128 SVG` function served at `GET /sprite/{kind}/{ref}` with a
  `/gallery` (`dreggnet-web/src/sprite.rs`); the board is a `CoordGrid` of unicode
  glyphs (`deos-view/src/web.rs:276`). There is **no raster image loader in the game
  path** (`docs/CONTRIBUTING-ASSETS.md`). Raster/hand/AI art is a *new, additive*
  layer — the `art:<pack>/<name>` handle designed in CONTRIBUTING-ASSETS.
- **Honest labelling.** The frontend "refuses to fake a wallet" and marks every
  not-yet-live control a preview (`drex-web-v2/src/app.js`). These tools carry the
  same discipline: nothing not-real is shown as real.

---

## 1. The 8-bit shader — **HAVE (seeded, runs)**

`web-studio/eightbit/` — a self-contained WebGL (with a CPU/canvas-2D fallback)
pixel-art shader.

**What it is.** It takes any image — an uploaded/AI-generated picture *or* a live
game canvas — and (a) downsamples to a chunky pixel grid (configurable pixel size),
(b) quantizes to a limited palette (configurable), (c) optionally applies ordered
Bayer dither + scanline/CRT darkening. Six palettes ship, two of them lifted from
the product theme (`dregg-navy` = the board, `dregg-dark` = DrEX) so output composes
with the real surfaces.

**How it's built.** One algorithm, two paths:
- `processRGBA(src, w, h, opts)` — a pure CPU function over an RGBA byte array; the
  canvas-2D fallback *and* the headless-verifiable core.
- `EightBitShader` — a GLSL ES 1.00 fragment shader (WebGL1/2) running the same math
  on the GPU per-frame; falls back to the CPU core when WebGL is absent.
- `index.html` — a live demo: drop an image → see it 8-bit-ified, with pixel-size /
  palette / dither / scanline controls, a live animated game-canvas demo, and a
  128×128 PNG export.

**Verified running (not "would render").** `node web-studio/eightbit/verify.mjs`
runs the shader on two synthetic inputs — a gradient "uploaded image" and a
procedural "game canvas" — and asserts, for each, that (1) every pixel block is one
flat color (pixelation), (2) every output color is a palette member (quantization),
(3) output ≠ input (real transform). All nine checks pass; it writes before/after
`.ppm` files. A rendered sample (gradient → dregg-navy 12-color, dither on) shows the
chunky dithered blocks directly.

**Composition.** This is the *normalize* stage of the asset pathway (see §3) and the
imagery normalizer for the launchpad (see §4). Build effort spent: **done.**

---

## 2. Preloader UX — **BUILD (small; designed here)**

**What it is.** A designed loading experience for the web surfaces — the moment
between "page requested" and "app interactive." Today that moment is a bare
`<div class="boot">loading DrEX…</div>` (`drex-web-v2/index.html`). A preloader turns
it into a branded, on-theme, *demonstrative* few hundred milliseconds.

**The design.**
- **Aesthetic.** An 8-bit motif that ties to the shader: the dregg mark (`◇` / `▚`)
  rendered as a pixel-grid that *resolves* — starts coarse (large pixels, 2-color)
  and sharpens (smaller pixels, fuller palette) as load progresses. This is literally
  the shader run at decreasing `pixelSize`, so the preloader *is* a demo of tool #1.
- **States.** `boot` (inline HTML, 0 JS — instant) → `hydrating` (module parsed,
  signals wiring) → `probing` (the real node/wallet probes the app already fires:
  `nodeStatus()`, `detectWallet()` in `app.js`) → `ready` (fade to app) →
  `degraded` (node offline / no extension — the honest states the app already has).
  The preloader reflects *real* readiness signals, not a fake timer.
- **Wiring.** A ~2 KB inline module in `index.html` before the main bundle: draws the
  pixel mark to a small canvas, advances it on `DOMContentLoaded` → first render →
  the app's existing probe promises resolving. It removes itself when the app calls a
  one-line `preloaderDone()`. Zero deps; reuses `shader.js`.

**Have-vs-build.** *Have:* the theme, the shader, the real readiness signals, the
`boot` slot. *Build:* the pixel-resolve animation + the state machine (~1 file, half a
day). **Effort: S.** It is the cheapest way to make the whole suite feel designed, and
it doubles as a live shader demo on every page load.

---

## 3. In-browser Asset Studio — **BUILD (medium; the sharpest next tool)**

**What it is.** The asset-production process, in the browser: **upload or AI-generate
an image → 8-bit-shader normalize → export a game-ready sprite.** It makes the manual
pipeline in `docs/CONTRIBUTING-ASSETS.md` ("generate large, remove the background,
crop square, export WebP/PNG at 512, downscale to 256 and 128, keep the palette close
to the board theme") into a guided in-page flow.

**How it composes.** It is the shader (tool #1) plus three thin stages around it:
1. **Ingest** — drag/drop, file pick, or paste. (An "AI-gen" tab is a labelled
   provider slot — honest: no key is bundled; see build note.)
2. **Normalize** — the 8-bit shader, with the board palettes preselected, so
   arbitrary art lands on the board's grid + colors. Plus background-key removal
   (chroma/edge) so it composes on the navy board — the manual "remove the
   background" step, automated.
3. **Export** — the three sizes the engine wants (512 source, 256, **128** = native
   `CANVAS = 128`, `dreggnet-sprite/src/svg.rs`), named per the kebab-case convention,
   with the manifest line for `assets/games/<game>/<slot>/` pre-filled.

The output drops into the **designed-not-yet-built** `art:<pack>/<name>` hand-art slot
(`docs/CONTRIBUTING-ASSETS.md`; the wiring is a `ServeDir` + a `parse_handle` scheme in
`dreggnet-web/src/sprite.rs`). Until that slot lands, the Studio still produces the
correct files + manifest entry — exactly what CONTRIBUTING-ASSETS asks a contributor
to submit — so it is useful *before* the wiring, and unblocks it.

**Have-vs-build.** *Have:* the shader, the palettes, the target format + slot spec,
the sprite gallery to preview against. *Build:* the ingest/crop/bg-key UI, the
multi-size export, the manifest-line generator (~2–3 files). The **AI-gen tab is a
slot, not a bundled model** — it posts to a user-supplied endpoint (or pairs with the
launchpad's image path in §4); the honest default is upload + normalize, which is
fully local. **Effort: M.** *This is the sharpest tool to build next* — it turns the
shader from a toy into the front door of the asset pathway, and it is the piece the
asset-production lane most directly wants.

---

## 4. Token / Microsite Creator — **BUILD (medium–large; verified answer to p0)**

**What it is.** Generate a token's **logo + a one-page microsite**, content-addressed
so the imagery and the page are *verifiable*, not just hosted. This is dregg's honest
answer to p0's launchpad, whose "RAPID MODE" deploys "a token with landing page … in a
single API call" and whose "BATCH" gives "unique sites, logos, and themes for each,"
with AI image-generation billed per megapixel (`docs/deos/P0-DEEP-DIVE.md`). p0 hosts
these on `*.p0.surf`; the verified-edge/registrar/hosting space "is wide open — p0 is
not in it" (same doc).

**How it composes.**
- **Logo** — the 8-bit shader (tool #1) normalizes an uploaded or AI-gen mark to a
  crisp, on-palette, content-addressable image. Where p0 charges per-megapixel image
  generation, dregg's differentiator is **provenance**: the logo is content-addressed
  (blake3, the same addressing `dreggnet-asset` uses for `AssetId` and
  `dreggnet-sprite` uses for its deterministic art), so the same input ⇒ the same
  bytes ⇒ a verifiable image. Optionally the logo *is* a deterministic sprite
  (`dreggnet-sprite`) seeded by the token's address — art nobody can silently swap.
- **Microsite** — a single self-contained page from a small template (the theme
  tokens, the shader-made logo, the token's real on-chain facts). The publish path
  already exists in the gateway/ingress spine: a cap-and-funding-gated **site
  publish** → `SiteCell` + receipt → live, with a pinned canonical endpoint (the
  public-endpoint-pinning discipline — a mismatch refuses to serve).
- **IPFS content-addressing** — the logo + microsite bundle is pinned via the
  `dregg-ipfs` family already ported into the monorepo (`grain-verify` /
  `sandstorm-bridge` / `dregg-ipfs`), so the content hash *is* the address. This ties
  the infra-pull IPFS lane: the microsite is
  reachable and verifiable by CID, not only by a mutable subdomain.

**Have-vs-build.** *Have:* the shader/logo normalizer, content-addressing primitives
(`dreggnet-asset`, `dreggnet-sprite`), the site-publish spine + endpoint pinning, the
`dregg-ipfs` family, and the launchpad design (`docs/deos/DREGG-LAUNCHPAD-DESIGN.md`).
*Build:* the in-browser composer UI, the microsite template, and the glue that binds
{logo CID, microsite CID, token address} into one publishable, receipted bundle. The
verified-provenance angle is the moat, not the image gen. **Effort: M–L.** Gated on the
launchpad + the IPFS lane; the *logo* half is buildable now on the shader alone.

---

## 5. Verify-Me interactive demo — **BUILD (medium; the demoing keystone)**

**What it is.** The reveal-nothing / proof story as a *playable web demo* — content
that demonstrates the tech instead of describing it. dregg's whole pitch is "every
move is a receipt" and "the guarantee never moves, only what the world sees"
(`drex-web-v2/src/app.js`, the tier dial). A Verify-Me demo lets a visitor *drive*
that: make a move / place a sealed bid / clear a ring, then watch the same fact shown
three ways — what the world sees, what the solver sees, what you see — and **re-check
the receipt themselves** in the browser.

**How it composes.** The pieces are already real and just need packaging as a
standalone, no-wallet-required demo:
- The **tier-dial viewer-lens** already redacts one real cleared ring per tier
  (Open = full flows, Shielded = blurred, Dark = sealed) using `drex-web/drex-viz.js`
  `ringGraph` (`app.js` `TierDial`). That *is* the reveal-nothing visual.
- The **sealed-bid commit→reveal** ceremony is real extension-signed crypto
  (keccak256 + EIP-712 + secp256k1); the demo can run a *local* keypair variant so a
  visitor without the extension still sees commit → reveal → "re-hash matches ✔"
  (`app.js` `SealedBidFlow`, `bindsCommitment` check).
- The **8-bit shader** themes it: the demo's board/render can run through the shader
  for a distinct, ownable "dregg demo" look that reads as *content*, not a form.

**Have-vs-build.** *Have:* the tier-dial lens, the real clear/settle receipt, the
commit→reveal check, the viz. *Build:* a self-contained demo shell (no real wallet,
no real money — an honest "sandbox" banner), a local-keypair sealed-bid path, and a
"verify this receipt" panel that re-runs the check in front of the user. **Effort: M.**
This is the *demoing* half of the suite's mandate — the content that sells the
verified story by letting people play it.

---

## The through-line & the build order

The web is where the verified engine becomes **makeable and showable**:

| tool | for | state | effort |
|------|-----|-------|--------|
| 8-bit shader | games + launchpad imagery | **HAVE (runs)** | done |
| Preloader UX | every surface (and a shader demo) | build | **S** |
| Asset Studio | the asset-production pathway | build | **M** ← sharpest next |
| Token/Microsite Creator | the launchpad (verified vs p0) | build | M–L |
| Verify-Me demo | demoing the verified story | build | M |

**Recommended order:** shader (done) → **Asset Studio** (turns the shader into the
front door of the asset pathway; most-wanted by the asset lane) → Preloader (cheap,
makes everything feel designed, reuses the shader) → Verify-Me demo (the demoing
keystone, all parts already real) → Token/Microsite Creator (highest leverage but
gated on the launchpad + IPFS lanes).

Two composition spines run through all of it:
- **Asset pipeline:** AI-gen / upload → **8-bit-shader normalize** → the game's asset
  spec (128×128, board palette, `art:<pack>/<name>` slot). The shader is the normalize
  stage; the Asset Studio is its UI.
- **Launchpad:** the shader normalizes the token logo; content-addressing
  (`dreggnet-asset` / `dreggnet-sprite` / `dregg-ipfs`) makes the logo + microsite
  *verifiable*; the gateway site-publish spine serves it. The moat over p0 is
  provenance, not image generation.

Everything self-contained, esbuild-bundled, no heavy CDN tree — the repo ethos, held.
