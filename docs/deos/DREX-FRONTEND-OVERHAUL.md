# DrEX Frontend Overhaul — from a vanilla-JS demo to a product frontend

*The plan + seed for the DrEX product frontend. The current `drex-web` is a
hand-rolled vanilla-JS demo server that has outgrown the protocol's trading /
clearing patterns — the 8-mechanism family, the Open / Shielded / Dark tiers,
sealed-bid commit→reveal, the deposit→shield→clear→settle composition, and
multichain. This doc assesses the current surface honestly (demo-grade), designs
a real product architecture on a lightweight self-contained framework, sequences
the build Open-first (tracking deployability, naming what is ember-gated per
phase), and describes the working seed shipped alongside it (`drex-web-v2/`).
What-is, present tense; every not-yet-live surface is labelled exactly.*

Read alongside: `docs/deos/USER-FACING-STACK-REALITY.md` (the honest current
state), `docs/deos/DREGGFI-PRIVACY-TIERS.md` (the three tiers, one kernel),
`docs/deos/SHIELDED-DEPOSIT-BRIDGE.md` (the composition), `extension/src/page.ts`
(the real `window.dregg` API the frontend routes signing through).

---

## 0. Five-line summary

1. **The current `drex-web` is demo-grade** — a hand-rolled `node http` server
   serving raw ESM, a **baked demo book**, standalone wasm, and one clearing
   flow. Real engine behind it; not a product frontend.
2. **The overhaul is a component architecture** over a lightweight framework:
   **Preact + htm + `@preact/signals`, bundled by esbuild** — ~19.6 KB gzipped
   all-in, zero runtime CDN requests, a 6-package build tree. Justified against
   the repo's minimal-deps ethos below (§2.1).
3. **The extension is central.** `./extension` (`window.dregg`) is the identity +
   wallet + signer; the frontend is the orchestrator. All signing — the sealed-bid
   commit→reveal, the EVM leg, the dregg-native order-turn — routes through the
   installed extension. No standalone wasm on the user path.
4. **The build is Open-first.** Phase 1 (deployable now): the Open-tier ring
   clear + receipt + launchpad rung-1. Phase 2 (as Tier-1 goes live): shielded +
   sealed-bid + the reveal-nothing display. Phase 3 (as composition/federation
   deploy): dark + deposit→settle journey + multichain. Each phase names its
   ember-gated deploy dependency.
5. **A seed ships and runs** (`drex-web-v2/`): the app shell, the first-class
   tier-dial (with the live viewer-lens reusing `drex-viz`), the Open-tier ring
   order-entry wired to the **real `/clear`**, and the sealed-bid commit→reveal
   two-phase **routed through the real extension** (honest install-prompt
   fallback when no extension is present). Build + run cited in §5.

---

## 1. Assessment — the current `drex-web` (honest: demo-grade, real engine)

The current surface is **real in exactly the way it claims and demo in every
other way**. The crypto core and the matcher/solver behind it are real; the
product framing is a single-flow demo.

| Aspect | Current state | Cite |
|---|---|---|
| **Server** | hand-rolled `node http`, raw ESM from disk, no bundler, single process | `drex-web/serve.mjs:450` |
| **Book** | a **baked demo fixture** (`demoBook`), not real order entry | `drex-web/app.js:14`, `drex-web/drex-clearside.js:25` |
| **Clearing** | REAL: `/clear` shells to `drex_clear` (solver.rs ring match → verified_settle.rs kernel fold) | `serve.mjs:455`, `exec-lean/src/bin/drex_clear.rs` |
| **Shielded** | REAL engine: `/clear-shielded` (fhEgg PDHG + Cert-F) + `/prove-shielded` (Cert-F STARK) | `serve.mjs:467,484` |
| **Settle** | REAL: `/settle` lands one turn on a **solo** dev node; no on-chain settle | `serve.mjs:549` |
| **Wallet** | standalone wasm with **demo deterministic keys**; NOT the installed extension; no EVM leg | `drex-web/drex-wallet.mjs:65` |
| **Tiers** | shown as a static text panel inside one flow; not a first-class control | `app.js:460` |
| **Sealed-bid** | a JS `sha-256` commit/reveal **floor**, folded into Clear, not the real ceremony | `app.js:220`, `drex-wallet.mjs:173` |

### The specific gaps for the intricate patterns

- **Per-mechanism order entry — MISSING.** One order shape (offer→want ring
  order). The 8-mechanism family (uniform-price bid, circulation ring, Fisher
  budget, discriminatory, CFMM route, Price-Cert derivative, QP portfolio,
  package/AON bundle — `DREGGFI-PRIVACY-TIERS.md §3`) each has a *different order
  shape*; there is no per-mechanism form and no mechanism selector.
- **The tier-dial — MISSING as a control.** Open/Shielded/Dark are described in
  prose inside the shielded panel, not a first-class dial the user turns, and the
  "what each viewer sees" display is a per-flow afterthought, not the product's
  organizing UI. (The privacy dial *is* the product — `DREGGFI-PRIVACY-TIERS.md
  §6` — and the current UI buries it.)
- **Sealed-bid two-phase — DEMO FLOOR.** The commit/reveal is a JS `sha-256`
  hash confirm folded into Clear (`app.js:220`), not the real EIP-712 +
  secp256k1 ceremony the extension now ships (`extension/src/sealedbid.ts`,
  `page.ts` `dregg.sealedBid`). No two-phase UX, no escrow signature.
- **The composition journey — MISSING.** `deposit → shield → clear → settle`
  (`SHIELDED-DEPOSIT-BRIDGE.md`) has no guided user flow; nothing expresses the
  four stages or their honest grades.
- **Unified wallet — SPLIT & BYPASSED.** DrEX loads the wasm standalone with demo
  keys and never touches the installed extension; the EVM escrow leg lives only
  in `launchpad-web`. One identity that does both does not exist on this surface
  (`USER-FACING-STACK-REALITY.md §2`).
- **Multichain — ABSENT from the frontend.** Chain-aware deposit-A→settle-B
  (`DREX-ROUTING.md`) has no UI; chainId 46630 appears only in backend crates.

**Verdict.** The overhaul is not a rewrite of the engine (the engine is real and
stays); it is a **product frontend** — a component architecture that expresses
the mechanisms, the tier-dial, the sealed-bid ceremony, the composition, and the
unified extension-wallet, replacing the single baked-demo flow.

---

## 2. Design — the architecture

### 2.1 Framework: Preact + htm + `@preact/signals`, bundled by esbuild

**The choice, and why it fits the minimal-deps ethos.** The repo's ethos is
self-contained, no heavy CDN trees, raw ESM served from disk. A 300-package React
tree violates it; a compiler-required framework (Svelte, SolidJS) adds a build
toolchain the repo does not otherwise carry. **Preact + htm** is the honest fit:

- **Tiny.** The whole seed bundle — Preact + signals + htm + the reused
  `drex-viz` — is **51 KB minified / 19.6 KB gzipped**, one self-contained file,
  **zero runtime external requests** (everything inlined). Preact core is ~4 KB.
- **No compiler.** `htm` is a tagged-template literal — `html\`<${App} />\`` —
  so there is **no JSX transform, no Babel, no compiler step**. Components are
  plain ES modules. The dev path can even run buildless (raw ESM), exactly like
  the current `serve.mjs`.
- **A 6-package build tree.** `npm install` pulls **preact (0 deps), htm (0
  deps), @preact/signals (→ signals-core + preact, deduped), esbuild (one
  platform Go binary)** — the antithesis of a 300-dep React tree.
- **esbuild is one dependency.** A single Go binary bundles `src/` into one
  minified `dist/app.js`. Not a webpack/rollup plugin ecosystem — one tool, one
  command (`node build.mjs`), ~12 ms.
- **Signals fit the domain.** The tier-dial, the mechanism selector, and the live
  book are reactive state; `@preact/signals` gives fine-grained reactivity
  (~2 KB) without a Redux-shaped store.

Rejected: React (dep tree, ethos violation); Svelte/Solid (compiler toolchain the
repo does not carry); lit (web-components/shadow-DOM ceremony is heavier than
tagged-template components for a form-dense trading UI). Preact keeps the React
mental model at 1/40th the weight and no compiler.

### 2.2 The extension is the wallet + signer (the central integration)

`./extension` shipped a real DrEX surface this session (`extension/src/page.ts`,
verified against the source, not assumed):

- `window.dregg` is injected by the content script; readiness fires a
  `dregg:ready` event. **Detection** = `window.dregg` present, or wait for
  `dregg:ready`, else honest install prompt.
- **Connect** — `dregg.authorize({action, resource, mode})` → the extension's
  authorization-first confirm popup.
- **EVM leg** — `dregg.evm.getAddress()`, `.personalSign`, `.signTypedData`
  (secp256k1; the EVM key derives from the same sealed seed as the dregg-native
  Ed25519 identity, so one recovery phrase restores both).
- **Sealed-bid** — `dregg.sealedBid.commit({auctionId, order, chainId?,
  verifyingContract?, deadline?})` → `{commitment, signature, escrow}` (keccak256
  commitment + EIP-712 `SealedBid`); `dregg.sealedBid.reveal({auctionId})` →
  `{order, salt, bindsCommitment, signature}` (the extension re-hashes and checks
  binding — the same check the on-chain `revealBid` runs).
- **Order-turn** — `dregg.drex.placeOrder(order, {holdings, offer, traderId,
  ring})` → a real dregg-native signed Turn + (given holdings) a Bulletproof
  solvency proof bound to the order-turn id + a blinded ring-membership proof.

**The rule: the frontend never holds a key or signs in-page.** It orchestrates;
the extension is the identity + wallet + signer. This closes the two-wallet split
(`USER-FACING-STACK-REALITY.md §2`, §3.3 item 1–2): one identity does the
dregg-native order and the EVM escrow leg. The seed wires this real path (§5).

### 2.3 The component architecture

```
App (signals: activeTier, activeMechanism, book, clearing, wallet, sealed)
├─ Header ......................... brand · node status · wallet/extension status
├─ WalletPanel ................... the extension handshake (detect → connect →
│                                   identity + EVM address) OR honest install prompt
├─ TierDial (FIRST-CLASS) ........ Open / Shielded / Dark toggle + the live
│                                   viewer-lens: the SAME cleared ring drawn three
│                                   ways (open=full flows, shielded=blurred
│                                   amounts, dark=🔒 sealed) — reuses drex-viz
│                                   ringGraph; + the "world / solver / you sees"
│                                   honest columns; previews labelled not-live
├─ MechanismRail ................. the 8 mechanisms; each names its order shape +
│                                   most-private tier; only live ones are runnable
├─ OrderEntry (per-mechanism) .... dispatches on the mechanism's order shape:
│    ├─ RingEntry (ring) ......... offer→want + priority; Direct clear OR Sealed-bid
│    │    ├─ DirectBook ......... build the batch → real POST /clear
│    │    └─ SealedBidFlow ...... commit → reveal, extension-signed (two-phase)
│    ├─ LimitForm (uniform / discriminatory) .... side · quantity · limit price
│    ├─ BudgetForm (Fisher) ..... budget + per-good utility weights
│    ├─ RouteForm (CFMM) ........ in→out · min-out · pools
│    ├─ DerivativeForm (Price-Cert) .. payoff legs over underlyings + strikes
│    ├─ PackageForm (AON) ....... bundle of (asset, qty) legs · AON · reserve
│    └─ PortfolioForm (QP) ...... target return · bounds · covariance ref
├─ ClearingResult ................ ring · allocations · per-asset conservation ·
│                                   reject-polarity — from the REAL solver
│    └─ SettleResult ............ land as one real turn on the live node
├─ CompositionStrip .............. deposit → shield → clear → settle, each stage's
│                                   honest grade (Phase 3 journey)
└─ MultichainBar (Phase 3) ....... chain-aware deposit-A → settle-B selector
```

**Per-mechanism order-entry.** The `MECHANISMS` registry (`src/model.js`) carries
each mechanism's `orderShape`, `endpoint`, `live`, and most-private `tier`. The
`OrderEntry` component dispatches on `orderShape` to the right form. The seed
implements `RingEntry` fully (live); the others are registered with their shape
and honest live-state so the architecture is visible and the forms drop in as
their engines wire a runner bin (`offerings.mjs` already runs several engines;
they need the JSON-CLI runner + tier wiring, not new UI framework work).

**The tier-dial** is the product-defining control. It reuses the session's viz
(`drex-web/drex-viz.js` `ringGraph(ring, reveal)`) to redact the **real cleared
ring** per tier — a faithful adapter turns a `drex_clear` result into the viz
shape (`toVizRing`, verified in §5, no shape drift). Turning the dial re-draws the
same ring from each viewer's vantage; the "world / solver / you sees" columns
state each posture exactly (no dark-washing — Shielded says "the solver sees
plaintext"; Dark says "t-of-n threshold, ≥t can reconstruct").

**Sealed-bid two-phase** orchestrates `dregg.sealedBid`: phase 1 commit (hide +
escrow-sign), phase 2 reveal (open + binding check), then the revealed order joins
the open batch and clears. Real extension-signed crypto; the on-chain escrow post
is labelled deploy-gated.

**The API surface it calls** (`src/api.js`, the single source of truth for
live-vs-gated):

| Call | Endpoint | Live today | Notes |
|---|---|---|---|
| `clearOpen` | `POST /clear` | **yes** | real drex_clear (ring/TTC) |
| `settle` | `POST /settle` | **yes** (solo) | solo dev node; no on-chain settle |
| `nodeStatus` | `GET /node/status` | **yes** | node probe |
| `clearShielded` | `POST /clear-shielded` | engine yes | fhEgg plaintext Cert-F |
| `proveShielded` | `POST /prove-shielded` | engine yes | Cert-F reveal-nothing STARK |
| `commitBid`/`revealBid` | `POST /bid`, `/reveal` | **no** | needs the public signed-data RPC |
| `deposit`/`clearDark` | `POST /deposit`, `/clear-dark` | **no** | escrow contract / MPC federation |

Signing does **not** appear in this table — it is the extension's, via
`window.dregg`, not a server endpoint.

---

## 3. The honest build sequence (Open-first)

Each phase is a shippable product with an honest privacy label; each names the
**ember-gated deploy dependency** that lets its not-yet-live pieces go live. This
is `DREGGFI-PRIVACY-TIERS.md §4`'s deployment ladder, made concrete for the
frontend. **UI is only built for a flow once that flow is at least engine-real;
not-yet-live tiers/mechanisms render as labelled previews, never as live.**

### Phase 1 — OPEN, deployable now (the seed)

- **Ships:** the app shell + wallet handshake + the first-class tier-dial (Open
  live; Shielded/Dark preview) + the Open-tier multilateral ring order-entry
  wired to the real `/clear` + the real cleared receipt (ring, allocations,
  conservation, reject-polarity) + solo-node settle + launchpad rung-1 link.
- **Real end-to-end with no privacy tier, no RPC, no attestor** — the fastest
  honest path a stranger can complete (`USER-FACING-STACK-REALITY.md §6.1`).
- **Ember-gated to go PUBLIC:** deploy `DreggLaunchpad` to a real testnet
  (Base-Sepolia cheapest; Robinhood 46630 if targeted) + **host** the frontend
  (today: local dev server on the tailnet). *Nothing in Phase 1 is blocked on new
  crypto — only on a deploy + a host.*

### Phase 2 — SHIELDED, as Tier-1 goes live

- **Ships:** the tier-dial's Shielded position becomes live; the sealed-bid
  commit→reveal two-phase (already extension-real in the seed) posts to a real
  on-chain `SealedAuction` escrow; the shielded clearing panel (`/clear-shielded`
  + `/prove-shielded`) with the **reveal-nothing display** (the solver-sees vs
  world-sees boundary, the redacted flows, the public-inputs-only proof); the
  per-mechanism forms for the shielded-tier mechanisms (uniform-price,
  circulation, CFMM, package).
- **Ember-gated deploy deps:** (a) the **Poseidon2 Merkle swap** so in-browser
  STARK membership is un-forgeable (`USER-FACING-STACK-REALITY.md §3.2` — today
  disabled); (b) the **public signed-data RPC** (`/bid` + `/reveal`) that carries
  a cipherclerk-signed order to the on-chain `commitBid` (today absent — the seam
  the shielded story rests on); (c) the concrete **v1 committee
  `IClearingAttestor`** (today interface + mock). The reveal-nothing *theorem* is
  RESEARCH (`DREGGFI-PRIVACY-TIERS.md §1`), and the UI labels the display as
  "private-by-construction; the reveal-nothing theorem is named, not discharged."

### Phase 3 — DARK + composition + multichain, as those deploy

- **Ships:** the tier-dial's Dark position; the deposit→shield→clear→settle
  composition as a guided journey (each stage's honest grade — `SHIELDED-DEPOSIT-
  BRIDGE.md`); the multichain bar (chain-aware deposit-A → settle-B); the
  Price-Cert / QP / Fisher forms.
- **Ember-gated deploy deps:** (a) the **persistent n-party MPC federation** for
  the no-viewer clear (today: solo committee-of-one); (b) the **deposit escrow
  contract** + lock-event storage proof (today: LC-verified holding + labelled
  `lock_ref`, contract unbuilt); (c) the **note↔order adapter** on the settle path
  + feeding a real shielded-clearing turn to the wrap-adapter (today: PoC'd, not
  fed end-to-end); (d) the **PQ commitment cutover** + the **VK-epoch re-key /
  re-genesis** for the shielded-bridge descriptors. All deploy-time, not code
  (`SHIELDED-DEPOSIT-BRIDGE.md` "EMBER-GATED").

---

## 4. What is honest vs aspirational (the labels the UI carries)

- **Live end-to-end today:** the Open-tier ring clear (real matcher + verified
  settle), the solo-node settle, the node probe, and the **sealed-bid ceremony's
  cryptography** (extension-signed keccak256 + EIP-712 + secp256k1).
- **Engine-real, not yet on the live user path:** the shielded clear + Cert-F
  STARK (`/clear-shielded`, `/prove-shielded`); the fhEgg mechanism engines
  (offerings surface).
- **Preview (labelled not-live-with-real-money):** the Shielded and Dark tier
  positions, the on-chain sealed-bid escrow post, and the seven non-ring
  mechanisms at tiers whose endpoint is not live.
- **Never implied live:** no UI element implies a not-yet-deployed flow carries
  real money. Previews carry a `PREVIEW — not live with real money` tag and their
  deploy-gated dependency is named in place.

---

## 5. The seed — `drex-web-v2/` (builds + runs; cited)

A working seed lives at `drex-web-v2/`, **separate from `drex-web/`** so it never
disturbs the current demo (`:8781`), the offerings surface (`:8790`), the games
deploy, or the integration-harness lane. It runs on **`:8782`**.

**Layout.**
- `package.json` — preact / htm / @preact/signals + esbuild (the whole tree).
- `src/model.js` — the 8 mechanisms, 3 tiers, composition stages as data (honest `live` flags).
- `src/api.js` — the real endpoint client + the live-vs-gated endpoint map.
- `src/extension.js` — the `window.dregg` handshake (detect / connect / sealedCommit / sealedReveal / placeOrder / evmAddress).
- `src/app.js` — the Preact app (shell, wallet panel, first-class tier-dial with the live viewer-lens, ring order-entry, sealed-bid two-phase, clearing/settle result, composition strip).
- `index.html`, `styles.css` — the shell + a self-contained theme-aware stylesheet.
- `build.mjs` — the esbuild bundle step (`node build.mjs` → `dist/app.js`).
- `serve.mjs` — the v2 dev server: real `POST /clear` (drex_clear local-first, else the prebuilt remote matcher), `GET /node/status`, `POST /settle`.

**What runs (this session, cited):**

- **Build** — `node build.mjs` → `dist/app.js` **51.2 KB min / 19.6 KB gzip**
  (Preact + signals + htm + the reused drex-viz, one file, zero runtime CDN).
- **Real Open clear** — `POST /clear` over a user-entered book returns the REAL
  solver's result: `ok:true`, ring `Bram→Ada→Cyl`, `twoCycles:0` (genuinely
  multilateral), `conservesOk:true`, reject-polarity refuses leg 0. This is
  `drex_clear` (solver.rs + verified_settle.rs), built locally
  (`target/debug/drex_clear`), not a mock.
- **The app mounts** — headless-Chrome render of `http://127.0.0.1:8782/` shows
  the Preact app fully mounted (tier-dial "Privacy tier", "Open multilateral ring"
  entry, "Composition journey", the header), boot placeholder replaced.
- **The tier-dial viewer-lens reuse is faithful** — `drex-viz` `ringGraph` fed
  the real-clear-derived `toVizRing` adapter renders open (full flows), shielded
  (blurred amounts), dark (🔒 sealed) with no shape mismatch.
- **The extension path is real, with the honest fallback** — with no extension in
  the headless browser, the wallet panel renders "extension not installed" and
  sealed-bid is disabled (no faked signature). With the extension installed, the
  same code calls `dregg.sealedBid.commit/reveal` and `dregg.drex.placeOrder` for
  real (the `window.dregg` API in `extension/src/page.ts`).

**Run it:**
```
cd drex-web-v2
npm install          # 6-package tree (preact, htm, signals, esbuild)
npm run build        # esbuild → dist/app.js
node serve.mjs       # → http://127.0.0.1:8782
```

---

## 6. See also

- `docs/deos/USER-FACING-STACK-REALITY.md` — the honest current surface + the gaps.
- `docs/deos/DREGGFI-PRIVACY-TIERS.md` — the three tiers, one kernel, the tier-as-type.
- `docs/deos/SHIELDED-DEPOSIT-BRIDGE.md` — the deposit→shield→clear→settle composition.
- `docs/deos/PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md` — the public RPC + attestor the shielded path rests on.
- `extension/src/page.ts` — the real `window.dregg` API (evm / sealedBid / drex).
- `extension/src/sealedbid.ts` — the sealed-bid commit→reveal crypto.
- `exec-lean/src/bin/drex_clear.rs` — the real Open-tier matcher the seed's `/clear` shells to.
- `drex-web/drex-viz.js` — the clearing viz the tier-dial reuses.
