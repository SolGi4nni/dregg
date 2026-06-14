# WEB-FORWARD-EVERYWHERE — dregg in the browser, every way the glass admits

*The execution roadmap for the web-forward thesis. Present-tense, first-principles.
The vision and the model live in `docs/design-frontiers/WEB-FORWARD.md` (the
firmament `(target, rights)` handle carried to pixels in a tab) and the slice
ledger in `docs/FRONTIER-ROADMAP.md` (N10–N15, the web cut). This doc is the
opposite of a north star: it is the **burn-down** — six concrete fronts on which
dregg already runs, verifies, acts, and reaches from a browser, each stated as
WHAT IS SHIPPED, the NEXT SLICE, and the ONE HONEST GAP with its closure lever.
Companion-but-distinct: `docs/EMBEDDED-WEB-SURFACE.md` is the INVERSE arrangement
(a browser running as a cap-confined GUEST inside dregg); do not conflate them —
this doc is dregg-in-the-browser, that one is the-browser-in-dregg.*

dregg is the verified accountability SUBSTRATE a web app integrates against, not
the agent runtime: the perceive/plan/act loop lives ABOVE. Everything below is a
connection of code that already exists plus one named seam at the edge — the WELD
method (the capability usually already exists, disconnected; welding beats
building). No item here is a green-field research vacancy; each names its primitive
the way the kernel names the crypto floor.

---

## 0. The shape of the browser today (what every front builds on)

Three facts, all shipped, are the floor every section specializes:

- **dregg RUNS in the tab.** `wasm/src/runtime.rs`'s `DreggRuntime` is a complete
  in-browser dregg world — a real `dregg_cell::Ledger` + a real
  `dregg_turn::TurnExecutor`, minting cells via `Effect::CreateCellFromFactory`,
  executing signed multi-agent turns, exposed through ~80 `#[wasm_bindgen]`
  functions (`wasm/src/bindings.rs`). The SAME `dregg-turn`/`dregg-cell` crates the
  node and starbridge-v2 link, compiled to wasm32. A faithful `n = 1` machine.
- **dregg VERIFIES in the tab.** `dregg-lightclient::verify_history` (the Rust
  embodiment of `Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history`)
  checks ONE recursive `WholeChainProof` against a `RecursionVk` trust anchor and
  reads off the bound commitments, re-witnessing nothing — and `wasm/src/bindings_lightclient.rs`
  already exposes the in-tab fold+verify (`light_client_demo`).
- **dregg ACTS + READS the wire from the tab.** `@dregg/sdk/browser`
  (`sdk-ts/src/browser.ts`) ships the full two-noun door (`Identity → .turn() →
  .sign() → .submit() → Receipt`, @noble-ed25519-backed) plus the fetch+SSE
  `BrowserNodeClient` and the `TrustlineClient` / `ChannelsClient` organs.

The surface compositor (`site/playground/compositor.js`) and the surface bindings
(`wasm/src/surface.rs` + `wasm/src/bindings_surface.rs`) carry the firmament's
`Target::Surface{cell}` arm to a `<canvas>`, with the killer demo wired in
`site/playground/sections/web-surface.js`. That spine is done. The six fronts here
are what turns "a real dregg world in a tab" into "dregg, web-forward in every way."

---

## (a) The proving Web Worker — get the ~150s prove off the main thread

**What is shipped.** Real proving runs in the tab today. The light-client tooth in
`site/playground/sections/web-surface.js` calls `wasm.light_client_demo(2, 100n)`
— a real k=2 recursive fold+verify over the audited p3 descriptor prover — and the
predicate/STARK toys in `wasm/src/lib.rs` (`generate_predicate_proof`,
`prove_committed_threshold`, `generate_demo_stark_proof`) all prove in-tab. The UI
is honest about the cost: the verify button is annotated *"Recursive STARK proving
in the browser is SLOW (this can take a couple of MINUTES and will block the
tab)."* It is dispatched via `setTimeout(..., 30)` purely so the "working…" message
paints before the synchronous, blocking prove — i.e. it runs on the **main
thread** and freezes the page for the duration.

**What is shipped (the Worker — DONE).** Proving runs in a dedicated **Web
Worker**: `site/playground/prove-worker.js` is a `{ type: "module" }` worker that
`import`s the wasm-bindgen module (`../pkg/dregg_wasm.js`), inits its OWN wasm
instance + linear memory, and owns the heavy `light_client_demo` /
`verify_history_against_anchor` / `genesis_vk_anchor` / `prove_*` calls behind a
whitelisted `postMessage` protocol (request `{id, kind, args}` → response
`{id, ok, view}` / `{id, ok:false, err}`, with a one-shot `{ready}` after init).
The page side is `site/playground/proving-client.js` — a `ProvingClient`
promise-wrapper that spawns the worker, correlates responses by `id`, exposes typed
methods (`lightClientDemo`, `verifyHistoryAgainstAnchor`, …), and `cancel()`s by
terminating the worker (killing the running FRI fold + its wasm memory) and
respawning a fresh instance for the next call. `web-surface.js`'s verify path now
does `await provingClient.lightClientDemo(2, 100n)` with a spinner + a Cancel
button: the page stays responsive (the surface demo above is drivable while it
proves), the prove is a *background* cost, and the work is cancellable.

**The honest gap (with the lever).** The Worker fixes *responsiveness*, not
*latency*: a recursive STARK fold is still ~minutes of single-core wasm work, and
wasm has no SIMD/threads guarantee across browsers. The real latency levers are
two, both named elsewhere: (1) the **proving-modality dial** (`docs/FRONTIER-ROADMAP.md`;
HORIZONLOG #169) — most reads need the light-client VERIFY (milliseconds), not a
fresh PROVE; proving belongs at trust boundaries, and a tab should usually verify a
node-produced aggregate, not produce one (that path is item (b)); (2)
cross-origin-isolated **wasm threads** (`SharedArrayBuffer` + `Atomics` behind
COOP/COEP headers) to parallelize the FRI, which the p3 fork would need to expose a
threaded prover entry for. Until those land, the Worker makes the in-tab prove a
*background* cost, not a *frozen-page* cost — the responsiveness floor, advertised
as such.

---

## (b) `verify_devnet_history` in-tab — the WholeChainProof serde envelope

**What is shipped.** The verifier exists and is the right shape:
`dregg-lightclient::verify_history(agg: &WholeChainProof, expected_vk:
&RecursionVk)` runs the single succinct recursive-STARK verifier (cost independent
of history length), enforces the VK-fingerprint pin (a from-scratch prover folding
a DIFFERENT circuit is REFUSED — `VkFingerprintMismatch`), reads the carried
`genesis_root` / `final_root` / `num_turns` / `chain_digest` as Fiat–Shamir-bound
public inputs, and returns an `AttestedHistory`. In the tab,
`wasm/src/bindings_lightclient.rs::light_client_demo` already folds a real K-turn
chain and light-verifies it end-to-end in wasm32, SELF-ANCHORING (the VK
fingerprint is minted from the locally produced fold — exactly how an honest setup
mints the anchor it distributes). The anti-pale-ghost tooth runs in-tab today.

**What is shipped (the config-not-artifact tooth + the versioned envelope).** Two
in-tab teeth now make "the anchor is YOUR config, not the artifact" tactile, both
running the REAL `verify_history`:

- `genesis_vk_anchor(k, step)` + `verify_history_against_anchor(k, step, anchor_hex)`
  (`wasm/src/bindings_lightclient.rs`): the first mints the root-circuit `RecursionVk`
  fingerprint a genesis/checkpoint config distributes (a function of the window
  SHAPE, not the history's content — the load-bearing anchor property); the second
  folds a real chain and runs `dregg_lightclient::verify_history` against the
  CALLER-SUPPLIED anchor — NOT self-anchored from `agg.root_vk_fingerprint()`. A
  correct config anchor attests; a TAMPERED anchor is REFUSED with the genuine
  `VkFingerprintMismatch` (NO attestation). The playground wires a "mint my anchor →
  verify → tamper one byte → verify (REFUSED)" flow.
- `verify_devnet_history(envelope_json, config_anchor_hex)` over a versioned
  `ExternalHistoryEnvelope { version, vk_fingerprint_hex, proof_bytes_b64,
  genesis/final/chain_digest/num_turns }`: the EXTERNAL-aggregate transport shape. It
  parses + version-pins the envelope, takes the client's anchor as a SEPARATE
  argument, and runs the **anchor-discipline check** — the envelope's claimed
  fingerprint is compared to the configured anchor and REFUSED on mismatch, never
  trusted FROM the envelope.

The node's `lightclient/src/bin/whole_history_demo.rs` is the producer side; the
envelope is serialized there, fetched by `BrowserNodeClient`, and
`verify_devnet_history` deserializes it — once the one missing field can be filled.

**The honest gap (with the lever).** The envelope, the version pin, and the
anchor-discipline check are all shipped; the ONE remaining seam is precise and
narrowed to a single envelope field — `proof_bytes_b64` is EMPTY because
`WholeChainProof.root` is a `RecursionOutput<SC>` wrapping an `Rc<CircuitProverData>`
(an **in-memory** proof object with NO serde/byte encoding — confirmed at
`plonky3-recursion/recursion/src/recursion.rs`: `RecursionOutput<SC>(pub
BatchStarkProof<SC>, pub Rc<CircuitProverData<SC>>)`). So the cryptographic
recursion-verify step cannot yet run over the wire, and `verify_devnet_history`
reports that seam honestly (the anchor discipline above is REAL; the byte-verify is
the one blocked step) rather than faking it — the project law (never launder a
missing path as present). **This is a CIRCUIT/FORK seam, not a wasm-lane one**: the
closure lever is a **fork-side serialization of the recursion proof** (the same
follow-up the `circuit/src/ivc_turn_chain.rs` module docs name), after which
`proof_bytes_b64` is populated and `verify_devnet_history` calls `verify_history`
over the wire. It is also coupled to the two named recursion-floor follow-ups
(thread `table_public_inputs` up the tree so leaf identity is host-checked in-band);
the serialization and the in-band-PI fix share the fork lever. The runnable in-tab
teeth meanwhile are `light_client_demo` and `verify_history_against_anchor` (real
`verify_history`, proof present locally).

---

## (c) The browser AS a light-client NODE — sync, locally verify, in a tab

**What is shipped.** The two halves of a light node both exist. The **wire** half:
`BrowserNodeClient` (`sdk-ts/src/browser.ts`) is a faithful fetch+SSE client —
`getJson` / `postJson` / `sseStream` / `operatorPublicKeyHex` — byte-for-byte the
wire behaviour of the main `NodeClient`, with the `NodeEvents` SSE receipt stream
(`sdk-ts/src/events.ts`) giving a tab the node's committed-receipt feed with
`Last-Event-ID` resume. The `AttestedQuery` surface (`sdk-ts/src/attested.ts`) is
the light-client READ face — attested roots + checkpoints. The **verify** half is
item (b): `verify_history` over a `WholeChainProof`. A tab can already subscribe to
the live dynamics feed and drive turns against the devnet.

**The next slice.** Compose the two into a **light-client node object** that lives
in a tab: subscribe to the node's root/receipt SSE stream, hold the latest
config-pinned `RecursionVk` anchor + last finalized checkpoint, and on each new
finalized aggregate call `verify_devnet_history` to advance an
`AttestedHistory` — so the tab tracks the chain head having *checked* it, not
trusted it. The read surface (item (f)) then answers cell-state queries against the
last attested root, and a remote surface (the §6 self-attesting pane of
`WEB-FORWARD.md`) checks its `sourceStateRoot` chains to that attested head. This
is the browser realization of the existing browser-node work (HORIZONLOG #67):
connect to devnet, follow the blocklace, locally verify.

**The honest gap (with the lever).** A *full* light node would also **sync the
blocklace** (the DAG of signed blocks) to verify finality certificates itself, not
just consume the node's finalized-root SSE. Two seams: (1) the same
`WholeChainProof` serde envelope of item (b) gates the verify-the-aggregate step —
without it the tab can FOLLOW the head but cannot independently CHECK the recursion
proof over the wire; (2) blocklace sync in a tab is bounded by browser networking —
no inbound connections, fetch/SSE/WebSocket only — so a browser light node is a
LEAF that pulls from a serving node, never a gossip peer (the same n-parametrized
bound as everywhere: a tab is a relaxed-bounds participant, not a validator). The
lever for (2) is the existing pull-based catchup (`docs/FRONTIER-ROADMAP.md`; the
state-catchup / orphan-buffer work, HORIZONLOG #73) exposed over the
`BrowserNodeClient` wire. Honest stance: a tab is a *verifying light client*
(checks the succinct proof) reachable today modulo (b), not a *full node* (a
browser cannot be a gossip validator); the gradation is the point.

---

## (d) A PWA / installable web app — dregg on the home screen, offline-capable

**What is shipped.** The static site (`site/`) is a complete client app — landing,
explorer, playground, the studio inspectors (`<dregg-cell>`, `<dregg-receipt>`),
the wasm module (`site/pkg/`) — served as plain static assets and already
self-contained enough to run the in-tab world with zero backend (the playground's
`DreggRuntime` needs no network). The app shell, the icons, and the wasm bundle are
all present.

**The next slice.** Add the two files that make it **installable + offline**: a
`manifest.webmanifest` (name "dregg", the π mark already used as the favicon,
`display: standalone`, theme/background colors from the existing `style.css`
tokens, start URL `/playground/`) and a **service worker** that precaches the app
shell + the wasm module + the playground sections, so the in-tab dregg world (which
is already backend-free) works fully offline and launches from a home-screen icon.
The service worker is cache-first for the static shell and network-first (falling
back to the last attested checkpoint) for devnet reads. This is a pure-frontend
addition: the site is static, the wasm is a static asset, and the playground
already runs without a server.

**The honest gap (with the lever).** No service worker registration exists in
`site/` today (only the unrelated extension MV3 service-worker, and per-app
`manifest.json` files under `site/dist/starbridge-apps/*` that are app metadata, not
a root PWA manifest) — so the site is not yet installable and not yet offline. Two
honest scope lines: (1) a PWA caches the LOCAL `n = 1` world fully (no network
needed), but the DEVNET-backed surfaces (acting, the live feed, item (c)) are online
features that degrade to "last attested checkpoint" offline — the cache cannot
invent fresh finality; (2) offline acting means QUEUING turns (the SDK/extension
outbox pattern, already shipped in the extension's durable offline outbox) and
submitting on reconnect, never committing offline — the substrate's "a turn commits
only when the node finalizes it" is unchanged. The lever for both is the existing
outbox + the item-(c) attested-checkpoint state; the PWA shell makes them
home-screen-reachable.

---

## (e) A browser-extension front door — dregg identity + `.turn()` from any page

**What is shipped — and this front is largely DONE.** `extension/` is a full
Manifest-V3 cipherclerk (Chrome + Firefox, `manifest.json` + `manifest-firefox.json`),
bundling the wasm module, with the real ocap front door:

- **`window.dregg`** injected into every page (`extension/src/page.ts` via the
  `content.ts` nonce-bridged content script): `authorize`, `signTurn` /
  `signTurnV3(turnBytes)`, `shareCapability(cellId)`, `acceptCapability`,
  `createHandoff(cellId, recipientPk)`, `postIntent` / `postEncryptedIntent`,
  `privateTransfer`, `createBearerCap`, plus the `dregg.on(...)` live-activity feed.
- **Named identity profiles** — an identity is a name you chose, not a hex key;
  every signing path reads the active profile's Ed25519 key, derived
  `blake3 derive_key("dregg/0", seed)` identically to the CLI/SDK (the golden vector
  `00..3f → 335840a9…` pinned in three suites).
- **Authorization-first signing** — `signTurnV3` never signs blind: the clerk
  decodes the turn, renders the faithful `explain.ts` reading bound to the canonical
  `[turn <hash>]` in a nonce-bound confirmation popup, and surfaces unreadable
  effects as UNKNOWN with a do-not-sign-blind warning. Origin allowlisting splits
  unrestricted reads from approval-gated acts (`content.ts`).
- **Receipt as the result** — signed turns travel as the node's `SignedTurn`
  postcard envelope to `/api/turns/submit-signed` with a durable offline outbox +
  retry, and the background tails the receipt SSE stream (badge count, recent
  receipts, `Last-Event-ID` resume). Keys at rest: BIP39 phrase per profile, PBKDF2
  + AES-256-GCM, auto-lock.

So "dregg identity + an authorized, human-confirmed turn from any page, with the
receipt streamed back" is shipped today; the extension is the stranger's first
ocap-native front door.

**The next slice.** Deepen the `.turn()` ergonomics toward the SDK's two-noun
shape: a one-call `window.dregg.turn(builderSpec)` that returns the clerk's faithful
`explain()` reading and a `Receipt`, mirroring `@dregg/sdk`'s
`Identity → .turn() → .sign() → .submit() → Receipt` so a dapp author writes the
SAME shape whether they import the SDK or call the injected provider. Bundle the
surface bindings (item (f)) so an extension-hosted page can open/share a `<canvas>`
surface under the clerk's identity, and surface the in-tab light-client verify (item
(b)) in the popup so a receipt can be shown against an attested head.

**The honest gap (with the lever).** Today `.turn()` from a page goes
page → content-script → background → node (and, when offline, to the outbox), with
the human in the loop at the confirmation popup — it is a *mediated* turn through
the clerk, not a direct page-side `.submit()`, and that mediation is the security
property, not a deficiency (the page never holds the key; cf. HORIZONLOG #171, the
signed-envelope adoption seam — agent/page turns route THROUGH the clerk/node, never
straight to the wire). Two named scope lines: (1) the page-side `window.dregg` is
the browser's `postMessage` bridge, so its integrity rests on the content-script
nonce channel + origin allowlist (the web's IOMMU-equivalent, the same
same-origin-policy primitive item F3 of `WEB-FORWARD.md` names) — not a dregg proof;
(2) Chrome Web Store distribution is not yet available (manual unpacked-load only,
per `site/extension/index.html`), so the front door ships as a developer-loaded
extension. The lever for (1) is unchanged (lean on the browser's origin isolation,
name it); for (2) it is store submission, a packaging step not a code gap.

---

## (f) `@dregg/sdk` browser bindings, deepened — the surface as TypeScript

**What is shipped.** `@dregg/sdk/browser` (`sdk-ts/src/browser.ts`) is the FULL
acting + reading surface, browser-clean: the two-noun door `Identity → .turn() →
.sign() → .submit() → Receipt` (now @noble-ed25519-backed, so it no longer imports
`node:crypto`), the fetch+SSE `BrowserNodeClient`, the `AgentRuntime`, the `Receipt`
noun with its `explain()` anti-blind-signing reading, the `NodeEvents` receipt
stream, and the organ clients (`TrustlineClient`, `ChannelsClient`). Authorization
is INESCAPABLE — there is no `Unchecked` constructor on this surface (it stays sealed
behind `@dregg/sdk/raw`); the auth field is private to the `.sign()` flow (#166).
The legacy wasm-bound playground client remains at `@dregg/sdk/wasm` (token toys,
proof toys, the `DreggRuntime` sim). `sdk-ts/examples/*` ships the worked snippets
(`transfer.mjs`, `trustline.mjs`, `channel.mjs`, `attested-query.mjs`,
`browser-front-door.mjs`, `devnet-walkthrough.mjs`).

**The next slice.** Give the browser SDK a TypeScript face for the two web-native
surfaces that today live only as raw wasm exports: (1) a **`SurfaceClient`** over the
`open_surface` / `present_surface` / `share_surface` / `revoke_surface` /
`surface_identity` bindings (`wasm/src/bindings_surface.rs`) so a dapp gets
`surface.open(cell, rights)` → `SurfaceView`, `.present(region)`, `.share(to,
narrower)` (a real `GrantCapability` turn; widening rejects), `.revoke()`, with the
T2 identity badge typed — the compositor (`site/playground/compositor.js`) becomes a
consumer of a typed client rather than calling wasm directly; and (2) an
**`AttestedHistory`** TS type over the item-(b) `verify_devnet_history` export, so
`AttestedQuery` (`sdk-ts/src/attested.ts`) can return reads bound to a
locally-verified head. Both are thin bindings over existing Rust — no logic
reimplemented in TS.

**The honest gap (with the lever).** Two scope lines, both about WHERE the work
runs: (1) the surface bindings drive the wasm `DreggRuntime` (the local `n = 1`
ledger), so a `SurfaceClient` against the LOCAL world is complete today, but a
surface shared with a peer's tab (`n > 1`) needs the remote-surface self-attestation
of `WEB-FORWARD.md` §6 carried over the `BrowserNodeClient` wire — relaxed bounds,
same verbs, gated on item (b)'s envelope for the `sourceStateRoot` check; (2) the
node still computes the factory descriptors / seal fan-outs the TS wire layer does
not carry (each organ client's "Honest scope" line states its node-side/client-side
split), so the browser SDK is the ergonomic FACE of node services, not a
reimplementation of them. The lever is the same throughout: bind, do not rebuild;
name the node-side half; carry the n-gradation honestly (a tab is `n = 1` complete,
`n > 1` relaxed).

---

## The discipline across all six

The in-tab world is REAL — the SAME `dregg-cell`/`dregg-turn` crates, the SAME
`granted ⊆ held` lattice, the SAME `TurnExecutor`, the SAME light-client verifier —
and it advertises itself as **"the real dregg crates in wasm32, differential-anchored
to the Lean producer,"** NOT "verified-in-browser" (the Lean executor compiled to
wasm is the F2 frontier of `docs/design-frontiers/WEB-FORWARD.md` §7, a build in
flight in `web/spike/`, not a research vacancy). Each of the six fronts above names
its one honest seam with its primitive the way the kernel names the crypto floor:

- (a) wasm single-core latency → the proving-modality dial + threaded-FRI behind
  COOP/COEP (a Worker fixes responsiveness, not latency);
- (b) `WholeChainProof`'s `Rc`-backed in-memory proof → a fork-side recursion-proof
  serialization (the versioned envelope);
- (c) a browser is a verifying LEAF, never a gossip validator → pull-based catchup +
  the (b) envelope;
- (d) the local world caches fully offline, devnet reads degrade to the last
  attested checkpoint → the outbox + item-(c) state;
- (e) `.turn()` from a page is MEDIATED through the clerk (the key never touches the
  page) → the content-script origin isolation (the browser's same-origin policy),
  named, + store distribution;
- (f) the browser SDK is the FACE of node-computed descriptors, `n = 1` complete and
  `n > 1` relaxed → bind-not-rebuild + the self-attesting remote surface.

None of these is a wall. Each is WORK with a stated lever, several of them sharing
ONE lever (the recursion-proof serialization unblocks (b), (c), and the `n > 1`
half of (f) at once). The web is dregg's reach; carrying the one capability handle —
and the one light-client verifier — out to the glass of a browser is connection plus
honestly-labeled seams, all the way to the canvas.
