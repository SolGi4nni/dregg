# wasm & in-browser deos

Two cdylib crates compile the dregg substrate to `wasm32-unknown-unknown` and
drive it from a browser tab. Both run the REAL `dregg-cell`/`dregg-turn` ledger +
verified `TurnExecutor` in-tab — not a mock and not a recorded crawl.

- **`dregg-wasm`** (`wasm/`) — the primitives + full-runtime playground: token
  ops, STARK/Merkle/Datalog demos, privacy primitives, a complete virtualized
  `DreggRuntime`, the web surface, the light-client-in-the-tab, transclusion, and
  the card/inspector worlds.
- **`starbridge-web`** (`starbridge-v2/web/`) — the cockpit MODEL in the browser:
  a JSON skin over `starbridge_v2::World` (`WebImage`), plus a gpui-on-WebGPU
  cockpit (`cockpit_web`) behind a feature gate, plus a PTY-over-WebSocket
  terminal bridge.

Both are `crate-type = ["cdylib", "rlib"]` — cdylib for the browser bundle, rlib
so integration tests link the crate and drive its `#[wasm_bindgen]` surface under
`wasm-pack test` (`wasm/Cargo.toml:10-14`, `starbridge-v2/web/Cargo.toml:6-8`).

---

## `dregg-wasm`

### The platform gate: `no-lean-link`

wasm32 cannot link `libdregg_lean.a`, so the local crates are pulled with the
`no-lean-link` feature and compile their Rust fallback paths
(`wasm/Cargo.toml:25-28`). This is a statement about THIS target's linker, not
about which guarantees native dregg has (there Lean is unconditional). Several
indirect deps are forced onto wasm-safe feature flavors via feature unification:
`clear_on_drop` → `no_cc` (no C compiler invocation, `wasm/Cargo.toml:137`),
`lockstitch` → `portable` (no x86/aarch64 AES intrinsics, `:141`), and `biscuit-auth`
→ `wasm` (its `performance_now()` `Instant` shim, `:148-149`).

### `DreggRuntime` — the virtualized distributed system in the tab

`runtime::DreggRuntime` (`wasm/src/runtime.rs:304-353`) is the complete in-browser
world: a `Ledger`, a `TurnExecutor`, a `NullifierSet`, agents, intents, revocation
channels, pending conditionals, federations, receipts/turns, an observability
`Emitter`/`EventLog`, and lazy proof caches. `DreggRuntime::new`
(`runtime.rs:439-477`) builds the executor and deploys a default "test cipherclerk"
factory; subsequent agents/cells are minted via the canonical
`Effect::CreateCellFromFactory` path against that VK (`runtime.rs:446-455`).

The load-bearing turn entry is `execute_turn_for_agent`
(`runtime.rs:1284-1382`): it builds a `Turn` with the agent's current nonce,
chains the previous receipt hash, signs the call-forest with the agent's
cipherclerk (`sign_call_forest`, `runtime.rs:1325`), and runs `self.executor.execute`
(`runtime.rs:1327`) — the SAME executor native callers exercise. Each result feeds
the observability `Emitter` (Committed/Rejected/Expired lifecycle events,
`runtime.rs:1334-1379`). The runtime carries lazy proof producers:
`prove_turn` (per-turn EffectVM STARK, `runtime.rs:674`) and
`prove_bilateral_aggregate` (the GOLDEN-tier cross-cell aggregate via
`dregg_turn::aggregate_bilateral_prover::prove_aggregated_bundle`,
`runtime.rs:510`, self-verified before caching) — NOT run at boot, since STARK
proving is expensive in wasm.

### `bindings.rs` — the `#[wasm_bindgen]` surface over `DreggRuntime`

Runtimes live in a `thread_local!` `Vec<Option<DreggRuntime>>` keyed by a `usize`
handle (`bindings.rs:24-26`); JS holds the handle. `create_runtime`
(`bindings.rs:61-76`) reuses tombstone slots; `with_runtime`/`with_runtime_ref`
(`bindings.rs:28-54`) borrow the runtime for a closure. The surface exposes 71
`#[wasm_bindgen]` functions covering cell/agent creation, factory deploy, token
mint/attenuate, turn execution (incl. `execute_turn_step_by_step`,
`bindings.rs:477`), app-program install + governed-namespace flows, capability
grant/revoke/tree, notes (create/spend), federations + consensus rounds, intents +
matching, conditionals, revocation channels, peer exchange, and inspector view
data. WASM is single-threaded so the `RefCell` store is safe (`bindings.rs:18-20`).

### `lib.rs` — the stateless primitive demos

Top-level `#[wasm_bindgen]` functions (35) over the crates directly, no runtime
handle: macaroon token mint/attenuate/verify (`lib.rs:58-228`), a demo STARK
(`generate_demo_stark_proof`/`verify`/`tamper`, `lib.rs:230-373`), predicate
proofs, Merkle root/membership/non-membership (`lib.rs:507-657`), Datalog
authorization eval + a CRDT-fold demo (`evaluate_datalog`/`demonstrate_fold`,
`lib.rs:658-845`), BLAKE3, threshold-commitment prove/verify, Schnorr keygen/sign/
verify, a garbled comparison, anonymous-membership proof, mnemonic keypair
derivation, turn build + `sign_turn_v3`, CapTP-delivered auth, and the cipherclerk
private-flow builders (`lib.rs:2136-2700`).

### `privacy.rs` — privacy + advanced primitives

25 `#[wasm_bindgen]` functions for the browser extension: stealth-address derive/
create/scan (`derive_stealth_keys`, `scan_stealth_announcements`,
`privacy.rs:26-281`), Pedersen value commitments + conservation prove/verify,
Bulletproof range proofs, SSE search tokens + sealed intent bodies, bearer
capabilities + proofs, factory `create_from_factory` + provenance verify,
sovereign-cell conversion, peer exchange with proof, proof composition
(`compose_proofs`/`compose_and_verify_proofs`, `privacy.rs:1479-1582`), and facet
masks. Intermediate private-key material is held in `Zeroizing` so the linear-
memory residue is scrubbed on drop (`privacy.rs:46-50`).

### `CardWorld` & `InspectorWorld` — the card-in-the-tab loop

`bindings_card.rs` carries the wasm analog of `deos_js::applet::Applet::fire`. A
deos-js card renders renderer-independently (the same `ViewNode` paints to gpui
pixels natively AND to browser HTML via `deos-view`'s web renderer); this module
closes the LIVE turn seam — a browser button-click fires its `{turn, arg}`
affordance as a real cap-gated verified turn (`bindings_card.rs:1-28`).

- `CardWorld` (`bindings_card.rs:60-171`) owns one `DreggRuntime` with one
  card-cell (agent 0, genesis, single-custody). `new(slot, initial)` mints the
  card and seeds the model slot via a real verified turn (`:77-91`). `fire(turn,
  arg)` (`:124-138`) handles the `"inc"` affordance — `count := count + arg` over
  the live model — and commits via `commit_set` (`:153-170`), which issues
  `Effect::SetField` + `Effect::IncrementNonce` through `execute_turn_for_agent`,
  the same two effects the native applet builds. `read` is a witnessed ledger read
  (`:102-108`); `receipt_count` is the audit-tape length (`:142-145`). `arg` is an
  `i32` so wasm-bindgen maps it to a plain JS number, not a BigInt (`:118-123`).
  `pack_u64`/`unpack_u64` (`:42-54`) are byte-identical to
  `deos_js::applet::{pack_u64, unpack_u64}` (little-endian into the low 8 bytes of
  a 32-byte felt).

- `InspectorWorld` (`bindings_card.rs:208-367`) carries the reflective-inspector
  card. `view_tree_json` (`:298-302`) generates the `{kind, props, children}`
  view-tree the web renderer consumes, by reading the focused cell's RawFields +
  Affordances faces off the live ledger via `deos-reflect`
  (`ReflectedCell::from_ledger`, `AffordanceSurface::project_for`,
  `inspector_view_tree_json` `:390-475`) — the gpui-free port of
  `deos_js::inspector_card::inspector_view_for`. Each affordance
  (`AFFORDANCES = [("tick",0),("add",1),("score",2)]`, `:372`) `fire`s a real
  verified `SetField` turn that advances its bound slot (`:317-325`).

The host-target test `card_fires_a_verified_turn.rs` drives the full loop
end-to-end (mint → witnessed read → fire `+1` → re-read; `:42-100`), and the
wasm32-target `wasm_loop` module (`:248-368`) runs the same loop in a real wasm
module under `wasm-pack test --node`/`--headless --chrome`, where the executor's
profiling clock routes through `turn_profile::Instant` = `web-time::Instant`
(backed by `performance.now()`) — closing the old "time not implemented" panic.

### `surface.rs` + `bindings_surface.rs` — a browser window IS a cell's surface cap

The in-tab realization of `sel4/dregg-firmament/src/surface.rs`'s
`Target::Surface{cell}` arm, mirrored onto the existing `DreggRuntime` ledger +
executor rather than a parallel surface model (`surface.rs:1-9`). Five verbs
(8 `#[wasm_bindgen]` entries in `bindings_surface.rs`):

- `open_surface` (`bindings_surface.rs:29-39`) — opens an agent's own cell as a
  surface, hands the owner an original self-cap, returns a `SurfaceIdentity`.
- `present_surface` (`:51-60`) — resolves the surface cap against cell-state via
  the REAL `dregg_cell::is_attenuation` (`required ⊆ held`); a wider request is
  refused (`surface.rs:20-22`).
- `share_surface` — a genuine `Effect::GrantCapability` turn through the executor;
  a WIDENING share is rejected with `DelegationDenied`, the no-amplification law
  at the pixel layer (`surface.rs:23-26`).
- `revoke_surface` — drops the holder's cap; at n=1 (the local tab) revocation is
  immediate (`surface.rs:27-29`).
- `surface_identity` — the anti-spoof T2 badge `SurfaceIdentity`
  (`owning_cell_id`, `lifecycle`, `source_state_root`, `balance`,
  `accepts_effects`) read FROM THE LIVE LEDGER, never the page's self-description
  (`surface.rs:54-74`). A label ≠ owner is impossible because the badge is a
  function of the cell's real state.

### `bindings_lightclient.rs` — the light client in the tab

`#[wasm_bindgen]` over `dregg-lightclient::verify_history`: fold a whole finalized
history into ONE succinct recursive aggregate and verify it re-witnessing nothing
(`bindings_lightclient.rs:1-46`). Six entries; the `k`-turn chain is clamped to
`[2,4]` (recursive chain-binding needs ≥2 turns; recursive proving in a browser is
heavy, `:86-90`). `AttestedHistoryView` (`:55-74`) is the JS view of
`AttestedHistory` — `attested`, genesis/final root, `chain_digest`, `num_turns`,
and a `named_floor` string surfacing the honest soundness floor
(`recursive_sound` — the recursion fork's FRI engine soundness, `:42-45`).

- `light_client_demo` (`:93-112`) — fold + light-verify in the tab; SELF-ANCHORS
  (mints the VK fingerprint from the local fold).
- `genesis_vk_anchor` — return the config VK-fingerprint anchor for a window shape.
- `verify_history_against_anchor` — fold, then verify against a CALLER-supplied
  anchor; a tampered anchor is refused with `VkFingerprintMismatch` (`:25-28`).
- `produce_external_history_envelope` / `verify_devnet_history` — produce + verify
  an externally-produced versioned envelope of proof bytes via
  `verify_history_bytes`, with the anchor a SEPARATE argument never read off the
  envelope under verification (the light-client invariant, `:35-40`).

Each leaf is a real Lean-descriptor EffectVM proof (`prove_vm_descriptor`)
verified in-circuit by the recursion wrap (`:80-84`). This is the only wasm path
that pulls the circuit prover + recursion tower (`wasm/Cargo.toml:95-103`).

### `bindings_transclusion.rs` — Xanadu made honest, in the tab

The minimal resolve/render path of `starbridge_web_surface::transclusion`
(`bindings_transclusion.rs:1-31`). A separate `thread_local!` store of
`TransclusionDemo` (a real `WebOfCells` — a genuine `dregg_cell::Ledger` +
`AttestedRoot` receipt-stream verifier — plus a name→`dregg://`-ref registry,
`:52-72`), disjoint from the `DreggRuntime` surface store. 10 `#[wasm_bindgen]`
entries drive: transclude a span (`transclusion_include`, a verified finalized
read — displayed bytes ARE the committed bytes), amend the source so a LIVE
re-read follows while a SNAPSHOT stays pinned, a forge attempt that REFUSES with
`ContentHashMismatch`, and a per-viewer projection through the real
`rehydrate::Membrane` (`granted ⊆ held`) (`:12-25`). It does NOT touch the circuit
prover or recursion path.

---

## `starbridge-web` (`starbridge-v2/web/`)

### `WebImage` — the cockpit model, JSON skin (default build)

`WebImage` (`starbridge-v2/web/src/lib.rs:38-186`) wraps a
`starbridge_v2::world::World` + three anchor cells, booted from the same
`demo_world` the native cockpit and the atlas crawl use (`:48-52`). Five methods
mirror `dregg-mcp`'s core tools, each driving the REAL embedded executor:

- `survey` (`:55-79`) — the cell roster with headline fields, via
  `reflect_cell`.
- `inspect` (`:82-95`) — a cell's presentation faces via `Registry::present`.
- `affordances` (`:98-116`) — the messages a cell understands, each with its
  effect + cap badge, via `InspectAct::build`.
- `act` (`:120-148`) — FIRE a message: `InspectAct::send` runs a real cap-gated
  turn through the verified executor, mutating the live image; returns the receipt
  (`post_state`, `computrons`, `action_count`) or the in-band refusal
  (`by_executor`, `reason`).
- `ocap` (`:151-157`) — the whole ocap web (cells + capability edges) via
  `OcapGraph::build`.

The JSON serializers (`field_value_json`/`body_json`/`presentation_json`,
`:210-257`) carry the seven `PresentationBody` shapes (fields/graph/prose/
timeline/gauge/state-machine).

### `cockpit_web` — the gpui cockpit on WebGPU (feature `gpui-web`)

Gated `#![cfg(all(target_arch = "wasm32", feature = "gpui-web"))]`
(`cockpit_web.rs:32`), pulling `starbridge-v2`'s `gpui-web` feature (gpui +
gpui_platform → gpui_web) (`starbridge-v2/web/Cargo.toml:25-40`). The wasm
entrypoint `boot_cockpit` (`cockpit_web.rs:64-` ) seeds a fresh sovereign genesis
image (`world::demo_genesis`), runs a single-threaded web gpui app
(`gpui_platform::single_threaded_web().run`, `:74`), registers the embedded
cockpit fonts (Lilex / IBM Plex — the web text system carries neither, `:79-86`),
initializes `gpui-component` (`:93`), and opens a window that creates the WebGPU
canvas and mounts `WebCockpitRoot` (`:100-137`). The run-loop drives paints/events
thereafter — every affordance click is a real cap-gated turn through the in-tab
verified executor (`:61-63`).

`WebCockpitRoot` (`:150-`) stacks the real `Cockpit` over two mounted panes, all
rendered into the ONE gpui_web canvas:

- `WebEditorPane` (`:224-`) — a firmament-backed editor over deos-zed's gpui-free
  `FirmamentFs` (`OwnedSpine` = `Ledger` + `TurnExecutor`). A SAVE is a real
  cap-gated `Effect::SetField` turn through the in-tab executor, leaving a
  verifiable `TurnReceipt`; the status line shows the GENUINE on-ledger receipt
  count + last post-state digest (`:212-303`). deos-zed's own gpui `Editor` is
  native-only — the gpui editor element tree is rendered HERE; the wasm-safe reuse
  is the executor-backed `Fs` (`:25-27`, `:219-223`).
- `WebChatPane` (`:380-`) — a chat view over deos-matrix's gpui-free `MockSource`
  `ChatSource` seam (`:16-24`).

The cockpit does NOT pull deos-zed/deos-matrix's own `gui`/`cockpit-surface`
features (those link native windowing, which cannot reach wasm32, `:25-27`).

### `pty_ws` — the terminal pane's PTY-over-WebSocket bridge

`pty_ws.rs` shares one wire codec, `WireMsg` (Resize / Exit, JSON in text frames;
raw PTY bytes ride binary frames, `:40-65`), across two ends:

- **native** (`cfg(not(wasm32))`, feature `pty-ws-server`): `serve`/`bind_serve`
  (`:93`, `:113`) bind a TCP listener and give each connection a fresh `$SHELL` on
  a PTY, splicing client binary frames → PTY stdin and PTY output → client binary
  frames (`:67-273`). Run by the `starbridge-web-pty-ws` bin
  (`starbridge-v2/web/Cargo.toml:14-17`).
- **wasm** (`cfg(wasm32)`): `WsTransport` (`:385-`) — a `web_sys::WebSocket` to
  that server, speaking the SAME wire, that the gpui-web terminal pane dials
  (`:20-24`). The e2e test (`starbridge-v2/web/tests/pty_ws_e2e.rs`) is a native WS client against
  the same server, proving the wire.

The default `starbridge-web` build (`WebImage`, JSON/atlas skin) carries only the
`WsTransport` client half; `gpui-web` is purely additive (`Cargo.toml:24-25`).
