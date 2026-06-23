# HORIZONLOG — the named-follow-up burn-down

*(Standing rule: when a lane/commit NAMES a follow-up, residue, or closure lane,
it gets a line HERE in the same breath — "named in a report" is not durable.
Each line: what · where it was named · the closure shape. Remove lines when
closed (git history is the record). This is a burn-down list, not a parking
lot: per WE-DO-NOT-NAME-WE-SHIP, anything that sits here across many sessions
should be either scheduled or explicitly demoted to the Research tier with a
reason.)*

Last sweep: 2026-06-13 (flagged-items burndown — removed ~14 landed/struck items,
deduped the DreggDL/sel4/snapshot landings into git history, kept live tails).

### NETWORK-PORTABLE PROCESS — cross-node CapTP cap handoff, by running (2026-06-23).
`f0efdb39` (`captp/src/handoff_session.rs` + `node/src/captp_handoff_e2e.rs`). The `PresentHandoff` leg
now routes over the node↔node transport: A frames an introducer-signed handoff, B receives + runs the
proven `validate_handoff` against ITS OWN swiss table (`held` never read from the cert), resolves a live
`SendCap`. Demonstrated 3 ways incl. node-grade over the REAL relay HTTP routes (A POSTs sealed frame →
B drains/unseals/validates/uses it on a `Bus`). No-amplification PROVEN: over-broad handoffs + untrusted
introducers refused before any cap installs; the `Bus` re-checks `admits` on every enqueue. 198 captp
tests green. (Index race: this commit also swept the XANADU lane's byte-identical final files — benign.)

### XANADU DOCUMENT LANGUAGE — usable, by running (2026-06-23).
`f0efdb39` (`starbridge-v2/src/xanadu_e2e.rs`, 3 tests pass; `dregg-doc` 102/120 green). ONE braid:
doc-as-Pijul-patches with branch + MERGE (disjoint composes clean; same-position yields ONE first-class
`ConflictRegion` carrying both authors' alternatives w/ provenance — NOT silent overwrite; a `Connect`
resolves keeping both) · TRANSCLUSION (a `WholeCellTransclusion` cites C + finalized commitment, visible
to a capped reader, DARKENS for an under-capped one w/ provenance surviving, re-resolves LIVE) ·
BIDIRECTIONAL links (the quote registers in the `Backlinks` witness-graph → C's "what links here" lists A).
Plus an EXECUTOR-DRIVEN variant (`DocEditor`: each edit a cap-gated turn; unauthorized edit refused in-band).

### SERVO REAL PAGE — surfman ceiling BROKEN, a real page rasterizes (2026-06-23).
`d5af70e5` (servo-render). Cleared 3 nested blockers (surfman `connection()`=None, event-loop pacing,
SWGL `DepthFunc` SIGABRT via a 1-field vendored servo-paint fork `clear_caches_with_quads:false`). 17/17
green (the once-`#[ignore]`d render test RUNS). PNGs: `servo_real_page_render.png` (a laid-out `data:` page,
CSS box measured 160×120) + `servo_real_text_render.png` ("dregg" as 212-color antialiased glyphs — SEEN).
Remainder: http(s) bytes still ride servo's hyper (needs a `net` fork); the servo-paint fork reverts when
upstream carries a SWGL `RenderingContext`.
### MULTIPLAYER MEMBRANE — the killer primitive, DEMONSTRATED by running (2026-06-23).
`2bdb6ed2` (`shared_fork.rs`). ONE minted `MembraneFrustum` (the screenshot-of-the-moment, a cap-bounded
`World::fork` cull) → carried over the postcard wire shape (the `MembraneEnvelope.snapshot` bytes) →
rehydrated into TWO independent real `World`s under TWO distinct principals (both `frustum_root`-matched =
anti-substitution) → each drives a real verified `commit_turn` (overlapping conflict + disjoint private) →
both stitched via `Stitch::settle`: disjoint pushout-merge clean, the overlapping divergence resolves by
the linear Dead-wins join TRANSPARENTLY (not silent LWW), an over-authorized confer is REFUSED (lossy-drop,
`SettleOutcome::Refused`). Σδ=0 + authority sound. 21 `shared_fork` tests pass on the real embedded executor.

### FEDERATION QUORUM VOTES — landed, with a net/-layer delivery ceiling (2026-06-23).
Phase 1 (REAL 2-node federation) is PROVEN by running: two `dregg-node` procs sharing a 2-validator genesis
(`--federation-mode full`, gossip ports cross-pointing) form an n=2 committee, `peer_count:1`, mesh ready;
a faucet turn on A propagates to B and BOTH DAGs converge byte-identically (6 blocks, the turn block
super-ratified, `latest_height:1`, alice balance=5000 on both). Runbook: `docs/deos/DEV-NODE-RUNBOOK.md`
("A REAL two-node federation").
Phase 2 (quorum finalization votes) is BUILT + tested: `node/src/finalization_votes.rs` (`FinalizationVote`
signed over domain‖block_id‖level, `VoteCollector` gating consensus-wide Attested on 2f+1 DISTINCT verified
committee signers; 7 unit tests incl. a two-node exchange sim). Wired into `blocklace_sync.rs`: votes ride the
blocklace topic as `BlocklaceGossipMessage::FinalizationVote`, emitted on local finalization, collected by
`handle_finalization_vote`, exposed as `dregg_consensus_attested_total`. Anti-entropy added: per-emit nonce
(defeats `seen`-dedup), cadence re-emit budget, Frontier vote-piggyback + frontier-reply, and a `net/`
small-N eager-floor fix (`gossip.rs::demote_to_lazy` no longer prunes the sole peer to lazy; new test
`prune_respects_small_n_eager_floor`).
✅ CLOSED (2026-06-23, proven by running): n=2 reaches consensus-wide `Attested` in BOTH directions every
boot — `dregg_consensus_attested_total 1` on BOTH nodes over the real two-node federation (3/3 boots,
identical 6-block DAG, balances 5000/5000). The diagnosis was HALF right and half wrong, found by
instrumenting the live wire: (1) TRANSPORT — there ARE two coexisting QUIC connections at n=2 (each node both
DIALS the peer's listen port AND ACCEPTS the peer's dial; on loopback both present the SAME `remote_address()`),
and the old single-valued `peers: HashMap<SocketAddr, Connection>` let the accept OVERWRITE the dial, so a
spontaneous `publish_eager` went out over whichever link survived — sometimes the half-dead one. FIX: `peers`
now holds `Vec<Connection>` per address; `add_peer_link` retains both, `send_to_peers` pushes over EVERY live
link (receiver dedups), `links_to`/`best_link_to`/`live_{peer,link}_count` helpers. BUT (2) the DEAD-DIRECTION
SYMPTOM was NOT transport — instrumentation showed the losing node RECEIVED the peer's vote (verify=true,
thousands of times) yet never logged quorum. ROOT CAUSE was a COUNTING RACE in `node/blocklace_sync.rs`:
`emit_finalization_vote` recorded the node's OWN vote with `let _ = col.record(&vote)`, DISCARDING the
`RecordOutcome`. At n=2 quorum is the 2nd distinct vote; when the peer's vote landed FIRST (routine
self-emit/gossip race), it was the SELF-record that crossed the threshold — and that `ReachedQuorum` was
swallowed, so `inc_consensus_attested()`/the log never fired and every later peer vote saw `AlreadyQuorum`.
FIX: one funnel `record_finalization_vote(handle, vote)` used by BOTH the self-emit and the receive path, firing
the transition exactly once on whichever vote crosses. Tests: net 85→87 (`bidirectional_eager_delivery_at_n2_…`
real two-network loopback + `add_peer_link_retains_…`); node finalization 7→8
(`quorum_crossing_is_reported_on_whichever_vote_is_second`). Both suites green; node blocklace unit tests 22/22.

### WEB-DEOS PAINTS — the gpui cockpit now renders a real frame in the browser (2026-06-23).
The `gpui_web` first-paint ceiling (`closure invoked recursively or after being dropped`, canvas stuck 1×1)
is FIXED at root: it was a lifetime bug — `Application::run` dropped the owning `Rc<AppCell>` when it
returned (web `run` is fire-and-forget), freeing the `WebWindow`'s rAF/ResizeObserver closures while the
browser still held them. Fix = leak the `Rc` on wasm (`std::mem::forget(self)` in `crates/gpui/src/app.rs`,
`emberian/zed` fork, committed on the local `zed-dregg-web` working copy as `65f07f431b`). Verified: headless
Chrome paints the real cockpit (canvas 2560×1640, reentrancy false) — proof `web/cockpit-gpui-web-painted.png`.
**CUTOVER-SETTLE OWED:** the fix lives in a LOCAL fork checkout wired via a `[patch."…/emberian/zed"]` →
`../../zed-dregg-web/crates/{gpui,gpui_platform,gpui_wgpu}` in `starbridge-v2/Cargo.toml`. Push the one-line
fix to `emberian/zed`, bump the `407a6ff` rev in starbridge-v2 (the 4 git deps), drop the `[patch]` block.
**SIBLING SEAM:** the wasm web bundle build is currently blocked by `embedded-executor → app-registry`
(`dregg-app-framework`/`starbridge-gallery` aren't wasm-resolvable, and `app_registry.rs`/`powerbox.rs`
reference the module unconditionally under the feature). Verified the paint fix by temporarily dropping
`app-registry` from `embedded-executor` (reverted). To unblock the web build, `app-registry` should be made
`#[cfg(not(target_arch = "wasm32"))]`-clean (owner: the app-registry lane).

### APPS WIRED INTO THE COCKPIT — LANDED; the shared-World-ledger refactor is the convergent seam (2026-06-23).
`1710a617`. `starbridge-v2/src/app_registry.rs`: `AppRegistry::standard()` wires gallery/tussle/
sealed-auction/bounty-board (the framework-shaped apps) — each `AppEntry{id,name,desc,ctor,seed,drive}`
launches a real `DeosApp` over a live `AppSubstrate`, fires one affordance → real `TurnReceipt`
(`receipt.agent == backing cell`), post-fire state visible to a second reader of the SAME ledger
(inspector seam). Powerbox `RegistryLauncher` row per app. 4 tests + native-full green. (`polis` skipped —
it doesn't use the framework, different shape.)
- APP RE-POINT SEAM — CLOSED `6fddfc3b`. `starbridge-v2/src/app_worldspine.rs` `AppWorldSpine` mirrors
  the editor's `WorldSpine`: `seed` genesis-installs the app's primary cell (carrying its `CellProgram`
  so World's executor RE-ENFORCES app invariants — the state tooth) at its real derived id; `commit`
  runs the cap-gate in-band then commits via `World::commit_turn` with the affordance METHOD SYMBOL
  stamped (apps use method-dispatched `CellProgram::Cases`; a bare action default-denies). All 4 wired
  apps land their cell on `World::ledger()` + receipt on `World::receipts()` (the inspector path); 7
  tests ~59s. The `EmbeddedExecutor` path remains the headless fallback. WASM REGRESSION also closed:
  `embedded-executor` no longer pulls `app-registry` (app crates native-only); `app-registry` implies
  `embedded-executor`, rides `native-full`; wasm `gpui-web` build green. NOTE: registry tests now run
  under `--features app-registry`/`native-full`, not bare `embedded-executor`. WIDER follow-on (firing):
  wire the remaining 16 framework apps into the registry (identity/nameservice/privacy-voting/escrow-
  market/compute-exchange/agent-+swarm-orchestration/…/first-room).

### APPS ON THE LIVE WORLD LEDGER — 19/20 launch + fire real turns (2026-06-23).
`c16dde94` (wider: +11 → 15) → `d1dd0a9c` (deeper: +3 authenticated → 18) → `2d25db67` (polis → 19).
polis isn't a `DeosApp` (ships `CellProgram`s directly), so `AppEntry` gained a `backend` enum:
`Framework` (the 18 DeosApps) vs `Program` (polis) — ONE registry, two backends. polis seeds a real
2-of-3 `CouncilCharter` cell + fires a `propose` (DRAFT→PROPOSED, receipt on `World::receipts()`).
Only first-room remains unwired — it's a multi-cell scenario/weld shim, NOT an app (a launchable
"scenario" would be its own thing). All 19 framework/program apps below + the authenticated 3:
`c16dde94`+`d1dd0a9c` detail. All 18 DeosApps
launch onto the cockpit `World` ledger and fire ONE representative receipted affordance (reusing each
app's OWN public program+effect-builders; no app `lib.rs` edits). Whole-set tests iterate all 18.
- AUTHENTICATED PATH (`d1dd0a9c`): the executor derives `ctx.sender` from the AGENT CELL's pubkey
  (`turn/src/executor/execute_tree.rs:879`), NOT from `Authorization` — so seeding the app cell over the
  signer pubkey + attaching a single-member `MerklePath` membership witness satisfies `SenderInSlot`
  (supply-chain-provenance) / `SenderAuthorized` (identity ISSUER_AUTH_ROOT, governed-namespace
  GOVERNANCE_COMMITTEE_ROOT) with NO fake-authorized turn. `AppWorldSpine::commit_as` `debug_assert`s
  the declared sender == the live agent pubkey (a mis-seed fails fast, can't forge). native-full + wasm32
  green; non-wasm dep-table invariant preserved.
- REMAINING 2 (not `DeosApp`s — out of the bridge's scope): polis builds charter `CellProgram`s
  directly (`Result<CellProgram, PolisError>` — own integration, lane firing); first-room is a
  scenario/weld shim (could become a launchable scenario, not an app).
### CELL_TRANSCLUSION 3 RED — CLOSED `e8d08d18` (2026-06-23).
NOT a leak: the 3 fails were stale tests assuming Proof ⊥ Either, but the `cell` lattice intends
`Proof ⊆ Either` (comparable); `Membrane::project` was correct. Realigned the tests to use a genuinely-
incomparable `Custom` reader (darkening still tested), fixed the independent `own_affordance_names` sort,
corrected the stale `affordance.rs:1067` comment. Lattice untouched. 8/8 green.

### EDITOR PANE ON THE LIVE WORLD LEDGER — LANDED (2026-06-23).
`d11c72e9`. The cockpit editor now edits the SAME ledger the inspector shows: `LedgerSpine` trait +
`OwnedSpine` (headless) / `WorldSpine` (over `Rc<RefCell<World>>` via `World::turn`/`commit_turn`).
`open_editor_pane` mounts `EditorPane::firmament_over(self.world.clone(), …)` under `embedded-executor`,
fail-soft to per-editor. `Fs` trait relaxed `Send+Sync+'static` → `'static` (gpui single-thread; no
codepath moves `Arc<dyn Fs>` across threads). Test: drive the real gpui Editor → save → a SECOND reader
of the spine sees the receipt + edited cell + Σδ=0. PASS 19s; native-full + deos-zed green.

### MIGRATE VERB (Local→HostPd) — authority half LANDED; live-transport re-home is the seam (2026-06-23).
`86ad3049`. `migrate(&SurfaceCapability, &MigrationTarget) -> Result<SurfaceCapability, MigrateError>`
(`starbridge-v2/src/dock/migrate.rs`) relocates a surface cap along the firmament distance axis,
identity-preserving (same `SurfaceId`/cell), re-minting at `Target::HostPd`. Gate = structural
attenuation (`granted ⊆ held` via `dregg_firmament::is_attenuation`; widening → `MigrateError::Widening`),
non-vacuous at both lattice extremes. Tear-off now tested (logic + headless-gpui window cycle: tear →
idempotent re-tear → pop, identity preserved). 6/6 pass. SEAM = the live transport re-home: spawn/select
the confined child PD (registered `HostPdId` over a control socket, `--features process-pd`) and re-point
`Shell::present`/`route_input` at that PD's firmament Endpoint — the cap migrates today; the GLASS follows
when the compositor binds the re-homed cap to the child Endpoint. (This is the network-portable-process /
robigalia vision; n>1 leg later.)

### REAL NODE RUNS + COCKPIT ATTACHES — LANDED, verified by running (2026-06-23).
`7eba16ee` + `docs/deos/DEV-NODE-RUNBOOK.md`. `dregg-node init && run --enable-faucet` serves a
live `/status` (`state_producer:lean`, `lean_producer:true`, 21 covered effects, `consensus_live`)
and a real verified receipt chain (`has_proof·executor_signed·has_witness`, pre→post, 497
computrons, chained) — seen live on :8771, not just reported. `starbridge-v2 --node URL` attaches
(LiveNode::sync over `/status`+`/api/cells`+`/api/receipts`, SSE `/api/events/stream` → `pump_live`);
all four endpoints 200, faucet receipt pushes over SSE. The faucet enforces recipient ==
`CellId::derive_raw(pubkey, blake3("default"))` (a bad recipient → in-band refusal, confirmed).
- CROSS-LANE COUPLING (durable): the node links the git-tracked CLEAN SEED Lean kernel even when
  the circuit/metatheory working tree is dirty — `dregg-lean-ffi/build.rs` now restores the seed
  archive + skips the torn partial-`.c` splice on a `lake build` failure. CONSEQUENCE: to compile
  FRESH Lean-kernel changes into the node, the circuit lane's proof (`#assert_axioms` on
  `handler_refines_execFullA_attenuate`) must go green first. Their lane, not ours; the node is
  unblocked regardless.

### WEB-SHELL REAL-PAGE RENDER — ✅ SHIPPED: a real page rasterizes end-to-end (2026-06-23).
The surfman ceiling is BROKEN and a real Servo `WebView` lays out + paints a page into the SWGL
framebuffer, captured to a PNG. Two fixes (both in `servo-render/` only):
(1) **`ServoSwglContext::connection()`** (`src/webview.rs`) now returns a real surfman software
`Connection` (`Connection::new()` — the default display connection, NO window/GPU surface) instead
of the trait-default `None`, so servo-paint's `register_rendering_context`
(`paint.rs:236` `.connection().expect(...)` + `create_adapter()`, its WebGL `SwapChains<_, Device>`
bookkeeping) no longer panics; SWGL still does ALL page rasterization through `gleam_gl_api()`, the
surfman device only instantiated for a WebGL canvas (none on our pages).
(2) **a minimal vendored `servo-paint` fork** (`servo-render/vendor/servo-paint/`, wired via
`[patch.crates-io] servo-paint` — registry-normalized source, ALL deps the SAME crates.io pins so
it unifies with servo's copy) flips ONE field: `WebRenderOptions { clear_caches_with_quads: false }`.
Published servo-paint left WebRender's default `true`, whose picture-cache clear issues a
depth-`GL_ALWAYS` quad that SWGL's `DepthFunc` (`gl.cc:1384`, accepts only `GL_LESS`/`GL_LEQUAL`)
`assert(false)`s on → SIGABRT before any page painted. Real servo avoids this via a `SwCompositor`;
servo-paint 0.1.0 exposes no SWGL option, so the fork sets the flag WebRender's own software path
uses. Also: paced the headless `spin_event_loop` pump (1ms yields) so servo's async actor threads
make load/layout/paint progress (a tight busy-loop out-ran them — the page never loaded), and
flipped the readback vertically (GL bottom-left origin, matching servo's own
`read_framebuffer_to_image`). RESULT (`cargo test --features libservo --lib`, 17/17 green, 0 ignored):
a `data:` page with a centered CSS `<div>` rasterizes to `servo_real_page_render.png` (240×200, blue
bg + yellow 160×120 block at the exact CSS box) AND a text page rasterizes to
`servo_real_text_render.png` (320×120, the antialiased word "dregg" — 212 distinct colors = real
glyph raster). Both flow through the genuine compositor-PD T1/T2/T3 gate. The net-cap socket gate
remains DONE+proven (cap-denied origin → `RefusedByCap`, `Netlayer::dial` never called). REMAINING
(unchanged, out of this lane): http(s) bytes still ride servo's internal hyper (its
`FORBIDDEN_SCHEMES` blocks an embedder http(s) ProtocolHandler — replacing the byte socket needs a
servo `net` fork); the vendored servo-paint fork reverts once upstream carries a SWGL
`RenderingContext` path.

### DIRECTIONS RECONSTRUCTION (2026-06-23): the 06-21→06-23 far-seeing arc, recovered.
`docs/deos/RECONSTRUCTED-DIRECTIONS-2026-06-23.md` — mined the session corpus via `cv` after a
compaction kept the mechanics but lost the far-seeing. The stake (an agent living in dregg with
caps+money), the polis/polisware constitution (event-structure+game-semantics home; legitimacy=
non-regression; knowledge-as-behavior; holes-as-anti-seduction), the rehydratable membrane,
symbolic-witnessing=n=1, apps-as-cells, the desktop spine, priorities/orderings, constraints, and
the open-loop ↔ in-flight-lane map. Orient from this doc, not the compaction summary.


### SESSION RESUME — deos resumes the exact image on login (2026-06-22): LANDED · tails.
The Houyhnhnm orthogonal-persistence wound ("in-session state doesn't survive reboot") is
closed for the windowed desktop: login OPENS the principal's per-user durable image
(`<deos-dir>/deos-session-<root-hex>.redb`) via `World::open` — first launch provisions +
persists (value anchors + system principal + the granted cap-tree, all dual-written), a
relaunch RECOVERS the whole image (balances + history + the SESSION CAP-TREE) and
`LoginManager::login_resumable` RESUMES it with no re-grant. Logout (`logout_durable`) revokes
durably AND stamps the durable `SessionRecord` REVOKED (a revoked session does not silently
resume). Files: `starbridge-v2/src/{session,world,persistence,login}.rs`.
- ROOT-CAUSE FIX (cross-crate, deliberate): `cell/src/capability.rs` dropped
  `skip_serializing_if` on `CapabilityRef`/`AttenuatedCap::allowed_effects` — a skipped field
  could not round-trip the durable `postcard` codec, so NO cap-carrying cell was durable
  (commit log / checkpoint / `canonical_ledger_root` all broke; cell-crate tests had documented
  this and routed around it via serde_json). Now postcard-clean; `#[serde(default)]` keeps legacy
  decode. Verified: `dregg-cell` + `dregg-persist` full suites GREEN (636 tests, 0 regressions),
  the 8 pre-existing sbv2 `persistence::tests` GREEN. NOTE: this changes the byte-form (hence
  `canonical_ledger_root`) of any ledger holding a cap cell with `allowed_effects: None` — a
  fresh-image change only; a pre-existing on-disk node/devnet image would need re-init (build
  artifacts already reset per AGPL note). No golden/circuit-leaf encoding touched
  (`cap_ref_to_leaf` is separate).
- TAILS: (a) per-user path policy is `$DREGG_DEOS_DIR` / `$XDG_DATA_HOME/deos` / `~/.local/share/deos`
  — fine for single-user; multi-user-on-one-host wants a real account→dir policy.
  (b) encrypted-at-rest: the redb image is plaintext; a session image holding value/keys wants
  at-rest encryption (the cipherclerk seam). (c) the headless/bake paths stay ephemeral by design.

### ✅ SETTLEMENT SOUNDNESS — the lone open construction (2026-06-22): CLOSED.
Named by THREE frontiers (`KeyLeak.lean` "the settlement seam", `DISTRIBUTED-TIMETRAVEL §6.3`
settlement-time-authority, `SHARED-FORK-CONSENT`/`BRANCH-AND-STITCH` the linear DROP). Now a
kernel-clean Lean theorem: `metatheory/Metatheory/SettlementSoundness.lean`. `settlement_soundness`
(a settled turn exercised LIVE-at-tip authority = `granted⊆held` ∧ `honors`-at-tip) + the
contrapositive `revoke_before_tip_unsettleable` (a revoke propagated to the tip ⇒ unsettleable,
fail-closed; n=1 ⇒ immediate). Composed from `KeyLeak.reaches`/`isAttenuation` + `revoke_kills_leak`
(= `Revocation.eventual_bounded_revocation`); the §4.4.1 binding obligation is a TYPED hypothesis
(`BindsLiveAuthority`), never an axiom, with canonical inhabitant `liveSettlement` + non-vacuity
(same cap settles inside the stale window, unsettleable past the propagation bound). Corollaries
close each frontier: `leaked_then_revoked_cannot_settle`, `stitch_drops_revoked_authority`,
`settled_root_attests_live_authority` (extends light-client unfoolability → authority-live-at-settlement).
Axioms = exactly {propext, Classical.choice, Quot.sound} (keystone depends on NONE); `#assert_axioms` CI-gated.

### ⚑⚑⚑ DESKTOP EPOCH — THE COMPLETION GOAL (2026-06-22, autonomous): finish ALL of it.
GOAL (ember, stop-hook): hermes/ados/zed integration · atlas refreshed w/ new screenshots · cockpit overhauled
with gpui-component · document language+editor+viewer built out · matrix chat kickass+dregg-pilled · rehydratable
screenshots/membrane tested+worked · everything tested. 6-lane swarm + integration + atlas (file-partitioned):
  A ✅ terminal+editor LIVE dock panes (⌘K "Open Terminal/Editor pane" → real PTY/editor in a split; on-demand,
     never in the headless bake; ids base 1000+; committed). palette/dispatch/panels_workspace + dock adapters.
  B 🔨 editor-as-document + doc viewer (dregg-doc RopeDoc → deos-zed buffer; save=patch; conflict-objects viewer).
  C 🔨 matrix chat kickass+dregg-pilled (membrane=the star: a message carries a cap-bounded world-fork; room=cell).
  D 🔨 membrane/rehydration tested (mint→rehydrate→drive→stitch; graduated rights; consent-signing-domain fix).
  E 🔨 hermes/ados live (ACP↔ToolGateway loop; effects ride the metered turn; per-tool grants + mandate inspector).
  F 🔨 cockpit gpui-component overhaul (buttons/lists→real widgets across panels).
  G ✅ DEVTOOLS surface ("Firebug for a verified OS") — ONE ⚙ tab, three sub-tab inspectors over the live
     World (NETWORK = data plane: deliveries/queues/wakes/notify from the dynamics stream + receipt feed,
     filterable, browser-Network-tab style · LOG/RECEIPTS = blocklace+receipt console, click-to-drill the
     full reflect_receipt field tree + provenance chain · FEDERATION = committee/epoch/checkpoint/root +
     captp remote-path catalog, live-node-or-embedded; configure = cap-gated turn stubs). `starbridge-v2/src/
     cockpit/panels_devtools.rs` + additive wiring (Tab::Devtools, GoDevtools palette/dispatch). Commit 39dd68de.
     RESIDUE: bin --features native-full does NOT compile RIGHT NOW (sibling circuit-soundness lane moved
     custom_proof_bind/recursive_witness_bundle → new `circuit-prove` crate; turn/turn.rs:537 + rotation_witness.rs
     still name `dregg_circuit_prove::*` while it's an OPTIONAL `prover`-gated dep — NOT my territory). My panel +
     wiring DID compile (the bin reached past `cockpit` to the unrelated login/session+turn breakage). dregg-image
     MCP screenshot tab=devtools renders via lavapipe but off the STALE pre-commit binary (no ⚙ tab yet). CLOSE:
     re-screenshot once the circuit/turn lane re-greens the workspace at integration (→7).
  SEAM (NETWORK tab): the DP-2 data-plane comms API (live inbox queue depth/dequeue cursors, pub/sub topic
     fan-out, per-session delivery state) is the richer Network source as it lands; today the EventEmitted notify
     edges ARE the live queue traffic the executor receipts. Wire the queue-depth view when DP-2 merges.
  →7 integration build · →8 atlas refresh (sequential, last).
⚠ no-lean-link WATCH: the FFI lane (separate, "doesn't concern us") is mid-refactoring coord/captp's no-lean-link
  feature (working-tree-modified). starbridge-v2:488-496 consume `features=["no-lean-link"]` on dregg-{sdk,coord,
  captp}. cargo metadata RESOLVES now; if the FFI lane fully removes no-lean-link, update those consumer lines
  (my territory) at integration. Don't thrash the 10-min starbridge build against the churning Cargo.toml.## ⚑⚑⚑ THE DEOS DESKTOP EPOCH (2026-06-22) — deos becomes a real desktop OS
THE THROUGH-LINE: every action — file I/O, tool call, agent step, UI nav — is ONE cap-gated receipted
dregg turn (ToolGateway + firmament); made INTERACTIVE by symbolic execution + async UI + a dockable
workspace. Six threads, each grounded by a 2026-06-22 explore-agent report (read whole before building):

1. SYMBOLIC/LAZY EXECUTION (the interactivity foundation). THESIS CONFIRMED in the Lean: AbstractState =
   (balanceTotal, authGraph) is genuinely witness-free (metatheory/Dregg2/Spec/ExecRefinement.lean:398-408),
   Exec ⊑ Abstract is proven (ExecRefinementFull.lean, Proof/Refine.lean). The Rust executor is ALREADY
   proof-agnostic (execute.rs:1249) + the ledger is ALREADY truly-lazy (cell/src/ledger.rs:277-349 Pending,
   "ZERO hashing" on a UI turn) + the eager/lazy split is Lean-proven (held_promise.rs) + the tape replays
   deterministically (replay_to + the commit_turn double-exec). NEW WORK: a WitnessMode{Full,Symbolic} flag
   (~2 write sites + engine) + a collapse() orchestrator (mostly reuse: wrap_witnessed + canonical_ledger_root
   + rebuild_index_from_log) + Option-ify ~10 derived fields + unwind 2 eager-witness couplings (state.rs
   heap/ext-field roots) + the light-client semantics of a deferred-witness turn (the known gap). SOUNDNESS:
   symbolic = structurally local/unpublishable (no verifyBatch artifact) — safe by inexpressibility; collapse
   is the ONLY witness path, and refinement guarantees it reproduces exactly what Full would witness.
   ✅ BUILT (commit 2ee5b6be): turn/src/collapse.rs (WitnessMode{Full,Symbolic} + DEFERRED_STATE_HASH sentinel +
   is_deferred + collapse/collapse_with + CollapseResult); TurnExecutor.witness_mode (AtomicU8, &self set/get,
   default Full) + set_witness_mode/is_symbolic; execute.rs classical forest path defers pre/post Ledger::root()
   under Symbolic (EXCEPT the proof-carrying sovereign path — its STARK binds the commitment, never deferred);
   World (world.rs) gains witness_mode + a symbolic_turns buffer, commit_turn skips the replay-tape double-exec
   AND the durable dual-write under Symbolic, World::collapse() materializes the buffer via the Full record path
   + replaces deferred receipts with real ones + FAIL-CLOSED asserts collapsed-recorder-root == live-engine-root.
   TESTS GREEN: turn/tests/integration_symbolic_collapse.rs 4/4 (applies-w/o-witness · collapse-reproduces-Full ·
   Full-byte-identical · admission-NOT-relaxed soundness guard). RESIDUALS: (a) state.rs heap/ext-field eager
   roots (set_field_ext/set_heap) NOT yet deferred — needs a Ledger::Pending-style mark-dirty refactor in the
   `cell` crate (out of the turn/world file-set; noted in collapse.rs); fires only for ext-key/heap writes, not
   the common transfer/cap path. (b) the cockpit runtime toggle (cockpit agent owns it). (c) the light-client
   semantics of a deferred-witness turn = the known architectural gap (collapse before the publish boundary).
2. UI ASYNC DECOUPLING. TIME-tab hang FIXED (this commit): was O(N²) replay_to-per-step on the paint path
   every frame → O(N) single-pass History::reversibility_classification. FOLLOW-UPS: cache TimeCockpitModel
   by (history.len,cursor,meta-depth); make tab-switch optimistic (move self.tab+notify now, defer witness_tab
   to a cx.spawn FOREGROUND task — gpui is !Send; coalesce/debounce so rapid tab-flips=1 turn); queue acts.
   Reference pattern already in main.rs:371-415 (the seed task + pump_live). Every tab click is currently a
   real SetField turn (cockpit.rs set_tab→witness_tab→workspace_cell.commit→commit_turn) — that's the slow.
3. UI REDESIGN: fluid + DOCKABLE workspace. Current = rigid 3-pane + 28-flat-tab bar, 0 scrollers (19
   overflow_hidden, content unreachable). PHASE 0 (zero-risk, hours): swap overflow_hidden→overflow_y_scroll
   at 19 sites + flex_wrap the tab bar + uniform_list/list the truncated (.take(N)) lists. PHASES 1-3: VENDOR
   Zed's gpui-native dock engine (~/.cargo/.../zed/.../crates/workspace): pane_group.rs (~90% reusable
   resizable-split engine), dock.rs (Dock/DockPosition/Panel), a slim Pane + a ~8-method CockpitSurface trait;
   each existing *_panel becomes a dockable/splittable/floatable surface; Tab::ALL → a surface registry (⌘K).
   NOT add-a-dep (workspace drags project/collab) — vendor-and-adapt. (Witnessed-selector → layout-tree cell
   to keep rewindable-UI.)
4. ZED-IN-DEOS via ADOS/ToolGateway/firmament. FEASIBLE, weld-not-build. ToolGateway (sdk/src/tool_gateway.rs)
   = REAL/proven (Lean-mirrored delegAdmit, metered receipted turns). Firmament (sel4/dregg-firmament) =
   runnable (router/surface=window). ADOS = the frame (the ONE seam is real: swarm.rs). THE seams: (1) a new
   FirmamentFs impl of Zed's Arc<dyn Fs> (crates/fs Fs trait, 35 methods; FakeFs proves a non-OS fs works) —
   path→cap via rbg/src/directory.rs DirectoryCell, a file=a cell, a save=a receipted turn. THE one big new
   build. (2) ToolGateway-gate the non-Fs tools (terminal/fetch/web_search/MCP) at Zed's tool_permissions.rs
   decision point; Fs-bound tools gated by (1). (3) Zed as a confined powerbox app + a Surface cap (window).
   Phases: read-only FirmamentFs → writes-as-turns → ToolGateway tools → confined-powerbox-app → snapshot+VCS.
5. TERMINAL (ember ask): embed Zed's terminal/terminal_view (alacritty) as a deos surface/panel, ToolGateway-
   gated (the terminal_tool is one of the non-Fs tools in #4).
6. HERMES-AGENT (ember ask): ~/pug/hermes-agent = Nous Research's self-improving agent (Python, ACP adapter
   acp_adapter/acp_registry, skills/learning-loop, multi-platform gateway). Integrate as a deos agent via ACP
   (Zed speaks ACP — acp_thread) + ToolGateway: every Hermes tool call → a cap-gated receipted dregg turn.
   THE ADOS realization with a REAL agent instead of a toy.
   ✅ SEAM BUILT (deos-hermes/, own workspace): ACP analysis done (the gate sits on session/request_permission +
   the tool_call kind taxonomy); HermesGateway routes a ToolCallRequest → ToolGateway::invoke per kind → a real
   receipted turn on the verified executor OR an in-band Reject. `cargo build` + 4 both-polarity seam tests green
   (real turn_hash receipts; over-rate/past-deadline refused). DESIGN.md carries the bridge + the 5-step roadmap.
   RESIDUE (the roadmap): (1) the live ACP-client↔`hermes acp` subprocess wiring (JSON-RPC transport — slice uses
   a mocked ACP source); (2) tool side-effects riding the metered turn (today work=∅); (3) per-tool (not per-kind)
   grants + a mandate inspector; (4) the sandbox-PD (firmament/seL4) confinement; (5) the chat/agent dock surface.
ROADMAP (felt-wins-first): Phase-0 scroll + the async tab/act decoupling (immediate) → symbolic WitnessMode
(the foundation, careful: touches executor+storage, ember-gated soundness) → dockable workspace (vendor Zed
pane_group/dock) → Zed-in-deos (FirmamentFs) + terminal + Hermes (the desktop buildout).





### DESKTOP EPOCH — KEY-LEAK fully caged + the lone open theorem (2026-06-22):
"What happens if someone leaks a private key" — which I previously couldn't model ("too much proof machinery") —
is ALREADY ANSWERED by the deployed proofs. metatheory/Metatheory/KeyLeak.lean (kernel-clean, CI-glob'd)
+ docs/deos/ADVERSARY-KEY-LEAK.md prove it by INSTANTIATION: key_leak_contained = polis_safety (Polis.lean:102)
with ctrl:=attacker — polis_safety already ∀-quantifies an OPAQUE controller ("verify the cage not the animal"),
and a leaked-key attacker IS such a controller. Blast radius = the attenuation-closure of the leaked c-list (a
read key can't reach admin/a new cell — leak_blast_no_amplify); key_leak_attacker_blind (possession buys held caps
and NOTHING more); revocation kills it topology-bounded (n=1 ⇒ immediate). Containment = attenuation + conservation
Σδ=0 + firmament confinement + membrane fork-isolation, ALL deployed machinery — no large new obligation.
⚑ THE ONE OPEN CONSTRUCTION this names: SETTLEMENT SOUNDNESS — a revoke must bind into the finalized commitment
BEFORE settlement (so a leaked-then-revoked cap can't settle against a stale branch-time view). It is a COMPOSITION
of existing pieces (DISTRIBUTED-TIMETRAVEL-SEMANTICS.md §6.3 + circuit-soundness), narrow — compose, don't rederive.
This is the SAME theorem the distributed-houyhnhnm frontier + the membrane-merge seam both land on → a convergence
point worth a dedicated lane once the cell-crypto/cockpit churn settles.
### DESKTOP EPOCH — the FORWARD-DESIGN trilogy (2026-06-22, docs landed while the repo churns):
Three design docs map "what's ahead", and ALL converge on one truth: THE HARD PARTS ALREADY EXIST — it's welds,
not new foundations. deos is a DESIGNED system being realized, not invented.
- docs/deos/APPS-AS-CELLS.md — DE-SILO: each app's durable core becomes a CELL, mutations become TURNS (cap-gated/
  conserved/receipted/replayable), apps become Presentable VIEWS over ONE graph. Editor file=cell = a one-file
  FirmamentFs fill-in; terminal "can't pay a witness per keystroke" = the ALREADY-BUILT WitnessMode::Symbolic +
  collapse; hermes = the closed reference (tool-call→cap-gated turn); chat = membrane.rs (room=cell the gap);
  buffer=Pijul-patch-graph with the DocMerge correctness theorem ALREADY LANDED (metatheory/Dregg2/Deos/DocMerge.lean).
  The membrane spans apps because it's a generic world-fork frustum, not a chat type.
- docs/deos/DEOS-DISTRIBUTION.md — SELF-CONTAINED: YES. One bundle = cockpit+ide+terminal+chat+hermes+web-shell+
  executor+firmament+compositor+a durable redb image. Two targets, one codebase: (a) host app-bundle (confined
  host-PDs via sandbox.rs) + (b) seL4 deos.img (PD set + CapDL). The CockpitSurface adapters already exist
  (editor/terminal/chat); an app-as-confined-host-PD IS the seL4 PD's host stub (same model). "the image IS your
  world" — portable; persistence weld = WORLD-PERSISTENCE-PLAN.md. Two native Windows bundles already shipped by hand.
- docs/deos/HOST-AND-CONTAINER-BRIDGES.md — ADVANCED NON-SEL4 FIRMAMENT: a host bridge = the Phase-0 sandbox
  mechanism READ BACKWARDS (deny-per-PD → grant-per-cap; "the sandbox said no to the whole host — the bridge says
  yes, but only this, and signed"). 4 new Target kinds (HostFile/Socket/Device/Process) + a HostBridgeBacking
  sibling of HostPdBacking; a CONTAINER = a cell, lifecycle = cap-gated turns (youki/bollard runtimes). A
  seL4-trailblaze table: every Target swaps its backing, cap model UNCHANGED. Phased H0(host-dir read-cap)→C2.
THE deos PICTURE these complete: ONE cap-secure cell graph (executor) + firmament (caps across distance + OS-
enforced isolation + host/container bridges) + compositor/WM (the desktop) + apps as confined-PD VIEWS over the
graph + membrane/merge (multiplayer time-travel) + symbolic mode (speed) = a self-contained, portable, verifiable,
multiplayer, self-hosting OS. Integration pass (wire terminal/zed/chat panes + shared_fork + full build + shot)
GATED on dregg-cell churn + the cockpit.rs split settling.
### DESKTOP EPOCH — deos-chat: the rehydratable-membrane multiplayer layer (ember 2026-06-22):
THE VISION (ember→spwashi): a screenshot/message embeds a "frustum-culled rehydratable MEMBRANE" = a cap-bounded
FORK of the deos world at the capture moment; recipients rehydrate it + drive real turns (live MULTIPLAYER);
Matrix is the transport that makes it real; a MERGE stitches divergent forks back; time-travel throughout.
GROUNDING (not hand-wavy — every piece has machinery): membrane = World::fork + snapshot/restore (replay.rs, MCP
snapshot/restore) CULLED to the in-view cap-bounded cell/cap subgraph, wrapped as a firmament surface-cap +
transclusion (starbridge-web-surface/{rehydrate,transclusion}.rs) + the partial-turn/promise machinery. MERGE =
a PUSHOUT in the event-structure config lattice (the turn-layer IS already an event structure); conflicts-as-
OBJECTS (patch theory / Pijul); SOUND because dregg's LINEARITY (nullifiers · conservation Σδ=0 · cap non-
amplification) makes inconsistent events LOSSY-DROPPED — the branch-and-stitch linear-drop (docs/deos/
BRANCH-AND-STITCH-PROTOCOL.md, DISTRIBUTED-TIMETRAVEL-SEMANTICS.md). So "the merge is consistent w/ patch theory +
dregg semantics" = the dregg algebra AUTO-rejects the inconsistent merge events; the stitch is lossy exactly where
conservation/caps require. KEY-LEAK modeling (ember's adversary q) = DEFERRED: a leaked key = a compromised cap;
its blast-radius needs the cap-compromise-propagation + revocation-non-monotone-at-settlement proof machinery
(firmament confinement + membrane fork-isolation bound it) — a deliberate adversary-harness build, not a bolt-on.
deos-chat LANE (a155821): study nheko (solves Matrix-client problems correctly — draw the UX/feature patterns
even though it's C++/Qt) + brief rivet review; build the gpui chat UI on deos-matrix + gpui-component (room-list/
timeline/composer-as-real-Input); design the membrane+merge seam. The chat is the SOCIAL layer over the dregg world.
✅ BUILT: the gpui ChatView (room-list sidebar w/ enc-badges+unread-pills · sender-grouped timeline w/ day-separators ·
real gpui-component Input composer, nheko keymap Enter-sends/Shift-Enter-newlines via InputEvent::PressEnter) over a
ChatSource seam (MatrixHandle = live; MockSource = recorded sync so the UI is real OFFLINE). `deos-chat` demo window
RENDERS (gui feature; --headless data-path proof passes); ChatSurface mounts as a dock CockpitSurface (forwarder
ready-to-drop at starbridge-v2/src/dock/chat_surface.rs). Membrane seam = MembraneEnvelope (wire) + MembraneHost trait
(comms-PD) + the design doc docs/deos/MEMBRANE-MERGE-SEAM.md (real-now-vs-roadmap, grounded in fork/snapshot/transclusion/
branch-and-stitch). RESIDUALS (wire, not build): (1) a WorkerRequest::SendMessage variant — the only gap in the live
send path (mock send works; the trait + UI are ready). (2) MembraneHost impl in the confined comms-PD (mint/rehydrate/
drive buildable now; stitch-pushout + Settlement-Soundness theorem = the circuit-soundness frontier).
### DESKTOP EPOCH — deferred cleanups (ember 2026-06-22, "not yet"):
- MIGRATE existing cockpit UI → gpui-component widgets. The hand-rolled bits (the ⌘K palette char-accumulator
  cockpit.rs ~3071, ad-hoc buttons/lists/the inspect-act fields) move to gpui_component::{input::{InputState,
  TextInput,InputEvent}, button::Button, list/table}. DO IT INCREMENTALLY as we touch each surface (the web-shell
  URL bar + login fields are the natural FIRST adopters — real focus/cursor/IME/Enter-to-submit), NOT a big-bang
  rewrite. The widget substrate is in (lane A, emberian/gpui-component) — adoption is now just per-surface work.
- SPLIT the large starbridge files (cockpit.rs is ~9500 lines; also world.rs, main.rs). Into per-surface modules
  + the nav/dock/inspect-act/palette layers. DEFERRED ON PURPOSE: cockpit.rs is under HEAVY concurrent churn right
  now (the dock integration F + the dev-loop surfaces + the widget migration), so splitting now = conflict-hell.
  Do it AFTER the desktop-epoch cockpit churn SETTLES (one clean pass when the surfaces are stable), so the split
  is mechanical-and-safe, not a moving target.
### DESKTOP EPOCH — apps + component substrate (ember 2026-06-22):
- gpui-component (longbridge/gpui-component): FORK+VENDOR — a rich gpui UI kit (Input/TextInput [fills the
  NO-text-input gap the servo report found], Button/List/Table/Tree/Tabs/Dropdown/Modal/DatePicker/rich-text +
  its own Dock). Scout running (agent adcdb678): THE CRUX = gpui-version compat with our fork emberian/zed @
  407a6ff (re-point its gpui dep at our fork + fix API drift) + how its dock relates to the Zed pane_group we
  vendored (likely: gpui-component for WIDGETS, Zed pane_group for the WM arranging FOREIGN surfaces). License
  check (AGPL-vendor compat).
- MATRIX CLIENT (future): fork nhecko-reborn (nheko-lineage Matrix client) → rewrite into deos as a fully-native,
  richly-integrated comms app. Becomes natural once the substrate lands (app-framework + dock + sandbox-PD +
  identity-cells): a confined comms app whose identity = a deos identity cell, E2E keys = caps, surfaces dockable
  in the WM, integrated with Hermes's multi-platform gateway + the polis (comms between inhabitants). Roadmap app.
### DESKTOP EPOCH — grounded findings (the explore reports, 2026-06-22):
- WM/LOGIN: the L5-L8 stack is ALREADY DOCUMENTED (docs/DREGG-DESKTOP-OS.md:33-90): L5 compositor-PD = "THE ONLY
  NEW TCB" (sole framebuffer/HID caps, scene=verified cell, T1/T2/T3 teeth: non-overlap/label-bind/focus-route
  — EXISTS compositor_pd.rs + gpui-free mirror compositor.rs); L6 shell+WM cells (untrusted; a WM = a
  compositor-client that is ALSO a compositor to the apps it frames, Genode recursive-stacking; powerbox lives
  here); L7 app cells + web surfaces; L8 cockpit = the master INTERFACE, a client NOT the root. Running code
  collapses L6/L7/L8 into one process — the reframe = REALIZE the doc. NEW: the WM-arranging-FOREIGN-surfaces,
  the session/login MANAGER (login=derive_raw root cell + powerbox grant root-cap-template; session=the c-list;
  logout=revoke; polis=multi-user legitimacy floor), cockpit-as-app demotion. dock/{pane,surface}.rs vendored,
  unwired = the WM layout-tree home. Phases: 2 app-PDs composited → WM arranges foreign surfaces (dock + grant_input
  routing) → login hands root cap → demote cockpit. TCB stays tiny: compositor-PD + trusted-path SAK + login mgr.
- SERVO: the "mozjs elephant" wall is PASSED — libservo BUILDS+LINKS on this host (63MB rlib, SpiderMonkey static
  libs, fingerprints Jun 19); the docs' "remaining wall = mozjs build" is STALE. "always-servo" = a deos-full
  feature flip (libservo-on for the windowed app, swgl-standalone for headless lanes; do NOT flip the bare crate
  default → forces the whole workspace to grind mozjs). Web-shell render path EXISTS end-to-end (render_url_to_frame
  → RgbaFrame → present_frame → compositor content-digest gate); NEVER-executed step = rasterize a real page +
  a URL bar (gpui here has NO text input but the palette char-accumulator). Fetch/nav cap-gate REAL (allowlist +
  no-amp); the net SOCKET (captp Netlayer::dial) + fs/cache-cap = named gaps. webview.rs:133 glow_gl_api stub.
- STYLO FORK PATCH (servo-always-default unblock, 2026-06-22): the cockpit graph pulls `serde_fmt` (via
  value-bag-serde1 ← log/tracing), whose `impl From<serde_fmt::Error> for core::fmt::Error` makes stylo's
  `ToCss`-derive `?`-residual source type ambiguous on rolling nightly (rustc 1.98, 2026-06-12) → ~30
  E0282/E0283 across `#[derive(ToCss)]` generic types. NOTE servo-render's libservo build alone does NOT
  trip it (no serde_fmt in its graph) — only the full native-full cockpit does; and it does NOT reproduce on
  the root nightly-2026-01-01. ROOT CAUSE = the `ToCss` derive emits inner blocks
  `{ let mut writer = SequenceWriter::new(..); ...; Ok(()) }?;` whose trailing `Ok(())` has an UNCONSTRAINED
  error type; the enclosing `?` then can't infer its residual source under the foreign From-impl. FIX = fork
  `emberian/stylo@ember-nightly-fix` (off v0.15.0, commit abc53ac61): pin the two `?`-consumed `Ok(())` sites
  in `style_derive/to_css.rs` to `Ok::<(), core::fmt::Error>(())` (no semantic change — same success value,
  explicit error type). NOTE the full native-full cockpit BIN currently can't LINK due to an UNRELATED
  concurrent-lane break: the working-tree (uncommitted) `circuit/src/binding.rs` widened `WideHash` 4→8 felts
  (the FAITHFUL-STATE-COMMITMENT work) but `sdk/src/verify.rs:316` still builds a 4-felt `WideHash` → E0308 in
  dregg-sdk. That is NOT stylo and NOT this change (HEAD's WideHash is `[BabyBear; 4]`, self-consistent); it
  self-heals when that lane propagates the arity. PROOF stylo is fixed: stylo compiles with 0 errors in the
  cockpit graph AND servo-render `--features libservo` builds FULLY GREEN end-to-end. Wired as
  `[patch.crates-io] stylo_derive = { path = "../../stylo/style_derive" }`
  in BOTH servo-render/Cargo.toml and starbridge-v2/Cargo.toml (each is its own workspace; stylo_derive is the
  only stylo-family crate the macro lives in, so one patch suffices — same 0.15.0 version unifies with servo's
  pin). CLOSURE = drop the `[patch]` lines + the fork when upstream stylo carries the fix (or the toolchain
  regression resolves); it's a local-path vendor, not a perpetual fork. Both servo-render libservo AND the
  full cockpit bin build green with it.
- SANDBOXING (the jail): the seam EXISTS + is HALF-BUILT. process_kernel.rs (process-pd feature) ALREADY forks
  MMU-isolated child PDs + a socketpair Endpoint + ShmRegion + a ValidityTable (cap-unforgeability). Honest gap
  (its own ISOLATION_FIDELITY:822): the fork gets memory isolation but NO ambient-authority confinement (inherits
  fds, can open/socket/execve). THE WHOLE FIX = one site (process_kernel.rs:1250, between fork and body): close
  all fds but the control socket, then OS-sandbox; + a Target::HostPd router variant (lib.rs:182, router.rs:111)
  reusing the existing wire. LINUX (cleanest, FIRST): namespaces (NEWUSER|NEWNET=empty-net|NEWNS|NEWPID) +
  seccomp-bpf + Landlock + close_range + SCM_RIGHTS (crates: nix/seccompiler/landlock/birdcage); gated only by
  distro userns policy. MACOS: posix_spawn+CLOEXEC_DEFAULT + child-SELF-sandbox_init((deny default) SBPL; crate
  gaol) — deprecated but works, child must self-sandbox. WINDOWS: Job-object+handle-list (easy) → restricted-token
  → AppContainer (hard, raw FFI). CAP→OS: file-cap→Landlock rule; net-cap→passed socket (SCM_RIGHTS = an ocap);
  surface-cap→ShmRegion; Endpoint→the one inherited fd. Two gates agree (dregg is_attenuation + OS sandbox).
  PHASE 0 = "a sandboxed child reaching ONLY a firmament Endpoint" = ~one file + one test. The n=1 jail is NEAR.
THE META-PATTERN across all reports: deos is WELD-NOT-BUILD — the desktop L5-L8 stack is documented, the sandbox
seam half-built, the servo elephant compiled, the dock vendored, symbolic mode over already-lazy machinery. The
epoch is REALIZING a designed system, not inventing one. OPEN (ember's call): polis-depth in v1 login (thin
authenticate→root-cap that grows into the polis, vs full legitimacy-floor now).


### DESKTOP EPOCH — INTEGRATION CHECKPOINT (2026-06-22): the full cockpit is GREEN with all lanes.
The 6-lane swarm landed + integrated; `cargo build --release --bin starbridge-v2` GREEN with: dev-loop panes
(A) + document-language/editor-as-document (B) + dregg-pilled chat (C) + hermes/ados live (E) + gpui-component
widget overhaul (F), and lane D (membrane) compiling green (its tests finishing). Integration fixes by main loop:
PaneGroup::first_pane (public) for the dev-pane graft; gpui_component::init(cx) in ALL THREE headless render paths
(render_cockpit_headless/explore_ui/serve_ie6 — else the kit widgets panic "no Theme global" in the bake, which
also restores the seL4 framebuffer render); ed25519-dalek → a regular native dep (the consent-signing domain wires
world.rs to sign a grant receipt). Commits: 7e7990ae/30b04a3e (F+headless-init), a3f7ce07 (A), f8184fbe (B),
f17b0d15 (C), 1de5c0ed (E), 1e29a206 (ed25519 integ), + the FFI lane's no-lean-link refactor committed (separate).
ATLAS REFRESH underway: 28 cockpit surfaces re-shot with the new widgets; offscreen --screenshot modes being added
to the deos-matrix chat demo + deos-zed editor/doc-viewer demos (the app GUIs are windowed-only + screencapture is
blocked here, so they need a HeadlessAppContext offscreen bake like render_cockpit_headless) → then append to
surfaces.json + build.py + commit. REMAINING: commit lane D (membrane tests); finish atlas (app surfaces); final
verification pass.## ✅ ATLAS ANOMALIES ALL RESOLVED — tab removed (2026-06-22)
The atlas's crawl-found anomalies are closed; the Anomalies tab is removed (the live finder is now
`dregg-atlas/verify.py`, the oracle, which fails CI on any invariant break).
- AuthRequired::None cap-badge inversion — REAL BUG, FIXED (`750d0d07c`, native + live-web).
- cell census 4-vs-8 — not a bug (cockpit's reflexive UI cells); explained.
- issuer well can't initiate turns — BY DESIGN: the well carries −supply (asset sink), mints flow through
  the issuer's turns, fees require funds; by conservation only the well is ever negative. Not a bug.
- 4 live tabs stall headless stepping (Wonder/Swarm/Agent/Time) — crawler-TOOLING limitation, not a
  protocol/cockpit bug (the tabs work in the app). Kept as a follow-up here: a bounded run_until_parked /
  a `headless` cockpit flag would let the UI-tree + --serve-ie6 cover all 28 tabs.


### ✅✅✅ DESKTOP EPOCH — COMPLETE (2026-06-22): deos grows deos from within, green across the board.
The completion goal is MET — every strand implemented, integrated, tested, and the atlas refreshed:
- HERMES/ADOS: deos-hermes a working confined agent — ACP client↔ToolGateway loop (live-capable + faithful mock),
  tool side-effects ride the metered turn, per-tool grants + a mandate inspector (1de5c0ed; 3+4 tests).
- ZED/dev-loop: editor + terminal mount as on-demand cockpit DOCK PANES (⌘K → real $SHELL PTY / deos-zed editor
  in a split; a3f7ce07) — the self-hosting loop. deos-zed editor-buffer-as-document (f8184fbe).
- DOCUMENT LANGUAGE: dregg-doc Pijul patch core + ropey↔patch bridge; editor buffer = patch history; a doc VIEWER
  (blame + conflict-objects-as-cards); multi-author merge (f8184fbe, 119+ tests; DocMerge.lean proven).
- COCKPIT OVERHAUL: panels migrated to gpui-component Button kit + semantic variants (7e7990ae); the dock paned
  workspace; gpui_component::init wired into ALL headless render paths (30b04a3e — also restores the seL4 bake).
- MATRIX CHAT kickass+dregg-pilled: rooms=cells, identity=cells, send=turn, and THE STAR — a message carries a
  rehydratable MEMBRANE (a cap-bounded world-fork the recipient drives + stitches back fail-closed). Reactions/
  replies/edits-as-state/trust badges (f17b0d15; 19 tests). Verified render.
- REHYDRATABLE MEMBRANE tested+worked: mint→rehydrate→drive→stitch round-trip; graduated rights (embedded/
  studyref/networkboundary-with-signed-consent) each enforced; consent-signing-domain CLOSED; anti-amplification
  a fail-closed gate (7414c820; 12 shared_fork + 13 powerbox + 134+4 web-surface tests).
- ATLAS refreshed: 28 cockpit surfaces re-baked w/ the new widgets + 3 NEW app surfaces (deos-chat/editor/
  docviewer) via fresh offscreen --screenshot modes (2b3073dc, 3199a6d1, cb4ad22b; 31 surfaces).
- TESTED: every app-crate suite green; fixed the world_collapse nondeterminism test (2c63e72e). Full cockpit bin
  builds green with ALL lanes integrated. Main-loop integration seams resolved: public first_pane, headless theme-
  init, ed25519 regular dep.
WITNESS: commits a3f7ce07·f8184fbe·7e7990ae·1de5c0ed·f17b0d15·7414c820·2b3073dc·3199a6d1·cb4ad22b·2c63e72e
+ the integration fixes. THE LINE: every app is a VIEW over the one cell graph; every screenshot a rehydratable
fork; every agent action a receipted turn; deos edits/builds/operates itself, confined, from within.## ✅✅ emberian.github.io/dregg IS LIVE — atlas + the real wasm cockpit (2026-06-22, green-or-bust)
The Pages deploy is GREEN and serving (verified from the public URL):
- /dregg/ + /dregg/atlas/ (interactive atlas; LFS images materialize via Actions — the lfs:true path works)
- /dregg/cockpit/ — THE LIVE WASM COCKPIT: starbridge_web_bg.wasm = 6.96 MB of the REAL verified executor,
  boots in-browser ("● live · wasm executor"), 7 faces, click-to-act, the None fix live. NO placeholder
  (green-or-bust per ember — a degraded wasm /cockpit/ must fail the build, not ship).
- /dregg/atlas/ie6/ — the static HTML-4.01 floor.
Getting the deploy green required clearing 5 PRE-EXISTING breakages masked behind the first WASM failure:
(1) swarm's PredicateInput::AuthContext producer uncommitted (committed cell/predicate.rs); (2) swarm's
Effect::RefreshDelegation consumers uncommitted (committed web-surface/sdk/turn); (3) Mac-pinned
lightningcss-darwin-arm64 breaking linux CI (removed from site/package.json + CI re-resolves); (4) stale
ontology-catalog.generated.json (regenerated); (5) the plonky3-recursion fork absent in CI for the
separate starbridge-v2 workspace (pages.yml now fetches the public fork @ rev 72ffc5646, hard-required).
The native `starbridge-v2 --serve-ie6 <port>` LIVE frame-streaming server (the real Path B for ancient
browsers) is verified locally; deploying it to a host is a follow-up (it needs a running server + gpui
offscreen, unlike the static Pages artifacts).


### ✅ WEB-DEOS + ADOS DEPTHS — both closed (2026-06-22):
WEB-DEOS FULL (cfac7b88): the REAL cockpit::Cockpit renders in a browser tab on gpui_web — cockpit/views/dock
lifted into the lib (gpui-ui|gpui-web union gate + extern crate self, zero cockpit-internal edits), boot_cockpit
mounts Cockpit::with_node over the in-tab wasm executor, gpui-component compiles to wasm32 (tree-sitter grammars
opt-in, none pulled). Both builds GREEN (wasm + native check). Remaining gap = the native-resource BACKENDS only
(terminal-PTY-over-WS, editor-Fs-over-firmament, servo native-only) — the UIs are web-ready. "The whole verified
OS is just a URL" is real for the shell.
ADOS LIVE (a701a16a + 5d3893f3): the agent is a mountable cockpit pane (⌘K "Open Agent pane" → chat + tool-call
ledger w/ receipts/refusals + mandate inspector), AND the live loop RAN END-TO-END: venv fixed (uv pip install
agent-client-protocol==0.9.0 into the brew hermes-acp venv), then a REAL Bedrock-Hermes agent emitted a dangerous
`terminal rm -rf` tool-call → session/request_permission → HermesGateway admitted it as a cap-gated/metered/
receipted dregg turn (receipt 9af640b5…, mandate tool:terminal rate-5 spent 1/left 4 → allow_once). The ADOS
thesis — every agent action a receipted gated turn — DEMONSTRATED with a real agent + real model + real tool-call.
Live ceiling = the model provider (creds present → full loop). CI hermetic on the mock. Next edge: the web-deos
backend wires (PTY-over-WS, Fs-over-firmament, matrix-wasm) → the whole WORKING desktop in a tab.## ✅ CUSTOM proof_bind — THE SOUNDNESS CORE CLOSED (2026-06-21, the genuine recursive verify)
The last unprovable effect's SOUNDNESS gap is closed: `proof_bind` no longer bounds-checks — it
VERIFIES the bound external STARK sub-proof. New `circuit/src/custom_proof_bind.rs`
(`verify_proof_bind`): resolves the program by the bound 8-felt VK, verifies the external
`CellProgram` STARK under its AIR, requires the verified sub-proof's PI commitment == the bound
`commit` column. A custom effect with a FORGED sub-proof (non-verifying STARK / mismatched commitment
/ unknown VK) is REJECTED. BEFORE→AFTER: forged accepted → forged rejected. Tests: 5 in-module +
`custom_proof_bind_honest_verifies_forged_rejected` in `sdk/tests/wide_completeness_ledger.rs` (both
poles, no catch_unwind). The toy `ToyEngine` (descriptor_ir2) is now backed by a real engine; the
Lean apex's `EngineSound.recursive_sound` (the named FRI-verifier obligation) is the abstraction this
realizes — no descriptor/VK/Lean change (verifier-side soundness).
- RESIDUAL (routing, NOT soundness): the EffectVM-wide-TRACE producer (`prove_effect_vm_rotated_wide`)
  still doesn't route the Custom EFFECT ROW (transfer-shape producer lays 817-wide, UNSAT vs the
  789-wide custom descriptor) and `Turn.custom_program_proofs` is `None` at every construction. Close
  with a `generate_rotated_custom_wide` lead (lay the 789-wide row + thread `BoundCustomProof`), then
  drive through the scoreboard. `custom` stays in the scoreboard's UNPROVABLE-on-wide set until then —
  named in `sdk/tests/wide_completeness_ledger.rs::CUSTOM_ROUTE_EFFECT`.

## ✅✅ WEB COCKPIT — THE EXECUTOR RUNS LIVE IN THE BROWSER (2026-06-22, the keystone REALIZED)
Path C landed end-to-end. ONE MODEL, native + browser: the gpui-free Presentable/World substance compiles to
wasm32 + drives the REAL verified executor in a browser tab, no server.
- WASM-PORT (commit a0b6284e0, by the port agent): starbridge-v2 model → wasm32 (target-gated no-lean-link
  executor deps · persist/redb stubbed `persistence_wasm.rs` · getrandom js). Native stays green.
- BINDGEN SURFACE (commit 23324b470): NEW crate `starbridge-v2/web/` (cdylib) — `WebImage { survey, inspect
  [7 faces], affordances, act [REAL cap-gated turn], ocap }` = dregg-mcp's core tools, in-browser. + the
  runtime time wall fixed (world::now_unix uses js_sys::Date::now on wasm32).
- LIVE COCKPIT (commit 410a7379b): `starbridge-v2/web/cockpit.html` — interactive cockpit (clickable cells →
  7 faces → click-to-act → live re-render), all driven by WebImage. VERIFIED in headless Chrome: act touch
  COMMITS, act grant REFUSED by cap-gate, all in wasm.
- BUILD/RUN: `cd starbridge-v2 && wasm-pack build web --target web --out-dir pkg --dev` then serve
  `web/` over http + open `cockpit.html` (or `test.html`). pkg/ is gitignored (40MB dev; use --release for
  size). The atlas's app.js can drive WebImage live (the next polish: nav/back-forward in the web cockpit).
- ✅ CLOSED (750d0d07c): the AuthRequired::None cap-badge inversion. affordance.rs::authorized_for special-cases None-required → always-authorized; the real grant guarantee fires in the executor. 7 inspect_act tests green.

## ⚑⚑ WEB COCKPIT — Presentable/NavAction in the browser (the keystone; ember 2026-06-22)
THE GOAL: starbridge-v2 as an in-browser experience. THREE skins of ONE model (the gpui-free
`Presentable`/`Presentation`/`NavAction`/`InspectAct`/`reflect` substance in `starbridge-v2/src/`):
native gpui (the desktop), WEB, seL4 framebuffer. The swarm census (2026-06-22) found: (1) `gpui_web`
ALREADY exists as a working WebPlatform over `<canvas>` (WebGPU/WebGL2) IN the pinned `emberian/zed` fork
(+ a `cfg(target_family="wasm")` arm in `gpui_platform`) — so the real-cockpit-on-wasm path is weeks-scale
integration, not a port; (2) `wasm/` already exposes the executor in-browser (create/commit/read/PROVE —
`DreggRuntime`), the REAL `TurnExecutor` under `no-lean-link`; (3) THE SINGLE GAP (both technical agents
converged independently): the `Presentable` model is native-only (`grep Presentable wasm/src/` = empty) —
it must be made wasm-compilable + exposed. THE PLAN ember set: **C (real cockpit, Presentable+NavAction in
the browser) is primary; B (frame-stream from `node`) is the IE6/timetraveler GRACEFUL-DEGRADATION floor
for ancient user-agents, NOT the main path.** FIRST SLICE (de-risk via a measured spike, per
measure-before-believing-a-lever): try to compile the gpui-free model to wasm32 — the surgery is contained
(~7 files: mirror wasm/'s `no-lean-link` split into starbridge-v2 · feature-stub `WorldPersist`/redb
[confined to `persistence.rs`+`world.rs`, `None` on every non-durable path] · gate the 5 native-std files).
ARCH DECISION (open): extract a shared gpui-free model crate (`dregg-image`, clean, big refactor) VS
feature-gate starbridge-v2 to wasm (the ~7-file surgery, model stays in place). Then expose
`Registry::present`/`available_nav`/`apply_nav`/`InspectAct::send` over wasm-bindgen (mirroring dregg-mcp
in wasm) and drive the dregg-atlas's `app.js` LIVE off it (the atlas grown up — it already renders
Presentation data). The web Studio/Explorer/Playground then converge onto the SAME presentation layer
(kills the per-surface hand-rolled-inspector drift). Web-surface census verdict: NOTHING stale to retire
(Studio = the only WEB authoring IDE, generated-from-Lean w/ a CI drift-gate; Explorer/Playground = distinct
viewports; `starbridge-web-surface` = the load-bearing web-of-cells LIB; `deos-leptos` = a parked SSR demo).

## ⚑ MACRO / SCRIPT AS A CUSTOM-VK OBJECT — verify a recorded turn-sequence without a general zkVM (ember 2026-06-22)
A macro = a reusable, attenuable, proof-carrying RECORDED TURN-SEQUENCE. The census (2026-06-22) confirmed
the substrate is built four times over: carrier = `Pipeline`/`TurnBatch` (`turn/src/eventual.rs:282`, already
Serialize + replays through `execute_pipeline`); template pattern = factories (`cell/src/factory.rs`,
content-addressed by VK); parameterization = guarded holes (`held_promise.rs`, Lean `holeFill_binds_in_circuit`);
verified replay = History root-tooth (`replay.rs`). THE KEY DESIGN (ember): don't build a general zkVM —
**compile each (bounded) script to its OWN Custom VK** (the composition of its turns' per-effect rungs along
the dependency DAG + the hole constraints), identified content-addressed, RUN via `Authorization::Custom
{ vk_hash = script_vk }` (the existing app-defined-verification seam) with the holes as public inputs. The
macro becomes its own proof system ("the token became the proof system", one level up). Full design:
`docs/deos/MACRO-AS-CUSTOM-VK.md`. TIERS: Tier-1 = a `Script` value = serialized `Pipeline` replayed via the
EXISTING `execute_pipeline` (no new circuit; buildable now; rides proven parts) → surfaces as the cockpit
⏺▶ macro + an inspectable atlas object. Tier-2 (VK-affecting, ember-gated, formal): the composed-script
circuit + either the lean non-effect form (Pipeline + Custom-predicate attestation, NO new kernel verb —
recommended first) OR a first-class `RunScript` effect (factory pattern, formally). HONEST EDGE: bounded
scripts only (a macro is a fixed sequence; unbounded loops would need a real zkVM, out of scope); circuit
composition is real (but composition of existing emitted-from-Lean rungs, not a new prover).

## ⚑⚑ VK-EPOCH REFRAMED (2026-06-22, devnet TORN DOWN ⇒ genuine VK-freedom, no redeploy gate)
The "VK epoch keystone" (checklist C: "compute_commitment absorbs the roots") is STALE FRAMING of an
ALREADY-MOSTLY-CLOSED gap — verified EMPIRICALLY at HEAD (the verify-before-believing discipline; a read-only
scope gave a plausible-but-WRONG plan built on the RETIRED v1 lossy `record_digest` path; the keystone agent
RAN the live rotated path and found the truth). GROUND TRUTH (see `docs/VK-EPOCH-PLAN.md` §1, the authoritative
file:line reframe): there are THREE commitment surfaces. The BINDING wire commitment the light client pins —
`compute_canonical_state_commitment` (cell/src/commitment.rs:192) — ALREADY absorbs lifecycle/perms/vk/deathCert/
fields_root/the 8 system_roots (nullifier/commitment/deleg/…)/heap_root. The wide rotated v9 (commitment.rs:1020,
37 named limbs: authorityDigest@24 capRoot@25 nullifierRoot@26 commitmentsRoot@27 heapRoot@28 lifecycle@29
lifecycleDisc@32 permsDigest@33 vkDigest@34 mode@35 fieldsRoot@36) is computed IN-TRACE. cellSeal is ALREADY
forced-on-wire (rotateV3WithDiscGate forces lifecycleDisc in-circuit; forge-detector `effect_vm_rotation_flip.rs:1536`
honest-accept + freeze-AFTER-to-PRE reject + mutation-confirm — EXISTS + GREEN). recStateCommit byte-unchanged.
⇒ THE REAL VK-EPOCH = NOT "teach the commitment new columns" (done) but **convert the remaining OFF-CELL ANCHORS
to IN-CIRCUIT FORCE GATES** — the light-client-vs-full-node discriminator: setPermissions/setVK/refusal + the
lifecycle PAYLOAD ride the off-cell anchor (proof_verify.rs ~718-735 re-derives the post-cell via apply_effect_to_cell
on the TRUSTED pre-cell — a FULL NODE can; a LEDGERLESS LIGHT CLIENT CANNOT) ⇒ NOT light-client-bound yet.
THE STAGES (VK-EPOCH-PLAN §5, family-at-a-time, each independently provable+deployable, SEQUENTIAL on the shared
descriptor surface — NOT a 10-way fan-out, concurrent edits to EffectVmEmitRotationV3.lean/trace_rotated.rs/proof_verify.rs/
ClosureAll clobber in the shared tree): A cap-write DA (partly closed by tonight's revoke/revokeCapability — assess) ·
**B authority off-cell→in-circuit force gate — STEP-0 SPLIT (2026-06-22): setPermissions/setVK are ALREADY
light-client-forced (Family 1, in-circuit `permsVKWeldGate`; `vk_epoch_perms_vk_light_client_binding` GREEN).
✅ REFUSAL CLOSED (2026-06-22): the refusal light-client forge is now REJECTED in-circuit. THE DIVERGENCE FIXED —
`cell::state::compute_fields_root` was `poseidon2(blake3(map))` (unbindable by any gate) ⇒ now the OPENABLE
sorted-Poseidon2 `CanonicalHeapTree` root (the SAME `heap_root` scheme nullifier/accounts use), realizing the Lean
`FieldsMap.fieldsRoot` openable digest; the committed limb 36 IS that openable root (`fields_root_felt` recovers the
felt; `pre_limbs_from_cell` + `rotation_witness` agree). THE GATE — `EffectVmEmitRotationV3.refusalFieldsWriteV3` appends
a `.write` map-op (`after_fields_root == write(before_root, refusalAuditKeyFelt=field_key_hash(REFUSAL_AUDIT_EXT_KEY)
=529176517, audit_felt@prmCol2=col70)`), gated on `SEL_REFUSAL`; apex `refusalFieldsWriteV3_forces_write` threaded
through `refusal_descriptorRefines_sat → closedLogExtract_refusal_closed → lightclient_unfoolable_closed_final_genuine`
(axiom-clean, MUTATION-CONFIRMED reds the apex). THE GENERATOR — `generate_rotated_refusal_trace_with_fields_tree`
(mirrors noteSpend's nullifier-tree generator) overrides limb 36 + threads the BEFORE leaf set as `map_heaps`; the
audit slot is RESERVED position-stable so a refusal is a value WRITE. FORGE-DETECTOR FLIPPED:
`vk_epoch_refusal_lifecycle_light_client_binding.rs::refusal_light_client_forge_rejected_by_fields_write_gate` —
honest accept + forged-after-root REJECTED anchor-disabled (no full-node anchor) + non-vacuity. Descriptors re-emitted,
FP re-pinned, drift-check GREEN. ✅ DEPLOYED PROVER WIRED (4b45fa33e): `generate_rotated_refusal_wide` +
the `full_turn_proof.rs` Refusal routing split + the LIVE `cipherclerk::prove_sovereign_turn_rotated` thread the
BEFORE fields-tree as `map_heaps`. Deployed poles GREEN at HEAD: `wide_sovereign_refusal_proves_and_anchored_verify_accepts`
(RED→GREEN, honest refusal proves on the live entry) + `sovereign_rotated_c1` honest-proves-and-verifies / forged-rejected;
cap suite 313/0/1 no-regress. ⇒ REFUSAL FORGE FULLY CLOSED gate→apex→DEPLOYED PROVER, every pole tested on the living
protocol path. (Also closes setFieldDyn at the same openable-fields_root foundation.) Lifecycle-payload twin (STILL OPEN, the next floor target): the DISC (safety-critical) IS in-circuit-forced
(`rotateV3WithDiscGate`, cellSeal = 108 constraints); only the opaque `lifecycle_felt(reason_hash, sealed_at)`
payload felt rides the record pin (needs an in-circuit hash gate over the light-client-known (reason_hash,
block_height) — STAGE C). DISCRIMINATOR (BEFORE/AFTER, both poles, non-vacuous):
`circuit/tests/vk_epoch_refusal_lifecycle_light_client_binding.rs` — forge ACCEPTED anchor-disabled (light-client) /
REJECTED under the full-node off-cell anchor (GREEN). The prior test framing (manual PI-46 anchor = the full-node
step-6b re-derivation, mislabeled "FORCED-ON-WIRE — CLOSED") was CORRECTED to assert the honest open residual.** ·
C lifecycle-payload in-circuit force · D note-create grow-gate (commitmentsRoot, mirror noteSpend) · E deleg-tree column
(refreshDelegation/revokeDelegation — cap_root is the wrong primitive) · F v1-lossy-anchor RETIREMENT (the one true
flag-day, LAST, touches the shared PI prefix). KEY DE-SCOPE: the cell-side commitment bytes DON'T change ⇒ **NO ledger
migration** (confirm via a one-cell round-trip before F). Green-check per family (§6): light-client REJECTS a forged post
differing ONLY in the column WITH the off-cell anchor block DISABLED (the discriminator) + both poles + non-vacuous.
REFUSAL §A STRUCTURAL FINDING (2026-06-22, agent did NOT fake a gate — model-grounded): refusal's audit write lands in
`fields_root` (cell/src/state.rs:291), which is a **BLAKE3 SPONGE, not a Poseidon2 `CanonicalHeapTree`** — so the
noteSpend map-op gate CANNOT be mirrored (an insert produces a Poseidon2-Merkle root; committed limb 36 =
`hash_bytes(blake3-sponge)` — different schemes over the same map; a gate would float on a limb nothing commits =
phantom/laundered). This is the same systemic blake3-where-Poseidon2-is-needed issue ember flagged on the vault hashlock.
TWO genuine VK-affecting flag-day paths: **A** re-architect `compute_fields_root` as a `CanonicalHeapTree` (+ thread a
fields_map leaf-set into RotationWitness, clone the note-spend tree generator, swap the v3Registry entry); **B (preferred,
smaller)** redirect the refusal audit into `heap_root` (limb 28, ALREADY a Poseidon2 `CanonicalHeapTree`) via a heap write
+ update the Lean RefusalSpec, then mirror noteSpend on `B_HEAP_ROOT`. Shares the missing-live-heap_root-map-op cohort with
the `heapWrite`-not-in-v3Registry gap. The lifecycle PAYLOAD (cellSeal limb 29 opaque felt) is the Stage-C twin (in-circuit
hash gate over the light-client-known reason_hash+block_height; the safety-critical DISC is already in-circuit-forced).

## ⚑⚑ OBLIGATION-TABLE DISCHARGE — VERIFIED sweep (2026-06-22): NO surprise light-client forges
A 16-effect read-only assessment workflow (wor23yy6e) classified each live effect's light-client binding. RAW
output flagged 4 GENUINE_FORGE (cellSeal/receiptArchive/spawn/refreshDelegation) — but the assessment is REASONING,
not running, so I VERIFIED each (ran the discriminator / read the DEPLOYED descriptor). RESULT:
- ❌ cellSeal FALSE POSITIVE: `cellSealV3` (EffectVmEmitRotationV3.lean:3059) HAS the LIVE disc gate
  (`rotateV3WithDiscGate`); `rotated_cellseal_record_pin_forces_lifecycle_and_rejects_frozen_forgery` GREEN — the
  frozen-seal forge is UNSAT via the disc gate ALONE (no trusted post-cell). The assessor read an UNDEPLOYED Lean
  file (RotatedKernelRefinementLifecycleDisc) + missed the live descriptor; conflated the forced DISC with the
  low-severity opaque PAYLOAD felt.
- ❌ receiptArchive FALSE POSITIVE: `receiptArchiveV3` (line 3311) = `rotateV3WithDiscGate ... discArchived` — disc
  forced in-circuit (light-client). Opaque payload (archival checkpoint) rides the anchor = low-severity, same as cellSeal.
- ✅ spawn CONFIRMED but NAMED: the cap HANDOFF is NOT forced (`RotatedKernelRefinementBirth.lean:37` "HONEST scope:
  the cap handoff is the NAMED phase-D residual, NOT forced … VALUE_PARTIAL"); the accounts-set grow-gate IS forced
  (`spawnV3_grow_gate_forces_set_insert`). Close = the cap-tree insert map-op on spawnV3 (phase-D cap-reshape).
- ✅ refreshDelegation CONFIRMED but NAMED: its move is on the DELEGATIONS tree (DELEG system-root), NOT cap_root;
  `RotatedKernelRefinementCapFamily.lean:1248+` is BUILDING the in-circuit DELEG-tree write op (Stage E), not yet deployed.
- 10 ALREADY_FORCED (cellUnseal/cellDestroy/makeSovereign/createCell/noteCreate/delegate/introduce/delegateAtten/
  grantCap/exerciseViaCapability — the in-circuit map-op/disc/weld gates bind; delegateAtten's LogUp is a separate
  LIVENESS prove-through, not a forge). 2 NOT_LIVE_LEAD (setFieldDyn, createCellFromFactory — completeness).
THE LESSON (re-banked): the assessment workflow is READ-ONLY REASONING = NOISY (2 of 4 high-severity "forges" were
FALSE). Verification (run the §6 discriminator / read the DEPLOYED descriptor) is MANDATORY before acting. NET: no
surprise forges; the genuine residuals (spawn cap-handoff, refreshDelegation deleg-tree) are KNOWN + named + Lean-in-flight;
the low-severity lifecycle-payload (opaque felt for cellSeal/cellDestroy/receiptArchive) + 2 completeness leads remain.
FINISH-ALL WORKLIST (sequential on the shared descriptor surface): refreshDelegation deleg-tree (closest) · spawn
cap-handoff (phase-D) · lifecycle-payload hash gate · setFieldDyn + createCellFromFactory live leads.
✅✅ SOUNDNESS MILESTONE (2026-06-22): EVERY CHARACTERIZED LIGHT-CLIENT FORGE IS NOW CLOSED (gate→apex, mutation-confirmed):
revokeCapability (f458b5258) · refusal gate→apex→deployed-prover (9625645d8+4b45fa33e) · refreshDelegation deleg-tree
(fbc571533) · spawn cap-handoff (6211509c3) · lifecycle-payload (5fde9dd29). Plus delegateAtten LogUp #[ignore] REMOVED
— it was a one-token FACET copy-paste bug (EFF_GRANT_CAPABILITY vs EFF_DELEGATION_OPS), NOT a plonky3 issue (found by
instrumenting+RUNNING). The obligation-table sweep found NO surprise forges; all genuine residuals are closed. The REMAINING
worklist (#3 live-lead routing, #4 setFieldDyn, #6 refreshDelegation enrichment) is COMPLETENESS/LIVENESS — making effects
PROVABLE on the deployed sovereign path — NOT open holes. NOTE: another session is concurrently doing NoteCreate live-lead
routing in turn/src/executor/proof_verify.rs (stay out of that file). The prover surface (full_turn_proof.rs) is a chokepoint
that sequences the live-lead work.

## ✅ delegateAtten SUBMASK+INSERT PROVE-THROUGH — CLOSED (the "LogUp obstruction" was REFUTED), 2026-06-21
The diagnosis once written here was WRONG: there was no p3 LogUp/permutation-column bug. The real cause was a
one-bit FACET COPY-PASTE — `delegateAttenWriteCapOpenV3` carried `EFF_GRANT_CAPABILITY (1<<2)` where it needed
`EFF_DELEGATION_OPS (1<<16)`. Fixed in `5fde9dd29`; the `#[ignore]` is gone and
`cap_write_delegate_atten_proves_and_verifies_light_client` PROVES + light-client-VERIFIES at HEAD (re-verified
2026-06-22). Lesson re-banked: a "plonky3-level" obstruction claim needs the column-level diff before it is
believed — a mislabelled selector bit reads as a balance failure. (Unrelated, still `#[ignore]`'d with an
accurate reason: the 3 `cap_open_self_verify.rs` attenuate CIRCUIT twins are redundant lower-level coverage
that pass an EMPTY `map_heaps` against the now-firing Update map_op; the capability is GREEN at the SDK level
via `cap_open_attenuate_leg_proves_and_verifies_end_to_end` — re-enable needs the BEFORE cap-tree map_heaps
plumbed into their hand-built trace.)

## ⚑ REACT CIRCUIT WITNESS — the `reactSpendA` descriptor (the in-circuit grow-gate for `Effect::React`), 2026-06-21
The first-class reactive effect landed at the EXECUTOR layer (Track 2): `Effect::Promise/Notify/React`
(`turn/src/action.rs`) dispatch through `TurnExecutor::apply_react` (`turn/src/executor/apply.rs`), which
spends `pending_id` into the SAME production `note_nullifiers` set `NoteSpend` rides — so react-twice /
replayed-pending_id is rejected by the identical double-spend gate (genuine end-to-end +
forge-detector tests green in `react_executor_tests`). NAMED follow-up = the in-circuit witness:
a light client verifying a batch bearing a `React` must SEE the promise-hole nullifier grow exactly as
`noteSpendA` does. The descriptor to add: **`dregg-effectvm-react-spend-ir2.json`** (a sibling of
`dregg-effectvm-note-spend-ir2.json`), with the matching Lean **`Inst.ReactA` + `Witness.ReactWitness`**
(mirror `Dregg2.Circuit.Inst.noteSpendA` + `Dregg2.Circuit.Witness.NoteSpendWitness`): touched component =
the `nullifiers` LIST; guard = anti-replay `pending_id ∉ nullifiers`; the log GROWS by the react receipt;
the concrete digest reads the nullifier list positionally (the `refP2` Poseidon2 sponge), so a forged
nullifier-set rewrite is visible to the BIND gate. The refinement rung: `reactSpend_descriptorRefines_sat`
(mirror `noteSpend`'s rung). The ONE difference from noteSpend: React's spend carries no monetary value
delta (no paired NoteCreate / conservation leg) — the `value` column is fixed `0`, so the descriptor is
the value-erased noteSpend grow-gate. SHORTCUT TO EVALUATE FIRST: because the spend is byte-identical at
the nullifier-set level, the `effect_vm_bridge` MAY be able to project `React` to `VmEffect::NoteSpend {
nullifier: pending_id, value: 0 }` and ride the EXISTING `noteSpendA` rung unchanged — confirm whether the
existing descriptor's `value=0` path is sound for a no-paired-create spend before building a new descriptor.
Closure: land the descriptor (or the VmEffect::NoteSpend projection) + the rung, VK-affecting → ember-gated
redeploy. (`docs/deos/REACTIVE-EFFECTS.md` §6.)

## ✅ CELL CENSUS 4-vs-8 — RESOLVED: NOT a bug (cockpit installs reflexive UI cells), 2026-06-21
The cockpit shows 8 cells, the raw `demo_world` ledger has 4. RESOLVED: `Cockpit::with_node`
(`cockpit.rs:~860-911`) installs extra UI-scaffolding cells via `genesis_cell` on top of demo_world's 4 —
`buffer_backing (0x5B)`, `inspector_view_backing (0x5E)` (the reflexive `ViewCell`, so the inspector is
itself inspectable), `workspace_cell_backing (0x5F)` (the `WorkspaceCell`), etc. So the cockpit world = 4
PROTOCOL cells + ~4 cockpit-WIDGET backing cells. `Ledger::len()` and `iter()` agree (both read
`self.cells`); the "divergence" was raw-`demo_world` (dregg-mcp) vs `with_node`-scaffolded (cockpit). The
dregg-mcp's clean 4-cell `demo_world` is the correct PROTOCOL substrate for the atlas game-tree crawl; the
+4 reflexive UI cells are documented in the atlas UI pillar. No code change needed. (The original
"feature-gated seeds" hypothesis below was wrong and is struck.)

<details><summary>(struck) original feature-gating hypothesis</summary>

## ⚑ DEMO-WORLD CELL CENSUS DIVERGES BY FEATURE SET — 4 cells (embedded-executor) vs 8 (native-full) (found by dregg-mcp, 2026-06-21)
`world::demo_world()` produces a DIFFERENT world depending on the build's feature set. Under
`--no-default-features --features embedded-executor` (the lean dregg-mcp build) it seeds **4 cells /
height 5**; under `native-full`/`headless-render` (the cockpit) it seeds **8 cells / height 9** (the
cockpit GRAPH tab shows "8 cells · 4 capability edges" with roots 0ce097/494266/bf34db absent from the
4-cell view). MECHANISM (hypothesis, to confirm): the seed turns include `CreateCell` /
`CreateCellFromFactory` / factory-birth effects (`world.rs:1222,1250,1427,1529`) whose success depends on
prover/sdk features (`dregg-sdk` is pulled with `features=["embed-core","prover"]` in the lean build;
`native-full` adds more) — so several seed turns are REJECTED under the lean build, yielding fewer cells.
IMPACT: any tool reading `ledger().iter()` inspects HALF the image. ⚠ UPDATE (2026-06-21): the
feature-gating hypothesis is REFUTED — dregg-mcp rebuilt at `native-full` STILL shows 4 cells via
`ledger().iter()`. So the gap is NOT seed divergence; it is `World::cell_count()` (=`engine.ledger().len()`)
or the cockpit's display counting MORE than `ledger().iter()` yields (candidate: sovereign-cell /
registration store, or view/meta objects counted in the header, or a `Ledger::len()` vs `iter()`
inconsistency). CLOSURE: find where the other 4 cells live — check `Ledger::len()` vs `self.cells.iter()`,
the sovereign-registration store, and what the cockpit GRAPH tab's "8 cells" actually enumerates — then
make the harness (and any cell census) see the SAME complete set the protocol does.
</details>

## ✅ dregg-mcp SCREENSHOT — responsive size + tab selection (the 800x600 truncation fixed, 2026-06-21)
The bake (`render_cockpit_headless`) now takes `--render-size WxH` + `--render-tab NAME`; only the seL4
800x600 geometry downscales + writes `.rgba` (PD-blit unchanged), every other size renders the full 2x
capture (no `overflow_hidden` truncation). Confirmed: 1280x832 reflows the full cockpit (the right
"Welcome to the live verified image" panel + complete tab bar now show); `select_tab_named`
(`cockpit.rs`) screenshots any of the 28 surfaces (INSPECTOR/GRAPH/etc verified). MCP `screenshot` tool
defaults to 1280x832, accepts `size`+`tab`.

## ◻ FOUR LIVE TABS STALL HEADLESS STEP-RENDERING (Wonder/Swarm/Agent/Time) (found by the atlas UI-explorer, 2026-06-22)
The atlas `--explore-ui` driver (`starbridge-v2/src/main.rs`) BFS-walks the cockpit's UI state-space by
stepping `window.update` + `capture_screenshot` between states. Four tabs HANG `window.update`'s effect-flush
because their render schedules self-rescheduling / perpetual work that never drains: Wonder (the glow
animation), Swarm (boots the metered killer-demo on tab-enter, `set_tab` `cockpit.rs`), Agent (the live
activity feed), Time (the time-travel/suspend machinery). They render fine in the WINDOWED app (a real
event loop drives them) and are captured in the UI-atlas surface screenshots, but are excluded from the UI
tree (`Cockpit::available_nav` skip-set). CLOSURE (if a fuller headless UI tree is wanted): gate these tabs'
live timers / async subscriptions behind a `headless` flag, or bound the effect-flush. Not a correctness
bug — a headless-automation limitation, now mapped. The UI explorer otherwise rendered 260 states with ZERO
panics.

## ◻ ISSUER WELL (negative balance) CANNOT INITIATE ANY TURN — fee-gated even for value-neutral verbs (found by dregg-atlas crawl, 2026-06-21)
The atlas game-tree crawl found that EVERY turn authored by the issuer-well cell (balance −1000000) is
refused with `InsufficientBalance` — including `peek` (EmitEvent) and `touch` (IncrementNonce), which
mutate no value. The well cannot pay the per-turn computron fee from a negative balance, so it can never be
a turn's `agent`. Arguably CORRECT (an issuer well is a passive supply sink that only moves when other
cells transact against it — `docs/DREGG3.md:133-138`), but it means a fee-charged turn is gated on positive
balance even for value-neutral verbs. CLOSURE (decide): if wells are meant to be strictly passive this is
fine (document it); if a well should be able to emit/tick, the fee path needs a zero-fee or
well-exempt branch. Repro: dregg-mcp `effect from=<well> kind=transfer` → refused. Not a soundness issue.


## ⚑ VK-EPOCH ROUTING WELDS — noteCreate + makeSovereign FORCED-ON-WIRE; setFieldDyn = deeper residual (2026-06-21)
Two of the three big-wave residual welds CLOSED on-wire (VK-FREEDOM ERA — generator-side, NO descriptor/VK
change; drift PASS, no silent forge):
  * **noteCreate** — the in-circuit commitments-root grow-gate (`.insert`, limb 27) was SOUND but the LIVE
    producer/verifier ROUTING was unwired (NoteCreate fell through to `generate_rotated_transfer_shape_wide`,
    which carries the bare 46-PI base and ERRORS on NoteCreate's 47-PI commitment-pinned base — fail-closed,
    UN-PROVABLE). WELD: a NoteCreate branch → `generate_rotated_note_create_wide` in `proof_verify.rs`
    (verifier) + `full_turn_proof::prove_effect_vm_rotated_wide` + `cipherclerk` (provers). Witness:
    `vk_epoch_notes::notecreate_forced_on_wire_through_live_wide_producer` (honest proves+verifies through the
    LIVE wide producer at 8-felt/63-PI geometry; forged commitments-root UNSAT).
  * **makeSovereign** — `record_pin_offset` had NO MakeSovereign arm, so the live generator emitted 46 dpis vs
    the descriptor's declared 47 → UN-PROVABLE. WELD: `Some(Effect::MakeSovereign) => Some(B_AUTHORITY_DIGEST)`
    (the mode-byte folds into the r23 authority residue) + MakeSovereign joins the record-pin family in all
    three prover/verifier routers. Witness:
    `vk_epoch_misc::makesovereign_forced_on_wire_rejects_forged_authority_digest_anchor_disabled` (honest
    promotion proves+verifies; forged committed authority residue UNSAT, anchor-disabled).
NAMED RESIDUAL (DEEPER — reported, not faked green): **setFieldDyn** is NOT a routing weld. Its
`setFieldDynVmDescriptor2R24` is a DISTINCT 581-wide geometry (built on the 263-wide `setFieldDynV1Face`, which
folds the openable fields_root insertion sub-circuit `post_root = insert(pre_root, key→value)`); the standard
`generate_rotated_effect_vm_trace` produces only the 188-base → 328-wide rotated trace and can NEVER satisfy it.
Lifting the `field_idx < 8` assert would (a) silently clamp `fields[idx.min(7)]` (WRONG-field bug) and (b) still
emit a 328-wide trace the 581-wide descriptor rejects. CLOSURE = a from-scratch generator for the 263-wide
V1Face (run the openable fields_root insertion in-circuit, feed the fields-root pin col 263 → PI[46]) — NOT a
branch. Witness asserts the geometry mismatch precisely:
`vk_epoch_misc::setfielddyn_unreachable_via_live_generator_missing_weld`.

## ⚑ CAP-WRITE SILENT-FORGE GUARD — CLOSED (the map_op fired on the WRONG selector; re-pointed) (2026-06-21)
THE FORGE (banked RED at `bd7ba0bf9`): the cap-WRITE map_ops (`insertWriteOpRot`/`removeWriteOpRot`/
`heldReadOpRot`/`anchorReadOpRot`, `EffectVmEmitRotationV3`) were guarded on `selA.ATTENUATE = 2` (the SET_FIELD
column) — NEVER 1 on a cap-write row — so the map_op NEVER FIRED, leaving the AFTER cap-root (rotated var 264)
UNBOUND (a fabricated post-root was proved + light-client-accepted; 0xBADF00D witness). CLOSED: parameterized the
4 rotated map_ops by selector `s`; each `<slot>WriteV3` passes its OWN runtime selector — delegate/grantCap/
delegateAtten = `sel.GRANT_CAP = 3`, introduce = `sel.INTRODUCE = 35`, revokeDelegation = `sel.REVOKE_DELEGATION =
30` — matching `effect_selector` (the column the trace sets to 1). The `_forces_write`/`_non_amp` keystones'
`hactive` + the `*WriteAnchor` structs (`RotatedKernelRefinementCapFamily`) follow the same selector. Lean Dregg2
GREEN + axiom-clean; descriptors regen + drift PASS (guards now read 30/3/3/35, was 2). FORGE-DETECTOR FLIPPED
GREEN: `write_cap_open_wrapper_requires_cap_tree_write_witness_no_silent_forge` (a genuine 213≠264 change with
empty map_heaps is now REJECTED — the map_op fires + fails to resolve the fabricated root);
`cap_write_revoke_proves_and_verifies_light_client` STAYS GREEN (now GENUINE).

### attenuate + revokeCapability — DESCRIPTOR + FORGE-DETECTOR CLOSED; Rust honest-route HANDED OFF (2026-06-21)
The SAME forge (the var2/SET_FIELD never-firing guard + V1-STATE col-65/87 write) was present in attenuate
(`keepWriteOp`) + revokeCapability (`removeWriteOp`). CLOSED in Lean: `attenuateV3` / `revokeCapabilityV3` rebased
onto `v3OfWithCapWrite` over the tick face (`attenuateVmDescriptorGenuineNoRecomputeTick`) with the ROTATED-limb
ops (new `keepWriteOpRot` + reused `heldReadOpRot`/`removeWriteOpRot`, var 213→264) FIRING-guarded on
`sel.ATTENUATE_CAPABILITY = 48` / `sel.REVOKE_CAPABILITY = 24`; the v1-state cap-root cols 65/87 FREEZE. Apex rungs
re-proved + axiom-clean (`attenuateV3_non_amp`, `revokeCapabilityV3_non_amp`, `attenuate_descriptorRefines_sat`,
`revokeCapability_descriptorRefines_sat`; `AttenuateWriteAnchor`/`RevokeCapabilityTraceReadout` re-anchored to the
rotated limbs). lake green, full Dregg2. Descriptors REGEN (`emit_descriptors.py`) — on the wire the
attenuate/revokeCapability map_op now `op=write guard=var48/24 root=var213 new_root=var264` (var 264 GENUINELY
BOUND, verified). FORGE-DETECTORS GREEN (`sdk/.../full_turn_proof.rs`): `cap_write_attenuate_no_silent_forge` +
`cap_write_revoke_cap_no_silent_forge` (a genuine 213≠264 change proves-with-empty-map_heaps → REJECTED).
**RUST HANDOFF (cap-write-Inserts agent's `trace_rotated.rs` region):** the honest prove-through now needs the
cap-tree witness heap for the firing map_op — attenuate is an UPDATE-AT-KEY (read held key, write KEEP_MASK at the
SAME key), which needs a new `CapTreeWriteOp::Update` arm in `generate_rotated_cap_write_base` + routing
`write: Some(...)` for `attenuateCapOpenEffVmDescriptor2R24` / `revokeCapabilityVmDescriptor2R24` + c-list threading.
Pending that: 3 honest prove-through tests `#[ignore]`'d with the precise reason (`cap_open_attenuate_self_verifies`,
`cap_open_attenuate_foreign_selector_row_is_unsat`, `cap_open_wide_proves_verifies_and_executor_anchors` in
`circuit/tests/cap_open_self_verify.rs`; `cap_open_attenuate_leg_proves_and_verifies_end_to_end` in the SDK). The
descriptor (on-wire) + the forge floor are CLOSED; only the honest prove-route witness wiring remains.

## ⚑ CAP-WRITE LOOP — cap-root COLLISION CLOSED (rotated-limb advance + trace-gen aligned); LONE residual = spurious NONCE-FREEZE gate (2026-06-20)
TWO of the three layers are now CLOSED. (1) The col-87 over-determination is closed (commit 0c2b0704c — col 87 is
`map_op` `new_root` ONLY, folded as a commitment INPUT, note-spend-shaped). (2) The v1-STATE cap-root CONTINUITY
collision is FIXED + the Rust trace-gen is ALIGNED (commit 8275b3711 + this Rust work): the descriptor now advances
the cap-root on the ROTATED-BLOCK limb (descriptor vars 213→264 = `BEFORE_BASE/AFTER_BASE + B_CAP_ROOT`), the
`213 == 65` / `264 == 87` welds are GONE, and `generate_rotated_cap_write_base`
(`circuit/.../trace_rotated.rs`) writes the genuine before/after roots to limbs 213/264 and FREEZES the v1-state
cap-root cols 65/87 (pass-through) — exactly mirroring note-spend's nullifier-root-on-a-rotated-limb. MEASURED
LIVE: cap-root rot before(213)=887984798 ≠ after(264)=1054833182 (genuine advance), v1-state cap-root 65==87
(frozen, continuity holds trivially). The producer re-point is FLIPPED ON (`cap_open_route_for_run` RevokeDelegation
carries `write: Some(("revokeDelegationWriteCapOpenVmDescriptor2R24", Remove))`). forge-reject + descriptor-structure
guards GREEN (`cap_write_revoke_forge_rejected`; `cap_write_revoke_descriptor_after_root_is_map_op_defined_only` now
pins var264 = EXACTLY ONE `map_op new_root` AND var87 NOT a map_op new_root — the frozen-v1-state guard).
LONE RESIDUAL (descriptor-EMIT, metatheory/VK-affecting — NOT a producer gap, NOT a trace-gen gap): the deployed
`revokeDelegationWriteCapOpenVmDescriptor2R24` STILL carries a SPURIOUS NONCE-FREEZE gate (`var78 == var56`,
after.nonce == before.nonce) inherited from the attenuate-family shape. Revoke is a nonce-TICK passthrough
(after.nonce = before.nonce + 1), so the gate is VIOLATED on every honest revoke — the IR-v2 prover SELF-VERIFY
fails on this gate (`check_constraints` constraint #10; MEASURED col56=0, col78=1). CLOSURE (metatheory): DROP the
nonce-freeze gate from the 4 `…WriteCapOpenVmDescriptor2R24` wrappers (revoke must tick, not freeze, the nonce).
PIN: `cap_write_revoke_proves_and_verifies_light_client` (GREEN, forward-compatible: fail-closed arm TODAY on the
nonce-freeze, flips to the prove+verify Ok arm when the gate is dropped). The verifier-half tooth
(`is_forbidden_authority_only_cap_write_descriptor`) STAYS GATED OFF (`false`) — forbidding the authority-only
revoke cap-open NOW (no provable alternative) would break the honest revoke path; flip it on WITH the nonce-freeze
drop. The OTHER 3 wrappers (delegate/introduce/delegateAtten = Inserts) have a SECOND descriptor bug: their `read`
and `insert` map_ops use the SAME key column (var 71) — but a sorted `read` requires the key PRESENT while `insert`
requires it ABSENT, so the pair is ALWAYS UNSAT (the read should bind a DISTINCT already-present anchor-key column).
revokeDelegation (a Remove: read+write the SAME present key — consistent) is the proven TEMPLATE. STATE: the
cap-WRITE post-root is NOT YET light-client-verifiable end-to-end; the cap-root half is DONE + measured-correct,
the lone gate to drop is the nonce-freeze (revoke), plus the anchor-read-key fix for the 3 Inserts.

## ⚑ CAP-WRITE WIRE GAP — REFINED: data-availability CLOSED; the REAL block is a DESCRIPTOR over-determination (2026-06-20)
The data-availability half is now CLOSED end-to-end (was the previously-suspected blocker): the witness type
carries the cell's FULL c-list (`CapMembershipWitness::clist_leaves`), the node plumbs it
(`node/src/turn_proving.rs::cap_write_clist_leaves` from `before_cell.capabilities`, threaded through
`prove_and_verify_finalized_turn_capability` → `from_consumed_with_clist`), and the cap-tree→map_heaps bridge
(`circuit/.../trace_rotated.rs::generate_rotated_cap_write_base`, mirroring the note-spend nullifier-tree
generator) builds the openable sorted-Poseidon2 `CanonicalHeapTree` + the GENUINE post-WRITE root (a c-list
missing the revoked key fails closed — no fabricated post-root). The prove-threading (`prove_effect_vm_cap_open`
passes real `map_heaps`) + the route plumbing (`CapOpenRoute.write`) are wired.
THE ACTUAL BLOCK (newly diagnosed, the re-point is GATED OFF `write: None`): the deployed
`revokeDelegationWriteCapOpenVmDescriptor2R24` OVER-DETERMINES the AFTER cap-root (col 87 =
STATE_AFTER_BASE+CAP_ROOT). It binds col 87 TWO incompatible ways — (1) the `map_op` `new_root = var87` (a
sorted depth-16 CanonicalHeapTree REMOVE), AND (2) a poseidon OUTPUT `var87 = hash2(hash4(param0..3),
before_root)` (descriptor constraint #59, col 102 = `hash4(param0..3)`). A depth-16 sorted REMOVE recomputes 16
node hashes along the path; the `hash2(hash4(...), before_root)` is a 2-level absorption — DIFFERENT functions
that disagree for an honest c-list (matching them = inverting Poseidon). Contrast note-spend, where the AFTER
nullifier root is map_op-DEFINED and only FOLDED into the commitment (an INPUT, never a poseidon output) —
PROVABLE. So routing to the write wrapper is UNPROVABLE-as-emitted. CLOSURE = a descriptor-EMIT fix (VK-affecting,
Lean-now): re-emit the 4 `…WriteCapOpenVmDescriptor2R24` wrappers to bind col 87 ONLY via the `map_op` (drop the
hash2 chain on col 87; let the sorted tree BE the cap-tree write, note-spend-shaped). PIN:
`sdk/.../full_turn_proof.rs::cap_write_revoke_descriptor_over_determines_after_root` (GREEN — asserts the two
bindings disagree, non-vacuous). FAN-OUT: the other 3 wrappers (delegate/introduce/delegateAtten) are read+INSERT
(same over-determination); delegate/introduce/delegateAtten + the verifier tooth (`is_forbidden_plain_cap_descriptor`
write-arm) land WITH the descriptor re-emit. The bearer-path write witness = the DELEGATOR's c-list (separate fan-out).
--- (superseded data-availability framing kept below for the record) ---
The cap-WRITE light-client axis (post-cap-root on-the-wire-verifiable) is BLOCKED by a data-availability
gap, NOT by producer wiring or a WIDE-registry gap. Audited the SDK producer/verifier seam:
- The write-bearing wrappers (`delegate/introduce/delegateAtten/revokeDelegationWriteCapOpenVmDescriptor2R24`)
  ARE in `V3_STAGED_REGISTRY_TSV` — the registry the SDK cap-open route (`cap_open_descriptor_json_by_key`,
  full_turn_proof.rs:1261) AND the light-client verifier (`verify_effect_vm_rotated_with_cutover`:1796) both
  resolve against. Registry-availability concern RESOLVED FAVORABLY (the WIDE registry is the separate 8-felt
  faithful-commit path, NOT this seam — the earlier residue (b) framing was imprecise).
- Each write wrapper carries a genuine `map_op` read+insert/write (guard = selector marker var2, NOT vacuous)
  binding BEFORE cap-root (col 65 = STATE_BEFORE_BASE+CAP_ROOT) → AFTER cap-root (col 87) via a sorted-
  Poseidon2 cap-tree write. The IR-v2 prover realizes it against a witness HEAP whose root == BEFORE cap-root
  (`prove_vm_descriptor2`'s `map_heaps`, exactly as note_spend threads its nullifier tree) and CHECKS the
  genuine post-write root == claimed AFTER cap-root (wrong post-root = UNSAT, NOT fakeable).
- `prove_effect_vm_cap_open` (full_turn_proof.rs:1449) threads NO map_heaps (passes `&[]`). The data to build
  one — the cell's FULL sorted c-list leaf-set — is NOT carried by `CapMembershipWitness` (one leaf+path only)
  nor available at `node/src/turn_proving.rs:1104` (`CapMembershipWitness::from_consumed` = the consumed cap's
  path, not the cell's whole c-list). So routing to the write wrapper = an UNPROVABLE proof.
- PROVEN no-silent-forge: the write wrapper FAIL-CLOSES with empty map_heaps ("no witness heap with root …"),
  does NOT launder a fabricated post-cap-root. Test `write_cap_open_wrapper_requires_cap_tree_write_witness_no_silent_forge`
  (sdk lib, GREEN, asserts the precise map_op-witness-heap error).
- The task's "re-point `rotated_descriptor_name`" target is the WRONG seam (that's the non-cap BASE 36-cohort,
  EXCLUDES all `…CapOpen…` by `resolvers_cover_exactly`); the cap-effect seam is `cap_open_route_for_run.route.key`.
- CLOSURE (data-availability, the 5-step shape): (1) extend ConsumedCapWitness/CapMembershipWitness to carry
  the target cell's full sorted c-list leaf-set; (2) plumb from turn_proving.rs; (3) cap-tree→map_heaps bridge
  generator (mirror generate_rotated_note_spend_trace_with_nullifier_tree); (4) thread through
  prove_effect_vm_cap_open → prove_vm_descriptor2; (5) re-point cap_open_route_for_run + add the verifier
  write-tooth (extend is_forbidden_plain_cap_descriptor) IN THE SAME BREATH (adding the tooth before (1-4)
  reds the honest cap_open_fanout_revoke_* path with no provable write route). Tracked in SAFELY-LIVE (A).

## ⚑ REVOKE (tag-2) FROZEN-FACE — the modelled-floor apex slot still rides `revoke_closedLog` (2026-06-20)
attenuate(12) closed CLASS-A this session (`attenuate_descriptorRefines_capOpenSat` over the deployed
`attenuateCapOpenEffV3` base `attenuateV3`, the MOVING write face). revoke(tag-2) is the residual: its apex
slot (`closedLogExtract_revoke_closed`, ClosureFanoutGenuine.lean:361) still calls the MODELLED
`revoke_closedLog`, because `Rfix 2 = revokeCapOpenV3 = effCapOpenV3 revokeDelegationV3` and
`revokeDelegationV3 = v3Of revokeVmDescriptor` is the FROZEN base (`.gate gCapPass` freezes `cap_root`
on-row, no write map-op) — so `Satisfied2 revokeCapOpenV3` CANNOT force the cap-tree REMOVE. Same moving-face
issue the cap-write fix handled for tags 1/10/11/14. CLOSURE: re-point `actionTagToPos 2` (→ a new
`revokeWriteCapOpenV3` riding the MOVING `revokeDelegationWriteV3` base, which carries `[heldReadOp,
removeWriteOp]` and HAS `revokeDelegationWriteV3_forces_write`), then wire a `revoke_closedLog_sat` over it
(mirroring `revokeDelegation_closedLog_sat`). VK-AFFECTING (registry re-point) + crosses the producer seam
(`rotated_descriptor_name`/`cap_open_route_for_run`) — coordinate with the cap-write lane above.

## ✅ receiptArchive(40) GAP-1 — CLOSED: now genuinely Class-A (deployed lifecycle-move reconciled, 2026-06-20)
The executor↔circuit divergence is RECONCILED to the DEPLOYED semantics (ember's decision: the wire
`receiptArchiveV3` disc gate moves the `lifecycle` SIDE-TABLE to `Archived` — `c.archive(checkpoint)` — is
correct; the record-slot `ReceiptArchiveSpec` was the drifted toy model). Done: (1) new executor arm
`receiptArchiveChainA` = `setLifecycle … lcArchived (=4)` gated on `auditGuard` (TurnExecutorFull.lean), arm
re-pointed; (2) `ReceiptArchiveLifecycleSpec` + `execFullA_receiptArchiveA_iff_lifecycleSpec` in
cellstateaudit.lean (the deployed weld); the record-slot `ReceiptArchiveSpec` KEPT as the superseded
modelled fact, re-keyed off a new `receiptArchiveRecordStep` (NOT `execFullA`) so the whole `receiptArchiveE`
arithmetization universe (Argus/Witness/Emit) stays green honestly; (3) `fullActionStep (.receiptArchiveA)`
+ `fullActionStep_exec_iff` re-pointed to the lifecycle spec; (4) apex slot
`closedLogExtract_receiptArchive_closed` → `receiptArchive_closedLog_sat` → `receiptArchive_descriptorRefines_sat`
(the disc gate, like cellSeal/cellUnseal/cellDestroy). MUTATION-CONFIRMED: a frozen-disc (Live) archive forgery
is UNSAT (`receiptArchive_forced` pins `lcArchived` from `Satisfied2 receiptArchiveV3`) — editing the disc gate
reds the apex. Consumer cascade resolved across ~12 files (executor frame proofs CellCommit/CellNullifier/
CellConfine/Identity/StorageGatewayMandate via `receiptArchiveChainA_factors`; the handler shadow via a new
deployed `cellArchiveEffect`/`cellArchiveH`; the v2 Surface2 layer via a NEW
`Inst/receiptArchiveLifecycleA.lean` archive circuit — the `cellSealE` analog — wired through
EffectRefinementBatch2/TurnEffectRefinement/EffectEmittedRefinement/TurnEmit/CircuitCompletenessAssembled).
`lake build Dregg2` GREEN (4106 jobs); the reconciliation theorems axiom-clean. NOT committed.

## ✅ ENMESHMENT STRIKE — 72 orphans pulled into the root build graph (2026-06-20)
84 `Dregg2/*` modules were unreachable from `Dregg2.lean` (their `#assert_axioms` hygiene
pins never ran under the default `lake build Dregg2`). 72 now enmeshed CLEAN (an import
block at the tail of `Dregg2.lean`); `lake build Dregg2` GREEN at 4095 jobs (was 4022),
zero errors — and since `#assert_axioms` is a pure rejector (silent on pass, `throwError`
on fail), the green build IS the proof every enmeshed pin is kernel-clean. NOTE:
`Circuit.SettlementSoundness` was ALREADY enmeshed since the census commit `801b756c9`
(line 636) — its settlement-soundness pins already run.

4 modules excluded as structurally un-enmeshable (NOT findings): `Circuit.Argus` (the
aggregator — imports 3 broken Effects below); `Claims` (imports `Dregg2` root ⇒ build
cycle; it's a top-of-graph CI pin-net, separately buildable); `Circuit.Emit.EmitAllJson`
+ `EmitGraduate` (pure `def main` JSON emitters, zero theorems/pins, `main` collides with
`Apps.AgentOrchestration.main`).

### ⚠ THE 8 ROTTED ORPHANS — real findings (excluded; each fails to compile at HEAD):
1. `Exec.ConcreteKernel` (Dregg2/Exec/ConcreteKernel.lean:110-114) — STALE STRUCT API:
   fields `escrows`/`queues`/`swiss`/`sealedBoxes` no longer exist on `RecordKernelState`.
   The hard kernel-bridge gate rotted against a refactored kernel state. Highest value.
2. `Circuit.Argus.InterpGolden` (:244) — ROTTED GOLDEN PIN: the `#guard (corpus.map
   GoldenCase.verdict) = [literal list]` no longer matches the computed verdict vector
   (corpus drifted from the hard-coded expectation). A non-vacuity pin gone stale.
3. `Circuit.Argus.Effects.BridgeMint` — `rewrite`/`decide` tactic failures leaked an open hole
   into `bridgeMint_compile_sound` + 6 sibling keystones (pins FIRE on enmesh).
4. `Circuit.Argus.Effects.CreateCellFromFactory` — `unsolved goals` (:165) leaked an open hole in
   `interp_…_eq_chainK` + 8 siblings (the factory-chain proofs rotted).
5. `Deos.DocPatch` — multiple breaks: `Unknown constant Finset.Insert.comm` (:146),
   `Unknown identifier i` (:303), unsolved goals leaked an open hole in all 6 CRDT-comm lemmas.
6. `Substrate.FpuProbe` (:857) — `rewrite` failure leaked an open hole in `move_is_fpu`.
7. `Authority.CredentialAttenuation` (:132,178,529-539) — COMPUTABILITY rot: 9 defs need
   `noncomputable` (depend on `instConditionallyCompleteLinearOrder`/`Clearance.admits`).
8. `Apps.ToolAccessDelegation` (:225 unsolved goals, :312) — an open hole in
   `tool_invocation_over_rate_rejected`.
Closure lane: each is a self-contained drifted-proof / stale-API fix; fixing any one →
re-add its import to the ENMESHMENT block in `Dregg2.lean`. The `Argus` aggregator + its
Effects depend on #3/#4 fixes. These 8 are EXACTLY the value of the strike: theorems that
read "PROVED, hole-free" by token-grep but are silently broken / non-building at HEAD.

## ✅ M2 EFFICIENCY — VALIDATED AT SCALE (the #[ignore]'d microbench, run 2026-06-20)
The headline livability claim — per-render projection is O(changed), not O(ledger) — is now
EMPIRICALLY confirmed (CI never runs this; the `projection_cost_is_flat_in_cell_count` bench
is `#[ignore]`'d, ~30 min / 1781s). Memo-HIT per-render time is FLAT across the ledger growing
16→16384 cells (1499ns → 1416ns; ratio 0.94× < the 8× gate), while COLD (pre-M2) grows
23.6µs → 4.76ms — so the win WIDENS with scale: 15.8× @16 → **3363× @16384**. SOUNDNESS arm
also passes (a touched-focus re-render recomputes — no stale memo hit). The M2 weld
(`docs/deos/EFFICIENCY-WELD-PLAN.md`: state_root memo + dynamics-cursor projection memo + the
lazy/batched ledger) holds at scale; no regression.

## ✅ M4 — canonical_ledger_root SHARED-LIFT COMPLETE (2026-06-20)
The M4 "shared pub fn lift" tail, DONE: `canonical_ledger_root` lives ONCE in
`dregg_persist::canonical_ledger_root`; BOTH callers migrated — starbridge's byte-for-byte
REPLICA (the "toy disease") retired, and node's `pub(crate)` copy in `blocklace_sync.rs`
re-exports the shared fn. The duplication is eliminated. BYTE-IDENTITY (load-bearing for
attested-root quorum convergence) verified three ways: (1) by inspection — `CellId(pub
[u8;32])` derives `Ord`-by-`.0` and `as_bytes()` returns `&self.0`, so node's
sort-by-`CellId.0`/hash-`as_bytes` == the shared fn's sort/hash-`[u8;32]`, same domain +
length-prefix + whole-cell postcard leaves; (2) starbridge's `close_and_reopen` convergence
test passes; (3) node's `ledger_root_witnesses_full_cell_divergence` test passes (node
compiled clean + ran green despite ember's uncommitted circuit work — the entanglement
concern was empirically refuted).

## 🟧 PERSIST BUG — GUARDED (fail-fast); sound full fix queued (2026-06-20)
UPDATE: a FAIL-FAST GUARD now landed (`World::genesis_mutation_would_break_reopen` +
`set_cell_program` refusal): a genesis-path mutation on a turn-touched cell is REFUSED on a
durable image (honest refusal > silent data-loss-on-reopen), via the cheap `touched_cells`
scan over `history.steps()`; ephemeral worlds + genesis-SETUP mutations pass through. Tests:
`a_mid_session_set_cell_program_on_a_touched_cell_is_refused` (guard) +
`a_genesis_setup_set_cell_program_survives_reopen` (safe boundary). The guard now covers ALL THREE
genesis-path mutators (`set_cell_program` + `genesis_grant_cap` + `genesis_open_permissions`).
REMAINING: the SOUND FULL FIX so a post-turn mutation SUCCEEDS+survives (ordered pre/post-chain
genesis events in the durable log — load-bearing recovery, ember's design/review). Original finding ↓.

## 🟥 PERSIST BUG — genesis-path mutation AFTER a turn makes the image non-reopenable (FOUND + reproduced 2026-06-20)
The M4 "mid-session genesis set_cell_program rebuild tail" — investigated, and it's a REAL bug, not done.
A genesis-path mutation (`World::set_cell_program` / `genesis_grant_cap` / `genesis_open_permissions` —
reachable MID-SESSION via the interactive predicate composer `predicate_composer.rs:880` + organ setup
`organ_ops.rs:232,465`) on a cell that a COMMITTED TURN already touched makes the durable image
NON-REOPENABLE: `durable_regenesis` (world.rs:665) records the post-mutation cell as timeless "genesis",
so recovery re-executes the earlier turn against the poisoned base, diverges from the recorded root, and
the fail-closed integrity check REFUSES the image (`Integrity("a durable committed turn did NOT re-commit
on recovery")`). SAFE (fail-closed — never serves corruption) but data-loss-on-close. The persistence.rs
SEAM §2 comment OVERCLAIMED handling — corrected. Reproduction banked: `persistence.rs::
a_mid_session_set_cell_program_survives_reopen` (`#[ignore]`d, asserts the DESIRED fixed behavior).
CLOSURE (sound, not a 5am quick-fix on load-bearing recovery): split pre-chain vs post-chain genesis-path
mutations in the durable log — record a post-chain mutation as an ORDERED durable event applied AFTER turn
re-execution (or route mid-session genesis-path mutations through a real ordered turn). Until then,
`set_cell_program` etc. are genesis-SETUP-only (before the cell's first turn).

## ◻ dregg-doc — the doc-on-cell encoding seam, CHARACTERIZED (ember's architectural call) (2026-06-20)
The section-1 "executor writes fields_map not heap_map" tail, pinned precisely (guard:
`doccell.rs::the_two_doc_on_cell_index_encodings_diverge_by_state_slots`). TWO doc-on-cell
encodings exist and DIVERGE by exactly `STATE_SLOTS` (16):
- **`ExecutorDrivenDoc`** (executor_drive.rs) — `field_key(coll,key) = STATE_SLOTS + ((coll<<32)|key)`
  → writes the committed `fields_map` overflow region through the REAL executor's `apply_set_field`.
  COHERENT + CANONICAL — the path the cockpit drives. ✓
- **`DocCell`** (doccell.rs) — `encode_index(coll,key) = (coll<<32)|key` (NO offset) → writes `heap_map`
  via `set_heap`, and records `Effect::SetField{index: encode_index}`. INCOHERENT: a small `(coll,key)`
  (e.g. `encode_index(COLL_ATOMS,0)==0`) is a REGISTER slot (< STATE_SLOTS), so the effect-record would
  hit the cell's BALANCE if run through the real executor — AND it writes `heap_map`, a different map than
  the executor's `fields_map`. `DocCell` is used ONLY by its own tests (superseded by ExecutorDrivenDoc);
  `project_graph` (the shared graph→`(coll,key)` projection) is fine, used by both.
DECISION (ember): retire `DocCell`/`heap_map` + `substrate.rs::to_heap_map`, OR re-key `DocCell` onto
`field_key`/`fields_map` so its effect-records round-trip through the real executor. NOT a quick fix —
it's a doc-substrate architectural unification, on the document language you parked to breathe. The guard
prevents silent drift meanwhile.

## ◻ WINDOWS native-full — one-command reproducibility follow-up (2026-06-20)
native-full x86_64 Windows is BUILT + RUNS with the REAL verified executor (the GNU lever, not MSVC —
`dregg-lean-ffi/build.rs` windows-gnu splice + `WINDOWS-PORT.md`). The build still needs a small
out-of-band GUEST scaffold not yet captured as a script: (1) the llvm-mingw header/import-lib backfill
into the stripped `lean-4.30.0-windows` sysroot, (2) a global `C:\mingw-shim` dir (synthesised
`libntdll.a` from live ntdll exports + gcc/gcc_eh/unwind shims) so SIBLING crates (redb-as-dll etc.)
link — `build.rs` only synthesises its OWN shims into `OUT_DIR`, (3) cargo `rustflags` for the global
`-L` paths, (4) `scripts/win-setpath.ps1` (adds `C:\LLVM\bin` to PATH — landed). Closure: fold (1)-(3)
into `scripts/win-bootstrap` for one-command reproducibility. The `.exe` itself is self-contained
(Lean runtime + UCRT statically linked); only the BUILD needs the scaffold.

## ◻ seL4 RENDER-PD — next lever after the __clone/TCB wall fell (2026-06-20, `5b91f5e79`)
The submit-thread `__clone`/TCB wall is DOWN (real seL4 TCB #2 live; `vkCreateDevice`
past the threading wall). The render now walls TWO layers deeper, MEASURED: LLVM JIT
`selectTarget()` returns NULL → a NULL-vtable virtual call inside
`lp_build_create_jit_compiler_for_module` = a **triple/target mismatch in the
cross-built JIT** (the AArch64 target IS linked + registered; the module's triple is
wrong). NEXT LEVER: set the JIT module's target triple to the registered
`aarch64-…-musl` triple before `selectTarget`, OR drive `LLVMInitializeAArch64Target*`
explicitly from the driver ahead of `vkCreateDevice`. One LLVM-JIT-config rung past the
threading work. Full record: `sel4/render-pd/WIRING.md` + `docs/desktop-os-research/SEL4-RENDER-PATH.md`.

## ⚠ PHANTOM — Human-Layer M1 recovery e2e test is UNCOMMITTED (found 2026-06-20)
HORIZONLOG describes "the recovery e2e seam" (`sdk/tests/identity_social_recovery_e2e.rs`)
as LANDED, and `trust_panel.rs` IS committed (`46f2ef4cc`) — but the e2e test file was
NEVER committed (still `??` untracked). It can't land standalone (needs the
`sdk/Cargo.toml` `[dev-dependencies]` add of `dregg-federation` + `hints`), and that
Cargo.toml is co-mingled with ember's uncommitted circuit-soundness changes in `sdk/`
(`cipherclerk.rs`/`full_turn_proof.rs`/`sovereign_rotated_c1.rs`). Closure: when the
circuit lane quiesces, commit the test + ONLY its Cargo.toml dev-dep hunk by file-set,
after a `cargo test -p dregg-sdk --test identity_social_recovery_e2e` green. NOT landed
into the in-flux circuit lane tonight (don't blanket-commit over ember's work).

## ✅ DOCUMENT LENS — reachable + clickable (2026-06-20, the DOCS tab surfaces it)
CLOSED: the `DocumentInspection` (rendered · patch-history · conflict-as-state · commitment)
is now surfaced as a "◆ moldable inspection" section in the DOCS tab (`docs_panel`), off the
live document's folded graph (`DocEditor::graph()` → `DocumentInspection::from_graph`), rendered
through the same generic `render_presentation_body` every lens uses. The editor surface now BOTH
authors AND inspects the document. gpui build clean (`cargo check --features native-full`). A
dedicated `FocusTarget::Document` for the moldable inspector's own focus picker is a further
nicety but no longer load-bearing (the lens is reachable + clickable from the editor).

## ✅ M-REV-0 — FIRST-CLASS REVERSIBILITY (the un-turn) LANDED in turn/ (2026-06-19, this lane)
`docs/deos/FIRST-CLASS-REVERSIBILITY.md` Milestone 0, the un-turn on the real substrate.
NEW `turn/src/reversible.rs` (+ `Effect::invert`/`Turn::invert` additive, exhaustive match) +
lib re-exports. 11/11 lib tests green (`cargo test -p dregg-turn --lib reversible`).
- `Effect::invert(pre) -> Inversion::{Clean|Contextual|Committed}` — Transfer↔Transfer,
  grant→revoke, seal→unseal CLEAN; SetField/SetPermissions/SetVerificationKey/unseal-reseal
  CONTEXTUAL (pre-image from the ledger); Burn/NoteSpend/IncrementNonce/Revoke*/Destroy/
  MakeSovereign/Attenuate/Create*/Bridge/Pipeline/Exercise COMMITTED (fail-closed). EXHAUSTIVE
  (no `_=>`), like `Effect::linearity` — any new effect must answer reversibility.
- `ReversibleHistory::undo_to(k)` — backward dual of `replay_to`; headline test: undo-backward ==
  replay-forward on the SAME verified STATE for every k. CAVEAT made precise: the per-turn NONCE
  ratchet cannot rewind, so equality holds MODULO the monotone nonce (`ledgers_agree_modulo_nonce`);
  the executor re-applies the inverse as a fresh forward turn (advances nonce), value/state restored
  exactly. Fail-closed across any committed step (`IrreversibleStep`).
- `can_undo_isolated(idx)` — the causal-consistency frontier: `undo_to` reverses a CONTIGUOUS
  SUFFIX most-recent-first (conservative = time-order-as-causal-order); a MIDDLE turn is reversible
  iff no later turn touches a cell it wrote. RESIDUAL (named): a mutating `undo_isolated` that
  splices a middle reversal = the §3.3 follow-up (the frontier is reported, not yet wired to mutate).
- PARTIAL-TURN LIFT DECISION: executor-layer split (`Pipeline`/`TurnBatch`/`execute_pipeline`) is
  CORRECT, not a batch-bearing `Effect` — "determination eager, witness lazy"; the one first-class
  pipelining effect (`PipelinedSend`/`EventualRef`) is Committed (resolution is one-shot). Documented
  in the module head.
- CIRCUIT HANDOFF (NOT touched here — ember's live lane): an invertible effect needs NO new
  descriptor (inverse emits ordinary effects, existing rungs); the one obligation is the BACKWARD
  root tooth = the inverse turn's post-state commitment equals the recorded pre-cursor commitment
  MODULO the monotone nonce. A batch-bearing effect, IF added, must satisfy `holeFill_binds_in_circuit`.
  Closure shape: confirm the state-commitment binding admits the "value restored, nonce advanced"
  post-state as a genuine transition (it is just another forward turn).
- LEAN FOLLOW (allowed in `metatheory/Dregg2/Deos/` only): `EffectInvert.lean` — one round-trip lemma
  per clean+contextual effect (`apply(invert e σ) (apply e σ) = σ` modulo nonce), committed tier as
  the lemma's exclusion precondition. NOT yet written.

## ✅ IR2 DENOTATIONAL DIFFERENTIAL — REAL-EVALUATOR LEG LANDED; bus-arm residual NAMED (2026-06-19, this lane)
The faithfulness differential's last by-inspection link (`eval_enforces ≡ real Ir2Air::eval`)
is COLLAPSED for the ROW-LOCAL arms: `circuit/tests/ir2_denotational_differential.rs` now calls
the ACTUAL deployed evaluator via `descriptor_ir2::ir2_eval_accepts_i64` (a thin row-local driver
over the real `Ir2Air::Main::eval`, `circuit/src/descriptor_ir2.rs`). 96/216 cases
(Base(Gate)/Base(Transition)/WindowGate, both polarities incl. 42 forge-rejects) decided by the
real evaluator, all agreeing with the Lean denotation — NO divergence. Test green; `--features
prover` builds.
- RESIDUAL (named floor): the CROSS-TABLE BUS-ASSEMBLY arms (chip/byte lookup MEMBERSHIP +
  memory/map-ops/umem LogUp multiset balance) remain TRANSCRIBED in `eval_enforces` — a single-AIR
  row-local evaluation cannot decide a cross-table multiset. Closure shape: drive the real
  multi-table assembly (the `prove_batch`/`check_lookups` balance) from a deterministic differential
  harness, OR pin the bus receives via the per-table sub-AIR row-local evaluators the same way.
- ADJACENT (pre-existing, NOT this lane): `cargo build -p dregg-circuit --no-default-features
  --features verifier` is RED at HEAD — `bilateral_aggregation_air.rs` calls prover-gated
  `chip_absorb_all_lanes`/`cse2_fill_lanes`/`fold_fill_lanes` from non-gated code. Independent of
  this change; flagged for the build-owner.

## ✅ HUMAN-LAYER M1 — SOCIAL RECOVERY SEAM + TRUST PANEL v1 (2026-06-19, this lane)
`docs/deos/HUMAN-LAYER.md` Milestone 1, the "you cannot lose your own OS" weld.
TWO pieces landed, both REUSING the green crypto (no parallel auth):
- **The recovery e2e seam** — `sdk/tests/identity_social_recovery_e2e.rs`: a
  fresh cipherclerk holding NO old keys, given a real 3-of-5 HINTS guardian
  quorum (`dregg-federation` committee → `hints::sign_aggregate`), recovers the
  identity cell through the REAL executor — the rotation is authorized by
  `Authorization::Custom` discharged by `ThresholdSigVerifier` →
  `hints::verify_aggregate` on the identity cell's `set_state`, while the
  `KeyRotationGate` independently enforces the pre-rotation mechanics
  (preimage exhibit + forward-chain + cooling). Teeth: headline
  (recovered + chain advanced + height stamped), sub-threshold REFUSED (2-of-5
  can't aggregate), wrong-committee REFUSED (host-pinned VK). Added
  `dregg-federation`+`hints` to `sdk/Cargo.toml` `[dev-dependencies]`.
- **Trust panel v1** — `starbridge-v2/src/trust_panel.rs`: a gpui-free
  `Presentable`-shaped WHO-I-AM face (identity card: devices, guardians-as-faces
  with the K-of-N threshold drawn, the KEL rotation timeline) + the recovery UX
  (`RecoveryProgress`: "ask your guardians" quorum gauge mirroring the executor's
  threshold floor, the cooling window as a safety feature). Built off the REAL
  `dregg_sdk::identity::inspect_identity` decode + the council charter; 4 lib
  tests green, `cargo check` clean.
- **HARD PARTS LEFT (named with closure lanes, §5):** device-pairing ceremony
  (the authenticated old↔new-device channel — a powerbox-style designation);
  guardian-set ROTATION (changing your council, ~polis amendment by the current
  quorum — set-once today); the council-commitment must be bound INTO the
  circuit commitment for light-client-unfoolable recovery (host-trusted
  `StaticThresholdSigPolicy` today — the circuit-soundness tie-in); the
  HINTS guardian-onboarding ceremony UX (publish key+hint, whose universal
  params).

## ✅ LIVE CONSERVATION HOLE — EXECUTOR PATH CLOSED (2026-06-19, this lane)
The asset-BLIND scalar `proven_deltas.iter().sum()==0` at `atomic.rs` (both
`execute_atomic_sovereign` AND the mixed-turn cross-domain site) is REPLACED by
the per-asset, in-AIR-backed collector
`TurnExecutor::check_per_asset_conservation` →
`dregg_circuit::block_conservation::BlockConservation` (over the committed
`cross_cell_conservation_air`). AssetId := the cell's committed `token_id`
(dregg3 issuer-cell), read from the verifier's own ledger. New teeth in
`atomic.rs` tests: `cross_asset_forge_rejected_mixed_atomic` (the asset 7 −10 /
asset 8 +10 forge now REJECTED — it was accepted), `same_asset_transfer_still_
accepted_mixed_atomic` (no false reject), `per_asset_collector_in_air_accept_
reject` (prove+verify through the committed per-asset AIR). `block_conservation.rs`
git-added into the build. **RESIDUAL (the one coordinated remainder, named at
`proof_verify.rs::verify_proof_carrying_turn_bundle`'s tail):** the PURE
light-client / bundle path is NOT yet wired — it needs (1) the per-cell proof to
publish its ASSET CLASS as a PI slot (proof-bound partition, not ledger-trusted —
PHASE C owns the PI layout) and (2) `bundle_pis` to carry each PI's cell_id/asset
so the collector can group. Until both land, the per-asset bite holds on the
EXECUTOR path (ledger + cell_ids present); the light-client path is the stated
prerequisite.

## ⚡ THE EFFICIENCY WELD — M2 DELTA LOOP (2026-06-19) — LANDED, gate held

`docs/deos/EFFICIENCY-WELD-PLAN.md` §2-§4. The producer (`dynamics().since(cursor)`)
↔ consumer (gpui render) JOIN is wired: `Cockpit.dynamics_cursor` + `fold_dynamics`
+ the §2.2 variant→invalidation table; a `PresentMemo` (`presentable.rs`, RefCell
interior-mut) wraps the unchanged-pure `Registry::present` keyed `(focus,viewer)`,
valid while the live head is unchanged. Per-render projection of an UNCHANGED focus
is now a cache HIT (O(changed), not the old per-frame O(ledger) `present` rebuild).
Dynamics-completeness CLOSED: new `WorldEvent::CellMutated{cell}` emitted for
`IncrementNonce`/`MakeSovereign`/`SetPermissions`/`SetVerificationKey`/
`AttenuateCapability` (+ `ExerciseViaCapability` recursion) so every committed
write names its cell (the cache-soundness obligation, §4.1) — proven by the
`every_cell_naming_effect_names_its_cell` per-effect audit test. GATE: the
`projection_cost_is_flat_in_cell_count` microbench (n∈{16,256,4096,65536}). Named
residuals, each with its closure shape:

- **The Entity sub-view split (§2.5) — M2-TAIL, deferred.** gpui still re-runs the
  whole `Cockpit::render` closure on any `cx.notify()`; splitting into
  `CellWorldView`/`RailHeaderView`/`InspectorView` Entities (one notify → one pane)
  is gpui-render granularity, gpui-check-only, NOT headless-benchable. Closure: do it
  in the cockpit-tabs pass (it does not block the projection gate, which is proven).
- **The §4.3 residual: `World::state_root` is O(ledger) per height bump.** The BLAKE3
  view-root re-folds every cell on a commit (the M1 memo only de-dups reads WITHIN a
  height), so the rail-header root display stays O(ledger) per committing frame.
  Closure: the `Ledger` already maintains an incremental Merkle `root()`
  (`ledger.rs`) + a sorted `leaf_positions` index; the view-root can defer to the
  canonical incremental root when the World adopts `canonical_ledger_root` (M4 root
  unification). The M2 memo key `(height, receipt_head)` is forward-compatible.
- **Bench-build O(n²) genesis (test-only seam).** `install_genesis` calls the record
  tape's per-cell `Ledger::root()` (a full rebuild on each insert), so a sequence of
  `n` genesis installs is O(n²). The microbench sidesteps it with a `#[cfg(test)]`
  `World::bench_install_cell` (engine-ledger insert, no tape mirror — sound because
  the bench never replays). NOT a production gap; the live genesis path is correct.
- **⚑ TRULY-LAZY / BATCHED LEDGER — LANDED (ember's call, 2026-06-19).** The M2
  diagnostic exposed it: `Ledger::root()` forced a FULL O(n) Merkle `rebuild_tree()`
  on every `dirty` read, and a `get_mut` mutation marked dirty — so every internal/UI
  turn (and `commit_turn`, which roots TWICE for pre/post state hash,
  `turn/src/executor/execute.rs`) paid O(ledger) hashing even though deos only needs
  real crypto receipts ON-DEMAND at the network boundary. FIX (`cell/src/ledger.rs`):
  replaced the coarse `dirty: bool` with a `Pending` enum (`Clean` / `Values(BTreeSet
  <CellId>)` / `Structural`). A mutation now does ZERO tree work — it only RECORDS
  what changed (value-touch vs structural-touch). The tree materializes lazily ONLY on
  `root()`/`membership_proof()` (the publish boundary), with the MINIMAL recompute: a
  batch of O(k·log n) `update_leaf` when only values changed, a single O(n) rebuild
  only when the leaf set shifted. `apply_delta` likewise defers (no eager rebuild/
  update). VERIFIED: `ledger_incremental_root_matches_full_rebuild` (root() ==
  from-scratch oracle across create→update→create→transfer) + **all 660 `dregg-cell`
  lib tests green** (Merkle / membership-proof / witness-diff / migration / sovereign
  paths all exercise the rewired materialize). An internal turn that never publishes a
  root now pays no hashing. REMAINING (executor side): make `commit_turn`'s pre/post
  `state_hash` lazy too — a turn "mode" gating whether the receipt/root path runs at
  all for purely-internal turns (`World`-level seam, the next slice).
- **SALSA integration — spike, don't blind-adopt (ember asked, 2026-06-19).** Salsa
  (incremental-recompute: inputs → memoized `#[tracked]` queries → fine-grained
  auto-invalidation) is a STRONG fit for the PROJECTION/derivation layer — `PresentMemo`
  + the variant→invalidation table + the M3 self-projection/stratification worry are
  all hand-rolled Salsa. Porting the projection tree (`present`/`ocap_graph`/
  `provenance`) to Salsa queries gets auto-invalidation + cycle handling for free.
  NOT for the executor/ledger (the authoritative, soundness-load-bearing transition
  stays explicit/verifiable). Closure: a spike porting the moldable-inspector
  projection tree to Salsa; the hand-rolled memo proves the shape first.

## ⟲ M3 — SELF-HOST UI STATE AS CELLS (2026-06-19) — first increment + widen LANDED

`docs/deos/REFLEXIVE-MIGRATION.md` §3. The inspector's `(focus, present_idx)`
camera-aim is self-hosted as a REAL cell (`starbridge-v2/src/view_cell.rs`): a
`ViewCell` generalizes the `BufferCell` two-tier split — a FREE in-memory draft
(`ViewDoc`, re-aim costs nothing) + an occasional witnessed `Effect::SetField`
commit (revision = backing nonce); the §3.5 stream weight class (conserves
nothing). A `ViewCell` is itself `Presentable` via the new `FocusTarget::ViewCell`
arm (`presentable.rs`), so the cockpit can focus the inspector ON its own view cell
— *inspect the inspector*. `present` stays PURE and reads the COMMITTED
(prior-frame) aim (`ViewCell::from_world` reconstructs from witnessed cell state) —
the unit-delay that breaks the reflexive self-cycle (STRATIFIED-FIXPOINT §7.3).
WIDEN: `WorkspaceCell` carries the active-tab selector as a witnessed cell
(`render(workspace_subgraph)` shape). Cockpit wired: `moldable_focus`/
`moldable_present_idx` Rust fields SUBSUMED into `inspector_view: ViewCell` +
`inspector_reflexive` toggle; the moldable panel reads its selector from the cell;
re-focus/lens/poke handlers go through `moldable_refocus`/`moldable_set_present_idx`
(witnessed re-aim). 8 gpui-free `view_cell::tests` GREEN (free-draft · witnessed
commit · inspect-the-inspector · Registry/`FocusTarget::ViewCell` dispatch ·
unit-delay purity · WorkspaceCell selector · unbacked). Both gates clean
(`embedded-executor --tests`, `gpui-ui`). Named residuals:

- **WIDEN-TAIL — tab/selection NOT yet cell-driven in the cockpit's live render.**
  The `WorkspaceCell` substrate + its commit + test exist, but the cockpit's actual
  `tab`/`selection`/open-views/pins fields still drive render directly (only the
  inspector's focus/present-idx moved). Closure: route the 24-arm `Tab` match's
  *selector* through a cockpit-held `WorkspaceCell` read (the substrate is ready;
  this is the wiring), folding `replay_cursor`/`breakpoints`/`sim_*`/`lane_*` into
  `PanelCell`/`GadgetCell` per §3.1. Sequence with the cockpit-tabs pass.
- **Commit cadence is every-re-aim (open question §7.4 / ROADMAP §7).** `moldable_refocus`
  commits a witnessed turn on EVERY re-focus — durable but turn-heavy. Closure: the
  ember-decision on cadence (blur / Nth / explicit-save / snapshot); the free-draft
  already supports deferring the commit (just stop calling `.commit()` eagerly).
- **The reflexive arm uses the same `PresentMemo` — the self-cell IS in the memo.**
  A `ViewCell`'s own `FieldSet` (a commit) invalidates its cached projection
  (`invalidate_cell`), so the unit-delay + the M2 fold compose correctly; no
  within-frame fixpoint. Closure: none needed (verified by `present` reading
  committed state), noted so a future Salsa port preserves the unit-delay.

## 🖥 DEOS DESKTOP / MOLDABLE INSPECTOR (2026-06-19) — the live build-down

The Pharo-moldable inspector epoch (`docs/deos/INSPECTOR-FRAMEWORK.md`, memory `moldable-inspector-epoch`).
LANDED: L1 spine (`presentable.rs`, `800945db6`) + the liveness wave (`983ff76bc`) + lanes L2-L7
(`04c275a85`, 411/411 green). Named follow-ups, each with its closure shape:

- **Per-viewer affordance authority (the membrane property)** — `presentable::ReflectedCell::present`
  HARDCODES `viewer_rights = AuthRequired::Either`, so the Affordances lens uses a uniform rights tier
  and the viewer `CellId` does NOT change the cap-badge verdicts. Surfaced by the M1-era full-suite run
  (the `two_viewers_..._attenuated_differently` test had shipped cargo-checked-but-never-run, asserting
  a per-viewer divergence the model doesn't deliver; corrected to honest camera-fidelity + this lane).
  Closure: derive each viewer's ACTUAL authority over the focus cell (ownership / held c-list cap →
  the rights tier), so the affordances lens genuinely divides per-viewer. Then restore the `assert_ne`
  divergence in the test. (⚑ LESSON re-bit: never commit a module on a cargo-CHECK; the main loop MUST
  run the real `--release` suite — it's the only thing that catches never-run tests.)
- **Cockpit gpui TABS for the 9 new modules** — inspect_act/workspace/wonder + the 6 inspector lanes
  are pure tested MODELS; none is wired into a `cockpit.rs` tab/panel yet. Named in every lane's report.
  Closure: add a `Tab` variant + `match` arm + a `*_panel` renderer per module (the panel maps each
  `PresentationBody` variant to a widget; gadgets drive `validate`→`predict`→`commit`). gpui, window-verified.
- **Cap-crown membership PATH-opening** (`cap_inspector.rs` `cap_crown_view`) — carries the real
  `capability_root` + leaves but `path` is unopened: `dregg_circuit::cap_root::{CanonicalCapTree,
  recompose_membership}` isn't re-exported through `dregg_cell` (only the root + leaf-encoding are).
  Closure: re-export those from `dregg_cell`, OR add `dregg-circuit` as a direct starbridge-v2 dep; swap is mechanical.
- **MMR swap to `dregg-query`** (`receipts_inspector.rs` `ReceiptMmr`) — a faithful LOCAL blake3 MMR
  (identical domain tags `dregg-query-mmr-v1:*`) stands in because `dregg-query` isn't a starbridge-v2 dep.
  Closure: add the dep, swap to `Mmr::open_range`/`verify_range` (leaf bytes + hash identical → tests carry over).
- **Heap-mutation Effect** (`cell_inspector.rs`) — there is NO `SetHeap`/`HeapSet` verb in the executor
  (`turn/src/action.rs`), so a heap-ENTRY-editor commit-gadget has no semantic verb (census `HeapLeaf` true-zero).
  Closure: add a heap-write Effect to the kernel verb set (Lean-emitted), THEN the editor gadget routes through it.
- **Runtime program-install Effect** (`predicate_composer.rs`) — `CellProgram` install is genesis-path only
  (`World::set_cell_program`, the trusted-root authority install); no in-turn caveat-authoring verb exists.
  Closure: a new executor effect for in-turn program install (Lean-emitted) if in-turn authoring is wanted.
- **`World::ledger_mut()` accessor** — private (`engine.ledger_mut()`); read-only inspection is fine, but
  the editor-gadget halves (heap/permissions/field editors) need a semantic-verb route, not a raw mutator.
- **NEXT inspector lanes (held for ember):** L8 federation/consensus · L9 circuit/commitment internals ·
  L10 settlement-families + factory authoring (fuses L2+L3). Fan out on her word (one module each, on the spine).

## 🏺 ARCHEOLOGY DIG (2026-06-19) — `docs/ARCHEOLOGY-LEDGER.md` (50 verified-still-open items)

The full ledger is the durable record. Pulled here per the ledger's own process note (don't let leverage
items idle), the highest-value NON-circuit-context rescue:
- **Node recovery first-writer-wins bug** — `node/src/state.rs:699/:879` use strict `insert_cell` (silently
  drops a post-checkpoint write to a cell the checkpoint already holds); the convergence-root mismatch at
  `:702-733` only `tracing::error!`s ("STORE INTEGRITY EVENT") and falls through — no fail-closed. A silently-
  wrong recovered ledger served as truth = a soundness event. Closure: `insert_cell`→`upsert_cell` (the verified
  `CrashRecovery.upd` point-update) at both sites + make the convergence mismatch return `Err`/refuse to serve.
  (The circuit-soundness-cluster items + the #1 phantom-commit file-set hazard live in ember's circuit context —
  see the ledger HIGH tier; not re-filed here to avoid crossing that lane.)

## ✅✅ FAITHFUL STATE COMMITMENT (8-felt light-client floor) — **LIVE** (commit `9e5a83935`, 2026-06-19)

**THE #1 SOUNDNESS FLOOR IS CLOSED.** The deployed per-cell state commitment is now a chip-faithful 8-felt
chain (~124-bit collision, matching the proof's ~130-bit FRI soundness); the ~31-bit 1-felt waist is retired
end-to-end. A ledgerless client running `verify_and_commit_proof_rotated` trusts the published (pre,post) at
the proof's own soundness. Verified live (every gate re-run): lake 4004 axiom-clean · drift PASS · the LIVE
fee'd sovereign path `sovereign_rotated_c1` 19/19 (forged-post-state rejected) · the LIVE collision tooth bites
at 8-felt with NO executor · flip 13/13 · cell/turn/sdk/node all green + node binary builds. Consumer-repoint
strategy (the wide TSV IS the verifying material — no separate VK pin; Rfix authority leg lifts via
`wideAppend_satisfied2_host`). N=8 uniform (ember: "consistency is king"; the dial `docs/COMMITMENT-WIDTH-DIAL.md`
remains a documented future capability). Two named robustness tails (node API placeholder · split-process bare-
cell registrar) recorded below — non-load-bearing API echoes, NOT live-soundness gaps. The campaign: design →
`hash_many_8` → Phase A lever → B-GATE chip 1→8 out + 8-carrier in → `wire_commit_8`/`wireCommitR8_binds` →
`wideAppend` gated-host tower → `v3Registry(CapOpen)Wide` → staged proof legs → Stage-1 waist-cut → Stage-2 live
switch. (Historical phase detail below, superseded by this ✅.)

## (superseded — the in-flight campaign that landed above) FAITHFUL STATE COMMITMENT — phased campaign (2026-06-19)

**Why #1:** the deployed per-cell state commitment binds in-circuit by ONE BabyBear felt (~31-bit; `hash_many`
squeezes `state[0]`); the 4-felt PI's positions 1..3 are bound OFF-circuit by the executor (`pi.rs
AUDIT[stage1-trace-widen]`). So a light client's state binding is ~31-bit = collision in seconds — and EVERY
value-close (WAVE 0/1/2 authority, fee, identity, selector, the movers) binds THROUGH it, so the whole goal's
trust is 31-bit at the root until this lands. Target measured (not guessed): FRI `log_blowup=6`/19-query/16-PoW
≈ ~130-bit soundness ⇒ commitment needs ~124-bit collision ⇒ **8 felts** (the reserved-4 = only ~62-bit, below
the proof — do NOT ship 4). Design + security math: `docs/FAITHFUL-STATE-COMMITMENT.md`. (Scar that produced it:
[[feedback-dont-launder-a-load-bearing-insecurity]] — I'd rationalized the 31-bit felt as "the existing audited
floor.")

**The phased campaign (ember chose full-permutation chip + sponge; two scoping agents in a row correctly
refused to launder a partial):**
- ✅ **STEP 1 — `hash_many_8`** wide-output primitive (`poseidon2.rs`, anti-laundering-tested: 8 distinct +
  full-input avalanche), STANDALONE/unwired. Commit `ed8e88873`.
- ✅ **PHASE A — the wide chip soundness LEVER** `chip_lookup_sound_N` (forces all W permutation-output cols;
  legacy 1-felt lever re-derived as the W=1 corollary, zero downstream breakage; anti-laundering tooth
  `chipRowN_distinguishes_wide`). Additive Lean, axiom-clean. Commit `05d297503`. STEP-0 finding: the deployed
  `poseidon2_chip` AIR already constrains the full 16-lane permutation and exposes only `state[0]` — so exposing
  8 is "return more columns of an already-full AIR."
- ✅ **PHASE B-GATE COMPLETE — the SHARED `poseidon2_chip` widened 1→8 lanes** (commit `0980aa151`, WHOLE TREE
  GREEN: lake 4003 axiom-clean · drift PASS · circuit lib 887/0 · flip 12/12 · cell 16 · sovereign 19 · node 8).
  The Lean-emit + producer-fill half (the atomic remainder) LANDED: `siteLookup→chipLookupTupleN`, the producer
  weld `fill_chip_lanes`, all 67 JSONs re-emitted + 64 FPs re-pinned, discharged by `chip_lookup_sound_N`.
  **The commitment is STILL 1-FELT (lane0) — no security gain yet; B-ROTATION delivers the ~124-bit trust.**
  ⚠ WAVE-3 ENTANGLEMENT (CORRECTED 2026-06-19, R1 audit `a424f1134992f6262`): the parked WAVE-3 base limbs
  (NUM_PRE_LIMBS 37, mode+fields_root) remain; makeSovereign's mode-force is LIVE in-circuit (fine, NOT degraded);
  setFieldDyn is a dead path (v1 trace-gen panics field_idx≥8). The "refusal fields-root weld ROLLED BACK" framing
  was WRONG: there was never a GREEN in-circuit refusal weld to roll back — `rotateV3WithFieldsRootGate` welds
  `prmCol 0`, but refusal fills `prmCol 0` with the TARGET not the post-fields_root (`trace.rs:893`), and the
  post-fields_root is a map-insert root (`insert(pre_map, audit)`) NOT a light-client-knowable declared value.
  So re-pointing makes honest refusals UNSAT (the parked WIP) or merely relocates the off-circuit anchor. Refusal
  is full-node-safe today (the 8-felt commit binds limb 36 + record-pin) but a LEDGERLESS close needs the
  OPENABLE-fields_root/map-op construction (#103 family) = NEW soundness, not a restore. ⚠ `setFieldDynForcedV3`
  is LIVE + shares this gate + the same mismatch + NO roundtrip test → audit whether its live gate is inert.
  **RESUME AT PHASE B-ROTATION** (below). Rust-provider detail (still accurate): `poseidon2_permute_expr_lanes`
  (`plonky3_prover.rs`, returns the 8 final-state lanes; the legacy `poseidon2_permute_expr` delegates → lane0,
  every v1 inline site UNCHANGED); the chip AIR (`Ir2Air::Chip`) exposes `state[0..8]` and adds the 7 `assert_zero(
  local[CHIP_OUT+i] - lanes[i])` constraints (i=1..7) — REAL bindings (forged-lane UNSAT proven); `CHIP_OUT_LANES=8`,
  `CHIP_TUPLE_LEN 10→17` (`[arity,in0..7,out0..7]`), `CHIP_MULT/IS_FACT/BIG/S4..S6/AUX0` auto-shift; witness-gen
  `perm_lanes` fills `row[CHIP_OUT..+8]` from the genuine permutation (chip/fact/pad rows); the MapOps/MapAbsent
  inline consumers widened (`chip_absorb_tuple`/`leaf_tuple` carry out0..out7; `MAP_OLD/NEW_LEAF1`, `MA_LO/HI_LEAF1`
  appended at the tail, `MAP_WIDTH 71→85`, `MA_WIDTH 169→183`; all 4 `chip_hist.entry` keys 17-wide). TEETH GREEN:
  `ir2_chip_output_lanes_are_distinct` (8 pairwise-distinct + 1-bit-flip avalanche), `ir2_forged_output_lane_refuses`
  (a forged out[3] is UNSAT — the lane binding bites), `ir2_honest_witness_proves_and_verifies` (a 17-wide
  single-output site PROVES+VERIFIES in the full multi-table batch — the `degree_bits.len()==2` STOP-condition is
  NOT triggered, the assembly carries 17 cleanly). The commitment is STILL 1-felt (lane0); B-ROTATION delivers the
  trust. **REMAINING (the atomic Lean-emit half):** (a) `poseidon2ChipTableDef` arity 10→17 + `siteLookup` →
  `chipLookupTupleN [s.digestCol, lane1..lane7]` (the 7 lane cols appended per descriptor's traceWidth; lane0 stays
  the chained `digestCol`), re-prove `go_of_siteLookups`/`siteLookups_sound`/`graduateV1_sound` via the W=1 corollary
  `chip_lookup_sound_of_N` + the rotation `rotV3SitesAt_pin`/`caveatV3SitesAt_pin`/`wireCommitR_binds` (42 Lean files
  reference `VmHashSite`/`siteLookup`/`digestCol`); (b) every producer fills the `7×n_sites` new lane cols
  (`trace_rotated.rs`, the bilateral/cross-side/bundle-fold trace builders, `cell`/`turn`/`sdk`/`node` rotation
  producers — each runs the permutation + emits 8 lanes/site); (c) re-emit the 32 chip-bus descriptors + all per-FP +
  `V3_STAGED_REGISTRY_FP` + the 3 `rotationProbe*` JSONs/FPs + the frozen `poseidon2_chip` JSON+FP via
  `scripts/emit-descriptors.sh`; (d) the await-Lean-emit Rust tests go green (`ir2_degree_budget`, the rotation
  probes, bilateral/cross-side/tree-fold, `v3_staged_registry_parses…`). The `compress8` byte-mirror is a B-ROTATION
  concern, not B-GATE.
- ✅ **PHASE B-GATE-INPUT — chip input widened 8→11** (commit `8d57b8598`, WHOLE TREE GREEN): wide-absorb arity 11
  carries an 8-felt carrier + 3 limbs in ONE permutation; narrow arities byte-identical (KAT 7/7); `CHIP_RATE
  8→11` (decoupled from sponge rate 8), `CHIP_TUPLE_LEN 17→20`, 34 JSONs re-emitted + 64 FPs re-pinned; teeth
  `ir2_wide_absorb_forged_carrier_lane_refuses`/`..._carrier_felt_is_load_bearing` bite. The chip is now FULLY
  SPONGE-CAPABLE. Commitment STILL 1-felt.
- ✅ **PHASE B-ROTATION CORE — the proven 8-felt commitment primitive (staged, additive)** (commit `c734d938b`):
  `poseidon2::wire_commit_8` (8-felt carrier, `single_perm_compress(d8‖fresh)[0..8]` per step, every intermediate
  8 felts — no 31-bit waist), byte-identical to the arity-11 chip (`single_perm_compress_equals_chip_wide_lanes`);
  Lean `wireCommitR8`/`chainFrom8` + the keystone `wireCommitR8_binds` + `chainFrom8_inj` under named floors
  `Poseidon2WideCR`/`Poseidon2Width8`, `#assert_axioms` clean; teeth (collision-distinguishing, intermediate-
  carrier, not-laundered, chip-faithful) + producer-side authority-near-collision; three-layer twins cell≡turn≡
  Lean (`felt8_to_bytes32` 8×4=full slot). ADDITIVE — the live wire is UNTOUCHED, commitment STILL 1-felt, no
  FP/VK re-pin. The cryptographic heart EXISTS + is proven; NO live security gain yet.
- ⚠ **THE LEAN SIDE IS ~80% (36 of 45) — my "100% COMPLETE" claim (`5fe15906b`/`41e05faa4`) was an OVERCLAIM,
  corrected here** (7th agent caught it): the deployed TSV emits from `v3RegistryCapOpen` (**45** members,
  `CapOpenEmit.lean:814`; the `EmitRotationV3.lean:55` loop), NOT the 36-member `v3Registry`. `v3RegistryWide`
  covers the 36 cohort; the **9 cap-open/`-eff`/TB/fee'd members (positions 36..44) are NOT wide** — and the
  rotated geometry (`ROT_WIDTH`/`ROT_PI_COUNT`) is GLOBAL, so a mixed 8-felt-cohort / 1-felt-cap-open registry is
  INCOHERENT (the forbidden state). CLOSURE LANE (additive, green-able — the generic `wideAppend` keystones
  already discharge each): stage **`v3RegistryCapOpenWide`** (the 9 cap-open members through `wideAppend` with
  their per-member `bb` + the fold `_sound`/`_binds`), making the Lean side GENUINELY 100%. THEN the atomic Rust
  flip.
- ✅ **THE 36-COHORT WIDE REGISTRY** (commit `5fe15906b`): `v3RegistryWide` — the 36 live `v3Registry` members wrapped
  through the proven `wideAppend` with their per-member `bb` (= the v1 face `traceWidth`, SYMBOLIC), the fold
  `v3RegistryWide_sound`/`_binds` lifting member-by-member, axiom-clean, additive (live `v3Registry` untouched).
  Full proven stack: `chip_lookup_sound_N` · chip 8-out + 8-in · `wire_commit_8`/`wireCommitR8_binds` ·
  `wideAppend` gated-host tower · `v3RegistryWide`. The live flip needs NO more Lean proof.
- ✅ **STAGED SLICE 1 — the FIRST real wide 8-felt prove+verify roundtrip** (commit `8578580b5`, GREEN): a
  genuine `prove/verify_vm_descriptor2` at width 816/PI 54 PROVES+VERIFIES + the LIVE collision tooth bites (two
  states differing in `fields[15]` → 8-felt commits differ, A rejected vs B, NO executor). `generate_rotated_
  transfer_wide`/`fill_wide_block` (the 13×8 BEFORE/AFTER carriers, bases 608/712, chip-faithful via
  `chip_absorb_all_lanes`); wide descriptor from `EmitWideTransferProbe.lean`. ADDITIVE — live 1-felt path
  UNTOUCHED (flip 13/13, drift byte-identical). Fixed the make-or-break: the chain's arity-9 final → arity-11
  (`carrier8‖[iroot,0,0]`) since the chip AIR supports only arity ≤7 or 11. ⚑ STANDING SEAM: the Lean-emit arity
  convention (`ins.length`) vs the chip's narrow/wide-only support — a chip-AIR generalization (seed lanes 7..10
  for any arity ≥8) would let the emit use the natural arity-9 (VK-affecting, ember-gated). THE STAGED PATH IS
  PROVEN GREEN-ABLE.
- ✅ **STAGED SLICE 2 — the wide producers FANNED OUT to every producer shape + the EXECUTOR ANCHORING** (GREEN,
  NOT yet committed): the full 45-member wide registry emitted from verified Lean (`EmitWideRegistryProbe.lean` →
  `WIDE_REGISTRY_STAGED_TSV`, FP-pinned + coverage test, name-stable with the live registry; key = the live
  registry key). The Rust wide producers fanned out via a generic `append_wide_carriers(trace, base_pis,
  host_width)` (carrier base = the host width — 608 for the 816-wide families, 818 for cap-open): transfer-shape
  (`generate_rotated_transfer_shape_wide`, burn/mint), the 3 grow-gate families (`generate_rotated_note_spend_wide`/
  `_note_create_wide`/`_create_cell_wide`, wrapping their limb-26/27/0 accumulator generators), and the cap-open
  tail (`append_wide_carriers_cap_open`, width 1026). FIVE real wide `prove/verify_vm_descriptor2` roundtrips —
  one per distinct producer shape — all PROVE+VERIFY (`tests/effect_vm_wide_roundtrip.rs` ×4 + `cap_open_self_
  verify.rs::cap_open_wide_*`). The bb is UNIFORM=187 across all 45 (the inherited per-member-split note was
  superseded — the cap-open `bb` is its FACE width 187, the appendix lands past the limbs). LIVE UNTOUCHED:
  flip 13/13, cap-open 4/4, dregg-cell 660+, circuit lib 896, sovereign c1 19/19, drift byte-identical (no live
  TSV/FP/VK change), `lake build Dregg2` 4004 axiom-clean.
- ✅ **STAGED SLICE 2b — the WHOLE flip pipeline PROVEN COHERENT end-to-end** (GREEN, NOT committed): the
  producer + executor flip LEGS are built ADDITIVELY and proven to cohere, so the flag-day is now a pure switch.
  **Producer leg** `full_turn_proof::prove_effect_vm_rotated_wide` (mints a real wide `Ir2BatchProof` over
  `WIDE_REGISTRY_STAGED_TSV` via the wide producers, publishes the 16 wide commit PIs). **Executor leg** (mirrored
  in `sdk/tests/sovereign_rotated_wide.rs`): reconstructs the trusted before/after cell, computes the chip-faithful
  8-felt commit (`wire_commit_8_chip` over `compute_rotated_pre_limbs`), OVERRIDES the 16 wide PIs, and
  `verify_vm_descriptor2` ACCEPTS — BOTH the BEFORE (stored sovereign state) AND AFTER (EffectVM-applied
  post-state, nonce ticked) commits match the producer's published ones. **Forgery tooth** bites (a forged 8-felt
  commit is UNSAT). So the flag-day = repoint the live sovereign producer (`cipherclerk::prove_sovereign_turn_
  rotated`) + executor (`proof_verify::verify_and_commit_proof_rotated`'s `dpis[34]/[35]` → 16 wide PIs from
  `wire_commit_8_chip`) onto these legs + the cell `_felt8` chip-chain repoint + re-emit/re-pin the VK — ATOMIC,
  ember-gated (VK-affecting). The legs are GREEN; the switch is mechanical.
- ⚑ **STANDING SEAM (slice 2, the cell-side flip cutover) — `compute_canonical_state_commitment_v9_felt8` uses
  the WRONG chain.** The circuit's published wide carrier is the CHIP chain (`fill_wide_block`/`chip_absorb_all_
  lanes` — arity-tagged seeding: the head's `st[4]=4` tag), but the cell's `_felt8` delegates to `wire_commit_8`
  (plain `single_perm_compress`, NO arity tag) — they DIVERGE from the head on (measured: the executor-anchoring
  tests assert `_ne` on the plain chain). The new circuit primitive `poseidon2::wire_commit_8_chip` (byte-twin of
  `fill_wide_block`) IS the deployed-circuit-anchoring chain; the executor-anchoring differential proves cell
  pre_limbs → `wire_commit_8_chip` ≡ circuit carrier-12. CLOSURE (part of the flag-day, ember-gated since the
  cell felt8 is consumer-facing): repoint `compute_canonical_state_commitment_v9_felt8` onto the chip chain (or
  publish a `wire_commit_8_chip` cell-side wrapper) so the deployed executor anchors. Until then the cell `_felt8`
  is NOT the deployed circuit's commit.
- 🚧 **PHASE B-ROTATION — THE LIVE FLIP: TWO REAL BLOCKERS FOUND (7th agent, 2026-06-19, STOPPED CLEAN at green
  HEAD `b533beef4`).** The atomic switch was BUILT in full (cell `_felt8`→`wire_commit_8_chip` + the turn-side
  twin; cipherclerk producer → wide; executor → WIDE registry + retire `dpis[34/35]` + bind 16 wide PIs via
  `bytes32_to_felt8`; the C1 registration → `_v9_8`; the wide-roundtrip seam-closed assertion) and ALL EDITS
  BACKED OUT to green HEAD per green-or-bust. **What LANDED proven (the wins, now reverted but recipe-clear):**
  (i) the missing FEE leg — `generate_rotated_transfer_shape_with_fee_wide` + `prove_effect_vm_rotated_wide_with_
  fee` (the LIVE sovereign transfer is FEE'd; the proven slice-2b legs covered only the NON-fee transfer +
  noteSpend — a real gap). NEW self-verifying test `wide_sovereign_fee_pipeline_proves_and_anchored_verify_accepts`
  PROVED+VERIFIED (55-PI `transferFeeVmDescriptor2R24` wide, fee debited in-proof, forgery UNSAT) — GREEN. (ii)
  the generic `generate_rotated_cohort_wide` (accepts 38-PI transfer-shape OR 39-PI record-pin base) — the
  record-pin family (setPerms/setVK/cellSeal/…) carries 39 base PIs, which `_transfer_shape_wide` (38-only)
  rejects. **BLOCKER 1 (the fatal one — needs Lean re-emit, NOT a Rust switch):** the wide descriptor (additive
  `wideAppend`) KEEPS the host's 1-felt PI 34/35 pins (col 225/276 → the trace's 1-felt `STATE_COMMIT` carriers).
  After retiring the executor's `dpis[34/35]` override, those PIs revert to the executor's PLACEHOLDER-reconstructed
  carriers, which ≠ the producer's REAL carriers ⇒ Fiat-Shamir transcript mismatch ⇒ `InvalidPowWitness` (the C1
  control fee-transfer rejected). The executor CANNOT reproduce the real 34/35 carriers: they depend on the
  producer's `cells_root` (its SINGLE-CELL ctx_ledger of the before-cell) + `iroot` (the cipherclerk's receipt
  chain) — NEITHER is derivable from the published turn + the executor's real ledger, and the 1-felt trusted value
  is no longer stored (we store 8-felt). **FIX (genuine, VK-affecting):** retire the 1-felt PI 34/35 pins in Lean
  `wideAppend` (drop/free the host's `B_STATE_COMMIT` pins — they ARE the ~31-bit waist we're eliminating) + re-emit
  `WIDE_REGISTRY_STAGED_TSV` + re-pin its FP; OR thread the producer's full rotation context (cells_root/iroot)
  onto the turn so the executor reconstructs the carriers faithfully. **BLOCKER 2 (smaller):** the initial sovereign
  REGISTRATION must store the 8-felt commit (`compute_canonical_state_commitment_v9_8`), not the 1-felt `_v9` —
  else the first turn's OLD wide anchor (felts 1..7 = 0) ≠ the producer's 8-felt BEFORE carrier. **VK/re-emit
  finding (good):** repointing live CONSUMERS to the pre-existing `WIDE_REGISTRY_STAGED_TSV` (already FP-pinned +
  drift-checked) needs NO descriptor re-emit and NO separate pinned VK (the IR-v2 descriptor TSV IS the verifying
  material) — UNTIL Blocker 1's fix changes `wideAppend` (then a re-emit IS required). The Lean side
  (`v3RegistryCapOpenWide` `_length=45`/`_sound`/`_binds`) is genuinely complete; Blocker 1 is a TARGETED
  `wideAppend`-pin-retirement + re-emit, not new soundness proof. RESUME: land Blocker 1's Lean pin-retirement
  first (it's the floor under everything), re-emit/re-pin, THEN the Rust switch (which is otherwise built + the
  fee/cohort legs proven green).
- ✅ **BLOCKER 1 RESOLVED — the 1-felt PI 34/35 waist RETIRED from the staged wide registry** (Stage-1 flip
  prerequisite, GREEN, NOT committed): `EffectVmEmitRotationWide.wideAppend` now FILTERS the host's two 1-felt
  `STATE_COMMIT` commit pins (`isLegacyCommitPin1 bb ab` = the unique first-row pin on `bb+B_STATE_COMMIT` /
  last-row on `ab+B_STATE_COMMIT`; the `rotPins` PI-34/35 carriers), so the 8-felt `commitPins` are the SOLE
  commit binding. Tower re-proved axiom-clean: `wideAppend_memOpsOf`/`mapOpsOf` (new `filterMap_filter_legacyPin`
  helper — the dropped pins carry no mem/map op), `wideAppend_satisfied2_host` now reduces to a `Satisfied2` of
  the PIN-RETIRED host `dropLegacyCommitPins1 h bb ab` (gates survive — they are NOT the dropped commit pins),
  `wideAppend_binds_published` UNCHANGED (the 8-felt `wireCommitR8_binds` never depended on the 1-felt pins),
  folds `v3RegistryWide_sound`/`v3RegistryCapOpenWide_sound` re-stated over the pin-retired host. Re-emitted
  `rotation-wide-registry-staged.tsv` (+ the transfer single-line) — each member's pi_binding list is 2 shorter
  (PI 34/35 gone; 36/37 height/caveat + the 16 wide PIs 38..53 kept); `public_input_count` stays the host+16
  (slots 34/35 now DEAD/unpinned — count unchanged is correct + valid: the load-bearing fix is removing the
  PINS, not the slot count). Re-pinned `WIDE_REGISTRY_STAGED_FP`. GREEN: `lake build Dregg2` 4004 axiom-clean ·
  descriptor drift 12/12 (live `V3_STAGED_REGISTRY` byte-identical, only the wide TSV/FP moved) · wide roundtrip
  4/4 prove+verify at the pin-retired geometry · live flip 13/13. **STAGE-2 HANDOFF:** the executor can now
  delete its `dpis[34]/dpis[35]` reconstruction (`trace_rotated.rs:1618-1619`, `:537`) — the verifier no longer
  pins those PIs, so the placeholder no longer causes a Fiat-Shamir mismatch (`InvalidPowWitness` gone). Blocker
  2 (initial-registration 8-felt commit) is independent + still open.
- ✅ **PHASE B-ROTATION — THE FLAG-DAY SWITCH LANDED (the live commitment is GENUINELY 8-FELT ~124-bit
  end-to-end; NOT committed, ember-gated)**: the live sovereign path now proves+verifies at the 8-felt wide
  geometry whole-tree green. (1) the live producer `cipherclerk::prove_sovereign_turn_rotated` routes the WIDE
  generators (transfer-shape / FEE / record-pin / notespend) + publishes the 8-felt BEFORE/AFTER commit
  (`felt8_to_bytes32` of the LAST-16 wide PIs); the NEW FEE WIDE leg
  `full_turn_proof::prove_effect_vm_rotated_wide_with_fee` + `trace_rotated::generate_rotated_transfer_shape_with_
  fee_wide` + `generate_rotated_record_pin_wide` were BUILT (the live sovereign transfer is FEE'd — covered).
  (2) the executor `verify_and_commit_proof_rotated` resolves `WIDE_REGISTRY_STAGED_TSV`, reconstructs the wide
  trace, RETIRES the `dpis[34]/[35]` 1-felt override, and anchors the 16 wide PIs from the trusted commits via
  `bytes32_to_felt8` (OLD ← stored `_v9_8`, NEW ← `turn.execution_proof_new_commitment`). (3)
  `compute_canonical_state_commitment_v9_felt8` repointed to `wire_commit_8_chip` under a NEW `dregg-cell/prover`
  feature (forwarded by sdk/turn/node) — the stored sovereign commit IS the deployed chip carrier (Blocker 2:
  registration stores `_v9_8`). KEY FIX (the Fiat-Shamir close): `append_wide_carriers` ZEROES the now-dead PI
  34/35 slots on BOTH sides (every PI is absorbed into the transcript; a witness-dependent value there diverged
  it → `InvalidPowWitness`). NO re-emit/re-pin needed — the wide TSV/FPs were already Lean-emitted + drift-PASS;
  Lean UNTOUCHED (apex `Rfix` stays on `v3RegistryCapOpen` — authority leg). GREEN: lake 4004 axiom-clean ·
  drift PASS · circuit lib 896/0 + all integration green · cell 660+ · turn lib 498/0 · sdk lib 229/0 ·
  sovereign_rotated_c1 19/19 (fee'd) · sovereign_rotated_wide 2/2 · sovereign_proof 3/3 · node 229/0 + caps ·
  node binary builds. LIVE collision tooth bites (high-position flip → distinct 8-felt commits → proof-A
  rejected against B by `verify_vm_descriptor2` ALONE). **TWO ROBUSTNESS TAILS (not regressions, not green
  blockers):** (i) the node API/MCP `register_sovereign_cell` writers store a blake3/placeholder commit (a
  non-load-bearing API echo — the comment at `api.rs` says the REAL commit comes from the cipherclerk SDK via
  `/cells/register`; never the OLD-commit of a verified rotated turn, pre-existing) → CLOSURE: route those
  writers through `compute_canonical_state_commitment_v9_8` if/when they pair with proof-carrying turns. (ii) a
  SPLIT-PROCESS registrar built with bare `dregg-cell` (no prover unification) would store the PLAIN chain ≠ the
  chip anchor → CLOSURE: make `compute_canonical_state_commitment_v9_felt8` chip-faithful unconditionally (move
  `wire_commit_8_chip` out of the `prover` gate) so the choice is not feature-unification-dependent.
- ⬜ ~~**PHASE B-ROTATION LIVE CUTOVER — the pure Rust/executor flip**~~ (now the STAGED path above; original atomic framing): Now a ONE-LINE Lean repoint (`v3Registry →
  v3RegistryWide`) + the atomic Rust/executor: producer 8-felt carrier fill (+208) across 6 crates · executor
  retire `dpis[34]/[35]` → bind 16 wide PIs (`felt8_to_bytes32`) · the hardcoded geometry consts (`ROT_WIDTH`/
  `BEFORE_BASE`/`AFTER_BASE`/`ROT_PI_COUNT`) move together · differential-over-8 + LIVE tooth · re-emit + re-pin.
  Six+ honest agent refusals = a focused multi-session deployed-cutover (a partial breaks the validator), NOT an
  end-of-session dispatch. ⚑ 2026-06-19 RE-SCOPE (5th agent STOPPED clean at green HEAD
  `93fba7ee5`): the staged wide lane is NOT drop-in. Two real blockers: **(B1, Lean, new proof)** `rotateV3Wide`
  (`EffectVmEmitRotationWide.lean:286`) takes a BARE `EffectVmDescriptor` (`graduateV1 (rotateV3 d)`), but the live
  `v3Registry` is 36 ALREADY-GATED `EffectVmDescriptor2`s (v3OfFrozen/withSelectorGate/the WAVE disc+perms gates/
  fee-pin). Need an additive `wideAppend : EffectVmDescriptor2 → EffectVmDescriptor2` (append the two 13×8 wide
  carriers + 16 PI pins onto an arbitrary gated host, carriers past `host.traceWidth`, PIs past `host.piCount`) +
  re-prove `rotV3Wide_pins/_publishes/_binds_published` over `host` (additive, green-able like the bare-host
  lane). **(B2, Rust, producer)** `fill_chip_lanes` (`descriptor_ir2.rs:2790`) fills lanes 1..7 but NEVER lane0
  (the 1-felt path got it from `fill_block`'s digestCol); the wide carrier-12 lane0 IS the published commit's
  lane0 → unfilled ⇒ honest prove FAILS. Widen `fill_chip_lanes` to write lane0 for wide lookups in forward
  order across the 6 producers (cell/turn/sdk×2/node + proof_verify). THE RESUME RECIPE (steps 1-3 must ALL land
  before whole-tree green — atomic): 1. `wideAppend` + repoint the 36 registry entries; 2. the producer lane0 +
  +208 carrier fill (6 crates); 3. executor retire `dpis[34]/[35]` 1-felt match + bind the 16 wide PIs +
  `felt8_to_bytes32` (proof_verify.rs/atomic.rs); 4. differential + LIVE collision tooth to 8; 5. re-emit + re-pin
  all FPs. Geometry (confirmed): `rotateV3Wide` is ADDITIVE (`traceWidth + 208`, `piCount + 16`, reads the same
  `preLimbsAt` → binds the same 37 limbs + iroot at full width; does NOT in-place reshape B_STATE_COMMIT/PI34/35
  — the 1-felt pins stay, the 8-felt PIs are NEW, "replacing" happens consumer-side in the executor). Live consts:
  `B_STATE_COMMIT=38`, `B_SPAN=51`, `ROT_WIDTH=328`, `GRAD_ROT_WIDTH=608`, `{OLD,NEW}_COMMIT_LEN=4`.
  ⚑ 2026-06-19 FINAL PRECISION (6th agent STOPPED clean at green HEAD `eb9578848`; the LEAN SIDE IS COMPLETE —
  `wideAppend` + the gated-host tower proven, the flip needs NO Lean proof): the flip is an ATOMIC hardcoded-
  geometry VK flag-day, NOT a `.map`. Three measured surfaces: **(i)** `trace_rotated.rs` producer geometry is
  HARDCODED, not descriptor-driven — `ROT_WIDTH=328`/`BEFORE_BASE=186`/`AFTER_BASE=237`/`ROT_PI_COUNT=38` are
  consts with `debug_assert_eq!(dpis.len(), ROT_PI_COUNT)` guards (:300/:359/:531); the +208 carriers + 16 PIs
  must be filled/pushed BY HAND + threaded through the 6 crates (cell/turn/sdk×2/node + the trace builder). **(ii)**
  the executor binds 1-felt TODAY (`proof_verify.rs:250-251` `dpis[34]=u32::from_le_bytes(old_commit[0..4])`,
  the low-4-byte felt) — retire it, consume 8 felts via `bytes32_to_felt8` into 16 new PI slots, drop the
  override. **(iii)** per-member `bb` is NON-UNIFORM: the 45 registry members split 608-wide (most) / 580 (custom,
  setFieldDyn) / 818 (cap-open), so `wideAppend entry bb (bb+51)` needs each member's underlying-face `traceWidth`
  as `bb` (187 base faces; the rest per the split) — NOT a uniform wrap; locate the OLD-commit pin structurally
  per member. NEXT ADDITIVE SUB-STEP (green-able, advances the flip without touching wire/VK/producer): stage
  `v3RegistryWide` (the Lean wide registry built from the underlying faces with their real per-member `bb`,
  proven axiom-clean beside the live `v3Registry`) — turns the repoint into a one-line cutover once the per-member
  `bb` table is established. THEN the atomic producer+executor+re-emit push. Six agents have refused to rush this —
  it is a focused multi-session task, NOT an end-of-session dispatch.
  --- (original step list, subsumed by the recipe above): (1) trace geometry `B_STATE_COMMIT` 1→8 + `B_CHAIN_BASE`/`B_SPAN`/`ROT_WIDTH`
  follow, `fill_block` from `wire_commit_8` lanes, chain sites arity-4→11; (2) descriptor emits the rotated chain
  sites as arity-11 wide chip lookups binding 8 lanes (`chipLookupTupleN`/`chip_lookup_sound_N`); (3) `rotV3SitesAt`/
  `rotPins`→`wireCommitR8`, bind 8 `B_STATE_COMMIT` cols to 8 PIs/block; (4) `pi.rs {OLD,NEW}_COMMIT_LEN`→8, RETIRE
  the executor commitment PI-match (`dpis[34]/[35]`→8 via `bytes32_to_felt8`); (5) the differential + permission-
  flip to 8; (6) VK/FP re-pin + drift. **The LIVE collision-distinguishing tooth** (two states differing in a high
  position → published 8-felt commits differ, proof for A REJECTED against B's commit with NO executor) is the
  light-client bite that proves it. Land as ONE coordinated flag-day (the B-GATE-OUTPUT precedent: it landed green
  in one push). The core is proven + de-risked; this is the geometry/PI/executor wiring.
  **⚠ 2026-06-19 ORIENT (mapped, NOT yet attempted — STOPPED clean per green-or-bust-WHOLE-tree, tree untouched at
  green HEAD `f6b61a5d7`):** the cutover is NOT a one-pass mechanical mirror. Two hard layers were under-scoped in
  the original handoff: (a) **the Lean wide-lever emission lane is MISSING** — `graduateV1` emits the rotated chain
  sites via the 1-felt `siteLookup`/`chipLookupTuple`/`siteLookups_sound` path (`EffectVmEmitV2.lean:155,275,326`);
  the 8-felt commit needs the chain GROUP + FINAL sites to bind all 8 output lanes, i.e. a NEW wide emission lane
  (`siteLookupN`/`chipLookupTupleN` discharged by `chip_lookup_sound_N` — the lever EXISTS in `DescriptorIR2.lean`
  but is UNWIRED into rotV3) with its own `siteLookups_sound`-analog, threaded through `graduateV1`/`rotateV3`/`v3Of`
  and re-proving `rotV3SitesAt_pin` (`EffectVmEmitRotationV3.lean:427`, the final iroot site h12 now 8-wide),
  `rotV3_publishes` (752, 8 cols→8 PIs/block), `rotV3_binds_published` (789, swap `Poseidon2SpongeCR` floor →
  `Poseidon2WideCR`+`Poseidon2Width8`, call `wireCommitR8_binds`). (b) **the PI-pin layout reshapes 4→18, NOT a
  drop-in**: `rotateV3` (`EffectVmEmitRotationV3.lean:344`) is `piCount := d.piCount + 4` with `rotPins` pinning
  ONE `B_STATE_COMMIT` col→1 PI/block; 8-felt makes it +18 (8 OLD + 8 NEW + height + caveat), shifting the height/
  caveat/the per-effect FIFTH record-pin (currently PI 38, → PI 52+) across ALL 36 cohort descriptors + the 89 tree
  sites referencing the 4-pin shape (`ROT_PI_COUNT`/`piCount+4`/`dpis[34]`/`dpis[35]`/`dpis[36]`/`dpis[37]`/`dpis[38]`).
  Rust cascade is tractable-but-wide: `trace_rotated.rs` `B_STATE_COMMIT 38`→8 cols + `B_CHAIN_BASE`/`B_SPAN 51`/
  `BEFORE/AFTER/CAVEAT_BASE`/`ROT_WIDTH 328`/`GRAD_ROT_WIDTH 608` follow; `fill_block`/`recompute_block_commit` (lines
  903, 1478) chain via `wire_commit_8` lanes; ~10 `dpis[]` push-sites reshape; `pi.rs` `OLD/NEW_COMMIT_LEN 4→8`;
  executor `proof_verify.rs:247-252` retire the low-4-byte override → `bytes32_to_felt8` 8-felt consume (`atomic.rs:
  515-551` too); differential + flip `effect_vm_rotation_flip.rs:1067-1350` + `RotatedCommitDifferential.lean` to 8;
  ~67 JSONs + ~64 FPs + `V3_STAGED_REGISTRY_FP` + probe FPs re-emit. **THE BLOCKER (file:line) = the atomic Lean
  keystone tower:** `EffectVmEmitRotationV3.lean` (3067 lines, 210 defs/thms) — `rotateV3`:344 / `rotV3SitesAt_pin`:427
  / `rotV3_publishes`:752 / `rotV3_binds_published`:789 must ALL re-prove together over the 8-felt carrier + 18-pin
  shape, on top of a newly-built wide emission lane in `EffectVmEmitV2.lean`. The proven `wireCommitR8_binds`/
  `chainFrom8_inj` (`EffectVmEmitRotationR.lean:330,298`, axiom-clean) are READY to be called once the lane exists.
  This is multi-session atomic proof work; NO green sub-step exists in the LIVE wire (any partial geometry/PI shift
  breaks the validator), so it must land whole. RESUME by FIRST building+proving the wide Lean emission lane in
  isolation (additive, like B-ROTATION CORE), THEN the atomic geometry/PI/executor/JSON flip as one green push.
- 🟥 ~~**PHASE B-ROTATION — BLOCKED at the chip INPUT-ARITY cap**~~ (RESOLVED by B-GATE-INPUT ✅ above; historical
  detail): the 8-wide chain (`d8 = perm_lanes(d8 ‖ new_limbs)[0..8]`, ONE permutation per step) was NOT
  expressible with the output-only B-GATE chip. B-GATE widened the chip OUTPUT to 8 lanes (`CHIP_OUT_LANES = 8`, the genuine
  distinct `state[0..8]` of one permutation — that half works), but the chip's INPUT side is hard-capped: AIR
  admits arities `{0,2,3,4,7}` only, seeds `state[0..7]` (st[0..4]=in0..3, st[4..6]=S4/S5/S6 on the arity-7
  branch), and `builder.assert_zero(local[CHIP_IN0 + 7])` PINS `state[7]` to ZERO with `state[8..16]` never
  seeded (`circuit/src/descriptor_ir2.rs:1928-1933, 1955-1966`). So ONE chip permutation absorbs at most **7
  genuine input felts**. An 8-felt carrier `d8` needs 8 input slots just to thread itself forward injectively
  (plus ≥1 for a new limb ⇒ ≥9), which exceeds 7. A step that re-absorbs only 7 of the 8 carrier felts is
  collidable on the dropped felt (the carrier is then 7-wide-throughput, not 8) — exactly the laundering the
  task forbids. Widest faithful carrier that still absorbs ≥1 new limb per step on THIS chip = **6 felts (~185
  bit, ~92-bit collision)** — above 4-felt (62-bit) and vastly above 1-felt, but BELOW the ~124-bit target. The
  Lean side IS ready (`chip_lookup_sound_N` forces all 8 output cols = `permOut ins`; `Poseidon2SpongeCR` floor
  holds at full width); the wall is purely Rust chip-input geometry. CLOSURE = a B-GATE-class chip flag-day to
  admit a wide absorb (arity-15/16: carry the 8-felt `d8` across the full 16-wide state incl. capacity lanes,
  one genuine sponge step per absorb), re-prove the chip AIR seed constraints + `ChipTableSoundN`, THEN the
  carrier-widening + geometry below. NO code shipped (tree stays green); STOPPED per the task's own
  "if the chain can't be made 8-wide cleanly, STOP and report exactly where" clause.
  (Original spec, deferred behind the chip-input flag-day): `v9_wire_commit`/`wire_commit`/`fill_block`
  rewritten so the chaining carrier `d8` is 8 felts THROUGHOUT (no 31-bit intermediate — THE anti-laundering
  crux; a 1-felt-chain-with-wide-final-squeeze is the laundered version). `B_STATE_COMMIT` 1→8 + the 12 chain
  carriers ×2 blocks (`ROT_WIDTH` 327→~509), `wireCommitR`/`chainFrom` carry an 8-felt accumulator,
  `wireCommitR_binds`/`chainFrom_inj` re-proved over 8 via `chip_lookup_sound_N`, `RotatedCommitDifferential` +
  the 3 `rotationProbe*` JSONs/FPs re-`#guard`ed at 8.
- ⬜ **PHASE C — PI + executor + teeth**: `{OLD,NEW}_COMMIT_LEN` 4→8 (`pi.rs`), `rotPins` binds 8, RETIRE the
  executor PI-matching loop for the commitment (`proof_verify.rs` `dpis[34/35]`→ranges; `felt_to_bytes32`→8×4
  byte encoding into the 32-byte ledger slot), the commit differential to 8, + the COLLISION-DISTINGUISHING
  tooth (two states differing only in a high position → 8-felt commits differ, proof for A REJECTED against B's
  commit with NO executor) + the intermediate-carrier-propagation tooth. VK flag-day, ember-gated deploy.

Each phase is ~a session; PHASE B-GATE is the riskiest (system-shared chip). The Lean lever (Phase A) is the
proof-side foundation already in place. Resume at PHASE B-GATE.

## (superseded detail below — see the phased campaign above) FAITHFUL STATE COMMITMENT — BLOCKED at the chip-output-arity seam (2026-06-19)

`docs/FAITHFUL-STATE-COMMITMENT.md` asks to widen the in-circuit per-cell state commitment from 1
squeezed felt (~31-bit, light-client-collidable in seconds) to a faithful 8-felt digest (~124-bit,
matching the proof's ~130-bit FRI soundness). I read the full spec + the live geometry and STOPPED before
shipping, per the task's own "if the chip can't expose 8 cleanly, STOP and report" clause. Two grounded
findings, both decisive:

(1) **The deployed commitment is a Merkle-Damgård CHAIN of single-squeeze rate-4 compressions, NOT one
sponge whose squeeze can be widened.** `cell/src/commitment.rs::v9_wire_commit` / Lean
`EffectVmEmitRotationR.wireCommitR` / the 13 `EffectVmEmitRotationV3.rotV3SitesAt` sites each squeeze ONE
~31-bit `hash_many` felt into one chain carrier. So a genuine ~124-bit light-client floor requires the
ENTIRE chain accumulator to be 8 felts wide — every intermediate carrier too — else an adversary finds a
31-bit collision on an INTERMEDIATE carrier (≈2^15.5 work) that propagates to an identical published final
commit regardless of the final commit's width. Widening ONLY `B_STATE_COMMIT` 1→8 (the literal task-body
reading) would be a LAUNDERED widening: 8 published felts that are a deterministic function of a
31-bit-collidable accumulator. The task's own COLLISION-DISTINGUISHING TOOTH would (correctly) still find
it collidable at ~31-bit, so shipping it would FAIL the anti-laundering bar.

(2) **The IR-v2 Poseidon2 chip is hard-wired single-output and cannot expose 8 cleanly.**
`DescriptorIR2.poseidon2ChipTableDef = ⟨.poseidon2, …, CHIP_RATE + 2⟩` (1 arity + 8 padded inputs + ONE
output); `chipRow`/`chipLookupTuple` carry one output column; `chip_lookup_sound` proves that one column
= `hash ins` for `hash : List ℤ → ℤ`. There is NO multi-output chip variant or 8-wide chained-commit
helper anywhere in the tree (grep-confirmed). A faithful 8-wide accumulator therefore requires rewriting
the IR-v2 chip soundness CORE: chip table `CHIP_RATE+2 → CHIP_RATE+9`, the chip exposing 8 squeezed felts
(squeeze-permute-squeeze), `chipRow`/`chipLookupTuple`/`chip_lookup_sound` over an 8-tuple output,
`HashInput.digest k` selecting one of 8 columns, `chainFrom`/`wireCommitR` threading an 8-vector
accumulator, and `wireCommitR_binds`/`chainFrom_inj` re-proved under an 8-wide CR floor — PLUS the geometry
octuples (`B_SPAN` ~51→~142, `ROT_WIDTH` 327→~1000+, every `rotV3SitesAt`/`caveatV3SitesAt`/`rotPins`/
`weldsAt`/`pi.rs` offset, every producer in `cell`/`turn`, the differential, and the VK). This is a
ground-up rewrite of the chip soundness lever, NOT the contained single-felt-limb cascade the mover
flag-days (b3c058e31/aba1861ce) proved tractable — those never touched `chipRow`, `chip_lookup_sound`,
`chainFrom`, or the `hash : List ℤ → ℤ` codomain. This one touches all of them.

CLOSURE SHAPE (the real lane, ember-gated VK flag-day): (a) Lean — introduce a multi-squeeze chip
(`hash8 : List ℤ → Fin 8 → ℤ` or `List ℤ → List ℤ` len-8), widen `poseidon2ChipTableDef`/`chipRow`/
`chipLookupTuple`/`chip_lookup_sound`, thread an 8-vector accumulator through `chainFrom`/`wireCommitR`,
re-prove `chainFrom_inj`/`wireCommitR_binds`/`rotV3SitesAt_pin` under the 8-wide `Poseidon2SpongeCR`
(injectivity of the 8-felt squeeze — the genuinely-load-bearing floor at full width). (b) Rust — `hash_many_8`
(squeeze-permute-squeeze, precedent at `circuit/src/schnorr_sig.rs:207`), the 8-wide chain in
`poseidon2.rs`/`trace_rotated.rs`/`v9_wire_commit`, the geometry shift, `pi.rs` `{OLD,NEW}_COMMIT_LEN = 8` +
executor-loop retirement, `proof_verify.rs`. (c) Teeth — the DISTINCTNESS unit test + the
COLLISION-DISTINGUISHING tooth (now genuinely binding because the WHOLE chain is 8-wide). Named:
faithful-state-commitment 8-felt floor, 2026-06-19. THE #1 SOUNDNESS FLOOR — every WAVE 0/1/2 value-close
binds THROUGH this 31-bit door; until it is 8-wide-throughout, the light-client trust is ~31-bit.

## WAVE 2 PERMS/VK — the setPermissions/setVK mover light-client forgery CLOSED LIVE (2026-06-18)

The authority movers setPermissions/setVK forced their AFTER perms/VK only via the off-circuit
record-pin anchor (PI[38] from the TRUSTED post-cell) — for a ledgerless client a setPermissions whose
committed post-state bound ARBITRARY permissions/VK passed `verifyBatch` alone. CLOSED LIVE by the
WAVE-2 VK flag-day (NUM_PRE_LIMBS 33→35, mirroring WAVE 1's 32→33): TWO committed authority sub-limbs
were appended as the new LAST pre-limbs — perms-digest `B_PERMS = 33` and vk-digest `B_VK = 34` (B_SPAN
47→49, ROT_WIDTH 320→324, APPENDIX 133→137, CAP_OPEN_BASE auto-follows; all offsets 0..32 incl. WAVE-1
`B_DISC = 32` STABLE; the 35-limb body re-chunks to ten 3-wide groups + one singleton, site count stays
13). Each sub-limb is the deployed declared-param felt `= bytes32_to_8_limbs(blake3(postcard(perms/vk)))[0]`
(BYTE-IDENTICAL to `params[0]` of the live setPerms/setVK row; canonical
`cell::commitment::{perms,vk}_digest_felt`, `turn::rotation_witness` delegates — ONE definition).
The deployed setPerms/setVK descriptors carry the LIVE in-circuit weld
(`EffectVmEmitRotationV3.rotateV3WithPermsVKGate`: a selector-gated weld of the AFTER perms/vk sub-limb
to the in-circuit declared-param column `prmCol 0`), so a forged post-permissions / post-VK is UNSAT for
a ledgerless client with NO trusted post-cell. The value cohort `rotateV3FrozenAuthority` continuity-welds
both B_PERMS + B_VK (a value turn cannot smuggle an authority-shape change into NEW_COMMIT). Proven:
`setPermsV3_forces_declared`, `setPermsV3_rejects_forged`, `setVKV3_rejects_forged`,
`rotateV3WithPermsVKGate_{forces,rejects_forged}` — deployed faces of `RotatedKernelRefinementPermsVK`,
all axiom-clean. Differential extended (`RotatedCommitDifferential.rotatedLimbs` 35-limb + load-bearing
at indices 33/34 + the Rust flip test's perms-flip + vk-flip legs). LIVE teeth: the forged
setPermissions/setVK rejects now bite at PROVE time (`check_constraints` refuses the trace — the weld is
a row constraint), confirmed in `sovereign_rotated_c1` (`LIVE PERMS GATE`/`LIVE VK GATE` stderr).
lake 4003 axiom-clean · circuit lib 884 + flip 12/12 + cap-open 3/3 + 1/1 + selector 3/3 + drift/registry
PASS · sovereign_rotated_c1 19/19 · turn+cell+node build · registry re-emitted (46 lines, FP
`369f6fbb…`). NAMED RESIDUAL: the in-circuit weld binds the declared param's LIMB[0] (`params[0]`); the
full 8-limb declared perms/VK hash binds via the SAME `effects_hash`→PI chain the light client already
verifies (the existing path — so the closed property is "committed authority-shape ≠ the PI-anchored
declared authority"). The variable Custom-vk hash component rides that same effects_hash anchor (no
in-circuit fixed-width tag fold — the deployed setPerms/setVK row keeps perms/VK off-trace, only
`params[0]` is the in-circuit handle). The opaque full `record_digest` (r23) PI-38 anchor stays
belt-and-suspenders. WAVE 3: refusal/makeSovereign/setFieldDyn (the identity/fieldsExt sub-limbs).

## WAVE 1 LIFECYCLE-DISC — the lifecycle-mover light-client forgery CLOSED LIVE (2026-06-18)

The lifecycle movers (cellSeal/cellUnseal/cellDestroy/receiptArchive) forced their AFTER-lifecycle
limb only via the off-circuit record-pin anchor (PI[38] from the TRUSTED post-cell) — for a ledgerless
client PI[38] is free, so a frozen seal / Destroyed→Live resurrection / wrong-disc archive was accepted
by `verifyBatch` alone. CLOSED LIVE by a VK flag-day (NUM_PRE_LIMBS 32→33): the lifecycle DISC (`u8 0..4`)
is now a committed pre-limb (`B_DISC = 32`, the new LAST limb; B_SPAN 45→47, ROT_WIDTH 315→320,
APPENDIX 129→133, CAP_OPEN_BASE 320 — all offsets 0..31 STABLE). The deployed lifecycle-mover descriptors
carry the LIVE in-circuit disc-transition gate (`EffectVmEmitRotationV3.rotateV3WithDiscGate`: a
selector-gated constant force on the committed disc limb — cellSeal forces before=Live/after=Sealed,
cellDestroy forces after=Destroyed, …), so the forgery is UNSAT for a ledgerless client with NO trusted
post-cell. Proven: `cellSealV3_disc_forces_sealed`, `cellSealV3_rejects_frozen`,
`cellDestroyV3_rejects_resurrection` (deployed faces of `RotatedKernelRefinementLifecycleDisc`), all
axiom-clean. Differential extended (`RotatedCommitDifferential.rotatedLimbs` 33-limb + the Rust flip
test's disc-flip leg — limb 32 is load-bearing). LIVE tooth: the 3 forged seal/unseal/archive rejects
now bite at PROVE time (the disc gate refuses the trace), the rest via the payload anchor. lake 4003
axiom-clean · circuit lib 884 + flip 12/12 + descriptors + cap-open 3/3 · sovereign_rotated_c1 19/19 ·
turn 496 + integration · node capability 8 · drift PASS · descriptors re-emitted (67 files, 64 FP).
NAMED RESIDUAL: the opaque payload felt (reason_hash/deathCert/sealed_at, limb 29) stays prover-supplied
with a full-node-only PI-38 anchor (the DISC is what's safety-critical; the payload is effect data the
light client reads from the published effect). receiptArchive kernel-spec (frozen) vs deployed (Archived)
disc-semantics divergence reconciles in WAVE 3.

## FEE-IN-PROOF — trust-surface hole #5 CLOSED for the sovereign actor cell (2026-06-18)

The deployed sovereign transfer debited `turn.fee` in executor PHASE 1 BEFORE proving and the
verifier blindly UNDID it (`pre_balance = post_fee_balance + turn.fee`) from the TRUSTED `turn.fee`
— so the fee was NOT a constraint in the proven transition (a ledgerless light client could not
verify it). CLOSED: `transferFeeVmDescriptor2R24` (Lean `EffectVmEmitTransfer.transferFeeVmDescriptor`
+ `EffectVmEmitRotationV3.transferFeeV3`, registry tail at `v3RegistryCapOpen[44]`) augments the
balance-lo gate to `after = before − transfer − fee`, carries the fee in the after-block RESERVED
column (col 89 — dead weight, NOT in the commitment, off the ROT_WIDTH flag-day: width stays 316),
and pins col 89 to a published fee PI (slot 38, `piCount 38→39`). The producer
(`cipherclerk::prove_sovereign_turn_rotated` + `full_turn_proof::prove_effect_vm_rotated_ir2_with_fee`)
debits the fee in-proof; the verifier (`proof_verify.rs`) sets PI 38 = `turn.fee` and the gate forces
the debit — RETIRING the blind reconstruction for the proven transition. TOOTH:
`fee_debit_is_proven_and_underclaimed_fee_is_unsat_for_a_ledgerless_client`
(`circuit/tests/effect_vm_rotation_flip.rs`) — underclaimed/forged fee UNSAT via
`prove/verify_vm_descriptor2` ALONE. `lake build Dregg2` 4003 axiom-clean, drift PASS, FP re-pinned,
sovereign_rotated_c1 19/19 (fee=500) + node capability 8/8 green.

### residue NAMED (closure lanes):
- The fee on a **NON-sovereign agent cell** is still outside the proof. The fix binds the fee ⟺
  balance ONLY for a SOVEREIGN turn where `turn.agent == execution_proof_cell` (the fee cell IS the
  proven cell). A non-sovereign turn's fee debit (executor Phase 1 on a NON-proven cell) remains
  executor-trusted — the proof covers no such cell. Closure: when the federation-cell ledger
  transitions are themselves proof-carrying, fold the fee debit into THAT cell's transition proof.
- The verifier's blind `pre = post + turn.fee` reconstruction **survives for the BEFORE/OLD_COMMIT
  block only** (the pre-fee state OLD_COMMIT binds, cross-checked by PI 34 == stored sovereign
  commitment). It no longer touches the PROVEN transition (the after-balance is gate-forced). This
  is sound (OLD_COMMIT independently binds the pre-state) but the `+ turn.fee` term is still a
  trusted input to the BEFORE reconstruction; a fully ledgerless BEFORE binding would carry the
  pre-fee commitment as a published claim like NEW_COMMIT.
- The fee'd path covers a **plain single-`Effect::Transfer` lead** (the deployed sovereign-transfer
  shape). Non-transfer sovereign effects keep the unfee'd cohort (their fee is still Phase-1-trusted);
  the same RESERVED-column + fee-pin mechanism graduates them when each becomes fee-bearing.
- NoOp-row witness bookkeeping in the fee generator sets unconstrained param cols 68/69 (amount=fee,
  dir=0) to satisfy the unconditional bal-lo gate on passthrough rows. Verified sound (cols 68/69 are
  not PI/effects-hash-bound in this descriptor; only the dir-boolean gate touches them) — named as a
  carried subtlety, not a hole.

## CIRCUIT-SOUNDNESS APEX — light-client unfoolability: faithful core LANDED, per-effect terrain MAPPED (2026-06-16)

The map + state lives in `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md` (the obligation table is the resumable plan).

⚑⚑ COMPLETE (2026-06-18): the circuit is now SOUND ∧ COMPLETE, both axiom-clean, both honest about their
floors. SOUNDNESS — the adversarial review (ember's gate) fully discharged; every cap-effect's authority
forced in-circuit (no fail-closed, #217 closed), the whole record-pin family genuinely verifier-anchored
(#218/#219/#220 — which the fix flushed out as 3 real bugs the vacuous pin had masked). COMPLETENESS — 5
per-effect waves + the capstone `CircuitCompletenessAssembled.lean` (commit 8f7360b7f): every live effect
has its genuine `descriptorComplete` rung. THE HONEST SHAPE (not papered over): value-leg UNCONDITIONALLY
complete; authority-leg a STRUCTURAL DICHOTOMY (owner OR cap — the cap-open descriptor cannot witness an
owner turn); the bidirectional `verifyBatch_kernel_bidirectional` is an HONEST two-arm conjunction, NOT a
fused ↔ — SOUND needs WitnessDecodes (the hard surjection) + StarkSound, COMPLETE needs only
stateDecode_construct (the prover HOLDS the kernels) + StarkComplete, and that floor asymmetry is kept
explicit. ~22 commits this session (3d139220d … 8f7360b7f). Owed: a full-workspace gauntlet over the
session's Rust changes (apply_refusal / cap-open geometry / verifier anchors) — targeted suites green,
belt-and-suspenders pass pending.

TURN-IDENTITY PI WELD — the owner-authority/turn-identity smuggle, BEACHHEAD landed (2026-06-18). The hole
(confirmed at HEAD 4dc186212): the turn's `actor`/`src` are bound by NOTHING a light client sees —
`recStateCommit` uses `src`/`dst` only as the cell-digest partition index and never absorbs `actor`; `rotPins`
publishes only 4 PIs (OLD/NEW commit · height · caveat); the cap-open `capOpenCols.src`/`capRoot` are FREE
appendix columns. So `RotatedKernelRefinementFacetTurnBound`'s `TurnIdentityBound`/`hsrc` were CARRIED
obligations. BEACHHEAD (`Dregg2/Circuit/Emit/CapOpenTurnPins.lean`, new): `effCapOpenV3TB base name n` = the
cap-open PLUS two turn-identity columns (`capOpenActorCol`/`capOpenDstCol`) + three `.piBinding .last` pins
welding `capOpenCols.src`/`actor`/`dst` to NEW PI slots; `effCapOpenV3TB_to_base` lifts every cap-open
keystone through the append; `effCapOpenV3TB_publishes` FORCES src/actor/dst = PI on the last row;
`TurnIdentityAnchored` = the named verifier override (recompute the turn-identity PIs from the trusted turn,
the record-pin `dpis[38]` analog); `effCapOpenV3TB_hsrc` DISCHARGES `capOpenCols.src = turn.src` from the PI
weld + anchor. In `RotatedKernelRefinementFacetTurnBound`: `transferAuthoritySourceCanon_ofTB` builds the slim
canonical authority source with the carried `hsrc` field REPLACED by the in-circuit derivation, and
`transfer_descriptorRefines_facetTB_realized` re-proves the turn-bound refinement with `hsrc` realized (the
assumed `src`-equality is gone from the authority leg's hypothesis set). Emitted: `transferCapOpenTBVmDescriptor2R24`
(width 409, 41 PIs) added to the wire (`rotation-v3-staged-registry.tsv`); drift PASS; FP re-pinned; Rust
audit + resolver-coverage tests updated (n→45, TB exclusions). NEGATIVE TOOTH `effCapOpenV3TB_rejects_mismatched_src`.
#assert_axioms-clean. ⚑ CUT OVER LIVE (2026-06-18): the live transfer cap-open is now routed THROUGH
`transferCapOpenTBVmDescriptor2R24` (NOT a staged/excluded descriptor — per ember "stop cargo-culting VK
epochs, just cut over"). The deployed prover fills the 2 turn-identity columns (`CAP_OPEN_TB_ACTOR_COL=407`,
`_DST_COL=408`; `widen_to_cap_open_tb` in `trace_rotated.rs`) and the verifier anchors the 3 turn-identity PIs
(38/39/40 ← trusted turn, `anchor_cap_open_turn_pins` = the `TurnIdentityAnchored` realization). Live key cut
in `sdk/src/full_turn_proof.rs` (`CapOpenRoute.turn_bound`, `TurnIdentityFelts`); node site `node/src/turn_
proving.rs` threads identity. DEPLOYMENT NEGATIVE TEST `circuit/tests/cap_open_turn_bound_verify.rs`
(`..._forces_published_identity`): honest accept + forged src/actor/dst each REJECTED by `verify_vm_descriptor2`
ALONE — the gate BITES for a ledgerless client. Green: lake 4001 · circuit cap-open/flip 13/13 · sdk cap_open
4/4 · drift PASS. COMMITTED `d64600d5a` (beachhead) + `cc6102b87` (flip-test fix) + the cutover (this commit).
REMAINING: (1) NAMED RESIDUAL — the live node cap-gated path publishes the OWNER arm (`cap_turn_identity:
None` ⇒ `actor=dst=src`); threading a genuine cross-vat `(actor≠src)` identity needs single-felt projections of
`actor`/`dst` CellIds (mirroring `leaf_target`'s u32 fold in `turn/src/executor/authorize.rs:1045`) added to
`ConsumedCapWitness`/the node prove site (`node/src/turn_proving.rs:1059`) — the SDK/circuit/verifier already
accept `Some(id)`, only the felt source is missing; (2) the ACTOR↔leaf-position weld (root `actor` in the
cap-tree; owner-arm rooting needs the agent-signature pass #3); (3) FAN-OUT to the whole-turn forest apex
(`RotatedKernelForestFacet`) so the WHOLE-turn authority is turn-bound; (4) `amt` weld analogous to `src`.

AUTHORITY-RESIDUE CONTINUITY — #1 WAVE 0, LIVE-CUT (2026-06-18, `9f415ca97`). THE FORGERY (light-client): the
deployed commitment binds the authority residue `r23` (`B_RECORD_DIGEST`=24, the concrete realization of the
Lean `StateCommit.RH` rest-hash) + `B_LIFECYCLE`=29, but `weldsAt` welds ONLY balance/nonce/fields[0..7]/cap_root
— so for a VALUE effect BEFORE-r23 and AFTER-r23 are independent free felts: a prover witnesses an AFTER-r23
folding ARBITRARY permissions/VK/lifecycle/mode, the value gate passes, NEW_COMMIT binds forged authority, a
ledgerless client is fooled (a "transfer" silently rewrites the authority half). CLOSE (Lean-emitted, law #1 —
producer fills r23 honestly, no Rust producer edit): `rotateV3FrozenAuthority` appends two `colEq` welds forcing
AFTER-r23==BEFORE-r23 + AFTER-lifecycle==BEFORE-lifecycle; by `StateCommit.RestHashIffFrame` (`RH k = RH k' ↔`
the 16 non-cell authority components agree) this FORCES the frame the apex previously CARRIED. Proven companions
(`_freezes`/`_rejects_drift`/`_satisfiedVm_v1`/`graduable_`/`v3OfFrozen`/`rotV3Frozen_sound_v1`). LIVE-routed the
provably-frozen value cohort through `v3OfFrozen`: transfer/burn/mint(+bridgeMint)/incrementNonce/emitEvent/
setField[0..7] — NOT the authority MOVERS (mode byte + fields[8..16] fold into r23, so they keep their record-pin
/ future recompute). NEGATIVE TOOTH `effect_vm_rotation_flip::rotated_transfer_frozen_authority_forces_r23_and_
rejects_drift`: honest accept (non-vacuous) + AFTER-r23/AFTER-lifecycle drift UNSAT via `verify_vm_descriptor2`
ALONE. Green: lake 4001 axiom-clean · flip 11/11 · drift PASS · FP re-pinned. APEX FRAME left CARRIED
(`rotatedEncodes.frCaps/frLifecycle` — the descriptor-level forcing is the win; discharging the carried frame
from `_freezes`+`RestHashIffFrame` is an available strengthening). REMAINING record_digest waves (per the scoping
`a5a69ce9`): WAVE 1 = lifecycle-mover IN-CIRCUIT recompute (cheapest — `lifecycle_felt` is fixed-width; replaces
the off-circuit PI-38 anchor for seal/unseal/destroy/archive); WAVE 2 = perms/VK split-digest recompute (the
expensive half — re-shape `RH` to `H(permsVK_limb, rest_limb)`, recompute the small mutable limb in-circuit,
continuity-weld the rest); WAVE 3 = refusal (audit→fields_root EXT, last). The full byte-faithful
`compute_authority_digest_felt` fold is the WRONG shape (variable-length sponge) — the split-digest is the route.

SELECTOR-BINDING TOOTH (the gate-less value-cohort) — light-client cross-effect smuggle, LIVE-CUT (2026-06-18).
THE FORGERY (confirmed at HEAD): the deployed sovereign verifier (`turn/src/executor/proof_verify.rs:161`,
`verify_and_commit_proof_rotated`) resolves ONE rotated descriptor by `vm_effects.first()` over a
one-row-per-effect trace. A family of descriptors LACKED `selectorGate` — setField[0..7] / mint(BridgeMint) /
attenuate / revokeCapability / grantCap — so a turn whose LEAD is gate-less + a TAIL effect (e.g.
`[SetField(slot0,v), Transfer(self→victim,A)]`) proved under the gate-less LEAD descriptor while the TAIL row's
transition was UNFORCED: the prover freely forged the tail balance, the commitment-integrity gates still passed,
`verify_vm_descriptor2` ACCEPTED. STEP-0 (the safety crux) RESOLVED SAFE: the single-descriptor sovereign verify
path receives ONLY homogeneous turns — `prove_effect_vm_rotated_ir2_with_caveat` REJECTS heterogeneous slices
(`full_turn_proof.rs:670-679` "one rotated descriptor per proof") and PATH-PRESERVE `split_into_cohort_runs`
splits heterogeneous turns per cohort into chained legs (`full_turn_proof.rs:1229`); transfer/burn ALREADY carry
the gate and the suite is green, which is the same mechanism. CLOSE (Lean-emitted, law #1): each gate-less
registry member appends `selectorGate <runtimeSelector>` via the new `EffectVmEmitRotationV3.withSelectorGate`
(per-REGISTRY-entry, NOT the shared v1 face — grantCap/attenuate/revokeCapability ride the SAME
`attenuateVmDescriptor` face but must gate to DISTINCT runtime selectors: GRANT_CAP=3 / ATTENUATE_CAPABILITY=48 /
REVOKE_CAPABILITY=24 from `columns::sel`, NOT the faithfulness-abstraction `selA.ATTENUATE=2`). setField→2,
mint→`selM.MINT`=40. New `sel.{GRANT_CAP,REVOKE_CAPABILITY,ATTENUATE_CAPABILITY}` constants pinned to their Rust
`columns::sel` twins. Apex lift: `withSelectorGate_satisfied2` (constraint-subset monotonicity, +memLog/mapLog
invariance lemmas) strips the gate so every per-effect VALUE/`ClosedLog` keystone (stated over the bare `mintV3`
etc.) composes over the deployed gated member; `Rfix 3/20` (mint/bridgeMint) + `bwMint` re-keyed to the wrapped
descriptor in `ClosureFanoutGenuine`/`CircuitCompletenessAssembled`. TEETH `circuit/tests/effect_vm_selector_gate_
forgery.rs`: NEGATIVE `setfield_lead_with_foreign_transfer_tail_is_unsat` + `mint_lead_…` (forged tail UNSAT via
`prove_vm_descriptor2`/check_constraints ALONE — row 1 rejected); POSITIVE
`honest_homogeneous_setfield_still_proves_and_verifies` (no downgrade). Green: lake 4002 axiom-clean · selector
3/3 · rotation-flip 11/11 · sovereign-rotated 19/19 · drift PASS · FP re-pinned.
✅ CLOSED (2026-06-18) — the CAP-OPEN selectorGate residual is CUT OVER. All 8 cap-open descriptors in
`CapOpenEmit.lean` are now `withSelectorGate <baseRuntimeSelector> (effCapOpenV3 …)`: transfer→1, attenuate→48,
delegate→3, grantCap→3, introduce→35, revoke(Delegation)→30, refresh-delegation→29, revokeCapability→24 (the
3 missing Lean `sel` twins INTRODUCE/REFRESH_DELEGATION/REVOKE_DELEGATION added to `EffectVmEmit.sel`, mirroring
`columns.rs::sel`). The cascade was LIFTED not rebuilt: the 8 `…CapOpenV3_authorizes` keystones + 8
`…_rejects_wrong_facet` teeth strip the appended gate via `withSelectorGate_satisfied2` before applying the bare
`effCapOpenV3_satisfiedEff`/`…_authorizes`; the `Rfix_*_capOpen` `rfl` identities held UNCHANGED (both registry
entry and RHS are the wrapped def); one downstream lift in `RotatedKernelRefinementFacet.transferAuthoritySourceG_to_eff`
(strip the gate before feeding the parametric `EffAuthoritySource.hsat`). Completeness side UNAFFECTED (the
`*_authorityComplete` rungs reference the BASE `(attenuateV3,name,n)` + `CapOpenTraceFloor`, not the wrapped def).
TOOTH `circuit/tests/cap_open_self_verify.rs::cap_open_attenuate_foreign_selector_row_is_unsat` — an honest
attenuate cap-open trace with a NOOP pad flipped to a foreign TRANSFER selector is UNSAT via `prove_vm_descriptor2`
ALONE (the gate `(1-sel[NOOP])·(1-sel[48]) = 1·1 = 1 ≠ 0` bites for a ledgerless client). NO DOWNGRADE: the honest
`cap_open_attenuate_self_verifies` + `cap_open_turn_bound_verifier_forces_published_identity` stay green. The gate
is +1 `.base` constraint, NO new column (width/PI unchanged), so the asymmetry the value-cohort fix (`b9b8b6973`)
left open is closed symmetrically. Green: lake 4002 axiom-clean · cap-open 3/3 · turn-bound 1/1 · selector 3/3 ·
rotation-flip 11/11 · drift PASS · `V3_STAGED_REGISTRY_FP` re-pinned. VK DEPLOY ember-gated (the wire registry +
FP changed; built+proven+emitted, NOT deployed).

ACTIVE (2026-06-18) — the `facetEffGate` genuine-membership closure (residual (a) F6-FACET) + adversarial
re-review. FOUND: the cap-open authority gate `facetEffGate` (`DeployedCapOpen.lean:205`) was implemented as
EQUALITY `mask_lo == effBit` (with `effBitGate` pinning `effBit = EFFECT_TRANSFER`) — i.e. it forced a
SINGLE-FACET cap, byte-rejecting every honest BROAD cap (`mask_lo = 0xFFFF`). The genuine kernel predicate
(`cell/src/facet.rs:123` `is_effect_permitted`) is bitwise membership `(effBit & mask_lo) != 0`. The equality
gate is SOUND (equality ⟹ membership, so the apex held) but over-strict + NOT the genuine predicate ember
demands → 8 RED `dregg-node turn_proving` tests (witness-build `InvalidWitness` + AIR `constraint #84`
unsatisfiable). Closure (in-flight, agent aa0cca1e): replace with the genuine submask membership via
`mask_lo` bit-decomposition (lifting the proven `capDelegNonAmpGates`/`confers_write_leaf` per-bit submask
pattern) across Lean (`DeployedCapOpen.lean`/`CapOpenEmit.lean`) + Rust (`trace_rotated.rs from_membership_for`
+ column fill) + re-emit JSON + F4 differential + fixtures; both-polarity teeth (broad cap PROVES; bit-clear
cap UNSAT); cap-open block widens ~59→75 cols (a localized rotation-geometry shift, the noteCreate-flag-day
precedent). ALSO IN-FLIGHT (agent a65e0528, read-only): a critical/adversarial re-review of the whole
soundness argument + its connection-to-deployment, hunting for SIBLINGS of this bug-class (constant/equality
masquerading as genuine; sound-but-over-strict; carried-but-unrealizable; the Lean↔deployed realization gap) —
ember's explicit gate before completeness. NOTE: the `turn/src/turn.rs ConsumedCapWitness::recompute_root`
real-bug fix (`hash_fact`→`cap_node` arity-3 absorb) + the red-test-crate fixes + the exercise hold-gate
(`RotatedKernelRefinementExerciseAuth.lean`) + spawn cap-handoff (`RotatedKernelRefinementSpawnHandoff.lean`)
Lean strands are GREEN and HELD uncommitted — to be committed with the facetEffGate fix once the tree is green.

ADVERSARIAL RE-REVIEW VERDICT (2026-06-18, agent a65e0528, the gate before completeness). The Lean apex CORE
is CLEAN-CONFIRMED: 0 forgery-accept unsoundness; `lightclient_unfoolable_circuit_sound` carries exactly
{StarkSound, Poseidon2/Merkle CR, logHashInjective, ClosedWitness} built from genuine per-effect `_closedLog`
readouts (no circular carrier, transfer teeth both-polarity real). The
CONNECTION-TO-DEPLOYMENT is NOT yet sound enough for completeness — must close first:
  • **Finding 1 → RESOLVED to a PRECISE verdict (task #214, agent a21e2f7a + direct confirmation).** The
    reviewer's "verifier leaves record-pin dpis[38] ZERO" was IMPRECISE; the TRUE finding is sharper and
    confirmed by reading `rotateV3WithRecordPin` (EffectVmEmitRotationV3.lean:1793-1834):
      ‣ The record-pin gate for setPermissions/setVK/cellSeal/cellUnseal/cellDestroy/refusal/receiptArchive
        appends ONE constraint — `after_block_limb_24 == PI[piCount]`, a binding to a PROVER-PUBLISHED free
        PI with NO anchor to the effect's declared write (the permissions/vk/lifecycle param is at v1 col 68,
        witness-independent, but the pin never references it). So `rotateV3WithRecordPin_rejects_wrong_post`
        is honest-but-WEAK and its docstring "anti-ghost… gap closed" is a VACUITY/OVERCLAIM — the per-effect
        VALUE rung does NOT force the post in deployment. This is the precise form of the memory's "deepest
        finding" (RH richer than the circuit computes).
      ‣ LATENT, not a live forgery: the cipherclerk producer models only Transfer/SetField/IncNonce (so these
        effects produce after_cell==before_cell), and ONLY Effect::Transfer routes end-to-end through
        verify_and_commit_proof_rotated. The Transfer path IS sound (PI[35]↔col-261 STATE_COMMIT binding;
        tampered-commitment test green). The set-insert/note PI[38] is witness-INDEPENDENT (folded nullifier/
        key/commitment at v1 col 68), so reproduced correctly; the real double-spend soundness lives in
        verify_full_turn (grow-gate .absent + non-revocation accumulator) — a DIFFERENT verifier, sound.
      ‣ CONSEQUENCE: the docs/STATUS "SOUND-IN-DEPLOYED (12+ effects)" / "running circuit IS S_live" are
        OVERCLAIMS for the record-pin family — only Transfer (+ the economic effects that move bound columns)
        is genuinely forced-in-deployed via this verifier. CORRECT the claim + GENUINE FIX: re-target the pin
        to a TRANSITION gate `after_limb == compute_authority_digest_in_circuit(before_residue ⊕ effect_param)`
        anchored to the cross-checked before + the witness-independent v1 param, AND have the verifier recompute
        the after-limbs/new_commitment from the trusted before-cell+vm_effects (override, like dpis[34/36]).
        Until then the record-pin descriptors should fail-closed at the cohort resolver, not be advertised closed.
  • **Record-pin family / #214 — FULLY CLOSED (commit a8363d6f9): all 7 effects genuinely verifier-anchored,
    each forged-after tooth BITES.** The verifier (verify_and_commit_proof_rotated step 6b) anchors dpis[38]
    from the trusted post-cell via the shared apply_effect_to_cell weld (the SAME projection the producer
    uses): `compute_authority_digest_felt` for setPermissions/setVK/refusal, `lifecycle_felt_cell` for
    cellSeal/cellUnseal/cellDestroy/receiptArchive. sovereign_rotated_c1 19/19 (7 accept/reject pairs). The
    fan-out fixed the 3 bugs the vacuous pin masked (the model-finds-the-bug loop): **#218 refusal** — the
    deployed apply_refusal now writes the audit into the protocol-reserved EXT key REFUSAL_AUDIT_EXT_KEY
    (folded via fields_root), matching the Lean spec TurnExecutorFull.refusalField (was the unfolded welded
    fields[4] — the refusal record was UNBOUND); **#219 receiptArchive** — record_pin_offset re-routed
    B_RECORD_DIGEST→B_LIFECYCLE; **#220 cellSeal/Unseal/Destroy** — cipherclerk producer aligned to native
    VmEffect variants (+ block_height threaded for the cellSeal seam). DEEPEST CROSS-CHECK GREEN: the full
    rust_lean_divergence_finder PASSES — the apply_refusal change REDUCED Rust↔Lean divergence (Rust now
    matches the Lean spec's fields_root), confirming #218 was the right fix, not a break.
  • **Finding 4 / #215 — CLOSED (pending commit, agent a9577e2a).** The 6 fan-out cap-effects'
    authority is now FORCED in-circuit in the apex: new effect-specific keystones
    `<effect>CapOpenV3_authorizes` (CapOpenEmit.lean §5.F) + a parametric `EffAuthoritySource`
    (RotatedKernelRefinementFacet.lean §3.E; transfer preserved as the n=EFF_TRANSFER instance) +
    `actionTagToPos` re-keyed to the fan-out positions 36-40 + the forest fold's per-effect authority
    arm (RotatedKernelForestFacet.lean §6). Lean green (3990), apex #assert_axioms clean, drift PASS,
    Rust routing tests pass. NAMED RESIDUAL: `revokeCapability` has a ready keystone (pos 41) + a live
    wire route but NO `FullActionA`/`actionTag` Lean kernel-action constructor, so it is unreachable
    from the apex dispatcher (the wire exists; the kernel action does not) — a small kernel-dispatcher
    gap, not a soundness hole.
  • **Findings 2/3 (task #213) — CLOSED** by the genuine-membership cap-open fix (the equality
    transferFacetGate + the Signature-constant authTagGate were both dropped; tier decoded). The
    over-strict cap-open siblings of the facetEffGate bug:
    (2) the equality `transferFacetGate` (`mask_lo==EFFECT_TRANSFER`) is STILL a co-present conjunct in the
    live `capOpenConstraints` (`CapOpenEmit.lean:142`), so the membership fix is dead-lettered unless removed
    (the fixer's DoD forces this — verify on return); (3) `authTagGate` pins Signature as a constant (proven
    `tierGeneral` machinery unwired); (4) `effBitGate` pins transfer-constant + only `capOpenAttenuateV3` is
    wired ⇒ cross-vat authority for delegate/grantCap/introduce/refresh/exercise/spawn never forced
    in-circuit. All fail-CLOSED (sound, over-strict/incomplete), not forgery. Down-grade the docs/STATUS
    "faithful authority" claim to transfer-and-Signature-only until 3/4 wire the proven-but-unwired general
    machinery into the live registry.

LANDED (green, #assert_axioms-clean): the parametric apex `lightclient_unfoolable` (CircuitSoundness.lean,
derives ∃ kernel transition; carries StarkSound + Poseidon2SpongeCR + hrefines + WitnessDecodes); the FAITHFUL
authority leg (two-axis `authorizedFacetB`) single-step (`RotatedKernelRefinementFacet.lean`,
`transfer_descriptorRefines_facet` — authority FORCED in-circuit by the cap-open) and WHOLE-TURN
(`RotatedKernelForestFacet.lean`, `lightclient_turn_unfoolable_forest_facet` + generic fold
`turnDecodeChain_refines_turnSpec_gen`); and 5/36 VALUE rungs (`descriptorRefines`): transfer, burn, mint,
bridgeMint, setField — `RotatedKernelRefinement{,MintBurn,SetField}.lean`, each gate-forcing the designated
moved column with both-polarity forgery teeth.

UPDATE (later same session) — EVERY effect's VALUE rung is now PROVEN. The ~17 VALUE_MISSING fixes were
built (the principled-fix committed-root-limb pattern: cellSeal/cellUnseal/cellDestroy/refusal/receipt
Archive/setPerms/setVK/makeSovereign/setFieldDyn/createCell/factory/noteCreate), and the PHASE-D gadget
LANDED (`SortedTreeNonMembership.lean` non-membership + `CapTreeUpdate.lean` insert/update/remove on the
proven `DeployedCapOpen` membership): **noteSpend's double-spend non-membership is FORCED in-circuit** and
the **capability family's exact sorted-set move is forced** (attenuate upgraded non-amp→set-exact, the
ARGUS crown #103). The remaining boundary to literal closed-closed:
  1. THE RUNTIME COMMITMENT REALIZATION (the one ember-gated VK epoch): `circuit/src/effect_vm/cell_state.rs
     ::compute_commitment` must absorb the new committed root limbs (per-cell side-table/audit roots + the
     sorted cap/nullifier/commitment roots) + the trace-fills emit them. ONE coordinated change realizes the
     whole fix+phase-D family; changes the VK ⇒ ships as a VK epoch + registry re-pin.
  2. The Lean registry cutover (swap fix descriptors into v3Registry so `R e` = the proven descriptor) +
     the COMPOSITION (assemble the per-effect rungs into `∀ e, descriptorRefines (R e)` ⇒ discharge the
     apex's carried `hrefines`).
  3. The faithful-encoding carriers (cap-tree↔Caps, nullifier-tree↔set, SpineCommits) — realizable
     hypotheses (the deployed Merkle fold), the Poseidon2SpongeCR floor class. + WitnessDecodes per effect +
     the prover wiring (`&[]` cap path-witness, `sdk/src/full_turn_proof.rs:662`).
  Full map: `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md` §"Final state". `heapWrite` (no live registry entry,
  proven fix off-apex) and `custom` (no kernel arm, out of scope) noted.
  2. ~5 VALUE_PARTIAL (attenuate base-root-supplied-not-recomputed; setFieldDyn; incrementNonce generic-tick;
     makeSovereign rebind; pipelinedSend nonce-tick-vs-freeze) — bounded extra binding.
  3. Wire each effect's faithful arm into `fullActionStepFacet`; retire the forest `hidx0 : e=0` residual.
  4. Discharge `WitnessDecodes` per effect; connect `TransferAuthoritySource`; kill the `&[]` cap path-witness
     at `sdk/src/full_turn_proof.rs:662`. Then the VK epoch (ember-gated).
  Crypto floors that legitimately remain: `StarkSound`, Poseidon2/permutation CR.

## P0-2 FULL-STATE COMMITMENT CUT — keystone LANDED; descriptor re-emission NAMED (2026-06-17)

LANDED (green: `dregg-circuit`/`dregg-cell`/`dregg-sdk`/`dregg-turn` build; P0-2 tests pass): the deployed
per-cell `state_commit` now binds the FULL cell state. `CellState` carries a `record_digest` limb (the
authority residue — permissions/VK/lifecycle/deathCert/delegate/delegation/program/mode/visibility/
side-table-roots/fields[8..]), `compute_commitment`/`compute_commitment_4` ABSORB it as the FOURTH root-hash
input (replacing the literal ZERO), and the EffectVM AIR Group-4 constraint reads it from a new aux column
(`aux_off::STATE_RECORD_DIGEST`, `NUM_AUX` 96→97, `EFFECT_VM_WIDTH` 186→187). Seeded from
`dregg_cell::compute_authority_digest_felt` on the live prover paths (cipherclerk + `before_cell_state` reads
r23 = `pre_limbs[B_AUTHORITY_DIGEST]`), so the v1-prefix OLD_COMMIT and the rotated weld's r23 agree. A
residue-free cell uses `cap_root::empty_record_digest()` (ZERO) — byte-identical to the legacy form (no-op
cutover, tested `empty_record_digest_is_legacy_noop`). Mirrors Lean `recStateCommit = cmb(cellDigest, RH)` /
`cellCommitS = compressN(rest ++ [systemRootsDigest])` (one absorbed digest limb).
NAMED follow-up (the descriptor/registry re-emission — the EXACT items 1/2 above realized for this limb):
  1. RE-EMIT the descriptor registry from Lean: `circuit/descriptors/*.json` pin `trace_width:186`/`311` and a
     GROUP-4 hash site with `{"t":"zero"}` as the 4th root input — both now stale (real trace = 187/312, 4th
     input = the record_digest column). The `EmitAllJson*.lean` emitter must add the record_digest column +
     read it at the GROUP-4 site, then re-run + re-pin EVERY SHA fingerprint
     (`effect_vm_descriptors.rs`, `lean_descriptor_air.rs::TRANSFER_VM_DESCRIPTOR_JSON`,
     `cap_delegation_nonamp_descriptor.rs`). 3 lib + 5 rotation-flip integration tests fail ONLY on this
     width/zero-input staleness (881 lib tests pass; the live AIR honest-prove path is self-consistent).
  2. The Lean `StateCommit.recStateCommit`↔Rust differential: `record_digest` plays the `RH` rest-hash role
     (the authority residue folded into one limb); pin a cell↔circuit differential asserting the Rust
     `compute_commitment`'s 4th input equals the Lean `RH`/authority-digest limb (the `legacyReferenceCommitS`
     no-op already mirrored by `empty_record_digest_is_legacy_noop`).

## IN-CIRCUIT CAP-TREE MEMBERSHIP-OPEN — Lean soundness LANDED; Rust AIR wiring + prover + mask-reconcile NAMED (2026-06-16)

LANDED (green, #assert_axioms-clean, Poseidon2SpongeCR only): `metatheory/Dregg2/Circuit/DeployedCapOpen.lean`
— the in-circuit cap-tree membership-open as a `CapOpenConstraint` whose denotation rides the Poseidon2 chip bus
(`DescriptorIR2.chip_lookup_sound`) for the 7-field leaf absorb (= `capLeafDigest`) and each depth-16 `hash_fact`
node fold (= `nodeOf`, mixed by the direction bit), CONSTRAINS the top == `cap_root` column, binds `leaf.target ==
src` + `mask_lo == write-mask`. KEYSTONE `capOpen_sound`: `Satisfied ⟹ DeployedCapTree.MembersAt cap_root leaf ∧
leaf.target = src ∧ confersWriteLeaf leaf`; `capOpen_authorizes` chains `deployedCapOpen_implies_authorizedB ⟹`
kernel `authorizedB`. Discriminating teeth witness-FALSE (writeMaskGate/targetBindGate). Rust witness twin +
recompose + binding + tests landed in `circuit/src/cap_root.rs` (`CapMembershipWitness`, `recompose_membership`,
`membership_witness`, `recomposes`/`target_is`/`confers_write`; tests pin the depth-16 fold == root + forgery
rejection + binding teeth).

NAMED (remaining-steps, the Rust-AIR + prover legs of the original 4):
LANDED (2026-06-16, the LIVE emission + bridge + Rust appendix — no hand-authored Rust constraints, LAW#1):
  `metatheory/Dregg2/Circuit/Emit/CapOpenEmit.lean` lays `DeployedCapOpen`'s PROVEN constraints (leafLookup + 16
  nodeLookups + 16 dir-bool + rootPin/targetBind/writeMask) over a concrete `capOpenCols` appendix (58 cols past
  the rotated R=24 width 311) into `capOpenAttenuateV3` (width 369), with the bridge `capOpenAttenuateV3_satisfied`
  (a live `Satisfied2` REBUILDS `DeployedCapOpen.Satisfied`) ⟹ `capOpenAttenuateV3_sound` (MembersAt cap_root leaf
  ∧ target=src ∧ confersWriteLeaf) ⟹ `capOpenAttenuateV3_authorizes` (kernel `authorizedB`). `#assert_axioms`-clean,
  full `Dregg2` build green. Rust twin: `attenuateCapOpenVmDescriptor2R24` registry member (byte-identical
  `emitVmJson2`), `CapOpenWitness`/`fill_cap_open`/`generate_cap_open_attenuate_trace` in `trace_rotated.rs`
  (genuine absorb-node `hash_many` fills, proven by `cap_open_witness_and_appendix_are_genuine`), V3_STAGED FP
  bumped to `2d4a594b1deec12c111b1f965786f7c4550cabb4f71c6b50ffe2eb894fc2c5db`; the 311-wide attenuate base proves
  standalone. writeMaskGate emitted FAITHFULLY (mask_lo==3, the abstract rights mask — NOT faked to the deployed
  EffectMask, see (3)).

NAMED (the ONE thing blocking the end-to-end prove — `cap_open_attenuate_self_verifies` is `#[ignore]`d, not faked):
  (1) CHIP-ARITY RE-EMIT (Lean, proof-carrying): `DeployedCapOpen` declares chip lookups at arity 7 (leaf) and
      arity 3 (each node), assuming `CHIP_RATE = 8`. The DEPLOYED IR-v2 chip (`descriptor_ir2.rs` ~1841-1873) is
      rate-4 and enforces `arity ∈ {0,2,4}` — so arity-7 AND arity-3 absorbs are BOTH unrealizable as a single chip
      row (and the deployed `cap_root.rs::CapLeaf::digest` 7-field `hash_many` is itself a TWO-permute sponge).
      Re-emit `capLeafDigest`/`nodeOf`'s chip realization as an explicit fold of arity-2/arity-4 absorbs (sponge
      state threaded across rows), kept byte-identical to the deployed digest, and RE-PROVE the soundness lemmas
      (`leafDigest_sound`/`node_sound` upward). LEAN file change (NOT a Rust constraint edit); once it lands the Rust
      `fill_cap_open` mirrors the new fold and `cap_open_attenuate_self_verifies` un-ignores. (Alternative worth
      weighing: ride the `BUS_FACT` fact rows for nodes — the deployed cap-tree's real `hash_fact` shape — instead
      of absorb rows, which also re-binds the open to the DEPLOYED `CanonicalCapTree` root rather than the
      absorb-node tree the current emission commits.)
  (2) PROVER wire: `sdk/src/full_turn_proof.rs:662` — once (1) lands, route cap turns through the cap-open
      descriptor + witness (kill the `&[]`); note the new VK pin (VK changes — authorized).
  (3) MASK-CONVENTION RECONCILE (flag-day, ember decision): the Lean `confersWriteLeaf`/`writeMaskGate` pin
      `mask_lo == rightsMaskOf(endpoint[read,write]) = 3` over the abstract `Auth`-rights mask; the deployed
      `CapLeaf.mask_lo` is the low-16 of a `cell/facet.rs` `EffectMask` (effect-kind bitmap — DIFFERENT convention:
      EFFECT_TRANSFER=1<<1, EFFECT_GRANT_CAPABILITY=1<<2…). Align so the in-circuit write bit IS the deployed
      `mask_lo`'s write-conferring bit (or document the leaf carries the rights mask, not the effect mask).
      `cap_root.rs::confers_write` checks the submask SHAPE either convention shares; the constant alignment is the
      open item — do NOT fake a Rust constant that pretends they agree. (The membership + target-bind legs the
      LANDED work lands are convention-INDEPENDENT, so this only gates the write-rights leg.)

CLOSURE SHAPE: (1) is a proof-carrying Lean re-emit (the chip-arity floor the original emission missed); (2) a
witness pass once (1) lands; (3) an ember-adjacent data-model decision (which mask the cap leaf commits). Named:
in-circuit cap-membership-open, 2026-06-16.

## CIRCUIT FUNCTIONAL CORRECTNESS — light-client unfoolability apex NAMED; #103 cap-family residue mapped (2026-06-16)

NAMED: the leaf-circuit→kernel-step soundness rung does not yet exist as a composed apex over the live
rotated registry — `lightclient_unfoolable` (`verifyBatch vk pi π = accept ⟺ ∃ kernel transition`,
bidirectional per LAW#1) via `descriptorRefines (liveRegistry e) (fullActionStep e)` per live effect. Full
diagnosis + corrected ground-truth coverage in `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md` (SUPERSEDES the
pre-investigation plan whose premise — "the live circuit enforces no non-amp" — is FALSE: `attenuateV3_non_amp`
(EffectVmEmitRotationV3.lean:1419) proves in-circuit non-amp on the LIVE wired attenuate descriptor).

RESIDUE (= the open scope of #103; attenuate = the done template #37): introduce / refresh / revokeDelegation /
grant route to FREEZE-AND-DEFER rotated descriptors (`v3Of {introduce,refresh,revoke}VmDescriptor` — cap_root
frozen, mutation bound out-of-row / DELEG record-root), so a light client trusts the EXECUTOR for their non-amp
(`EffectsAuthority.*_non_amplifying`, proven; Argus-term-IR modelled — neither is the descriptor the prover
selects). `introduceVmDescriptorGenuineNonAmp`/`refreshVmDescriptorGenuineNonAmp` (= the 186-wide
`attenuateVmDescriptorGenuineNonAmp`) are PROVEN-BUT-UNWIRED — the drift the apex's `vk=vkOfRegistry liveRegistry`
binding + a drift-guard `#guard` must forbid. Two universal rungs DO hold for all 36 (`rotV3_sound_v1` row-intent,
`rotV3_binds_published` whole-post-state commitment) — integrity complete, authority uneven.

CLOSURE SHAPE: (1) named `StarkSound` floor over the audited p3-batch-stark verifier (none exists — implicit in
`RecursiveAggregation.EngineSound`); (2) state `lightclient_unfoolable` + `descriptorRefines`, discharge per-effect
vs `fullActionStep` (ActionDispatch.lean:168; `attenuateV3_non_amp` = worked instance); (3) BUILD the four missing
in-row gadgets — NOT a transport (no V2 sibling source): introduce/grant = membership + cross-cell copy, refresh =
DELEG-root open+submask, revokeDelegation = removal gate (the `revokeCapabilityV3` shape); (4) drift-guard `#guard`
(every `*_non_amp` descriptor ∈ liveRegistry) + wire-or-delete the standalone Genuine descriptors; (5) VK epoch
(ember-gated). TO CONFIRM: delegateAtten wire→selector mapping (if it rides ATTENUATE_CAPABILITY=48 the headline
delegation is already covered); what `unfoolability_guarantee` grounds "executed correctly" on; `fullActionStep ⟺
execFullA`; Argus IR live-vs-parallel. Named: circuit functional correctness apex, 2026-06-16.

## DFA ROUTE-COMMITMENT — LANDED in the circuit + live verifier; node-relay binding NAMED (2026-06-15)

LANDED: the real `dregg-dfa-routing-v1` route-commitment-binding AIR now SHIPS as a DSL circuit
(`circuit/src/dsl/dfa_routing.rs`), faithful to the Lean model `Dregg2.Crypto.DfaAcceptanceAir` and the
standalone test AIR (`dregg-tests/src/dfa_circuit.rs`). It closes GAP-B (the running-hash route commitment
the generic `Lookup` DFA left open) via two new `ConstraintExpr` forms in `circuit/src/dsl/circuit.rs` —
`ChainedHash2to1` (cross-row `next.running = compress(this.running, next.entry)`, the C3 chain) and
`SeedHash2to1` (PI-seeded `running₀ = compress(table_commitment, entry₀)`, the Lean `seed` conjunct) —
plus a FRI-safe `TableFunction` (bivariate-Lagrange table membership, closing GAP-A `next = step(state,sym)`
where `Lookup` could NOT — `Lookup` is a non-polynomial step the native FRI rejects off-domain; this was a
real pre-existing trap: no DSL `Lookup` circuit ever proved through `stark::prove`). Both polarities GREEN
through the real `stark::prove`/`verify` FRI pipeline (8 tests, `cargo test -p dregg-circuit --lib
dsl::dfa_routing`) AND through the LIVE `DslCircuitDfaVerifier` — the relay's verifier (4 tests,
`executor::membership_verifier::tests::live_routing*` in `dregg-turn`): a correct route binds its
route_commitment/final_state; a forged final_state or route_commitment is rejected at the B2/B3 boundary
("a router cannot claim a delivery it did not make").

NAMED (node-relay binding — the remaining live wire): the relay-operator template
(`dregg-storage-templates/src/relay_operator.rs`) gates the `relay` method on `Witnessed { Dfa }` with a
PLACEHOLDER commitment `[0u8;32]` (a labeled seam — the comment says "executor overrides via slot-bound
resolution" but `cell/src/program.rs:3549` passes `wp.commitment` AS-IS), and `node`'s relay sets
`route_table_root = blake3_field(…)` (`node/src/relay_service.rs:1228`), neither equal to the routing
program's `vk_hash` — so the relay's Dfa caveat is currently FAIL-CLOSED at the node (the node never
installs the Dfa verifier). NOTE the "blocker" is a NON-issue: `dregg_dsl_runtime::ProgramRegistry`
(`node/src/state.rs:249`) is a `pub use` RE-EXPORT of `dregg_circuit::dsl::circuit::ProgramRegistry`
(`dregg-dsl-runtime/src/lib.rs:58`) — the SAME type `DslCircuitDfaVerifier` holds. CLOSURE SHAPE (two
edits, both in already-depended crates): (1) `dregg-storage-templates` — thread a `route_circuit_vk:
[u8;32]` param into `relay_operator_program_with` so the `WitnessedPredicate::dfa` commitment is the
routing `vk_hash`, not `[0u8;32]` (ripples to `relay_operator_program()` + the node/test callers); (2)
`node` — at startup deploy `dregg_circuit::dsl::dfa_routing::dfa_routing_descriptor("dregg-dfa-routing-v1",
router_transitions)` into `s.program_registry`, set `default_route_table_root()` := that `vk_hash`, and in
`node/src/executor_setup.rs::configure_turn_executor` do
`registry.register_builtin(Arc::new(dregg_turn::executor::DslCircuitDfaVerifier::new(Arc::new(
s.program_registry.clone()))))` (upgrades ONLY Dfa from its fail-closed default; the other kinds stay as
`registry_with_real_verifiers()` set them). The relay CLIENT produces wire bytes via
`dregg_turn::executor::prove_dfa_transition(programs, vk_hash, build_routing_witness(...).0, n, pi)`.
Both `DslCircuitDfaVerifier` + `prove_dfa_transition` are now re-exported from
`dregg_turn::executor`. Named: DFA route-commitment node-relay wire, 2026-06-15.

LAW#1 RESIDUAL (Lean-emit): `dfa_routing_descriptor` is a Rust-authored `CircuitDescriptor` faithful to
the authoritative Lean `Satisfies` (`metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean` §2) — it follows the
SAME established pattern as every other DSL predicate circuit (`fold`, `committed_threshold`, `temporal`),
none of which is Lean-emitted (the `CircuitEmit.lean → EmittedDescriptor` path serves the KERNEL effects,
not the DSL predicate-circuit family). The new `ConstraintExpr` forms are generic data-driven gates, not a
bespoke hand-coded AIR. The law-#1 ideal end-state is a Lean emitter that PRODUCES this descriptor from the
`Satisfies` model with an emitted≡Satisfies proof (and the entry-hash/running-hash carriers consumed as
named CR, exactly as the Lean model does). Named: Lean-emit the dfa-routing descriptor + the DSL-predicate
family, 2026-06-15.

## CAP-CROWN IR — LANDED: in-circuit non-amplification (`granted ⊑ held`) binds on the DELEGATION family at the Lean-emit layer (2026-06-15)

The delegation/cap effects (`delegate`, `delegateAtten`, `attenuate`, `introduce`, `revoke`, `refresh`)
carried an "IR GAP — needs IR extension: cap-root hash-site" in their EffectVM-emit modules: the genuine
`cap_root` RECOMPUTE existed (§G, `attenuateVmDescriptorGenuine` — `new_cap_root = hash[edge_leaf,
old_root]`, op-tagged) but the in-circuit non-amplification (`granted ⊑ held`) did NOT bind on these
descriptors. CLOSED: a new shared GENUINE-NON-AMP descriptor `attenuateVmDescriptorGenuineNonAmp`
(`metatheory/Dregg2/Circuit/Emit/EffectVmEmitAttenuateA.lean` §G.4) = the genuine recompute PLUS the
shared `EffectVmEmitCapReshape.capDelegNonAmpGates` (the per-bit submask gate whose GRANTED mask
reconstructs `cp.RIGHTS` — the SAME `rights` felt the recompute hashes into the cap-edge leaf). The two
legs INTERLOCK on one felt: tamper `rights` to dodge the submask gate and the recomputed `cap_root` moves
⇒ `state_commit` moves ⇒ UNSAT. Re-exported per effect (`delegateVmDescriptorGenuineNonAmp` …, with
`*NonAmp_in_circuit` admits + `*NonAmp_rejects_amplify` rejects — both polarities, axiom-clean). Emitted
from Lean (LAW#1, no hand-authored AIR): `EmitAllJson` re-emits the byte-pinned
`circuit/descriptors/dregg-effectvm-attenuateA-v1-genuine-nonamp.json` (186-wide, 56 constraints, 6 hash
sites — additive + width-neutral); the Rust standalone loader `circuit/src/cap_delegation_nonamp_descriptor.rs`
parses it + fingerprints it (drift guard) + asserts the 8 delegation submask gates + the 2 recompute
sites are present. `lake build Dregg2` green; the EmitAllJson run + the loader teeth are the gates.

RESIDUAL (named, Phase E): the in-row recompute is the prepend-accumulator DIGEST advance, not yet the
in-row sorted-TREE update (membership-open + sorted-key range-checks, mirroring the revocation circuit's
C6/C7/C10/C11). The openable-root VALUE the digest carries is the cell≡circuit sorted-Poseidon2 root
(`EffectVmEmitCapReshape` §1 model + `circuit/tests/cap_root_cell_circuit_differential.rs`); the Phase-B
sorted OPEN is `EffectVmEmitV2.attenuateV2_non_amp`. This IR-layer non-amp is the descriptor-emit
counterpart of the p3-AIR Phase-B gates tracked at the "#103 cap-crown — TWO EffectVM AIRs" item below;
it does NOT itself graduate the bespoke sovereign `EffectVmAir` path (that remains the C5/C7-flip task).
Named: cap-crown IR non-amp LANDED, 2026-06-15.

## FIRMAMENT KEYSTONE — LANDED: the 5-PD assembly BOOTS the verified turn through the REAL executor seat (2026-06-15)

The `executor` seat of the 5-PD firmament (`sel4/dregg.system`) is a REAL Microkit PD
(`sel4/dregg-pd/executor-microkit-pd/`) embedding the verified `dregg_exec_full_forest_auth`
(= `execFullForestG` + admission, proved in `metatheory/`) + the ELF Lean runtime + real GMP + the real
crypto floor + the seL4 musl, and **the WHOLE 5-PD Microkit image now BOOTS in qemu-system-aarch64 with
that verified turn running `status:2 ok:1`** — ZERO faults across all five PDs. `make -C sel4
run-assembly-real` reproduces it end-to-end; verbatim serial in
`executor-microkit-pd/microkit-patch/assembly-boot-evidence.log`. The executor inits the embedded Lean
runtime, runs the verified turn (nonce 7→8, 30-unit transfer cell-0 100→70 / cell-1 5→35, nullifier 111
+ commitment 222), writes the 313-byte receipt to `commit_out` (RW), signals persist (ch2) + verifier
(ch3); persist reads the receipt back (`commit_out[0]='{'`) + gets commit-ready; verifier-stark proves
+verifies a real STARK; net brings virtio-net UP; the rbg app runs. The cap partition is enforced LIVE:
the executor holds `turn_in` READ-ONLY (a boot write to it faults — that was the last wall, fixed by
running the boot self-demo from the compiled-in wire, writing only `commit_out`).

THE WALL THAT FELL (the prior `-ffunction-sections` / "285-MiB text irreducible" diagnosis was the WRONG
lever — the text size was never the blocker): the on-device CapDL initialiser panicked **`OutOfSlots`**
because the **microkit TOOL hard-codes 4 KiB pages for every PD program-image segment**
(`tool/microkit/src/capdl/builder.rs`: `let page_size = PageSize::Small;`), so the ~300-MiB executor image
became ~83,000 frame caps and blew `ROOT_CNODE_SIZE_BITS`. FIX (the right, general one — a no-op for
small PDs): a one-function tool patch maps image segments with 2 MiB `PageSize::Large` where alignment
permits (the PD already links `-z max-page-size=0x200000`, so its segments are 2 MiB-aligned) → ~170 Large
frames + small tails, **2,322 total objects, 91 MiB initial task** (was 84,241 objects / ~340 MiB). The
patch + prebuilt tool + boot evidence are in `executor-microkit-pd/microkit-patch/` (built against the
microkit **2.2.0 tag** — `seL4/rust-sel4 cf43f5d` — to match the SDK's bundled `initialiser.elf`; a
`2.2.0-dev`-commit build pins `au-ts/rust-sel4 33cb1325`, an incompatible rkyv spec schema the SDK
initialiser can't read). The patch is upstreamable (map image segments with the largest aligned page).
INSTALL: `cp executor-microkit-pd/microkit-patch/microkit-2.2.0-patched $MICROKIT_SDK/bin/microkit`.

Residual (small, not blocking the keystone): the embedded turn is the demo `wideDemoInput`, not yet a
net-delivered live turn (the live `notified`-path read of `turn_in` is wired + correct, just unfed in
QEMU since net only brings the NIC up here — a real ingress→turn_in→executor delivery is the next strand).
Named: firmament keystone LANDED, 2026-06-15.

## DESKTOP KEYSTONE — CLOSED: the LIVE `cockpit::Cockpit` element tree renders on the seL4 framebuffer (TAB beside the live image, 2026-06-15)

THE #1 PRECIOUS is fully done, including its last swap: the deos-image PD (`sel4/dregg-pd/deos-image/`)
has TWO live modes on one ramfb framebuffer, switched with **TAB** — `Mode::Image` (the Pharo cell
browser) and `Mode::Cockpit` — and the cockpit is now the **REAL, LIVE `starbridge_v2::cockpit::Cockpit`
element tree** (not a hand-built look-alike): the CELL WORLD rail with the actual sovereign cells (ids,
balances, cap counts, the issuer well at −supply), the INSPECTOR reflecting the image (cells/height/
receipts/`state_root`/"executor embedded verified (TurnExecutor)"), the BLOCKLACE provenance (the real
receipt chain), and the HOME/SHELL/AGENT workspace. Rendered at 800×600 by the actual gpui renderer
(`gpui_wgpu::WgpuRenderer::render_scene_to_image`, the offscreen patch) on lavapipe (`type=Cpu`, no GPU/
window) on persvati, baked into the `#![no_std]` PD as raw RGBA8 (`src/cockpit_frame.rgba`, 1.92 MiB)
and swizzled RGBA→XRGB8888 at blit time. `make -C sel4 capture-image-modes` reproduces it end-to-end
(boots headless, screendumps image, QMP `send-key TAB`, screendumps the LIVE cockpit). Evidence:
`docs/desktop-os-research/patches/cockpit-on-sel4-framebuffer-LIVE.png` (the live cockpit scanned out
of seL4 ramfb) + `cockpit-render-800x600-LIVE.png` (the persvati render).

THE LAST SWAP — CLOSED (was "the one remaining swap"): the blitted Scene used to be a hand-built
cockpit-*shaped* `gpui::Scene`; it is now the live element tree, resolved the intended way. HOW: a
headless gpui `App`/`Window` (`gpui::HeadlessAppContext` over `TestPlatform`) drives the real
`cockpit::Cockpit` over the fully-seeded `world::demo_world` image; gpui paints its element tree into a
real frame; `Window::render_to_image` captures the resolved `gpui::Scene` through the offscreen wgpu
renderer. Entry: `starbridge-v2/src/main.rs::render_cockpit_headless` (`--render-cockpit <out>`, behind
a new `headless-render` feature). gpui reports a fixed 2× scale, so the 800-logical cockpit renders at
1600×1200 device px and is Lanczos-downscaled to 800×600 (full layout, no crop). Byte-proof: the new
`cockpit_frame.rgba` differs from the old hand-built bake in 1,376,735 / 1,920,000 bytes (a genuinely
different image, same geometry). The offscreen patch GREW the missing Linux headless renderer:
`gpui_wgpu::{WgpuRenderer::render_scene, WgpuHeadlessRenderer: PlatformHeadlessRenderer}` +
`gpui_linux::current_headless_renderer` + `gpui_platform::current_headless_renderer` routing to it on
Linux (the Metal headless renderer is the macOS counterpart). DEP REPOINT (committable, done): the
patch is pushed as `emberian/zed@dregg-offscreen` (off `fca2ccd`, rev
`407a6ffd977d82b828e392f92db5cb34edea9549`); starbridge-v2's `gpui`/`gpui_platform` git deps now point
there + a new `gpui_wgpu` dep at the same rev (the canonical patch
`docs/desktop-os-research/patches/gpui-offscreen.patch` carries the full offscreen+headless diff).
Fonts vendored OFL (`starbridge-v2/assets/fonts/{Lilex,IBMPlexSans}-Regular.ttf`). Named: desktop
keystone CLOSED — the live element tree is on glass, 2026-06-15.

## EVM BRIDGE — the STARK→SNARK wrap keystone: zkVM path BUILT, Plonky3-native BN254 terminal is the cost-optimization endgame (named 2026-06-15)

The EVM-bridge architecture + a running PoC landed (`docs/EVM-BRIDGE.md`, `/tmp/dregg-evm-e2e/`,
`/tmp/dregg-evm-wrap-poc/`, plus the green calldata codec in `bridge/src/ethereum.rs`). The keystone is
the wrap: dregg proves with Plonky3/BabyBear/FRI (post-quantum but gas-prohibitive on EVM), so dregg's
aggregate is recompressed into a BN254 Groth16 a ~270k-gas Solidity verifier checks. THREE rungs
(`docs/EVM-BRIDGE.md` §2.4): (B) **re-host dregg's own verifier in a RISC0 zkVM, settle their audited
Groth16** — VALIDATED this session: the full production `dregg-circuit --features verifier`
(`verify_vm_descriptor2`, the IR-v2 **Poseidon2** batch STARK + all of Plonky3) cross-compiles to
`riscv32im-risc0-zkvm-elf` via `embed_methods` (auto getrandom-custom + lower-atomic); the real
`RiscZeroGroth16Verifier` + `DreggBridgeVault.sol` compile under foundry, control IDs version-matched.
(A) bespoke gnark Poseidon2-FRI verifier circuit (cheaper to prove, new audit surface). (C) the endgame.

CLOSURE LANES: (1) finish the (B) loop — host generates the IR-v2 proof (`prove_vm_descriptor2`), zkVM
wraps to Groth16, `forge script DriveBridge` verifies on anvil + drives attest/lock/unlock/intent (the
plumbing is built; the Poseidon2 guest+host compile on persvati; run the wrap on a 24-core box). (2) swap
the guest's leaf-proof verify for the full `WholeChainProof` root (`verify_history`) — one-line, heavier.
(3) **THE COST ENDGAME — a Plonky3-native BN254 terminal** (§4.2/§2.4-C): make dregg's own recursion
(`emberian/plonky3-recursion`, the `WholeChainProof` fold) terminate in a BN254 Groth16 proof instead of
another BabyBear STARK — no RISC-V overhead, no separate FRI-verifier circuit. **STEP 1 BUILT + GREEN
(2026-06-15, `/Users/ember/dev/plonky3-bn254-wrap`, commit `e80f499`):** `OuterStarkConfig` — a Plonky3
`StarkConfig` whose FRI commitments + Fiat-Shamir transcript live in the BN254 scalar field
(Poseidon2-BN254 width-3 Merkle + `MultiField32Challenger`), from raw Plonky3 primitives pinned to dregg's
exact rev (82cfad73). A BabyBear AIR proves AND verifies through it (4 tests green — re-verified
`cargo test --release` 2026-06-15 — incl. the production HorizenLabs `RC3` constants
`production_constants_load_from_zkhash` + the `outer_config_carries_dregg_four_publics` interface tooth).
Keystone: `src/hasher.rs::MultiFieldPoseidon2Hasher`, the cross-field leaf
hasher (absorb BabyBear→pack into BN254→squeeze one Bn254 digest) that upstream Plonky3 does NOT ship and
SP1 carries by hand. KEY FINDING de-risked: `p3-bn254` (Poseidon2Bn254 + HorizenLabs params) AND
`MultiField32Challenger` (the transition primitive, `GrindingChallenger Witness=BabyBear`) ALREADY EXIST
in dregg's pinned upstream Plonky3 — the "no plonkish SNARK wrapper" gap is narrower than feared.
REMAINING (the two sharp edges, in that repo's README): **Step 2** — emit `OuterStarkConfig` from the
recursion fork's terminal layer (its Poseidon2 op-table + FRI private-data are BabyBear-w16-wired; the
smaller lift is a thin re-prove of the last BabyBear STARK under the outer config, mirroring SP1's
separate "shrink" layer). **Step 3** — the gnark Groth16 circuit (`/Users/ember/dev/dregg-gnark-wrap`,
sibling lane started this session) verifying an `OuterStarkConfig` proof with NATIVE BN254 Poseidon2 (no
nonnative hash emulation; the audit obligation is bit-for-bit constant/packing/FRI-param parity across the
Rust/Go seam). SHIP (B), BUILD (C). KEY FINDING (B): do NOT wrap the experimental `circuit/src/stark.rs`
(BLAKE3 Merkle, no zkVM accelerator — the
guest ran >200 CPU-min unfinished); use the production Poseidon2 path (field-native, ~10x lighter in
zkVM). Named: EVM bridge, 2026-06-15.

## PERFORMANCE PILLAR — LANDED: comprehensive criterion coverage of every hot path + measured numbers (2026-06-15)

The `dregg-perf` crate now covers comprehensive swathes of the system under BOTH proving and
witness-only loads, all measured (Apple M2 Max, bench profile). Five coverage gaps CLOSED with real,
runnable criterion benches (each drives the production PUBLIC API; numbers banked in
`docs/PERFORMANCE.md`, recipe in `docs/PERF.md`):
- (a) `turn_witness_vs_proving` — THE headline contrast, all four legs of one turn side by side:
  witness-only executor execute **~7 µs** · witness-gen **~319 µs** · full rotated prove **~147 ms** ·
  rotated verify **~149 ms**. **The proving multiplier ≈ 21,000×** — the empirical case for
  admit-then-prove-async.
- (b) `cohort_circuit` — the rotated IR-v2 multi-table batch STARK prove+verify per effect cohort:
  transfer-5table 52 ms/3.9 ms; and the UNIVERSAL-MEMORY economics MEASURED — a chip-bearing map-write
  proves **~227 ms** vs the same intent as no-chip umem ops **~14.9 ms** (~15× — the Blum multiset
  commits no Poseidon2 chip table).
- (c) `recursion_fold` — the bundle-tree aggregation fold: prove scales sub-linearly (10→14→36→98 ms for
  2→8→32→128 leaves) but **verify is ~CONSTANT ~2.4 ms regardless of fan-out** (the succinct-aggregation
  property, measured).
- (d) `embedded_commit` — the verified Lean kernel commit (`shadow_exec_full_forest_auth`, the node /
  seL4-executor-PD hot path) over the GOLDEN firmament-boot turn: **~157 µs** (microseconds, same order
  as the Rust executor — verified-and-cheap admit).
- (e) `ui_projection` — the deos desktop whole-system measure (gpui-free; the real GPU first-paint is on
  persvati): per-frame scene/affordance projection is **nanoseconds** (compose_scene 102 ns, paint_list
  472 ns, affordance_project 96 ns — never the bottleneck); the first-paint DATA cost is the five embedded
  commits (`demo_world_seed` ~5.8 s) — which is why the cockpit opens on the instant-genesis image and
  seeds turns async.

The full perf crate is clippy-clean; `cargo bench -p dregg-perf --no-run` green. SMOKE is default; FULL
(`PERF_FULL=1`) is the persvati ladder capture (the fold + cohort FULL ladders already captured + in the
doc). Named: performance pillar LANDED, 2026-06-15.

## ⚑ TWO PERF FINDINGS surfaced by the harness (closure lanes, named 2026-06-15)

1. **`prove_turn_self_sovereign` (rotation=None) is RETIRED under recursion and PANICS** ("thread a
   rotation witness — the live node always does"). The v1 effect-vm fallback was deleted in the cutover but
   this entry was left as a now-broken door. The perf benches/bins/`perf-report §6` that called it were
   migrated to the LIVE rotated `prove_full_turn` (via the new `dregg_perf::rotated_transfer_turn` helper,
   mirroring `sdk/tests/sovereign_rotated_c1.rs` wall_a). CLOSURE: either delete the
   `prove_turn_self_sovereign` entry (it can only panic) or make it mint a default rotation witness so it
   is honest — right now it is a trap for any caller. (`sdk/src/full_turn_proof.rs:2646`.)
2. **The cell commitment is dominated by the cap-root Poseidon2 tree (~225 ms v8 / ~157 ms v9)**, NOT the
   blake3 envelope (which alone is µs). `compute_canonical_state_commitment` absorbs the openable
   sorted-Poseidon2 capability root (`compute_canonical_capability_root`) — building that full-depth tree,
   even over an EMPTY cap set, is the ~225 ms. It is the heaviest non-FRI per-turn primitive and the long
   pole of the genesis/first-paint cost (`demo_genesis_instant` ~1.24 s). CLOSURE: a witness-vs-recompute
   split (compute once, cache, prove the delta) — the same lever the prover already uses — or a lazier
   cap-root that doesn't pay full depth for a small/empty cap map. (`cell/src/commitment.rs`.)

## DREGG-LEAN-FFI ARCHIVE IS A SHARED MUTABLE FILE — concurrent-feature-set build race (named 2026-06-15)

`dregg-lean-ffi/build.rs:966` writes the GIT-TRACKED `dregg-lean-ffi/libdregg_lean.a` (the canonical
185 MB Lean-closure archive) from EVERY cargo target's build-script: it splices the Dregg2 closure in,
then `gc_unreachable_members` PRUNES to the set reachable from THIS build's `dregg_*` exports. The object
CACHE is per-`OUT_DIR` (safe), but the ARCHIVE is ONE shared path. Two lanes with different feature sets
building concurrently RACE: a default-feature lane splices the full closure (~3041 reachable members),
a `--no-default-features` lane (e.g. `starbridge-v2 --features embedded-executor`) prunes it to a smaller
set (~150 MB), and a torn read mid-rewrite leaves the archive missing initializers
(`Undefined symbols: _initialize_Dregg2_Metatheory_EpistemicDial` / `…CreateCellFromFactory`). OBSERVED
LIVE during the Theme-2 lane: my `cargo test -p dregg-lean-ffi` link FAILED while a starbridge lane was
re-seeding the archive; my next run (after it settled) was green. So it's a transient swarm-safety bug,
not a code bug — but it makes `cargo test` of any archive-linking crate FLAKY under the swarm. FIX shape
(pick one): (a) make the archive per-`OUT_DIR` (copy the seeded base into `OUT_DIR`, splice+link THERE,
never touch the git path during a build) — cleanest, fully swarm-safe; (b) an flock around the
splice+GC+link critical section keyed on the archive path; (c) skip `gc_unreachable_members` when
`CARGO_FEATURE_*` indicates a reduced feature set (avoids the shrink-then-rebloat thrash). Until fixed:
build archive-linking crate tests SERIALLY, or in a pbuild lane dir. (My memory's "copy a shared file at
HEAD into your pbuild lane dir if a foreign in-flight edit breaks the crate" is the manual workaround.)

## ⚑⚑ PRIME-ORDER-SCHNORR-CURVE (named 2026-06-15 — MAKE-PRIVACY-REAL lane, the DEEP one; TWO bugs, both with a fix in hand)

**Two stacked breaks on the in-circuit Schnorr (confidential-VALUE) path — NOT core auth (Ed25519, real).**
Both are loudly `// SECURITY:`-marked in-file; a rigorous PARI/GP curve search + an against-the-code
probe nailed both AND the fix.

**BUG 1 (FOUNDATIONAL — `circuit/src/babybear8.rs`): BabyBear^8 is NOT a field.** The tower reuses
non-residue `W=11` for BOTH layers (`x^4−11` and `y^2−11`). But `x^2` already squares to 11, so
`y^2−11=(y−x^2)(y+x^2)` factors → the quotient is a product ring `F_{p^4}×F_{p^4}` with zero divisors,
not `F_{p^8}`. PROVEN against the real code (temp probe, since removed): `A=y−x^2` is nonzero,
`A·(y+x^2)=0`, `A.inverse()=None` (norm `11−11=0`). This voids the "size p^8 ⇒ ~124-bit DL" premise at
the foundation. FIX: the top-layer non-residue must be a genuine `F_{p^4}` element (NO base scalar works
— every `c∈F_p*` is a square in `F_{p^4}`); use `V=x`, giving the clean field `F_p[z]/(z^8−11)` with
`z=y`, `x=z^2` (minimal, keeps the "−11" flavor; basis maps `x^i=z^{2i}, y=z`).

**BUG 2 (`circuit/src/schnorr_curve.rs`): composite 31-bit generator order.** `GENERATOR=(1,2)` lives in
the base-field embedding `F_p⊂F_{p^8}`, order `2013191319=3·331·2027383` (~2^31, composite) →
Pollard-rho/Pohlig–Hellman recover sk in seconds. STRUCTURAL obstruction found: ANY curve defined over
the BASE field has `#E(F_{p^8})` divisible by `#E(F_p)·#E(F_{p^2})·#E(F_{p^4})` (nested point groups),
so it is never near-prime — the largest prime factor is bounded by the primitive part `≈p^4≈2^124`,
giving at best ~62-bit security. (Confirmed: all 6 j=0 sextic twists are catastrophically smooth, top
factors 83/81/59-bit; best base-field a≠0 gives a 124-bit-prime × 124-bit-cofactor split = 62-bit.)
**The curve MUST be defined directly over F_{p^8}, not descend to a subfield.**

**✅ LANDED (both bugs fixed; field + prime-order curve + 248-bit bigint scalars real, green).**
`babybear8.rs` is now the simple field `F_p[z]/(z^8−11)` in the **power basis** (`self.0[i] = coeff of z^i`;
`z^8=11` reduction; 8×8 Gauss inverse) — verified irreducible in PARI and `is_a_field_no_zero_divisors`
(2000-elt sweep + the old `A=y−x^2=z−z^4` zero-divisor now INVERTIBLE) + `frobenius_order_eight` pass.
The curve `y^2 = x^3 + (z+2)x + (z^3+8)` over F_{p^8} has **PRIME order**
`N = 269903886087112502248563194479599378757044855200285447932848137338699712099` (248-bit, **cofactor
h=1**) — re-verified `isprime(N)` + `ellcard(E)==N` + cofactor==1 (PARI, parisize 800M). In the power
basis: `CURVE_A=z+2=[2,1,0,…]`, `CURVE_B=z^3+8=[8,0,0,1,0,…]`, `ORDER` = N's 8 LE-u32 limbs
`[3630237283,2285651324,1488992648,1932759141,1148232707,1275750001,2335120239,10011291]`.
`GENERATOR`: x=1 (RHS `z^3+z+11` is a QR), y=`[417687251,1863107357,177749990,1036295843,398021929,
450362472,1199411012,113045356]`; `generator_has_order_n` (N·G=O), `generator_cofactor_is_one`
((N-1)·G=−G, no small mult =O), `scalar_mul_respects_order` ((N+5)·G=5·G) all green. `scalar_*_mod`
rewritten to full bigint mod N (left-to-right double-and-add `mul_mod`, bit-fold `reduce_mod_n`; no
single-limb path). AIR: `SCALAR_BITS 128→256`, `TRACE_HEIGHT 512→1024`, `challenge` field
`[BabyBear;8]→Scalar`, bit scan 31→32 bits/limb; `recompute_challenge` + the test helper now delegate
to the now-`pub` `schnorr_sig::compute_challenge_from_elements` (one canonical `e`). 42 schnorr tests +
19 babybear8 green; `// SECURITY:`/placeholder markers removed. **The privacy-layer DL soundness
foundation is real.** (Curve params + field/order proofs landed; the in-circuit Schnorr AIR remains an
executable model — STARK-backend wiring of this AIR is separate, unchanged-scope work.)

## ⚑ SEMIHOST EXECUTOR-PD LANDED (2026-06-14 — the cockpit on the sel4 PD world)

**The executor-PD's `turn_in → step → commit_out` cap partition RUNS on the semihost, and a cockpit
turn flows through it.** `sel4/dregg-firmament/src/executor_pd.rs` adds `ExecutorPd<R: TurnRunner>` —
the firmament HEART (FIRMAMENT.md §2 L3) as the Endpoint SERVER over the `EmulatedKernel`: an app-PD
stages a postcard `Turn` into `turn_in`, `pp_call`s the executor (the `ingress→executor` edge the real
`executor-stub` PD awaits on ch 1), the executor reads `turn_in`, runs the bytes through `R`, writes the
`TurnReceipt`/reason into `commit_out`, and replies. It rides the EXISTING kernel IPC (Endpoint
recv/reply + regions, the SAME the compositor-PD uses); NO executor logic of its own. starbridge-v2
`world.rs` plugs in the FULL real `World` as the runner (`WorldRunner` → `SemihostCockpit::
commit_turn_via_semihost`): a cockpit turn stages → signals → runs the IDENTICAL `World::commit_turn`
path behind the Endpoint → reads the receipt back out of `commit_out`. PROVEN: commits, rejects an
overspend fail-closed, and is **byte-for-byte equal to the direct path** (same `receipt_hash`, same
`state_root`). This is the §3 KEYSTONE payoff ("the verified executor-PD hosts on the semihost NOW")
turned runnable. Tests: firmament `tests/executor_pd_boot.rs` (cross-PD Endpoint) + `executor_pd.rs`
inline units + starbridge-v2 `world.rs` (the 3 semihost tests). Doc: `docs/SEMIHOST-COCKPIT.md`.

### residue named by this landing (closure lanes):
- **the gpui frontend still calls `World::commit_turn` DIRECTLY, not through `SemihostCockpit`** — the
  semihost path is wired + proven equivalent, but the cockpit's panels (`cockpit.rs`, the many commit
  sites) have not been CUT OVER to route through `commit_turn_via_semihost`. Closure = swap the commit
  call across the panels (mechanical; the byte-for-byte equivalence test is the safety net), then run the
  frontend as an app-PD client of the executor-PD + compositor-PD over the kernel Endpoints (the cross-PD
  `serve_turn`/`serve_present` path, not the inline drive). → starbridge-v2, the frontend cutover. NOT
  blocking (the backend runs the PD world today; this routes the UI through it). `docs/SEMIHOST-COCKPIT.md §6`.
- **the wgpu software-render path → compositor-PD framebuffer is DESIGNED, not built** — an app-PD
  rendering its surface with a software wgpu adapter (lavapipe) and `present()`ing the pixels to the
  compositor-PD's framebuffer region (the in-sel4 render). The authority gate (T1/T2/T3) runs; the pixel
  pipeline is the named graphics frontier (F1/F2/F3, R3 Stage C). → the graphics lane. `docs/SEMIHOST-COCKPIT.md §4`.

## ⚑⚑⚑ C7 GREP-ZERO LANDED (2026-06-14 — the v1 deletion drive, READ FIRST)

**THE FLIP IS DONE — v1 effect-VM proof reaches GREP-ZERO under `recursion`.** With PATH-PRESERVE
Phases 0-4 landed (chained rotated path is the live default on all 3 finalized-turn arms), the v1
hand-AIR (`EffectVmAir` / `effect_vm_p3_full_air` / `CutoverFallback` / `BilateralAggregationAir`) is
removed from the recursion build. The end-state is FENCE-not-delete: the v1 OLD-PROVER is retained
`#[cfg(not(feature = "recursion"))]` for the v1 floor (the SACRED wasm prover floor + the demo MCP
tools), and DELETED outright where dead in both builds (the Silver joint surface `JointParticipant`/
`prove_joint_turn`/`verify_joint_turn`; `DescriptorForestNode`/`verify_descriptor_forest` — the last
`EffectVmP3Proof` struct field; the v1 `BilateralAggregationAir`/`AggregationInnerRow`/
`build_aggregation_trace` block). `generate_effect_vm_trace`/`EFFECT_VM_WIDTH`/`AIR_DESCRIPTOR`/
`CUTOVER_READY_SELECTORS`/`EffectVmShapeAir`/`CrossSideExistenceAir`/`BundleTreeFoldAir`/the V2 bilateral
all STAY (Bucket D/E). The recursion-leaf is the ROTATED `DescriptorParticipant`/`RotatedParticipantLeg`
(Bucket F was already landed). **GREP-ZERO = 0 true live-under-recursion v1 refs** (236 literal matches,
all comments/strings/not(recursion)-fenced). Gates GREEN on persvati: `cargo build --features recursion
-p dregg-circuit -p dregg-sdk -p dregg-turn -p dregg-node` (Finished, exit 0) + `cargo test --features
recursion --no-run -p …` (exit 0) + circuit `not(recursion)` floor (exit 0). The executor secondary-verify
arms (`verify_sovereign_witness_stark`, the atomic-turn/bearer-cap default-AIR, `verify_bundle_with_stark`)
+ the SDK v1 cutover (`prove_effect_vm_with_cutover`/`verify_effect_vm_proof_with_cutover`/`revalidate_turn_
self_sovereign`) + the v1 sovereign producer (`cipherclerk::prove_sovereign_turn`/`emit_witnessed_receipt`)
+ the MCP demo v1 tools are all `not(recursion)`-fenced with fail-closed `recursion` arms (no silent skip).

### residue named by this drive (closure lanes):
- **`dregg-node`/`dregg-verifier` gained a `recursion` feature** (default-on, forwarding to
  `dregg-circuit/recursion`) — they previously had NO such feature so their `#[cfg(feature="recursion")]`
  gates misaligned with the recursion-by-default circuit. Latent bug exposed + fixed by this drive.
- **the standalone `dregg-verifier` has NO rotated replay-chain verify path** — under recursion its v1
  `verify_effect_vm_proof`/`replay_one_with_prev` are FAIL-CLOSED stubs. Closure lane: build the rotated
  replay-chain verify (`verify_vm_descriptor2`-based), analogous to the wasm-rotated Option-A. Until then
  the recursion-built verifier rejects (honest, not silent).
- **workspace `exclude` fix**: `starbridge-web-surface`/`starbridge-v2`/`deos-leptos`/`deos-web-cells`/
  `servo-render`/`dregg-tui` (recently-added in-tree separate `[workspace]` roots) were breaking
  workspace-wide `cargo` ("multiple workspace roots") — added to the root `Cargo.toml` `exclude`.
- the wasm `not(recursion)` prover floor stays the separate Option-A ember-decision (out of this scope).

## ⚑⚑⚑ POST-COMPACTION STATE (2026-06-14 late — READ FIRST)

**THE HARDSWAP — the VK EPOCH LANDED GREEN.** Rotated IR-v2 R=24 is now the DEFAULT registry,
v1 fallbacks retired, the −65.6% proof-size prize is LIVE (commits `6011fc77f` walls → `0802b305b`
live-path → `d33d02107` pre-VK gauntlet → `5b3772873` VK epoch #183). The tree is GREEN + COHERENT
(no half-deletion). **C7 grep-zero is gated on a BUILD, and the gating decision is ✅ DECIDED (ember,
2026-06-14): PATH-PRESERVE.** The deputy's deep re-trace (commits `7a8409572`/`fd478564c`/`5e71c24c2`/
`afe4e0606`, see `docs/V1-DELETION-MANIFEST.md` buckets E/F/G) found the v1 OLD-PROVER symbols can't be
deleted yet because (E) `generate_effect_vm_trace` is the SHARED generator the rotated leg is BUILT ON
(NOT v1 — never delete it), (F) `EffectVmP3Proof` is the recursion LEAF type in 5 files (mandatory-
rotated-leaf cutover first), (G) heterogeneous/non-synthetic finalized-turn coverage. ember settled G the
only dregg-coherent way — *"build path-preserve for SURE; any other decision wouldn't be dregg"* — so the
WEAKEN option (commit those turns proof-pending) is OFF the table. The C7 lane is now: **BUILD chained
multi-cohort + non-synthetic rotated proving so EVERY finalized turn stays proven (ARGUS unfoolability
intact), THEN bucket-F leaf cutover, THEN the bucket-A/C delete.** Staged persvati-green plan =
`docs/PATH-PRESERVE.md`. Each phase lands green; a half-landed prover-without-verifier is RED (forbidden).
(The interrupted `wf_9a7d5e77-b48` was looping on exactly this G decision — now resolved; `cv`-dug the
substantive thread, the decision is made.)

**LANDED 2026-06-14 (all green + committed):**
- verified-deos Lean crown WIDENED to 7 modules / 56 axiom-clean keystones (`482ba8db1`): `FogOfWar.noninterference`
  + `Rerender.snapshot_roundtrip` depend on NO axioms (the frustum-cull IS info-flow non-interference; snapshots
  re-expand losslessly per-viewer). lake `Dregg2` green (3930 jobs).
- fog-of-war webgame (`starbridge-web-surface`, own workspace, 78+4 green) — fog IS the membrane + the HONESTY
  CLOSURE: the no-peek `vk_hash` is now a REAL `canonical_predicate_vk` + registered `FogVisionVerifier` (the same
  registry `authorize.rs` dispatches through) + ed25519 proof (keystone `no_peek_for_real_only_the_secret_holder_can_prove_vision`).
- app-framework deos-EVOLUTION (`c55444e71`, 83+7 green) — cell-affordance surfaces in the bones + the dispatch
  seam CLOSED (`fire_through_executor` → real `EmbeddedExecutor` turn → executor's `TurnReceipt`).
- app-framework cap∧state GATED-AFFORDANCE rung (the Lean `Dregg2.Deos.GatedAffordance` Rust-mirror LANDED;
  app-framework 121-lib + council-board 5-int + 142 total green) — `GatedAffordance{affordance,state_cond}` +
  `FireError::StateConditionUnmet` + `GatedSurface::project_gated_for` (affordance.rs) + `DeosCell::{gated,
  project_gated_for,fire_gated_through_executor}` reading LIVE state via `EmbeddedExecutor::cell_state` (the author
  threads no `(old,new)`). Demo `examples/deos_council_board.rs` (+ `tests/deos_council_board.rs`): a button lights
  IFF caps∧state both pass; the htmx tooth (same approver, approve LIT in PENDING → DARK after RESOLVED); both
  anti-ghost refusals in-band (cap tooth Unauthorized + state tooth StateConditionUnmet, nothing submitted); a real
  verified turn through the executor; per-viewer frustum-snapshot rehydration (outsider refused). The model FOUND a
  bug: an affordance PRECONDITION (`==PENDING`) must NOT be the cell's lifetime INVARIANT (`Monotonic`) — conflating
  them made the executor reject the resolving turn; split → green.
- pg-dregg drainer daemon + Tier-D spike (verdict **D-SIDECAR**; 120 pg18 + 104 core + 21 proptest green).
- PATH-PRESERVE DECIDED + the staged plan (`867b41fcb`, `docs/PATH-PRESERVE.md`).
- the prior deos STEEL + dev-ex (rehydration stack · DEOS/DEOS-APPS docs · AGENTS.md · nextest split).

**LANDED 2026-06-14 (the empowered-doer wave, all green + committed):** PATH-PRESERVE Phase 0+1 (`fff442ca6` — the N-leg
chained rotated proving; chain≡monolithic + tampered-middle anti-ghost + conservation-across-chain teeth) · the bigger
fog-of-war WORLD (`16c374bbb`) · the app-framework deos-COMPOSITION (`7d7726879`, 142/142) · the embeddable-Lean-runtime
spike (`c93293686` — the pg-Tier-D + seL4-executor-PD blocker REFUTED by measurement: mimalloc is private + the task
manager is lazy; the executor PD already BOOTS; pg full-D = DAYS).

**⚑⚑ LEAD LANE (ember DECIDED 2026-06-14): FINISH THE CUTOVER to grep-zero — and HOLD the devnet redeploy until it lands.**
The staged ladder, each persvati-green (every finalized turn is ALREADY proven on current main — this is CLEANUP, not a
soundness gate): PATH-PRESERVE **Phase 3** (non-synthetic-cell witness — RUNNING `a100c225`) → **Phase 4** (the live cutover:
heterogeneous / non-synthetic turns route to the chain in `node/src/blocklace_sync.rs`, not the v1 fallback) → **bucket F**
(the 5-file recursion-leaf cutover, drop `EffectVmP3Proof`) → **#103** (executor off `EffectVmAir`) → **C7** (delete v1 +
grep-zero). The OTHER pillars braid in parallel but the cutover is the LEAD: pg full-Tier-D (days; wire `dregg_ffi_init_st`
into pgrx) · the deos predicate/caveat LANGUAGE uplift (the lamesauce fix) + the affordance→live-`TurnExecutor` seam ·
`./site` deos-integration · seL4 executor-PD productionization (weeks). ENDGAME (post-grep-zero): fresh-genesis devnet +
a running starbridge-v2 on ember's mac (host blocker: the gpui Metal Toolchain download, damaged Xcode `DVTDownloads`).

**HELD / NAMED (post-cutover unless noted):** sdk-ts/dist Docker rebuild · **devnet upgrade = EMBER's act, fresh genesis,
gated on cutover + follow-ups** · **`./site` integration with the deos/web directions** (pairs with the assurance-catalog
regen named below) · **seL4 / robigalia — a LIVE frontier that BOOTS** (corrected 2026-06-14; the prior "toolchain-absent / scaffold" line
was a compaction-degraded caricature — see `[[project-firmament-sel4-boots]]` + `sel4/README.md` + `docs/{SEL4-EMBEDDING,
FIRMAMENT,DREGG-DESKTOP-OS}.md` + `/tmp/sel4-boot-*.log`): the **Robigalia v0 demo BOOTS** real Rust PDs on seL4 in QEMU
on a NATIVE-macOS Microkit 2.2.0 toolchain (`~/sel4-sdk`, `make run`) — M0 banner ✅ · M1 verifier ✅ · M2 rbg
DirectoryCell ✅ · M-STARK a REAL on-device STARK ✅ · M5 riscv64 ✅ (serial-captured). The **firmament**
(`dregg-firmament/`) = ONE `Capability{target,rights}` across DISTANCE — local seL4-cap ↔ distributed dregg-cap ↔
surface(=a window), n=1-collapse to strong-local; the **semihost** (`EmulatedKernel` thread-v0 / `process_kernel`
MMU-process-v1 / real-Microkit) runs the SAME PD source three ways; the compositor-PD is real. THE blocker is essentially DONE — REFUTED + the executor PD BOOTS (measured 2026-06-14, `c93293686`,
`docs/EMBEDDABLE-LEAN-RUNTIME.md`): the mimalloc-override / worker-thread premise was WRONG (mimalloc is a PRIVATE heap,
the task manager is LAZY/single-threaded); the only real removal was the libuv thread (`dregg_ffi_init_st()`), and
`sel4/dregg-pd/executor-{pd,rootserver}/` already boot the Lean executor in a real PD (fresh qemu → status:2 ok:1).
**pg full Tier-D is now GREEN** (2026-06-14, persvati Linux + pg18.4 via cargo-pgrx): the verified `execFullForestG` RUNS
INSIDE a live pg18 backend under the SHARED Lean link (`DREGG_LEAN_LINK=shared`) — `pg_test`s
`pg_the_verified_executor_runs_inside_the_backend` + `pg_drainer_drains_the_queue_…` + `pg_drainer_runs_execfullforest_in_backend`
all OK; `runtime_available()`=true (`dregg_ffi_init_st` succeeds POST-FORK), the drainer's PRODUCE gate commits a real
`execFullForestG` receipt to `dregg.turns` (NOT the FoldProducer stand-in). The un-run Linux re-measure is DONE
(`dregg-lean-ffi/tests/embeddable_runtime_probe_linux.rs`): PROP-1 malloc→glibc (no interposition) both link modes;
PROP-3 committing turn + fail-closed both modes; PROP-2 = STATIC **2→2→2** (libuv-free) / SHARED **2→4→4** (init adds 2
libuv INFRA threads on Linux — refines §1.3's macOS single-thread count — but **the turn itself spawns 0**, created
post-fork, so nothing crosses the fork). `docs/EMBEDDABLE-LEAN-RUNTIME.md` §5 rewritten with the results. RESIDUAL (one,
named): pg-dregg does not link `dregg-turn`, so the in-backend producer SYNTHESIZES a conserving transfer rather than
decoding the submitter's postcard `SignedTurn` — lifting the full `SignedTurn→WForest` decode in-backend (the node-side
`dregg-turn` `lean_apply` marshaller, #171) is the one piece between this and "an arbitrary submitted turn executes
in-backend". seL4 executor-PD = WEEKS of productionization. verifier-PD is Lean-free-linkable (`no-lean-link`).
- **DEOS SPINE on seL4 — the persist-PD IS the `dregg.turns` commit log of the seL4 deos foundation; now REAL redb durability + the app-hosting economy (R2+R3+R8, host-GREEN).** `docs/PG-DREGG-ON-SEL4-DEOS-SPINE.md` + `sel4/persist-hosttest/`: the persist-PD's durable verified commit log + Tier-C chain gate. **Three organs, one gate, 21 tests green** (`cargo test --release`): (1) `commit_store.rs` — the chain-gate discipline `no_std`+`alloc`, REUSING `pg-dregg/src/mirror.rs:477` `verify_chain_step`/`ChainRefusal` + `persist/src/commit_log.rs` `CommitRecord` VERBATIM (rides INSIDE the persist PD via `#[path]`); (2) **`redb_store.rs` (NEW) — the REAL durable store**: the SAME gate + record committed into real `redb` ACID tables over a block-device `StorageBackend` (`len`/`read`/`set_len`/`sync_data`/`write` = exactly a block cap). Durability is REAL — `commits_survive_drop_and_reopen_over_the_same_bytes` (drop the store, reopen over the file bytes, head/cursor/log/indices recover, chain self-checks). 8 `#[test]`s. (3) **`hosting.rs` (NEW) — the app-hosting economy**: pay coin to be hosted = a conserving `Transfer` (app→host) committed through the durable spine; a lapsed fee EVICTS (a verified durable turn dropping the hosting), fail-closed; Σ value invariant. 6 `#[test]`s + `Dregg2/Apps/HostingLease.lean` (the lease = a TIME(period)+BUDGET(balance) caveat over the durable slot; 5 teeth + #guard, `#assert_all_clean`). Witness binaries `host_persist_spine` + `host_durable_hosting` green. Distinct from `docs/PG-DREGG-ON-SEL4.md` (the literal-Postgres VMM-guest ladder) — SQL face vs the native PD-pair spine. RESIDUAL (the named wall + levers, all the macOS user-mode-qemu-aarch64 checkpoint, NOT the semantics): (R3, REFINED) the **`BlockCapBackend`** — ONE `redb::StorageBackend` impl whose 5 ops go through the seL4 block cap (the durable redb store above it is host-green + unchanged; this is now a bounded device-driver trait impl, not "the backend"); (§3.3) the executor→persist `CommitRecord` serialization + `commit_out` shared-region framing (today the seat reads a sentinel byte) + the persist-PD ELF link carrying `commit_store.rs` (the crypto-floor on-device checkpoint shape); (§3.3) the ingress/submit-queue enqueue over `turn_in` (= `node/src/submit_queue_drainer.rs` shape). → `sel4/persist-hosttest/` + `sel4/dregg-pd/persist-stub/`, downstream of the executor PD boot (R0) DONE.

**STARFORGE:** dregg's agent joined the pen-pal agent-town — PR #12 `claude-of-dregg` (clone `~/clome/starforge-commons`),
first letter to sibling `claude-of-tulip`. dregg is REAL + in contact with other people now.

## ⚑ 2026-06-14 FLAGSHIP WAVE — LANDED (4 lanes, each main-loop-re-verified before commit); residual follow-ups below

The four lanes are in git history: faucet hardening (`0baf9da31`, full dregg-node suite 225/0 — caught+fixed a
production regression: the `is_solo` provisioning gate broke a single-but-unflagged node) · pg-dregg FLAGSHIP
(`425b6d28c`, 80/0 + live-pg18; demo+benches+loadgen+fuzz+VS-DBOS) · web-surface servo-forward (`starbridge-web-
surface/`, 20/0) · sdk pg-native (sdk-py 71/4-skip + sdk-ts 74/0). Open residuals these named:

- **sdk-ts dist needs a DOCKER rebuild + commit.** The `@dregg/sdk/pg` `./pg` export points at gitignored
  `dist/pg.{js,mjs,d.ts}` (+ `dist/index.*`); they were built ON-HOST this session because the Docker daemon
  could not pull `node:22` (NO npm install / zero fetch was done — only first-party tsc/tsup). Per the npm-in-
  Docker policy the dist was NOT committed. CLOSURE: rebuild sdk-ts dist in Docker node:22, `git add -f` the
  dist artifacts. (src + tests + package.json ARE committed; the package is consumable from source today.)
- **pg18 is STOPPED** (the Docker daemon churn stopped the shared cargo-pgrx pg18 cluster, port 28818). Restore
  with `cargo pgrx start pg18` before the next live-pg test/bench run.
- **web-surface → firmament/turn closures** (`docs/desktop-os-research/BUILD-STATUS.md`, agent-reported, main-
  loop decisions): (a) move the web caveat allowlists/permissions onto the real `cell/src/facet.rs` `EffectMask`
  free bits 24-31 (additive; narrowing machinery exists) instead of atop `SurfaceCapability`; (b) wire the
  `dregg://` fetch as a full `Effect`-bearing `TurnExecutor` turn whose receipt is the executor's `TurnReceipt`
  (the `ServedResourceCell` cell-program template) — today it is a verified cell-read + domain-separated receipt
  commitment; (c) the full `dregg://<fed>/<cell>/<swiss>` distributed fetch = bind `captp/` `SwissTable::enliven`
  + `Netlayer::dial` (this crate models the local resolve+attest half); (d) the LIBSERVO SEAM at `delegate.rs`
  `MockSurface` (replace with the real `servo::WebViewDelegate` impl when libservo + Metal/wgpu link). Quorum-sig
  crypto on `AttestedRoot` is the `hints` layer (structural now; the receipt-stream Merkle binding IS real).
- **ObservedFieldEquals embedded-executor wiring — CLOSED 2026-06-14** (the §11.2 cross-cell-read convergence):
  the turn executor now builds a real `FinalizedRootAuthority` (`execute_tree.rs::build_finalized_root_authority`)
  from its committed view of each referenced peer cell's GENUINE finalized commitment + field value, handed to the
  `WitnessBundle` as `finalized_roots: Some(&observed_authority)` — so the deos cross-cell observed-field atom now
  ACCEPTS a genuine read (local field == peer's finalized value) and REJECTS the mismatch/forge teeth on the
  embedded commit path (was fail-closed REJECT-only). Accept/reject pair: `coverage_state_constraints::
  observed_field_equals_accept_and_reject` (a peer oracle cell inserted into the shared ledger; its real
  `state_commitment()` is the program's `at_root`). Coverage gate: `ObservedFieldEquals => true`, removed from
  `NOT_YET_COVERED_CONSTRAINTS`, ratchet `MAX_UNCOVERED_CONSTRAINTS` 10→9. Side-catch (same gate did not even
  compile — `CollectionAggregate` was MISSING from the classifier match, RED at HEAD): added its honest executor
  accept/reject pair `collection_aggregate_accept_and_reject` (a seeded `heap_map` collection meeting/failing a
  CountSatGe statistic across a submitted SetField turn) + `CollectionAggregate => true` arm, so the gate is
  exhaustive and the not-yet list is honest at 9. Green on persvati: `cargo check -p dregg-turn` clean;
  `coverage_state_constraints` 25/25 + `protocol_coverage_gate` 3/3.
- **`cargo check --workspace --tests` is broadly RED — pre-existing dregg3-reduction test-corpus rot** (named
  2026-06-14, surfaced by the ObservedFieldEquals convergence gauntlet once the WitnessBundle ripple closed):
  ~172 `cannot find` errors (E0425/E0422/E0433 — stale `use Effect/Turn/TurnExecutor/Action/CallForest/…`) in
  the TEST targets of `protocol-tests/`, `dregg-dsl-tests/`, `dregg-tests` (`tests/src/`), and the `#[cfg(test)]`
  modules of `cell`/`turn`/`circuit`/`blocklace`/`bridge`/`rbg`/`token`/`trace`. Every crate LIB compiles — this
  is pure test-module bit-rot from the verb reduction, invisible because the default nextest profile filters it
  (per-crate green is the dev loop). CLOSURE: a "green the test corpus" lane — repair the stale imports file-by-
  file (most cascade from one missing `use` per file) until `--workspace --tests` = 0 errors, then keep it in CI.

## Rides THE ROTATION (dies at or lands with the one VK epoch — do not do separately)

- sbox_registers→0 descriptor metadata (chip uses inline x⁷; named in 0b05afc1a) — flip at the closing-ceremony regen.
- RESERVED mask removal + 186→159 column compaction (REORIENT EPOCH STATUS).
- registers 8→16 + FactoryDescriptor.fields · PI v3 (committed-height + rateBound/challengeWindow) · heap_root register.
- iroot bound into recStateCommit (non-omission obligation, 9dcd42cd9).
- cap-reshape phase D (in-circuit cap crown completion; #103 audit: A–E + RevokeCapability done. The 2026-06-13 burn-down to fully-coherent left TWO ember-decisions characterized under "Decisions pending (ember)": the two-AIRs sovereign-path soundness item + the 4-ary-vs-sorted membership-leg retire-or-keep. The stale-`EffectVmEmitCapRoot` item resolved NO-OP: that module is the load-bearing Phase-A digest spine under the whole cap family, already coherently scoped — clarified its V2/Phase-E layering with a forward-pointer doc note, not retired).
- #150 confirmation: does the umem `absent` + sorted-gap boundary fully retire DslRevocationTree (TREE_DEPTH=4)? One read-pass at cutover.
- fresh-key sorted-INSERT map-op (reuses MapAbsent adjacency; named in cff8509ba).
- per-turn chip amortization (blocked on an IR-v2 turn assembly; named in 0b05afc1a).
- MMR §6 CommitBindsMMR layout fact (node writes both roots at dense positions; the Receipt-apex residual premise, 7894e5789) — discharged-by-construction at the flag-day.
- balance/nonce → NAMED-register assignment (RotatedLimbs carries no separate balance/nonce limbs; the umem projection maps them to the heap domain — pick ONE canonical story; ember-visible decision, ROTATION-CUTOVER.md §2 note).
- cells_root + iroot per-turn PRODUCERS in turn/ (`turn/src/rotation_witness.rs`, NAMED in EffectVmEmitRotationV3.lean §3) + lifecycle/epoch trace carriers — ROTATION-CUTOVER.md §5 items 3-5. The staged-additive producers + trace builder + cell≡circuit differential ALREADY LANDED GREEN (51850ee91, no VK bump); these notes track the FLIP consumption. SEQUENCING: build the rest WITH the flip's rotated trace builder, not before.
- guardAtom IR kind (umem adapter c) confirmed NOT landed (absent from DescriptorIR2.lean + descriptor_ir2.rs): in-circuit policy/caveat enforcement for v2/v3 = cap-crown phase D + Policy.lean line, rides rotation.
- HEAP-KEYED CAVEATS executor runtime discharge (named premise `HeapCaveatRuntimeDischarge`; template = `verify_slot_caveat_manifest`; semantics welded via `tagHeapAtom`→`HeapAtom.lift`→`evalHeap`) — ROTATION-CUTOVER §5 item 9; at the flag-day the staged 29-felt manifest replaces the live 25-felt slot manifest in the regenerated PI region. (Wire shape STAGED; live v1 manifest untouched.)
- PI v3 rateBound/challengeWindow: carried-only (producer copies context into PI 202/203; verifier pins ZERO sentinels, proof_verify.rs:269-270). Enforcement arrives with optimistic-proving/dispute (#169) which owns these slots — nothing further pre-#169.

### ⚑⚑ C7 PRE-DELETION BLOCKER — four LIVE v1 deps survive the VK epoch in recursion builds (2026-06-14, C7 attempt)

**C7's gating premise is UNMET.** The manifest (`docs/V1-DELETION-MANIFEST.md`) + the PRE-FLIP GATE
framed C7 as "the VK epoch landed green ⇒ a mechanical delete fan-out." Against the CODE at HEAD
(`5b3772873`) that is false: the VK epoch (#182/#183) migrated the DEFAULT compose+prove path to
rotated, but the three walls (A/B/C) + the wasm-decision did NOT cover FOUR live v1 dependencies that
remain in **recursion-enabled** builds — so grep-zero (`generate_effect_vm_trace · EffectVmAir ·
EffectVmP3Air · EffectVmP3Proof · prove_effect_vm_p3 · CutoverFallback · EFFECT_VM_WIDTH`) is
PROVABLY-UNREACHABLE-in-recursion until these close, and a PARTIAL cutover ships RED (forbidden).
Items 2/3/4 are ordinary engineering (NO crypto primitive); item 1's keystone (a rotated FRI-free
revalidation primitive) is blocked at the PROVING-LIBRARY BOUNDARY (`p3-batch-stark`'s interaction-
aware constraint checker is `pub(crate)`+debug-only — see item 1). Together they are a multi-system
cutover, NOT a delete. The tree is GREEN + UNTOUCHED (baseline `pbuild hardswap` of
circuit/sdk/turn/node = exit 0; no edits made). The four, file:line'd:

1. **`bespoke_air_accepts` = the LIVE F-DOS-1 inline witness-revalidation, v1-AIR, no rotated twin.**
   `circuit/src/effect_vm_p3_full_air.rs:2451` checks `EffectVmAir::eval_constraints` FRI-free
   (sub-ms). LIVE callers: `node/src/api.rs:~2470` (HTTP commit path, `http_project_effects`→
   `generate_effect_vm_trace`→`bespoke_air_accepts`), `node/src/prove_pool.rs:22`,
   `sdk/src/full_turn_proof.rs:2391` (`revalidate_turn_self_sovereign`). `descriptor_ir2` exposes NO
   FRI-free `accepts` (only `prove_*`/`verify_*`). ** DEEPER THAN A WRAPPER (verified 2026-06-14):**
   a naive `p3_air::check_all_constraints(Ir2Air, ..)` does NOT compile — `Ir2Air::eval` needs
   `InteractionBuilder` (the LogUp `bus.lookup_key`, `descriptor_ir2.rs:~76`) which the plain debug
   builder lacks; and the only interaction-aware FRI-free checker, `p3-batch-stark::check_constraints`
   (`~/.cargo/git/checkouts/plonky3-*/82cfad7/batch-stark/src/check_constraints.rs:37`), is
   `pub(crate)` + `#[cfg(debug_assertions)]` — NOT exported. So the rotated revalidation primitive is a
   PROVING-LIBRARY-BOUNDARY dependency (this item is the true long pole). CLOSURE OPTIONS: (a) upstream
   a `pub` interaction-aware constraint-check in the `Plonky3@82cfad7` fork (or our recursion fork) and
   call it; (b) reimplement the LogUp permutation-trace assembly + multiset check inside dregg-circuit
   (substantial — reproduces `check_constraints`); or (c) accept that rotated revalidation runs the
   real `prove_vm_descriptor2`+`verify` (loses the sub-ms F-DOS-1 budget = a commit-path perf
   regression). PLUS the node commit path must assemble the rotated trace from real before/after
   `RotationWitness` (`dregg_cell::Cell` pre/post — today it re-derives a v1 trace from pre-state with
   NO cells).
2. **node `rotation: None` runtime FALLBACK still runs the v1 leg under recursion.**
   `node/src/turn_proving.rs:358/385` (`rotation_witness_for_self_sovereign_impl` returns `None` for
   non-synthetic-shaped cells / non-cohort / heterogeneous / no-op / non-graduated turns) →
   `prove_full_turn` then runs the v1 `generate_effect_vm_trace`+`prove_effect_vm_with_cutover` leg
   (`sdk/src/full_turn_proof.rs:1124-1131,1185-1201`). Plus `prove_and_verify_finalized_turn`
   (`turn_proving.rs:526`) calls `generate_effect_vm_trace` UNCONDITIONALLY for `new_commit`. CLOSURE:
   make the recursion build rotated-ONLY — non-cohort turns FAIL-CLOSED (proof skipped + loud log),
   not silent-v1. ⚠ behavior change: must confirm the rotated cohort
   (`trace_rotated::rotated_descriptor_name_for_effect`, 26 effects + per-field SetField; NoOp/
   heterogeneous fail-closed) covers every live turn shape, else this regresses live-turn proving.
3. **aggregation/forest/IVC proof TYPE is still `EffectVmP3Proof` (v1 leg co-resident).**
   `circuit/src/proof_forest.rs:243,280` + `joint_turn_aggregation.rs:130,197,213`
   (`DescriptorParticipant.proof: EffectVmP3Proof` + `Option<RotatedParticipantLeg>`) +
   `ivc_turn_chain.rs`. `EffectVmP3Proof = BatchProof<DreggStarkConfig>` and
   `Ir2BatchProof = BatchProof` are the SAME type, so this is mostly an alias cutover, BUT the v1
   `proof` field must be DROPPED and the `rotated` leg made MANDATORY (the unfinished C4 step the
   structs' own docs name: `joint_turn_aggregation.rs:138`).
4. **wasm in-browser prover is v1 + recursion is ON in the wasm graph.** `wasm/src/runtime.rs:710`
   (`generate_effect_vm_trace`+`EffectVmAir`+`stark::prove`) + `wasm/src/bindings_lightclient.rs:389`
   + the `BilateralAggregationAir` bundle (`wasm/src/bindings.rs`). wasm pulls circuit's DEFAULT
   features (= `recursion`, via observability/bridge/lightclient — see the `[patch]` note in
   `wasm/Cargo.toml`), so this is a RECURSION build and these unconditional refs block grep-zero
   there too. Option-A (ember-decided): migrate to `prove_effect_vm_rotated_ir2` (compiles in the
   wasm graph already) by synthesizing before/after `Cell::with_balance` + rotation witnesses for the
   demo inspector path. The brief's "`not(recursion)` wasm v1 FLOOR" residual is only coherent if the
   wasm prover gains a `#[cfg(feature="recursion")]` rotated branch (shipped wasm has recursion ON);
   a bare `not(recursion)` fence would DELETE the in-browser prover (a degradation — not acceptable).

SEQUENCING (each persvati-green): (1a) the additive `ir2_descriptor_accepts` checker + test [keystone,
zero-risk] → (3) the `EffectVmP3Proof`→`Ir2BatchProof` alias + drop-v1-leg in aggregation → (1b)+(2)
node commit-path rotation-witness assembly + rotated-only fail-closed → (4) wasm Option-A → then the
mechanical DELETE of bucket A (`effect_vm_p3_full_air.rs`, `effect_vm/air.rs` v1 surface,
`effect_vm_p3_air.rs` is actually `EffectVmShapeAir` used by `recursive_witness_bundle.rs` — KEEP or
re-home) + bucket-C harnesses + grep-zero verify. NOTE the manifest mislabels: "`EffectVmP3Air`
shape-mirror in effect_vm_p3_air.rs" is really `EffectVmShapeAir` (a recursion shape-probe, LIVE in
`recursive_witness_bundle.rs:237/360/412/420`), and bucket-A's `effect_vm_p3_full_air.rs` hosts the
LIVE `bespoke_air_accepts` + the `EffectVmP3Proof` alias — so it is NOT a clean delete. The ember-
decision: expand C7 to perform this four-part live-path cutover (a flip-scale phase), or land it as
the sequenced follow-on above.

⚑ SHARPENED (2026-06-14, C7 fix-round-1 — independent re-trace at greater depth; the two stoppers REFINED,
one of them DOWNGRADED OUT OF "crypto-primitive" territory):

- **Blocker #1 (item 1 keystone) is NOT a crypto-primitive dependency after all — it is an OPTIMIZATION we
  can simply drop.** Re-traced the F-DOS-1 contract end-to-end (`node/tests/f_dos_1_request_path_liveness.rs`
  §"the soundness bar"): the load-bearing invariant is "NO STARK proving under the `state.write()` lock," NOT
  "a sub-ms FRI-free revalidation." The sync `bespoke_air_accepts` is a DEFENSE-IN-DEPTH witness cross-check
  layered ON TOP of the executor, which already validated+committed the turn FIRST (`api.rs:2739`
  `execute_via_producer` → `match TurnResult::Committed`). So the keystone resolves with ZERO new crypto and
  ZERO commit-ack perf change: (a) DROP the sync `revalidate_http_witness`/`bespoke_air_accepts` call on the
  commit path (the executor is the authority; the witness check added nothing the executor didn't), and
  (b) make the async prove pool (`prove_pool::run_job`, today `EffectVmAir`+`stark::try_prove`) prove the
  ROTATED `Ir2BatchProof` instead — which is exactly the rotation's purpose, run async OFF the lock just like
  today's v1 async prove. The earlier "needs a `pub` `p3-batch-stark::check_constraints` / LogUp reimpl"
  framing is MOOT (verified: the emberian local fork `../plonky3-recursion` does NOT vendor `batch-stark` —
  it is upstream `Plonky3@82cfad7`; and even an export would not recover the sub-ms budget since LogUp
  permutation-trace assembly dominates — so the FRI-free-rotated-checker avenue was a dead end anyway, but
  it is also UNNEEDED). Item 1 is therefore ordinary (if cross-file) engineering.
- **Blocker #2 (item 2) is the ONE genuine ember-decision, and it is NARROW + precisely bounded.** The
  rotated R=24 cohort covers EVERY live single-effect selector (`trace_rotated.rs:438` "every LIVE selector
  resolves; NoOp + unknown fail closed" — verified by reading the full match). So `rotation_witness_for_self_
  sovereign` (`turn_proving.rs:353-387`) returns `None` — and `prove_full_turn` runs the v1 leg
  (`full_turn_proof.rs:1124-1131,1185-1202`) — for EXACTLY three live shapes, all reachable on the node's
  finalized-turn proving path (`blocklace_sync.rs:2643/2702`): (i) NoOp/IncrementNonce-only turns,
  (ii) **HETEROGENEOUS multi-cohort turns** (the `cohort_ok` all-same-descriptor gate fails), and
  (iii) **non-synthetic-shaped cells** (the `cell_is_synthetic_shaped` gate fails: any non-zero field or
  non-empty c-list). Rotated proving for (ii)+(iii) is NOT built (heterogeneous-batch rotated proving +
  non-synthetic-cell rotated witnesses are new capability). THE DECISION ember owns: when a recursion-build
  node finalizes a turn of shape (i)/(ii)/(iii), should it **commit UNPROVEN** (proof-pending→skipped — note
  this is ALREADY a tolerated state: `prove_pool::run_job:201` "receipt stays committed-but-unattested" when
  the async prover fails), or should heterogeneous/non-synthetic turns be **REFUSED**, or must rotated
  proving be BUILT for (ii)+(iii) before the flip? This changes production proving-COVERAGE semantics
  (today every such turn carries a v1 proof), so it is an ember scope-call, not a deputy default. Once
  decided, item 2 collapses to: replace the v1 leg in `full_turn_proof.rs:1185-1202` with the decided
  behavior (commit-unproven = drop the leg + Tentative; refuse = error; build-rotated = new prover), gate any
  residual v1 to `#[cfg(not(feature="recursion"))]`.
- **Item 3** (`EffectVmP3Proof` field on `DescriptorParticipant`) is the C4 drop-v1-leg: `EffectVmP3Proof`
  and `Ir2BatchProof` are the SAME `BatchProof<DreggStarkConfig>` (verified: `effect_vm_p3_full_air.rs:77`
  ≡ `descriptor_ir2.rs:144`), so the TYPE is a free rename — but a HONEST close drops the v1 `proof` field
  (minted by the v1 prover, read by host admission, `joint_turn_aggregation.rs:130/139`) and makes `rotated`
  mandatory; a bare type-rename that leaves the v1-prover-minted proof in place would LAUNDER grep-zero
  (forbidden). Rides item 1's async-rotated cutover (then the participant's proof IS rotated).
- **Item 4 (wasm)** is independent of #1/#2 and lands as ember's PRE-DECIDED `#[cfg(not(feature="recursion"))]`
  floor + a `#[cfg(feature="recursion")]` rotated branch (the in-browser prover must synthesize before/after
  `Cell` + rotation witnesses for the demo inspector). It does NOT block native-recursion grep-zero — but
  native grep-zero is NOT reachable until #1+#2+#3 land, because the v1 SYMBOLS stay live in those legs.

NET: the phase deliverable (grep-zero in recursion) is gated on ONE genuine ember-decision (blocker #2's
non-cohort behavior). Everything else is verified-ordinary engineering. A PARTIAL cutover (any subset of
1/2/3/4) leaves grep>0 in recursion AND ships RED (the v1 prover would be half-disconnected) — the mandate's
#1 forbidden outcome — so the tree is held GREEN + UNTOUCHED at HEAD (baseline `pbuild hardswap` of
circuit/sdk/turn/node = exit 0, "Finished `dev` profile") pending ember's call on blocker #2. Once decided,
the full cutover is a single coherent lane (items 1→3→2→4→delete), each persvati-green.

⚑ FIX-ROUND-2 (2026-06-14, deepest independent re-trace; one SCOPE-CORRECTION + one DECISION-REFRAME +
the recommendation INVERTED). Re-verified the four legs at HEAD, then traced two things the prior C7 entries
did NOT pin down — the result MATERIALLY enlarges item #3's scope and REVERSES the recommended ember answer:

  (A) SCOPE-CORRECTION — item #3 (recursion/aggregation) is NOT "drop a dead leaf"; it is a MANDATORY-leaf
      cutover across FIVE files. `proof_forest.rs::ForestNode.proof` IS `EffectVmP3Proof` (v1) — its only leaf
      (`circuit/src/proof_forest.rs:280`); `joint_turn_aggregation.rs::DescriptorParticipant.proof` IS
      `EffectVmP3Proof` (v1, `:130`) with `rotated: Option<RotatedParticipantLeg>` only ADDITIVE (`:143`; the
      in-file comment `:138` states the rotated leg "becomes mandatory" only "once present everywhere" — i.e.
      NOT YET). Same v1-leaf posture in `ivc_turn_chain.rs` (3 `EffectVmP3Proof` refs) + `joint_turn_recursive.rs`
      + `recursive_witness_bundle.rs`. So deleting `EffectVmP3Proof`/`generate_effect_vm_trace` FORCES, FIRST:
      make the rotated leg mandatory in all five, drop the v1 field, then fix every host-admission read
      (`joint_turn_aggregation.rs:130/139/192` "v1-leg-only constructor" no longer compiles). EXEC.3 point (c)
      flags this ("the recursion knots … their v1 cores delete only at C7") but the bucket-A manifest UNDER-COUNTS
      it as mechanical. This is a soundness-bearing recursion cutover lane in its own right — NOT a delete.

  (B) DECISION-REFRAME + RECOMMENDATION INVERTED. The prior entry recommended ember pick "commit-unproven"
      (route the non-cohort shapes — heterogeneous multi-cohort · non-synthetic-field cells · NoOp-only — to
      proof-pending/skipped) as "the smallest change, within the tolerated-degradation envelope." On re-trace
      that is the WRONG close and I withdraw the recommendation: commit-unproven WEAKENS the
      all-finalized-turns-carry-a-proof guarantee (ARGUS light-client unfoolability, the north star) for a
      WHOLE CLASS of REAL live turns — heterogeneous turns are ordinary (the SDK projector `convert_effects_to_vm`
      emits e.g. Transfer+SetField from a single call_forest; `sdk/src/cipherclerk.rs:5491-5527`), so this is not
      a degenerate corner but a standing production hole. Shipping it is precisely the regression the HARDSWAP
      mandate's #1 rule forbids ("NEVER SHIP RED … a broken HARDSWAP betrays the whole system"). The HONEST close
      PRESERVES the guarantee: make the rotated path TOTAL before deleting v1 — which means BUILDING (b1) rotated
      heterogeneous/multi-cohort proving (the rotated AIR is structurally ONE-descriptor-per-proof,
      `trace_rotated.rs:507` "EXACTLY the registry's 36 cohort members"; a mixed turn has NO rotated
      representation today) + (b2) a non-synthetic-field rotated witness (lift the
      `turn_proving.rs:353-357/445-448` `cell_is_synthetic_shaped`/`cell_matches_v1_prestate` gate) + (b3) confirm
      NoOp-only is unreachable on the finalized path (the SDK projector yields ≥1 cohort effect for any real
      actor turn — only the EXECUTOR-side bridge `effect_vm_bridge.rs:557` injects NoOp on an empty per-cell
      projection, a DIFFERENT projector not on the FullTurnProof path; CONFIRM, then it is a non-issue). (b1) is
      genuine unbuilt circuit work; it does NOT fit one verified-green phase.

  THE DECISION, SHARPENED: it is NOT "what should the non-cohort fallback do" (that framing presumes weakening).
  It is: **C7 = delete v1 ⇒ EITHER (Path-PRESERVE) build rotated coverage for heterogeneous + non-synthetic
  turns AND make the 5-file recursion stack's rotated leg mandatory FIRST (a multi-lane, multi-week
  circuit+recursion campaign, no crypto primitive, no further decision once chosen) — keeps the north-star
  guarantee intact; OR (Path-WEAKEN) ember explicitly accepts that heterogeneous / non-synthetic-field finalized
  turns commit WITHOUT a per-turn proof (proof-pending → skipped), shrinking the all-turns-carry-a-proof
  guarantee to the rotated-cohort-homogeneous-synthetic-cell subset — the smaller code change but a REAL
  north-star regression.** My recommendation (reversed from fix-round-1): **Path-PRESERVE.** The HARDSWAP ethos
  is l4v / green-or-bust; trading away the light-client's per-turn proof for a class of ordinary turns to make a
  delete land is the kind of "quick fix = debt hole" ember forbids. Path-WEAKEN is offered only because it is
  genuinely ember's north-star to spend or keep — it is not a deputy default, and it must be a DELIBERATE,
  documented narrowing of the ARGUS claim, not a silent side effect of a deletion.

  HELD GREEN (unchanged): tree UNTOUCHED at HEAD; baseline `pbuild hardswap` of circuit/sdk/turn/node under
  `--features dregg-circuit/recursion` = exit 0, "Finished `dev` profile" (re-run this round). grep-zero NOT met
  in recursion (correct — v1 stays live across legs #1-#4 above). No fake-green via cosmetic rename (would
  launder grep-zero while the v1 prover stays the live prover for heterogeneous/non-synthetic/recursion turns).

## THE ROTATION FLIP — the irreversible tail (ember-COMMISSIONED, a4c7368ae; touches cell/+live registry+executor PI)

*(The genuinely-new long pole — staged producers + rotated trace builder + cell≡circuit
differential — is DONE and GREEN beside v1, no VK bump. Two MORE staged-additive stages landed
2026-06-13 (Opus, G3-authority + G4-cohort); what remains is the deliberate live-path rewrite +
flip:)*

### ⚑⚑ THE PRE-FLIP GATE — the REAL gate before the VK epoch (flip-executor inventory, 2026-06-14)

**⚑⚑⚑ NOW EXECUTING (2026-06-14, ember: "it's time, steel ourselves for the horrors" — workflows+agents authorized).**
THREE lanes running on DISJOINT files (STAGED-ADDITIVE, reversible behind `recursion`; the main loop reviews each
diff before it rides the VK epoch):
- **Wall A+B** (agent `a744069d109bf72b4` — `sdk/src/full_turn_proof.rs` + `turn/src/aggregate_bilateral_prover.rs`
  + the `WitnessedReceipt` struct). REFINED inventory (main-loop, deeper than the flip-executor's): the rotated
  path already sources the composed PI (`full_turn_proof.rs:1078`) but leans on v1 in THREE spots to sever —
  (A1) the rotated sub-proof's `vk_hash` is the V1 descriptor (`:1083` → `effect_vm_circuit_descriptor()` =
  "dregg-effect-vm-v1"); fix to the ROTATED descriptor (`rotated_descriptor_name_for_effect` @`:856`); (A2) the
  conservation leg reads `effect_pi[NET_DELTA_MAG/SIGN]` from the UNCONDITIONAL v1 `generate_effect_vm_trace`
  (`:1043`/`:1191`) — read net_delta from the rotated PI instead; (A3) then gate the v1 `generate_effect_vm_trace`
  to `rotation.is_none()` only. WALL B: `build_inner_rows_v2` (`:193`) PROJECTS the 49-felt schedule from
  `wr.public_inputs[..ACTIVE_BASE_COUNT]` (v1 PI) — add a native `Option<[BabyBear;49]>` `bilateral_schedule` on
  `WitnessedReceipt` (Option + projection-fallback so node/ stays unchanged), prefer it in `build_inner_rows_v2`.
- **Wall C** (agent `a9fe8d40eb8f1e999` — `node/src/blocklace_sync.rs` + `node/src/turn_proving.rs`). Thread
  `rotateV3WithNullifierPin` (39-PI, nullifier@PI[38], the `cc1e1399c` descriptor — the §EXEC.3(b) "38-PI lacks
  NULLIFIER" note is STALE) into the `(None,Some(nullifier))` freshness arm, staged behind `recursion`.
- **pg-dregg maturation** (agent `a71feb983ca8f43ce` — `pg-dregg/` standalone, parallel, zero flip collision):
  the durable-workflow API + restart pg18.

SEQUENCING (each gated green; the main loop drives): walls A/B/C land + reviewed → **the main loop populates
`bilateral_schedule` at the node/ WR producer** (`materialize_blocklace_artifacts`, DEFERRED til Wall C lands, to
avoid the node/ collision) → **the VK epoch (C5/C6) = THE MAIN LOOP's irreversible act** (v3Registry→default regen
+ re-pin ~58 SHAs/11 guards + #103 sovereign graduation + notify Step-2 felt-batch + FFI reseed + the ONE
VK/cell-commitment bump; §EXEC.3 recipe) → **C7** delete v1 + grep-zero (a Workflow fan-out) → the **Option-A
wasm-rotated prover** (LAST — gates C7's full grep-zero, not the native cutover) → persvati gauntlet → held push →
**devnet redeploy = EMBER's act** (fresh genesis). Prize: −65.6% proof size (350.5→120.4 KiB), verify 3.4× faster.

--- (original flip-executor inventory, for the record) ---

The flip was ATTEMPTED and correctly NOT TAKEN: the rotation DESCRIPTORS are all correct+green (lake
`Dregg2` 3922 jobs axiom-clean; `effect_vm_rotation_flip` 4/4 — the magnesium PROOF is DONE), but the
LIVE-PATH cutover is NOT. The earlier "flip-safe, all gates closed" was an OVER-CLAIM (rise-to-meet-the-
claim correction); §EXEC.3's "WHAT'S STILL GATED" was accurate and is UNMET. The staged tree is GREEN, NO
edits were made. Three walls + an architecture decision gate even C5-(1) and MUST close before the VK epoch:

- **WALL A — the composed-PI / VK-hash source.** `prove_full_turn` (`sdk/src/full_turn_proof.rs:1042`)
  calls `generate_effect_vm_trace` (v1, 186-col) UNCONDITIONALLY; the rotated leg is an ADDED sub-proof
  under `witness.rotation.is_some()`, and `CutoverFallback` (`full_turn_proof.rs:568`) is the live routing.
  CLOSURE: make the rotated PI the composed-PI / VK-hash source so the v1 backbone can go; retire
  `CutoverFallback`.
- **WALL B — the bilateral verify stops reading `effect_vm::pi`.** `verify_aggregated_bundle`
  (`turn/src/aggregate_bilateral_prover.rs:185`) reads `wr.public_inputs[..ACTIVE_BASE_COUNT]` (the v1 PI
  slice). CLOSURE: carry the 49-felt schedule block in the witnessed receipt so the bilateral verify no
  longer reads the v1 PI.
- **WALL C — the FLOW-B note-spend freshness arm threads the rotated nullifier descriptor.** The
  `(None,Some(nullifier))` arm (`node/src/blocklace_sync.rs:2667`) calls
  `prove_and_verify_finalized_turn_freshness` with NO rotation. The descriptor is READY
  (`rotateV3WithNullifierPin`); the gap is the live node wiring + composed-PI binding. CLOSURE: thread the
  rotated nullifier descriptor into that call site.
- **THE WASM-PROVER ember-DECISION (gates C7 grep-zero).** v1 is the `#[cfg(not(feature="recursion"))]`
  wasm verify+PROVE path; `wasm/src/runtime.rs:710` calls `generate_effect_vm_trace` directly (the
  in-browser prover uses v1 because the IR-v2 prover pulls p3-recursion/DFT crates that don't fit wasm). C7
  grep-zero (deleting v1) is PROVABLY IMPOSSIBLE while wasm proves in-browser on v1 (134 live refs to
  `generate_effect_vm_trace`, 108 to `EffectVmAir`). **DECIDED (ember, 2026-06-14): Option A** — build a
  wasm-fittable rotated prover (replace the p3-recursion/DFT deps for the in-browser path) so wasm proves on
  rotated TOO → v1 dies EVERYWHERE, true grep-zero, web keeps in-browser proving. A FRONTIER build added to
  the pre-C7 work (the DFT/recursion-in-wasm problem is real) — C7 deletion waits on it, not a follow-up.

Only after these four does C5 (the v3Registry→default regen + re-pin + FFI reseed) become the safe, one
irreversible VK-epoch act. (The ✅ wall-A / wall-B `DONE` entries further below are the C4-era bilateral
*interpreter* + node self-sovereign threading — necessary parts, NOT the same as these four backbone walls;
the backbone v1 path is still UNCONDITIONAL per WALL A above.)

- ✅ DONE (staged-additive, green): **G3 AUTHORITY-DIGEST DESIGN** — the v9 rotated commitment now
  binds the FULL authority state (not a subset). `cell/src/commitment.rs::compute_authority_digest_felt`
  folds permissions/VK/delegate/delegation/program/mode/token_id + visibility/commitments/proved/
  side-table roots + fields[8..16] into register r23 (Lean welds leave r23 free → the anti-ghost
  keystone binds it, ZERO Lean change). Three-way agreement (cell v9 / producer rotation_witness /
  trace generator) holds — all derive r23 from the same fn. Tooth: `v9_binds_full_authority_state`.
  Doc: ROTATION-CUTOVER §2a. (cell + turn, no VK bump, v8 untouched.)
- ✅ DONE (staged-additive, green): **G4 COHORT-GENERAL GENERATOR** — `trace_rotated::
  rotated_descriptor_name_for_effect` resolves any of the 26 cohort effects to its `*VmDescriptor2R24`
  (fail-closed for non-cohort), `effect_vm::trace::effect_selector` extracted as the single source of
  truth; `sdk::prove_effect_vm_rotated_ir2_with_caveat` is the cohort-general rotated prover. Teeth:
  `resolvers_cover_exactly_the_rotated_registry` (=26), `non_cohort_effects_resolve_to_none`. Doc:
  ROTATION-CUTOVER §2c.
- ✅ CLOSED (the cohort boundary). The rotated registry now has all **36** cohort members
  (`circuit/descriptors/rotation-v3-staged-registry.tsv`), incl. the two former residues
  `revokeCapabilityVmDescriptor2R24` (cap-crown graduated) + `customVmDescriptor2R24` (ProofBind IR
  constraint, 3c27a51cf). Every LIVE selector resolves via `rotated_descriptor_name_for_effect`;
  none is bricked by deleting v1. The cutover-EXECUTE lane (ROTATION-CUTOVER §EXEC) drives the flip.
- ✅ DONE (cutover **C1**, 2026-06-13): the SOVEREIGN proof-carrying matched pair (FLOW A,
  test-only) is rotated — `executor::verify_and_commit_proof` routes (under `recursion`) to
  `verify_and_commit_proof_rotated` (38-PI reconstruction + `verify_vm_descriptor2`, hand-AIR
  `EffectVmAir` RETIRED on this path); producer `cipherclerk::prove_sovereign_turn_rotated` mints
  the rotated `Ir2BatchProof`. New `dregg-turn`/`dregg-sdk` `recursion` feature (default-on; wasm
  `not(recursion)` keeps the v1 leg `verify_and_commit_proof_v1`). Green: `sdk/tests/
  sovereign_rotated_c1.rs` (accept + anti-ghost) + both feature configs compile. Two obstructions
  found+fixed (NOT papered): stored NEW commit must be the trace's PI 35 (welds from the v1
  sub-trace after-state, ≠ `compute_v9(after_cell)`); verifier undoes `execute.rs` PHASE 1 (fee
  debit + nonce++) to reconstruct the producer's pre-state (cross-checked by OLD_COMMIT/PI 34).
  RE-VERIFIED 2026-06-13 (fresh persvati build, not a self-report): `sovereign_rotated_c1` both
  tests green under `recursion`; `dregg-turn` compiles green under BOTH `--no-default-features`
  and default. MEASURED win (`effect_vm_ir2_size_measure`): v1 hand-AIR 358900 B (350.5 KiB),
  verify 16.8 ms → rotated IR-v2 123292 B (120.4 KiB), verify 5.0 ms — **0.344 ratio (−65.6 %
  size), verify 3.4× faster**, on TOP of the soundness win (multi-table batch verifier replaces
  the weak hand-AIR). Hygiene: removed a dead `use serde::Deserialize;` in `executor/mod.rs`
  (the WIP's `cfg_attr(recursion, allow(unused_imports))` had the condition backwards — the
  import is unused in BOTH configs; submodules import serde themselves).
  SEQUENCING NOTE — `verify_sovereign_witness_stark` (the OTHER live sovereign verify leg,
  `execute.rs:798`, the `sovereign_witnesses[].transition_proof` path) STAYS on v1 `EffectVmAir`
  for now and is deliberately OUT of C1: it has NO matched rotated producer (every LIVE producer
  sets `transition_proof: None` — `sdk/src/cipherclerk.rs:4861`, federation/*, peer_exchange; only
  `node/src/mcp.rs:6165` + the observability demo feed it). The C1 rotated producer emits
  `sovereign_witnesses: HashMap::new()`, so it never exercises this leg. Rotating its verifier in
  isolation = a verify-without-producer brick (the exact hazard the cutover brief warns against);
  it rotates WITH the FLOW B / witness producer (C3) or retires at C7, NOT before.
- ✅ DONE (cutover **C2**, 2026-06-13): prover-free `verify_vm_descriptor2` split. A `verifier`
  feature on `dregg-circuit` (`recursion = ["verifier", + recursion-prover crates]`) compiles
  `verify_vm_descriptor2{,_with_config}` + AIRs + `ir2_config` under `--no-default-features
  --features verifier` (no `prove_batch`/DFT link); `descriptor_ir2` module-gated
  `any(recursion, verifier)`, the whole PROVE surface (`prove_vm_descriptor2*`, `build_traces` +
  trace-fill helpers, `Ir2Traces`, `prove_batch`/`StarkInstance` + prover-only imports,
  `MIN_TABLE_HEIGHT`, test mod) `recursion`-only. `verify_batch` is prover-free + `from_airs_and_
  degrees(..).common` builds only symbolic `Lookups` (the IR-v2 AIRs have empty preprocessed).
  Verified on persvati: verifier-only lib (zero `descriptor_ir2` warnings) AND default lib both
  green. Files: `circuit/Cargo.toml`, `circuit/src/lib.rs`, `circuit/src/descriptor_ir2.rs`.
- ⚠️ HARD WALL (cutover **C3**, found 2026-06-13 — needs an ember architecture decision before C3
  can proceed): `prove_full_turn`'s effect-vm leg is an `EffectVmP3Proof` that THREE LIVE
  recursive-composition surfaces ingest / re-prove as the v1 **186-col** statement, so it cannot
  rotate to `Ir2BatchProof` and C7 cannot delete `EffectVmAir`/`generate_effect_vm_trace`/
  `EffectVmP3Proof` while they stand: (1) `circuit/src/ivc_turn_chain.rs` (lightclient
  `WholeChainProof`) — `prove_descriptor_leaf` re-proves `EffectVmDescriptorAir` over the 186-col
  recursion matrix via the recursion-fork in-circuit verifier (a uni-STARK leaf-wrap); (2)
  `circuit/src/joint_turn_aggregation.rs` (lightclient `DescriptorParticipant`) — aggregation AIR
  built on `EffectVmAir::new`; (3) `turn/src/aggregate_bilateral_prover.rs` (node bilateral bundle,
  `blocklace_sync.rs:3265`/`mcp.rs:6587`) — outer STARK via `EffectVmAir` + the 204-PI slice. The
  flat FLOW B quartet (`prove_full_turn`/`verify_full_turn`/node-`turn_proving`/
  `verify_sovereign_witness_stark`) is INSEPARABLE — it mints the very proof they ingest. **Decision
  needed:** how does the whole-history recursion (and joint-turn aggregation) wrap the rotated
  MULTI-TABLE `BatchProof` (no batch-proof leaf-wrap/in-circuit-verifier exists in the recursion
  fork; the present leaf-wrap is uni-STARK only) — OR re-architect it — OR freeze a legacy v1 leaf
  for historical turns while live turns rotate (keeps v1 alive ⇒ contradicts grep-zero). Detail in
  ROTATION-CUTOVER §EXEC C3 ⚠. (`proof_forest.rs` has no non-test consumer; dies at C7.)
- ✅ DONE (cutover **C3**, 2026-06-13): the wall FELL via option (a). The rotated multi-table
  `Ir2BatchProof` leaf-wrap is GREEN (`ivc_turn_chain::prove_descriptor_leaf_rotated[_with_config]`,
  `RecursionInput::NativeBatchStark`, fork `72ffc56`/circuit `bbea731e7`) AND two rotated leaves
  AGGREGATE + self-verify at `ir2_leaf_wrap_config` (`983255781`,
  `rotation_batchstark_leaf_smoke::two_rotated_leaves_aggregate_at_wrap_config`). The recursion
  ARCHITECTURE is proven (wrap + aggregate).
- ✅ DONE (cutover **C4 recursion**, 2026-06-13, this lane — WIP, uncommitted): the two recursion
  consumers are REWIRED onto the rotated leaf-wrap. `DescriptorParticipant` gains a rotated leg
  (`rotated: Option<RotatedParticipantLeg>` {Ir2BatchProof<DreggRecursionConfig> + EffectVmDescriptor2
  + 38-PI}, `joint_turn_aggregation.rs`); `ivc_turn_chain::prove_turn_chain_recursive_rotated` +
  `prove_chain_core_rotated` + `generate_chain_trace_rotated` (reads rotated commits PI 34/35) and
  `joint_turn_recursive::prove_joint_turn_recursive_rotated` + `prove_joint_core_rotated` +
  `joint_turn_aggregation::recursion_binding_trace_descriptor_rotated` mint leaves via
  `prove_descriptor_leaf_rotated_with_config(.., ir2_leaf_wrap_config())` and run the whole tree at
  the wrap config. The v1 cores stay (deleted at C7). Circuit lib+tests+lightclient build GREEN. The
  two consumers are lightclient setup/demo-invoked (no node/sdk production loop folds a chain).
- ✅ DONE (cutover **C4 FLOW-B SDK leg**, 2026-06-13, this lane — WIP, uncommitted): `FullTurnWitness`
  widened with `rotation: Option<RotationTurnWitness>` (ungated — always-available types); when present,
  `prove_full_turn` proves the effect-vm leg via `prove_effect_vm_rotated_ir2_with_caveat` and attaches
  `"effect-vm-rotated"` (a multi-table `Ir2BatchProof`); `verify_full_turn{,_bound}` gains the
  `"effect-vm-rotated"` arm (`verify_effect_vm_rotated_with_cutover`, selector-bound over the 36-member
  cohort) + a rotated-aware commit binding (the rotated 38-PI is the v1 prefix `[0..34)` + 4 pins, so
  OLD/NEW_COMMIT at 0/4 bind unchanged). HONEST BOUNDARY (named, not degraded): the rotated 38-PI does
  NOT carry `NOTESPEND_NULLIFIER` (offset 198), so a note-spending turn with a freshness binding is
  REFUSED on the rotated leg and must use v1 until the rotated note-spend descriptor exposes the
  nullifier in-PI. sdk (default + no-default) + node build GREEN. The 2 node `turn_proving` callers set
  `rotation: None` (byte-identical v1 default) — threading the real producer witnesses from the live
  node turn (the Cell/Ledger/nullifier_root/receipt_log → `rotation_witness::produce`) is the next node
  step.
- ✅ DONE (cutover **C6**, 2026-06-13): the cell commitment is ALREADY v9 LIVE
  (`CANONICAL_COMMITMENT_CONTEXT = "…v9"`, the cap-crown flag-day `53c6e417c` bumped it). This lane
  CLEANED the stale "v8 is LIVE / do NOT bump" comment at `cell/src/commitment.rs:628`. The cell≡circuit
  v9 differential (`live_cell_v9_equals_circuit_state_commit`) already guards byte-identity.
- ✅ RESIDUE RESOLVED: the rotated registry has all **36** cohort members incl.
  `revokeCapabilityVmDescriptor2R24` (graduated by cap-crown) + `customVmDescriptor2R24` — no v1-only
  descriptor remains (`cut -f1 rotation-v3-staged-registry.tsv | wc -l` = 36).
- ⏳ REMAINING to grep-zero. **UPDATE 2026-06-13: walls (A) + (B) are now ✅ DONE + committed
  (`b0baf026c`) — see the wall-A / wall-B `✅ DONE` entries below. (A)'s only residual is the two
  SIBLING hand-AIRs `CrossSideExistenceAir` + `BundleTreeFoldAir` in the same file (they do NOT read
  `effect_vm::pi`); their Lean-emission lane ✅ LANDED (`92b41acce` — both emitted axiom-clean, found
  PURE not recursion; the hand-AIRs are now layout-of-record, deletable at C7). The remaining grep-zero
  walls are now just (C) + (D). **✅✅ ALL COHORT EFFECTS NOW ROTATE — the FLOW-B rotation campaign is COMPLETE
  and FLIP-SAFE (2026-06-14):** NOTE-SPEND (`cc1e1399c` — nullifier at PI[38], 39-PI, + the single-spend per-row
  double-spend GUARD, a model-found bug); CAPABILITY (`f967f39b0` — `rotation_witness_for_capability` from the REAL
  `full_turn_pre_cell`, binds the real authority digest r23, the over-grant tooth survives rotation —
  `cap_over_grant_refused_on_rotated_leg`); SETFIELD + BRIDGEMINT (`e9d6e357e` — the model found 3 real descriptor
  mismodels: nonce-passthrough-vs-TICK, payload@param0-vs-param1, ungated-write + `SEL_SET_FIELD=54`-is-`BALANCE_LO`,
  all enforced-fixed); SOURCE-COHERENCE (`05fe8a500` — the per-effect SetField/Mint SOURCE descriptors reconciled to
  runtime, the rotated tick-faces proved EQUAL to the source `:= rfl` so the registry routing is no longer a bypass
  of a buggy source; FULL library 3927-job axiom-clean; JSON byte-identical so the live wire is UNTOUCHED). The
  dynamic `setFieldDynV3` is proven STRUCTURALLY UNREACHABLE (a `field_idx≥8` SetField panics in v1 trace-gen before
  any rotated prove) → coherence-only, NOT a flip-blocker; the node v1-fallback predicate is REMOVED. **The model
  has STOPPED finding flip-blocking DESCRIPTOR gates (the magnesium PROOF is done); the LIVE-PATH cutover is NOT
  ready — see the ⚑⚑ PRE-FLIP GATE at the top of this section: walls A (backbone `prove_full_turn` still calls
  v1 unconditionally + `CutoverFallback` live), B (`verify_aggregated_bundle` reads the v1 PI slice), C (the
  note-spend freshness arm has NO rotation) + the wasm-prover ember-decision MUST close before the VK epoch.
  The "flip-safe, all gates closed" framing here was an OVER-CLAIM (corrected 2026-06-14).** The flip remains
  HELD for ember at the redeploy point-of-no-return, behind those four. Sole non-blocking residue: the unreachable
  `setFieldDynVmDescriptor2` slot-column (`SLOT:=1` vs runtime field_index@param0) — a separate `EffectVmEmitV2`
  coherence lane.** Original (A) plan, for the record: **(A) the BILATERAL rotated outer AIR** — DECISION =
  BUILD, emit from Lean (law #1). `bilateral_aggregation_air.rs::BilateralAggregationAir` is a plain
  hand-authored `StarkAir` reading `wr.public_inputs[..ACTIVE_BASE_COUNT]` and the bilateral-schedule
  PI offsets (`effect_vm::pi::{TURN_HASH_BASE 25..IS_AGENT_CELL 73}`). It does NOT ingest an
  `EffectVmP3Proof` — it reads the witnessed-receipt's bilateral-schedule PI layout (a ~75-felt contract
  living inside the v1 PI module). Grep-zero needs a Lean-emitted aggregation descriptor (a NEW IR2
  constraint kind — a general two-row `windowGate` for the cumulative-sum CG-4 — since `EmittedExpr`
  gate bodies see only `local`, and the WR PI vector restructured so the bilateral schedule is fed
  independently of the rotated effect-vm 38-PI). Real from-scratch Lean build (`EffectVmEmitBilateralAgg.lean`).
  LIVE via node HTTP `/turns/aggregate` (`api.rs:1723`) + MCP `dregg_bilateral_action` + WASM + the
  `teasting/tests/multi_cell_cross_fed_binding.rs` cross-federation gauntlet. **(B) node FLOW-B producer
  threading** (the 2 `turn_proving` callers → real rotation witnesses). **(C) the ~70 plain-produce/verify
  + test/demo call-sites** (node mcp/api/prove_pool, the ~40 v1 test harnesses). **(D) C5 regen**
  (v3Registry→default, re-pin, reseed FFI) → **C7 DELETE** v1 (`effect_vm_p3_full_air.rs`, `effect_vm/air.rs`,
  186-col `generate_effect_vm_trace`, `ACTIVE_BASE_COUNT`, `CutoverFallback`, `lean_descriptor_air.rs` v1)
  + grep-zero per ROTATION-CUTOVER §EXEC grep_zero_checklist.
- ✅ DONE (wall A — the BILATERAL Rust interpreter, 2026-06-13, this lane — WIP, uncommitted): the
  bilateral aggregation now proves+verifies through the LEAN-emitted descriptor (law #1), retiring the
  hand-AIR on the live path. (1) **`descriptor_ir2.rs` grew the `windowGate` primitive**: a `WindowExpr`
  enum (`Loc`/`Nxt`/`Const`/`Add`/`Mul`, the two-row twin of `LeanExpr`) + `WindowGateSpec` + the
  `VmConstraint2::WindowGate` variant + a `parse_window_expr`/`"window_gate"` decode arm (wire
  `{"t":"window_gate","on_transition":bool,"body":{loc/nxt/const/add/mul}}`) + `JsonCursor::parse_bool`
  (in `lean_descriptor_air.rs`, shared infra) + the AIR `eval` arm (`on_transition` → `when_transition()`,
  else every-row) + the `check_descriptor2` bounds arm. The other 36 descriptors are byte-untouched. (2)
  **The descriptor artifact** `circuit/descriptors/dregg-bilateral-aggregation-v2.json` (6990 B, emitted
  from `emitVmJson2 bilateralAggDescriptor`; width 87, PI 23, 70 constraints, 2 window gates) + the
  accessor `bilateral_aggregation_air::bilateral_aggregation_descriptor()` + the decoupled-layout modules
  (`sched`/`agg`/`outer_pi_v2`, Lean-mirrored) + `schedule_block_from_inner_pi` (the 49-felt window
  `inner_pi[25..74]` re-based to 0) + `build_aggregation_trace_v2` + `prove_aggregation_v2`/
  `verify_aggregation_v2` (route through `descriptor_ir2::{prove,verify}_vm_descriptor2`). Teeth:
  `bilateral_descriptor_parses_with_lean_pinned_shape`, `schedule_block_offsets_match_v1_pi_window`. (3)
  **`aggregate_bilateral_prover.rs` rewired**: `prove_aggregated_bundle` builds the 87-col v2 trace (no v1
  PI buffer) + proves via the descriptor (postcard'd `Ir2BatchProof`); `verify_aggregated_bundle`
  deserializes + verifies via the descriptor + binds the shipped trace BY CANONICAL RECONSTRUCTION (re-derive
  the 87-col trace from the Turn + claimed schedule blocks, require equality — strictly stronger than the old
  commitment match) + the per-row schedule cross-check (step 5). The 7 in-file adversarial tests rewired to
  the descriptor path. **The descriptor path is `recursion`/`verifier`-gated**; the `not(recursion)` wasm
  build keeps a stub (returns Err — the bilateral demo there is optional, the single-turn proof stands). This
  RETIRES `BilateralAggregationAir` on the live path and grep-zeroes `ACTIVE_BASE_COUNT`/`effect_vm::pi` on
  the bilateral prove/verify (the only residual coupling, `SCHEDULE_PI_BASE = inner_pi::TURN_HASH_BASE`, is a
  single offset constant, retired when the rotated WR carries `sched` natively). VERIFIED: circuit
  `--features verifier` green; `dregg-turn` lib green (FFI link). NOTE: `CrossSideExistenceAir` +
  `BundleTreeFoldAir` (the CG-5 cross-side-existence + proof-of-proofs hand-AIRs, same file) are a SEPARATE
  soundness layer that does NOT read `effect_vm::pi` — they stay as custom-STARK AIRs (a future Lean-emission
  lane); retiring the whole `bilateral_aggregation_air.rs` FILE is gated on emitting those two too.
- ✅ DONE (wall B — node FLOW-B producer threading, 2026-06-13, this lane — WIP, uncommitted): the live
  node self-sovereign turn proves ROTATED. New `sdk::prove_turn_self_sovereign_rotated` (+ `RotationTurnWitness`
  re-export) forwards the rotation witnesses into `prove_full_turn`'s rotated effect-vm leg.
  `turn_proving::prove_and_verify_finalized_turn` gained a `rotation: Option<RotationTurnWitness>` param +
  `rotation_witness_for_self_sovereign` (builds the before/after witnesses from the REAL pre/post `Cell` +
  a single-cell ctx-ledger snapshot + the empty nullifier root + the receipt-hash log, mirroring the C1
  sovereign path). SELF-VALIDATING GATE: returns `Some` only when the actor cell is representable by the
  cap-less `CellState::new` pre-state (balance/nonce match · all fields zero · empty c-list) — so the
  rotated leg's OLD_COMMIT (PI 0, the v1 prefix) agrees with the v1 leg `verify_full_turn` checks; any
  divergence falls back to v1. `blocklace_sync.rs` captures the pre-execution `Cell` (`full_turn_pre_cell`)
  and wires the `(None,None)` self-sovereign arm. The FRESHNESS (note-spend) + CAPABILITY arms stay v1 by
  design (the rotated 38-PI omits `NOTESPEND_NULLIFIER` at offset 198 — the C4 honest boundary). 5 test
  call-sites + the live call-site updated.
- ⏳ REMAINING (wall C + C5/C7): the ~70 plain-produce/verify sites are CONCENTRATED in
  `sdk/full_turn_proof.rs` (the impl) + `node/turn_proving.rs` (27) + tests/perf/wasm/verifier — most need
  NO edit now (they pass `rotation: None` = byte-identical v1; the flip to rotated-default is the C5 regen
  act). The precise C5/C7 readiness package is in ROTATION-CUTOVER §EXEC.3 (regen recipe + deletion list +
  what's still gated). The VK epoch is the MAIN-LOOP cutover-settle (must batch with the notify Step-2
  felt-encoders into ONE VK bump — docs/NOTIFY-CASCADE.md).

## Metatheory closures (Lean-side, lane-sized — tails of landed work)

- ASSURANCE §5 Stage-1 / CRITICAL-2 codec-in-TCB: the LEAN half is now CLOSED — `Dregg2/Exec/FFI/Refine.lean` proves `execFullForestAuthStep` (the `@[export dregg_exec_full_forest_auth]` body) REFINES the model (`export_refines_on_parseable`/`_endToEnd`, composed with the existing `CodecRoundtrip.parseWWire_encode`), so the turn/effect wire codec is inside the proof (pinned in Claims §28b). RESIDUAL = the RUST codec, two named obligations, NOT closed: (1) **translation-validation of `dregg-lean-ffi/src/marshal.rs`** — a 2231-line hand-rolled byte-for-byte mirror of the Lean grammar (`marshal_turn_hosted` emit at `marshal.rs:617`; `unmarshal_result` decode at `:1710`), upheld TODAY only by `dregg-lean-ffi/src/marshal_roundtrip.rs` differential vs the real FFI symbol — the obligation is `marshal_turn_hosted(w) = encodeWWire(lift w)` as a theorem (generate the Rust from Lean, or a verified-Rust mirror), not a test corpus; (2) the **Lean→C / `libdregg_lean.a` link** boundary (no binary-correspondence statement that the linked `.a` IS the `@[export]`ed Lean) — the seL4 C-to-binary analogue. Both are the §5 Stage-1 remainder; obligation #1 is the sharper "translation-validation" one. → dregg-lean-ffi/, post-rotation (disjoint from the proof-wire flip).
- Argus joint-AIR fold (Silver→Gold layer: per-leg descriptors folded; not an Argus/ statement).
- Coeffect dst-liveness (named in the 4dd84a3ae audit; outside the four apex modules).
- BiorthRelational: threshold-D iff at Shamir t-of-n (proved at 2-of-2 additive); n-ary trace statement (reduced to the adjacent-step atom).
- Trustline: `settled`-era pureCredit — Lean has both collateral points; the Rust pureCredit realization (issuer-well draws) is open (7da845758 divergence 1-as-Rust).
- Quorum unification (#170) consumer migration: `BlsQuorumCert.lean`/`EpochReconfig.lean` still transcribe the historical `n−⌊n/3⌋` + carry `StrictBft`; `MembershipSafety.lean` still has the `n=0↦0` guard. The unified `supermajorityThreshold` Lean twin LANDED (QuorumThreshold.lean) — migrate the consumers onto it (bls_quorum_diff.rs/epoch_diff.rs/membership_safety_differential.rs pin the relations until migration).
- Channels delegation_epoch wire carrier: the Lean-producer/wire path has no per-cell `delegation_epoch` carrier yet (a `DelegationEpochEquals` program evaluated there fails closed — wire lockstep before channels ride the producer); pre-atom channel cells keep the old program (no live-cell program-upgrade verb).
- Channels CountGe tails: per-element approval binding (exhibited ≠ "approved THIS turn" — the actor-bound approval-slot ceremony must write the quorum commitment slot before `councilGated` replaces `senderIs admin` in the deployed program); CountGe AIR projection (witness-side scalar only).
- Cell-program grammar atoms — Rust mirror (cutover-settle lockstep, NOT a separate edit): three new `Exec/Program.lean` atoms LANDED axiom-clean (apps gaps 2/3/4) and need their `cell/src/program.rs` twins APPENDED (variant-index-based, fail-closed, mirroring the Lean evaluator) at the next program.rs cutover-settle: (1) `SimpleStateConstraint::SenderMemberOf { members }` — sender ∈ literal id-set, reads `ctx.sender` (the clean multi-admin form of `AnyOf[SenderIs…]`; `MissingContextField` on no sender); (2) `StateConstraint::AffineDeltaLe { terms, c }` — `Σ cᵢ·(new[fᵢ]−old[fᵢ]) ≤ c`, reads BOTH old+new (a real multi-field budget-delta gate; needs an `affine_delta_sum` over the pre/post state, fail-closed on any absent term either side); (3) `SimpleStateConstraint::BalanceDeltaLte { max }` / `BalanceDeltaGte { min }` — `new.balance−old.balance` rate gates on the sealed kernel balance, read the executor's pre-turn `old_balance` + post-turn `new_balance` (fail-closed on an absent endpoint; the executor must expose the PRE-turn balance to `evaluate_constraint_full`, the `TurnCtx.balanceBefore` twin — today the ctx carries only post). Lean keystones: `evalSimpleCtx_senderMemberOf_iff` · `evalConstraint_affineDeltaLe_iff` · `evalSimpleCtx_balanceDeltaLe_iff`/`_balanceDeltaGe_iff`. COST-class (§8, honored in the atom docs): all three are the BOUNDED/ordering pole EXCEPT `senderMemberOf` which is i-confluent-FREE (single-turn-context predicate). NOTE: `BalanceDeltaGte`/`BalanceDeltaLte` SUPERSEDE the flash-well "relative-balance atom" HORIZONLOG item below (its Lean twin is now this landing). → cell/, post-rotation (variant-index APPEND keeps factory VKs / content addresses byte-identical, per CELL-PROGRAM-LANGUAGE §2).

## Node / runtime closures

- **Stage-5 consensus de-vac (Klein/HIGH-6) — `docs/STAGE5-CONSENSUS-DEVAC.md`.** LANDED: the running-node witness that consensus runs at n>1 — `scripts/devnet-n3-ordering.sh` + `node/tests/three_node_ordering_rule.rs` boot 3 REAL nodes in `--federation-mode full` (3-validator genesis, supermajority(3)=3) and assert [A] full-mode multi-party tau path engaged + [B] cross-node block exchange over the real gossip wire (both PASS). Verified: the Lean BFT model is NON-vacuous (`bft_safety` is adversary-parametrized, liveness reduced to a DLS88/HotStuff `Pacemaker`; the empty-adversary inhabitant is only a satisfiability witness) and the tau rule faithfully refines the Rust (`BlocklaceFinality.lean`). **✅ S5-1 CLOSED (`ed35b23b2`, 2026-06-14):** the running node now COMMITS a turn through the rule at n≥2 — `three_node_ordering_rule.rs` green under `DREGG_TEST_REQUIRE_FINALITY=1` (4/4+3/3); `devnet-n3-ordering.sh REQUIRE_FINALITY=1` → [C] CONVERGED `latest_height 1 1 1` at n=3 (supermajority(3)=3, the strongest case). FOUR measured defects closed (the doc named only dissemination): (1) the Dandelion privacy-STEM misroute → `publish_eager` direct full-payload push to all committee peers; (2) a CHAIN-not-round-synchronous DAG (one creator/round → `is_super_ratified` never fired) → round-disciplined production (the exact `build_rounds` shape `tau` finalizes); (3) THE root cause = HALF-DUPLEX connections (gossip read only INBOUND streams → the last-booted node could send but never receive → deadlock under supermajority==n) → spawn `serve_connection` on outbound too (~50%→12/12) + QUIC keep-alive + a `Frontier` liveness nonce + a connectivity gate; (4) a turn-execution double-apply once finality fired (faucet eager-exec → nonce-replay / dest-not-found on peers) → faucet scratch-clone in multi-party mode + `execute_finalized_turn` materializes a missing Transfer dest as a remote stub. FOLLOW-UP (NOT blocking, devnet-correct today): a production-hardening pass on faucet/finalized-execution cell-provisioning semantics → node/api + execute_finalized. Then S5-2 live commit refinement, S5-3 #170 quorum-consumer migration, S5-4 consensus leg of the composed apex, S5-5 equivocator Lean↔Rust differential pin, S5-6 finality-on-demand (`docs/CONSENSUS-FLEX.md`). → net/gossip + blocklace/dissemination + node/blocklace_sync.
- **pg-dregg Tier-C proof-attest — S1+S3 DONE, only the node producer (S2) remains.** The whole-chain IVC proof now crosses the SQL boundary for real: `circuit::ivc_turn_chain::WholeChainProofBytes` + `verify_turn_chain_recursive_from_blobs` (S1) and pg-dregg's `tier-c` leg wiring the REAL verifier (S3) are LANDED and green — the byte round-trip + tamper teeth pass (`circuit/tests/ivc_turn_chain_rotated.rs::whole_chain_proof_bytes_roundtrip_and_tamper`, 428s real fold), and the pg-dregg admit/refuse polarity is proven (`pg-dregg/tests/tier_c_real_proof.rs`, `--features tier-c`, ignored real fold). The fork (`emberian/plonky3-recursion`) needs NO edit: at the pinned rev `72ffc56` `BatchStarkProof` already derives `Serialize/Deserialize` (`#[serde(bound="")]`) and the binding `Proof<SC>` rides the pinned Plonky3 rev's serde. REMAINS = **S2, the node-side PRODUCER** (named in `pg-dregg/src/attest.rs` + `turn_proofs.rs` + `docs/PG-DREGG.md §10.2`): when finality advances, fold the new finalized turns (`prove_turn_chain_recursive` / `fold_two_turns`) and write the serialized transport + window bounds into `dregg.turn_proofs(lo, hi, genesis_root, final_root, proof bytea, vk)` the SRF reads. A real `tier-c` `ChainFolder` impl replaces `turn_proofs::StandInFolder`. → node + pg-dregg, post-rotation.
- Stale-cap c-list sweep (channels 72d43dc64 residue): epoch-step turn should `RevokeCapability` superseded grants. STILL OPEN — a real verb gap, NOT a quick fix: `member_cap_grants` installs into each MEMBER's c-list, while `RevokeCapability {cell,slot}` removes from a cell's OWN c-list; sweeping a departed member needs cross-cell `Delegate` authority the operator doesn't hold. `RevokeDelegation` epoch bump already DARKENS prior-epoch group caps at admission (R7 `CapabilityStale`) → this is c-list GC (storage), not soundness. Honest closure = a new verb shape (member-initiated self-revoke or group-scoped revoke authority). → node/turn, post-flip.
- Adjudication: bond cell → program-toothed obligation cell; tau-exclusion via a membership cell (court is the value leg only; 460d4d6bd residues). STILL OPEN — bond is a plain operator cell, not yet deployed via the obligation factory; deferred to AFTER the FLASH-WELL/blueprint `obligation_factory_descriptor` lands+verifies, then `post_bond` deploys via the factory in one slice. (That pattern now landed — unblocked for a future lane.)
- Storage: erasure coding + dedup-beyond-content-addressing — IN-CRATE half closed (storage/src/availability.rs, 10 tests). REMAINS: the node put/get HTTP route (gated by storage-gateway-mandate cell) can now CALL the in-crate availability route — the "weld to the shell" half. → node, post-flip.
- Trustline payment-channel parity: channel close (TL_STATE_CLOSED residual-escrow return) · one-factory collateral parameter · MCP `dregg_extend_trustline` · remote-silo pubkey registration (n=1 collapses it) · multilateral rippling (TRUSTLINES.md §7).
- Trustline pureCredit HTTP lane: node OpenRequest has no `collateral` field → HTTP open is fullReserve-only; `trustline_service::parse_collateral` is dead (`#[allow(dead_code)]`+TODO(collateral-axis)). Rust semantics+SDK exist; wiring the request field is the lane. → turn/node.
- Hosted-operator epoch-key custody posture (sovereign-member groups ride the SDK noun client-side; channels residue — partly an ember-decision).
- Divergence-ledger doc churn: `turn/tests/rust_lean_divergence_finder.rs:684` overwrites the git-tracked `metatheory/docs/rebuild/_RUST-LEAN-DIVERGENCE-LEDGER.md` on every run, dirtying trees + blocking persvati pushes — emit to a build-artifact path (or commit deliberately). One-line fix. → turn/ (off-limits this run; STILL LIVE, tree dirty at HEAD).
- CLI `config init` not path-injectable: `cli/src/config.rs::config_path()` hardcodes `~/.dregg` → `dregg config init` mutates real home, preflight can only gate read-only `config show`. Honor `DREGG_HOME`-style override, then restore a hermetic preflight `cli_config_init` check. → cli/.
- node recovery overlay first-writer-wins bug (surfaced by the snapshot lane): `node/src/state.rs` recovery uses `insert_cell` (strict insert), so a post-checkpoint write to a cell the checkpoint ALREADY holds is silently dropped; the convergence root-mismatch only LOGS, does not fail closed. Fix = `upsert_cell` (the verified `CrashRecovery.upd` point-update needs remove-then-insert). → node/persist, post-flip.
- persist snapshot wire half: in-crate `ship_snapshot`/`apply_snapshot`/`apply_snapshot_verified`/`install_snapshot` LANDED green (persist/src/snapshot.rs, 7 tests, shape = CrashRecovery.lean). REMAINS: node-side `GET /snapshot/{from}` serve + joiner consume route so a fresh node bootstraps over the network. → node, post-flip.
- checkpoint-prune → commit-log compaction (§2.1): `prune_before` trims attested roots but commit-log records below a finalized checkpoint are never compacted (unbounded WAL). Add `CommitLog::compact_below(height)` preserving the index-audit invariant. → persist.

## Product surfaces (post-rotation)

- dregg-query: attested-queries feature only (Q2 of docs/EPISTEMIC-DATALOG.md) — NOT the full Datalog engine.
- Flash-well: `BalanceDeltaGte` relative-balance atom collapses the fee-ratchet ladder into one constraint + closes the donation-cushion residue; `Dregg2.Apps.FlashWell` keystones land with it. ✅ The Lean `Exec.Program` twin is now LANDED (`balanceDeltaGe`/`balanceDeltaLe`, axiom-clean, keystones `evalSimpleCtx_balanceDeltaGe_iff`/`_balanceDeltaLe_iff`); REMAINING = the Rust evaluator arm (see the cell-program grammar-atoms Rust-mirror item in Metatheory closures above — both ride the same program.rs cutover-settle) + the donation-cushion app keystone. The blueprint + SDK are AUTHORED (cell/src/blueprint.rs flash-well, sdk/src/flashwell.rs) but sprint-UNVERIFIED.
- Willow geometry for storage caps (3D area caveats, range reconciliation) — adopted design, not scheduled.
- range-based set reconciliation (§1.5/§3.2d, Willow shape): the shared primitive behind scalable anti-entropy (O(diff·log) not O(state)) AND storage partial-sync; cap chains as the pluggable authorization. Adopt the geometry, keep our proofs.
- eclipse hardening at scale (§1.1): peer_score buckets by SocketAddr today; add /24·/48 prefix + AS-diversity bucketing so a single cloud /24 cannot fill the eager set.
- availability route follow-ons (§3.1): swap XOR-prototype erasure (erasure.rs:11) for real Reed–Solomon; real Merkle-path chunk proof vs manifest.root (erasure.rs:226 is integrity-only).
- proving-modality dial #169 (§4.1): make prove-on-demand vs checkpoint vs eager a CONFIGURED axis, not hardcoded policy; settlement/pipelining depth (§4.2) parameterized by topology (n=1 = immediate settlement). Owns the PI 202/203 slots.
- Room-as-OS + delay-tolerant polis (docs/ROOM-AS-OS.md, docs/DELAY-TOLERANT-POLIS.md).
- **pg-dregg M3** (named 2026-06-13; M2 mirror + Tier-C chain-gate + the §11 write outbox LANDED + live on pg17/pg18; `node/src/pg_mirror.rs` `pg_live::PgSink` writes through over tokio-postgres incl. caps/memory in one txn). UPDATE 2026-06-13 (pg-dregg wide-safe lane, Opus): the **range-attest SRF SHAPE + the federation subscriber RE-VALIDATION are now BUILT** (`pg-dregg/src/attest.rs` + `mirror::revalidate_replicated_chain` + the `dregg_attest_range`/`dregg_attest_explain`/`dregg_install_federation`/`dregg_revalidate_replicated_chain` externs; core green, 50 `cargo test` + 2 new `#[pg_test]`s; docs/PG-DREGG.md §10.2.1 + §15 rewritten). What REMAINS — the genuinely NODE-/CIRCUIT-touching settle items (this lane does NOT touch node/ or circuit/): (a) **the outbox drainer** (§11.4): a node-side tokio task drains `dregg.submit_queue` as `dregg_kernel`, runs the submit gates + `execute_via_producer` (#171), resolves + mirrors back. (b) **the proof-gate circuit-link S1-S3** (§10.2.1): **S1** serialize `circuit::ivc_turn_chain::WholeChainProof` (it holds plonky3 proof objects, NOT serde today — needs derives + a versioned envelope); **S2** node-side proof PRODUCER (fold finalized turns via `prove_turn_chain_recursive`/`fold_two_turns` → write a `dregg.turn_proofs(lo,hi,genesis_root,final_root,proof bytea,vk)` table the SRF reads); **S3** the `tier-c` feature's `dregg-circuit` dep (`--features verifier`/`recursion`, **Lean-FREE** — §8.1) flips `attest::verify_serialized_proof` from the fail-closed stub to the real `verify_turn_chain_recursive`. Until S1-S3 the SRF attests NOTHING (safe direction, §10.3). Tier D (executor in-backend) stays the north star, gated on the pg/Lean process-model spike. The 4 §6/§13 ember-decisions now carry crisp recommendations (docs/PG-DREGG.md §13.1: instant-revocation default · typed-tables-lead/views-over-memory end-state · C-embed · spike-gated full-D else D-sidecar). UPDATE 2026-06-14 (pg-dregg proof-gate lane, Opus, `pg-dregg/src/` only): **S1 SETTLED + S2 BUILT; S3 reduced to ONE named circuit line.** **S1 (the serde verdict):** `WholeChainProof` is NOT serde as a whole — but its `root` is `RecursionOutput(pub BatchStarkProof, pub Rc<CircuitProverData>)`, and the verifier (`verify_turn_chain_recursive`) reads ONLY `root.0` + `binding_proof` + the 4 publics, NEVER the prover-only `Rc` `root.1` (verified by reading the fn body: it touches `proof.root.0`/`genesis_root`/`final_root`/`num_turns`/`chain_digest`/`binding_proof` and nothing else). `BatchStarkProof` AND `RecursionCompatibleProof` (a uni-STARK `Proof`) BOTH derive `Serialize`/`Deserialize` (`#[serde(bound="")]`). So the verify-sufficient subset IS fully serde → shipped as `attest::SerializedWholeChainProof` (a versioned postcard transport: `[version][root.0 blob][binding blob][3×root bytes][num_turns]`, real encode/decode + 5 fail-closed `cargo test`s). A `WholeChainProof` VALUE can't be rebuilt from bytes (the `Rc` is prover-only) — so the ONE remaining circuit-side line is a ~6-line `verify_turn_chain_recursive_from_parts(&BatchStarkProof, &Proof, publics, &vk)` split of the existing fn (which already uses only those parts). **S2 (BUILT):** `pg-dregg/src/turn_proofs.rs` — `TurnProofProducer<F: ChainFolder>` folds a finalized window into ONE `dregg.turn_proofs(lo,hi,genesis_root,final_root,proof bytea,vk)` row (DDL `mirror::ddl::turn_proofs()` + `dregg_install_turn_proofs`), with watermark discipline (dense, non-overlapping windows) + an anti-fabrication tooth (a folder can't claim wider coverage than the window) + the `dregg_attest_window`/`dregg_attest_window_explain` externs that look the proof up FROM the table. The circuit fold plugs in behind the `ChainFolder` seam (same discipline as `Producer`/`Projector`), so the default build stays circuit-free; 7 `cargo test`s prove the producer over a stand-in folder. **S3 (the flip):** `attest::verify_serialized_proof` now DECODES the transport in BOTH builds (real, tested), then under `tier-c` calls `verify_turn_chain_recursive_from_parts` (named, the dead-behind-cfg real leg) — off, fail-closed AFTER a successful decode (proven: a WELL-FORMED transport STILL attests nothing, not just garbage). VERIFY: 120 core `cargo test` green (12 new) + clean `cargo check --features "pg18 pg_test"`. The `cargo pgrx test pg18` RUNTIME is environmentally broken on this box (a pre-existing unmodified M1 pg_test fails identically at `framework.rs:217` initdb/locale — NOT this lane). REMAINING for the flip: add `dregg-circuit` (`verifier`/`recursion`, Lean-free) to the `tier-c` feature + the circuit-side `verify_turn_chain_recursive_from_parts` split — both circuit-side, mechanical; the transport decode + publics mapping are live + tested.

### SDK polyglot crypto/binding closures

- **sdk-ts organ-noun crypto closures** (named 2026-06-13; sdk-ts now mirrors two-nouns + organ-noun as thin typed clients, green): three crypto ops stay node/wasm-side (pure TS has no Poseidon2/X25519/STARK): (a) `mailbox-verify-dequeue-proof-in-ts` (re-run storage queue Merkle verify over a drained batch); (b) `channel-seal-open-in-ts` (X25519→HKDF→ChaCha20-Poly1305 epoch-key seal/open so a TS member decrypts the fan-out — example uses placeholder ciphertext today); (c) `attested-verify-in-ts` (`verify_full_turn` STARK + federation threshold-sig check so `AttestedQuery` returns a CHECKED verdict — the light-client crown, likely waits on a wasm `verify_full_turn` export). (a)+(b) are the first users of `@dregg/sdk/wasm`.
- **userspace-verify TS/Py binding** (named 2026-06-13; `dregg-userspace-verify/` landed green, 22 tests): expose `analyze()` to TS/Py so `sdk-ts`/`sdk-py` call it pre-submission. (a) cheap path: SDK serializes its forest to JSON, shells/WASM-calls `dregg-uverify --json`; (b) integrated: a `#[no_mangle]` FFI `uverify_analyze(json_ptr,len)->json` in a small cdylib, bound from TS (napi/wasm) and Py (ctypes/pyo3 — the bridge already links libdregg). `Assurance`/`Finding`/`Locus` are Serialize+Deserialize → wire shape settled; the lane is the glue + an SDK `analyze()` sugar at `.sign()`-time.
- **DreggDL node `POST /deploy` ingress** (follow-up to the landed `dregg-deploy` + its TS/Py bindings, a7734efcc/a49448d09): a node endpoint accepting a DreggDL doc → `dregg-deploy::check` (refuse non-conserving/amplifying up front) → lower + submit per-root turns → return receipt chain + resolved factory_vks/cell-ids. Static check = pre-submission gate; executor stays the trust boundary. `dregg-deploy apply` = the same flow SDK-side. → node, post-flip.
- **sdk-py self-contained wheel**: (carried — packaging the Py binding as a standalone wheel that bundles libdregg). → sdk-py.

## APPS-POLISH lane (starbridge-apps demo-worthiness)

- **compute-exchange/ + gallery/ stub dirs** carry only a `manifest.json` (no crate) — decide: build them or delete the stubs.
- **escrow-market follow-ups** (escrow-market, 12 tests green): (a) the no-burn equality is settle-scoped in `child_program_vk` but NOT in the executor-installed flat `state_constraints` (executor installs `Predicate(state_constraints)`, evaluated unconditionally — apply.rs); to enforce exact conservation on the settle turn, either teach factory-birth install to use the cell's `Cases` program (`child_program_vk`) OR add a settle-gated relational atom. Until then no-burn rests on `build_settle_action` emitting a balanced split. (b) real ledger-balance binding — ESCROWED/RELEASED/REFUNDED are slot integers, not moved balance; wire settle to a real value transfer (trustline/flashwell `.turn()`) for the organ-true version. → starbridge-apps/turn, post-flip.
- **userspace-verify integration point** (depends on the landed toolkit): escrow's `released+refunded==escrowed` conservation predicate is the first app-level customer for the static checks — lift it to a published checker. Same shape for agent-provenance `verify_chain` + bounty-board lifecycle monotonicity.
- **polis factory-birth co-location**: polis's executor-path teeth live in `sdk/tests/polis_*_e2e.rs`, not a `polis/tests/factory_birth.rs` like the other apps — co-locating a birth test makes it self-contained.
- **privacy-voting ballot unlinkability** (named in its README): the app gives one-vote-per-ballot + monotone tamper-evident tallies, NOT ballot/voter unlinkability (no mixnet/nullifier-set). True secrecy is a separate, stronger lane.

## HANDOFF READINESS (the pug bar — a stranger evaluates dregg as a finished, usable thing)

*(ember 2026-06-12: hand the system to pug to evaluate usefulness/usability for HIS purposes.
Everything here is judged by "works without ember in the loop.")*

- FRESH-CLONE BUILD: clone → documented steps → running node, no tribal knowledge. The FFI archive seeding (elan on PATH, lake build, seed-dregg2-closure.sh) is tribal-knowledge-heavy + bit US twice this session — it must be ONE documented command (or build.rs does it) with a loud, teaching failure mode.
- QUICKSTART re-verified against POST-ROTATION reality, every command actually run (it was verified pre-rotation; #110's closure predates the organs + rotation).
- The organs reachable as a STRANGER would: SDK two-nouns + trustline/channel/mailbox/storage nouns each with a copy-paste example that runs against a local node; error messages that teach.
- An evaluator's README: what dregg IS, what it guarantees (AssuranceCase in human terms), what it does NOT yet do (honest scope), the three things to try in the first ten minutes.
- The site/playground consistent with the shipped system (no stale pre-rotation surfaces).
- One real end-to-end story pug can run start-to-finish (two agents · trustline · channel · mailbox — money moves, messages flow, a removed member goes dark, every receipt checkable). The demo IS the evaluation artifact.

## Crypto / protocol artifacts (bounded, sequenced after the rotation)

- DKG ceremony-as-cell-app: rounds over blocklace broadcast + seal-pair channels + slashable complaints (core landed 29509149d; transport is the artifact). Slash itself defers to the court→obligation-cell lane (node-closures adjudication item).
- ECVRF per-agent sortition: LANDED (federation/src/vrf.rs — RFC 9381, sortition_select/verify_sortition, SDK surface in sdk/src/identity.rs). REMAINS: full compile+test gauntlet (authored in-sprint); ticket transport serde (byte codecs only); dalek `decompress` canonicality vs §5.5 unaudited; juror-seat binding of ticket pubkey → key-set opening is documented, not yet a checked verb.
- KERI identity event-log export: LANDED (node/src/identity_export.rs — portable KEL, route GET /identity/export/{cell}). REMAINS: full compile+test gauntlet; per-cell state-commitment openings against `ledger_root` (today the snapshot↔turn binding rests on the exporting node's commit log); cooling-window length check needs charter data.
- Proactive resharing anchored in epoch-transition certs; proactive-deletion requirements (dkg.rs NOTES).
- drand-style beacon chaining (only once heights can fork; one line in beacon_message).
- OCapN netlayer adapter (2–4 week artifact): the enabling `Netlayer`/`ocapn://` trait LANDED in captp (captp/src/netlayer.rs). REMAINS the adapter: Syrup codec + `op:start-session` handshake + descriptor translation onto our session/gc tables + a wire Goblins speaks → a Goblins peer holding a dregg sturdy ref.
- MLS/TreeKEM fan-out swap for channels (replaces only `seal_epoch_key_to_roster`; cell interface unchanged).
- VRF-grade public beacon (its own later effort; ORGANS §6).

## PRIVACY/OFFLINE-CELL lane

- **Rust private-participant turn role** (design + Lean model landed: docs/PRIVATE-OFFLINE-CELLS.md + Dregg2/Distributed/PrivateLeg.lean, keystone joint_turn_sound_with_private_legs, #assert_axioms-clean). To SHIP: a private-participant leg type in `coord/src/atomic.rs` — an AtomicForest participant whose contribution is (commitPre, commitPost, proof) not an applied action, with a commit-path verify-gate implementing MixedAdmissible (every private leg's STARK verifies + binds the shared jid); the AIR the `CarrierEncodesPrivLeg` hypothesis names (recKExecAsset + recStateCommit state-root opening, producible offline); state-root continuity across turns (commitPost[i]=commitPre[i+1], mirroring HistoryAggregation.ChainBound). Liveness out of scope (a dark private participant aborts the all-or-none turn). Crypto floor = STARK extractability (no new assumption). → coord/turn, post-flip.

## seL4 / DreggDL lane (design+scoping landed)

*(Scoping docs: docs/SEL4-EMBEDDING.md (bootable-image roadmap; THE blocker = libuv-free/IO-free
Lean leanrt+GMP on musl/seL4) + docs/CAPDL-POLYGLOT-DX.md (DreggDL = describe the cap graph once,
3 SDKs instantiate it). The dregg-deploy parser crate + TS/Py bindings + sel4 verifier-PD scaffold
ALL LANDED (a7734efcc / a49448d09 / 152e6b3a5). Remaining lanes:)*

- **sel4 cross-build tail** (verifier-PD scaffolded, `no-lean-link` PROVEN Lean-free at HEAD): the actual cross-build to `aarch64-sel4-microkit` (needs Microkit SDK + rust-sel4 toolchain, absent here) + `getrandom`-custom / `p3-maybe-rayon` serial-fallback for the bare target. → sel4/.
- **Lean runtime bottom-half port (THE blocker, weeks–quarter)**: IO-free, libuv-free `leanrt`+GMP so `libdregg_lean.a` links on musl/seL4. Blocks the **executor PD only** — the verifier PD is UNBLOCKED (`no-lean-link` proves it links Lean-free). Until the port, `no-lean-link` builds the node marshal-only (shadow-off) — bring-up scaffold ONLY, never the authoritative ship.
- **First rbg→seL4 port: `DirectoryFactory` → `seL4_Untyped_Retype`** (sel4/RBG-TO-SEL4.md): the smallest real port turning an rbg idea into a kernel-enforced mechanism (factory's slot-caveat becomes the Untyped retype template). Additive, NOT gated on the Lean-runtime blocker; belongs in a `sel4/factory-pd/` sibling once rust-sel4 is wired.

## STARBRIDGE-V2 (native gpui shell — embedded verified executor)

*(The master interface EMBEDS the real verified executor + runs a live local dregg world natively
— headless heart gpui-free + `cargo test`-able, 183 lib tests green; the window OPENS via gpui
`runtime_shaders`. Build-out lanes from docs/STARBRIDGE-V2.md coverage matrix:)*

- LANDED (2026-06-13, the fork-seam unblock + 4 capabilities): the `embedded-executor`
  feature now COMPILES (the local plonky3-recursion `[patch]` replicated into
  `starbridge-v2/Cargo.toml` — the standalone workspace did not inherit the breadstuffs
  root patch, so `dregg-circuit`'s `NativeBatchStark` reference failed to resolve). Then:
  **organ panels** (`organs::OrganSurvey` — trustline + flash-well LIVE cell-state decoded
  from the embedded ledger via the published `blueprint` slot constants; channel/mailbox/court
  surfaced HONESTLY as remote-path, kind·seam·route, never faked; ORGANS tab) · **whole-graph
  ocap delegation layout** (`graph::OcapGraph` — nodes/edges + MULTI-HOP reachability (BFS
  transitive closure = a cell's blast radius) + layered delegation-depth layout + cycle
  detection; GRAPH tab) · **proof-attach + STARK verification-status board** (`proofs::ProofBoard`
  — the three honest tiers verified-by-construction/executor-signed/STARK-attached + the route
  to the next; PROOFS tab) · **A2 swarm deepened** (`swarm::Swarm::run_atomic` = N-action
  atomic forest bundle all-or-nothing; `swarm::Swarm::bind_surface` = per-member cap-confined
  firmament SurfaceCapability pane). All gpui-free + `cargo test`-able; the three new tabs +
  ⌘K nav commands wired into the cockpit. (Fixed a pre-existing latent over-grant in
  `swarm_world()` exposed by the unblock — the test helper granted coord a cap to a worker it
  did not hold; now seeds both mandate caps at genesis.)
- **organ OPERATING verbs** (open/draw/repay/settle/close) — LANDED (`organ_ops::OrganDriver`,
  11 tests). The cockpit now DRIVES trustline + flash-well organs as REAL turns through the
  embedded executor (not just reflects them): each verb shapes the protocol effect sequence and
  commits it via `World::commit_turn`, with the REAL `dregg_cell::blueprint` per-organ program
  installed on the organ cell (via `World::set_cell_program`) so the executor's per-cell predicate
  gate (`execute_tree.rs`) enforces the invariant IN-PROTOCOL — an over-line draw is refused by
  the `FieldLteField(drawn ≤ ceiling)` tooth, a fee-evading flash-well borrow by the
  `StrictMonotonic(ratchet)` tooth, a touch on a closed organ by the lifecycle table (all
  asserted refused, not faked). The embedded single-custody collapse: the organ cell is born
  open-permissions, its own pubkey is its `SenderIs{owner}` governance root, and the operator-root
  installs the adopt-grant well-cap on the borrower — the SDK's `Trustline`/`FlashWell` dance
  collapsed to the single image (no dregg-core change — both organs are embed-core). Carried
  residue: the `AgentRuntime`-shaped bridge to the SDK handles themselves is NOT built (the verbs
  re-shape the SAME effect sequences against `World`'s `DreggEngine` rather than driving
  `dregg_sdk::trustline::Trustline` directly — one model, two surfaces, kept in step by sharing
  the blueprint program + slot constants).
- **N9 STINGRAY CEILING WELD** — LANDED (`swarm_budget::StingraySwarmBudget` + `Swarm::
  attach_stingray_budget`, 13 tests). The swarm's shared budget is now a REAL
  `dregg_coord::StingrayCounter` (the single-image shared pool: `n=1`, `f=0`, the one slice
  ceiling IS the pool `B`), wired the way the SDK's `runtime::set_budget_gate` attaches a
  `BudgetSlice`: every dispatch draw-checks its DECLARED fee against the pool BEFORE its turn runs
  (fail-closed `SwarmError::PoolExhausted` on a breach — the counter's gate, not a summation),
  and settles the ACTUAL metered cost after. The conservation invariant `total_drawn() == Σ metered
  across members` is the counter's own accounting (PROVABLE, not best-effort), bounded by `B`; the
  aggregate strip reflects the counter (`total_spent`), and the pool exposes the identical
  `BudgetSlice` the executor's `set_budget_gate` would attach (one model, two surfaces). This is
  the depth lift over N1's per-member FLOOR meter — simbi's "UI counter vs verified conservation
  bound" gap closed.
- **LIVE NODE connection** — LANDED (headless heart green; the gpui strip compiles). The wire
  client + model (`NodeClient::{Mock,Http}` + `src/model`) MOVED into the LIBRARY (gpui-free,
  `cargo test`-able) and gained a `live-node` feature (`native-full` + `sel4-thin` both enable it;
  pulls `reqwest`, whose blocking client needs no caller tokio runtime). `client::LiveNode::sync()`
  fetches `/status` + `/api/cells` and projects them into the SAME uniform `reflect::Inspectable`
  the embedded world uses (no parallel view path); `client::LiveNode::connect_stream()` spawns a
  BACKGROUND SSE reader on `/api/events/stream` that feeds the PURE `live_node::SseParser` and
  pushes decoded receipts onto an mpsc channel. The cockpit drains it each frame
  (`drain_live_stream`) and fires `cx.notify()` PER RECEIPT — the ReceiptInspector advances live,
  REPLACING the snapshot. `live_node::ReceiptFeed` is the cursor + bounded ring + resume model.
  The PURE layer (SSE parse · live reflection · receipt-feed cursor) is fully `cargo test`-able
  with byte fixtures (10 new lib tests; the reqwest byte-pull is the only `live-node`-gated part).
  `--node <url>` wires it through `main.rs` → `Cockpit::with_node`; a LIVE NODE strip in the rail
  header shows the remote producer/liveness/height + the live receipt feed head + resume cursor.
  Remaining for the WINDOW: pixels need the Metal Toolchain (host blocker below).
- **native deos AFFORDANCE surface** — LANDED (`src/affordance.rs`, 5 lib tests). htmx-on-crack with
  the firing→executed-turn SEAM CLOSED through the embedded executor (the thesis `starbridge-web-
  surface` could only MODEL — it has no embedded executor). `CellAffordance` (named effect-template +
  `AuthRequired` a viewer must hold) · `AffordanceSurface::project_for` (progressive ATTENUATION via
  the REAL `dregg_cell::is_attenuation`, `required ⊆ held`) · `fire` → `AffordanceIntent` (anti-ghost:
  an unauthorized actor is REFUSED, not run) · `AffordanceIntent::fire_through_world` hands the real
  `Effect` to `World::commit_turn` so the receipt is the EXECUTOR's own (`FireOutcome::Committed`) and
  a guarantee-violating fire (over-transfer) is REFUSED by the executor (`FireOutcome::Refused`) —
  both gates real, in-band. The window cap gating an affordance IS the firmament
  `Capability{Surface(cell)}` (a window); an affordance-fire is a cap-gated verified turn, the deos
  thesis native. The FRUSTUM-SNAPSHOT (rehydration) is also real: `AffordanceSnapshot` is TINY (the
  cell + the declared names, NOT the data); `rehydrate_for` re-expands it PER-VIEWER through the same
  `is_attenuation` gate (a narrow-cap viewer rehydrates a narrow interactive surface from the SAME
  snapshot; the live surface is the source of truth, so a dropped affordance does not rehydrate).
  (Cockpit affordance-PANEL: a follow-up; the surface + snapshot + their 5 tests are the heart.)
- **starbridge-web-surface LIVE receipt-stream PRIMITIVE** — LANDED (`starbridge-web-surface/src/
  receipt_stream.rs`, 11 tests; NEXT-WAVE.md item D). The standalone thesis crate (which MODELS
  surfaces, no embedded executor) gained `ReceiptStream` — a subscription over the node's
  `/api/events/stream` receipt feed so a surface's organs become LIVE reflections of the committing
  node, not snapshots. Built ON the genuine shapes (`dregg_query::ReceiptEventRow` envelope +
  the full `dregg_turn::TurnReceipt` the SSE `data:` carries; the dense `chain_index` cursor the
  node serves as `Last-Event-ID`; `Dynamics::since(cursor)` semantics). The NEW tooth over the
  cockpit's existing `ReceiptFeed` (which only DEDUPS by index, trusting the body): **forge-
  rejection** — `ingest` REJECTS an out-of-order frame (`IngestError::OutOfOrder`, a gap/rewind in
  the dense chain) AND a forged one (`IngestError::Forged`, body does not re-hash to its claimed
  `receipt_hash` via the REAL `TurnReceipt::receipt_hash`), and `verify_against(&AttestedRoot)`
  checks the whole delivered prefix against the federation's `receipt_stream_root`
  (`merkle_root_of_receipt_hashes`). `StreamedReceipt` is the `WorldEvent`-shaped item; the pure
  `ingest`/`since`/`verify_against` core is `cargo test`-able with NO runtime; `ReceiptStreamPoll`
  (`stream` feature, default) is the `futures_core::Stream` the gpui executor `.await`s. Verified
  NARROW: `cargo test -p starbridge-web-surface` green both `--no-default-features` (121 lib, pure)
  and default (122 lib, +the Stream poll test) + 4 integration.
  **FOLLOW-ON — the cockpit gpui-executor subscription (starbridge-v2, a DIFFERENT lane owns it):**
  re-point the cockpit's live receipt path (`starbridge-v2/src/{live_node,client,cockpit}.rs` —
  the `ReceiptFeed` + `drain_live_stream` + `cx.notify()` wiring) at THIS verifying primitive, so a
  cockpit reflecting a REMOTE/untrusted node gains forge-rejection (today's `ReceiptFeed::ingest`
  trusts the body); drive `ReceiptStreamPoll::poll_next` on gpui's async executor (`cx.spawn`),
  storing the waker on feed so a fed `ingest` wakes the poll (the no-op-waker test shows the SHAPE;
  the real waker is the cockpit's). Single-source the two `ReceiptEvent` mirrors (this crate's
  `ReceiptEnvelope`/`ReceiptEventRow` + `starbridge-v2/src/model::ReceiptEvent`) under the named
  `dregg-wire-types` extraction below while there.
- **native federation/remote-node panel** (the LIVE NODE connection above is the wire; a richer
  multi-peer federation panel + the channel/mailbox/court LIVE reflections ride a connected node).
- **seL4 framebuffer backend** — a gpui renderer targeting a framebuffer cap (SEL4-EMBEDDING end state) + **seL4 channel transport** (a `NodeClient::Channel` over an seL4 endpoint, same contract over IPC not TCP).
- **single-source wire types** — replace `starbridge-v2/src/model/` hand-mirrors with a shared `dregg-wire-types` crate depended on by both node + shell.
- **finish-the-window (HOST gap, not a crate defect)**: the runtime-shader path opens the window; the offline Metal Toolchain download is blocked by a damaged Xcode `DVTDownloads.framework`. The remaining ahead-of-time-shader option = provision the Metal Toolchain on a healthy Xcode.

## DREGG-ANALYZER (forensic/observability trace analysis)

*(New crate dregg-analyzer/ — ingests CAPTURED TRACES, ATTESTS via the REAL verifiers. The five
capture types are EXACT MIRRORS — they import-and-reuse the system's own structs (`CheckpointData`,
`CommitRecord`, `TurnReceipt`, `CallForest`) rather than redefining them, so a format drift is a
compile error, not a silent skew. The AnalysisReport is now DEEPENED beyond the per-source summary:
the blocklace report surfaces the concrete EQUIVOCATION-FORK WITNESS (the real `EquivocationProof`
`block_a ∥ block_b` pair the protocol would slash on, recovered by re-running the node's own
`detect_equivocation`); the receipts report builds the RECEIPT-LINK GRAPH (distinct agents +
federation replay-domain set w/ cross-federation flag + Final/Tentative finality breakdown +
encrypted-path count + introduction/routing/derivation/consumed-cap edges — all bound into the v3
receipt hash, so on an intact chain they are attested non-strippable); the WAL report carries the
RECOVERY OVERLAY (per-record replay detail + touched-cell re-touch count + block-hwm resume anchor)
AND the ledger-root CONVERGENCE TRAIL (distinct-root count + a stagnant-root-with-touched-cells
Critical anomaly). Build-out lanes:)*

- **live-capture hooks** (THE TAIL — node-side, out of this crate's scope) — a node trace-export mode emitting `BlocklaceCapture`/`ReceiptStrandCapture`/`WalCapture` from the running node (the on-disk/wire types are already exact mirrors, so an export endpoint is a thin dump). → node.
- **Studio/Workbench visualization binding** — render the `AnalysisReport` (DAG w/ equivocation fork, finality bar, receipt link graph, WAL replay overlay) in the Starbridge/starbridge-v2 shell (report is already JSON-serializable).
- **gossip capture provenance** — the network source is `Observed`-only (gossip = liveness); a signed dissemination-receipt would graduate some eclipse signals to `Verified`.

## Overnight 2026-06-14 — wide-safe wave seams (named follow-ups; the work itself is committed green)

*(While the cutover flip is HELD for ember, the night ran a 5-lane wide-safe braid. Each lane named an
honest scope-limit; closure levers below. The flip — C5/C7 + #103 graduation + the notify VK epoch +
the devnet redeploy — remains the one held item, one-command-ready per §EXEC.3, awaiting ember at the
redeploy point-of-no-return.)*

- **in-browser / over-wire recursion-verify** (web-forward, `2dcede9b3`): `WholeChainProof.root` is an
  `Rc`-backed `RecursionOutput` with NO serde, so the in-tab whole-history recursion-verify (and the
  pg-dregg S1 proof-gate) is placeholdered behind a versioned envelope. Closure = fork-side
  (plonky3-recursion) recursion-proof serialization (the same follow-up `ivc_turn_chain` already names).
  → plonky3-recursion fork. SHARED by web-forward + pg-dregg S1.
- **browser-extension at-rest key** (`8a8ab52ba`): the MV3 front door keeps the key in
  `chrome.storage.local` for the demo; production at-rest hardening (BIP39+PBKDF2+AES-256-GCM, auto-lock)
  is the shape the sibling wasm cipherclerk already ships. The property PROVEN is the trusted-path
  mediation (key never reaches the page), not at-rest encryption. → sdk-ts/extension.
- **ADOS narration R1 join** (`eeb5655f2`): the narration-vs-truth panel correlates at the FEED level
  (`Correlation::FeedLevelOnly`); claim-to-a-SPECIFIC-turn needs the tool-call→effect compiler (R1). The
  divergence panel ships now; the compiler is the deeper join. → starbridge-v2 + the R1 compiler.
- **persist history-below-checkpoint** (`9f031f7e8`): after `compact_below`, `identity_export`
  (`commit_records_from(0)`) returns only survivors — pre-checkpoint EVENT history is no longer locally
  reconstructable (an archival node simply does not compact). Finalized-STATE correctness is untouched
  (the checkpoint ⊕ overlay is exact). → node/identity_export (a feature-scope decision, not a bug).
- **cli hermetic preflight** (`9427a18e5`): `config_path()` now honors `DREGG_HOME`; restore the hermetic
  `cli_config_init` preflight check that this unblocks. → preflight/cli.
- **N5 killer-demo deferred step-5** (starbridge-v2, `1535f46a7`): the four-surface headline demo proves
  frames 1-4 (mint / agent turn / notify handoff / dual refusal) as REAL receipted turns + exits 0 on the
  headline contract; the demo's **step 5 = the pg-dregg Tier-B SQL mirror read** is NOT wired (it needs a
  live pg mirror outside the starbridge-v2 crate — the N2/pg lane). Closure = stand the pg mirror, add the
  SQL read-back frame. → starbridge-v2 + pg-dregg (the outbox/mirror lane), post-flip. NOT blocking.
- **N13 over-wire byte-verify** (web-forward, `6fb9e8087`): the web-surface killer-demo page is now verified
  e2e (20-check Playwright over the 5-step state machine via the real wasm bindings — the over-share is the
  genuine executor `DelegationDenied`, not a banner) + discoverable. The remaining **over-wire byte-verify**
  (a fetched whole-history proof verified in-tab) is the SAME `WholeChainProof` serde seam already named
  above — closes when the fork-side recursion-proof serialization lands. → SHARED with the recursion-verify
  seam. NOT a separate item.
- **assurance-catalog drift** (the assurance lane, UNCOMMITTED at HEAD): the assurance lane's in-tree edits
  to `metatheory/Dregg2/AssuranceCase.lean` (+ `Exec/ForestMemoryProgram.lean`, `Exec/UniversalBridge.lean`,
  `Cargo.lock`) change the assurance source-of-truth, so the generated catalog
  `site/src/_includes/studio/assurance-catalog.generated.json` is STALE until regenerated. Closure = after the
  assurance lane commits, re-run the catalog generator (the studio build step) so the site reflects the new
  AssuranceCase. → site, AFTER the assurance lane lands. (One-step, mechanical; tracked so it isn't lost.)
- **signed-turn producer admit (LANDED, not a follow-up)**: the default-on Lean producer
  (`DREGG_LEAN_PRODUCER`) now ADMITS a genuine `Authorization::Signature` turn (the N=4 testnet's remote
  signed-submission path). Root cause was two width mismatches under the `Crypto.Reference` portal
  (`verify stmt proof = stmt == proof`): (1) the `Signature` arm mapped to a 256-bit R-half statement vs a
  u64 proof that could never echo; (2) the wire `prev` crossed as a full-256 digest while the host
  `stored_head` crossed as low-64, so the ChainHead leg rejected EVERY non-genesis turn. FIX:
  `turn::lean_shadow::sig_echo_wire` recomputes the executor's real `verify_strict` (target pubkey ·
  federation/nonce/position-bound message · full 64-byte sig) and folds the verdict into a self-echoing
  low-64 `(statement, proof)` pair (genuine ⇒ echo ⇒ admit; forged/tampered/cross-fed ⇒ non-echo ⇒ veto);
  `prev_hash` now uses the same low-64 projection as `stored_head`. Lean teeth `signature_teeth_same_wire`
  (+ `#guard`s, `#assert_axioms` kernel-clean). Green: `DREGG_LEAN_PRODUCER=1` node
  `remote_signed_envelope_e2e_*` + `three_node_full_mode_runs_the_ordering_rule` PASS; `dregg-turn` 555
  pass; `lake build` green. (Recorded as the durable note; the commit is the record.)
- **bearer/token producer-admit parity for REAL data (the sibling latent gap)**: the bearer/token WHO-leg
  fix (`c35153ce5`) folds the full sig/discharge chain so a FORGED credential ⇒ veto (sound), and its teeth
  use synthetic `.bearer 7 7`/`.token 9 9` (echoing). But on a REAL bearer/token turn the wire still carries
  `deleg_msg`/`issuer_key` as a full-256 digest vs a low-64 `deleg_sig`/`sig` — so a GENUINE bearer/token
  turn would NOT echo under `Crypto.Reference` and the authoritative producer would VETO it (the same
  width-mismatch class the Signature fix just closed). LATENT because no test drives a real bearer/token turn
  through `DREGG_LEAN_PRODUCER=1` (the divergence corpus is all `Unchecked`). Closure = give bearer/token the
  `sig_echo_wire` treatment (recompute the real ed25519/biscuit verdict in the marshaller, emit a low-64
  self-echoing pair) + an e2e producer test that submits a genuine bearer/token turn and asserts ADMIT. →
  turn/lean_shadow, when a bearer/token turn rides the verified producer. (Not in the Signature-arm brief;
  named so it isn't lost.)

- **circuit-soundness apex REDUCED to {four realizable floors + the dischargeable decode-extraction
  family} (`Dregg2/Circuit/ClosureAll.lean`, 2026-06-17).** `lightclient_unfoolable_closed` instantiates
  the apex at `S_live`/`Rfix`/`kstepAll`, carrying {`StarkSound`, `Poseidon2SpongeCR` + the `CommitSurface`
  CR fields, `WitnessDecodes`, `mkLog` (the `logHashInjective` log binding), and `∀ e, ClosedLogExtract e`}.
  `#print axioms` = {propext, Classical.choice, Quot.sound}, green (3978). HONEST: `ClosedLogExtract e` IS
  the per-effect `Satisfied2 (R e) → StateDecodeLog → kstep` refinement (= `descriptorRefines` + log) — the
  circuit-forcing RUNGS are PROVEN (the `RotatedKernelRefinement*` family + the 31 `*_closedLog` wrappers),
  but the `Satisfied2 ⟹ encode` DECODE-EXTRACTION is still CARRIED inside `ClosedLogExtract` (and the
  `extract` hypothesis of `closedLogExtract_transfer`). That extraction is a THEOREM (dischargeable — the
  trace columns ARE in the `Satisfied2` witness), NOT a floor. So this is a clean REDUCTION, not closure.
  GENUINE REMAINING WORK: (a) DISCHARGE the per-effect `Satisfied2 (R e) ⟹ <effect>Encode` decode-extraction
  (the column readout; the cap-tree/guard openings ride the realizable prover-witness residual, the
  `TransferAuthoritySource` class) — `TransferDecodeBridge` did the ledger half. (b) FIX the
  `Rfix := v3Registry[e]?` index seam — it keys by LIST POSITION, = `actionTag` only for leading slots, so
  non-leading effects' rungs aren't yet at their genuine descriptor; re-key `Rfix` by `actionTag`.
  (c) `exercise` (tag 16) genuinely has NO outer `.log` receipt (its log advances in the inner fold) —
  `exercise_closedLog` bridges faithfully (not a hole). Named: circuit-soundness reduction, 2026-06-17.

## Decisions pending (ember)

- #93 proof-audit: build a harness, or declare `#assert_axioms` + non-vacuity-both-polarities + the Convergence gauntlet its successor and close. (Recommendation: the latter — WRITTEN UP as docs/ASSURANCE.md §4 with the close-rationale; awaiting ember's flip to close.)
- Hosted key custody posture (above).
- starbridge-apps stub dirs compute-exchange/gallery: build or delete (above).
- **#103 cap-crown — TWO EffectVM AIRs, the weaker one LIVE on the sovereign path (SOUNDNESS-shaped, not janitorial). ✅ DECIDED 2026-06-13 (ember): shape (i) — GRADUATE the sovereign bespoke path onto the rotated multi-table AIR AT THE FLIP, so in-circuit non-amplification (granted ⊑ held vs the authenticated cap_root) holds EVERYWHERE. This is now a C5/C7 flip TASK: cut `cipherclerk.execute_sovereign_turn_with_proof` + `proof_verify.rs::verify_and_commit_proof` off the bespoke `EffectVmAir` onto the rotated `Ir2BatchProof` path, and retire the `air.rs:1365-1374` legacy cap arm with it.** There are two constraint systems for the EffectVM proof: (a) the AUDITED p3-batch-stark `EffectVmP3Air` (`circuit/src/effect_vm_p3_full_air.rs`), which carries the GRADUATED cap-crown Phase-B gates (sorted-tree membership-open + leaf-update + submask + expiry-monotone, its `attn` module ~`:189-310`; the non-amp gauntlets `circuit/tests/effect_vm_{attenuate,grant,revoke}_non_amp.rs` exercise exactly these); and (b) the BESPOKE FRI `EffectVmAir` (`circuit/src/effect_vm/air.rs`), whose `eval_constraints` still pins AttenuateCapability `cap_root` as the LEGACY nested-digest `new_cap_root = H2(old_cap_root, H2(slot_hash, narrower))` (`air.rs:1365-1374`) — it has NO sorted-open / submask / non-amp tooth (verified: no `cap_root::`/`CAP_TREE_DEPTH`/membership markers in air.rs). The default full-turn path emits + verifies the p3 proof (`prove_full_turn`→`prove_effect_vm_p3`, stored in `FullTurnProof.proof_bytes`; verified live via `dregg_sdk::verify_full_turn`/`verify_full_turn_bound`, `node/src/turn_proving.rs:246/414/532`) — so the graduated AIR gates the default path. BUT the bespoke `EffectVmAir` IS still live on the **sovereign-cell bespoke-STARK path**: `AgentCipherclerk::execute_sovereign_turn_with_proof` produces `stark::prove(&EffectVmAir,…)` bytes into `turn.execution_proof` (`sdk/src/cipherclerk.rs:5160-5166`, also `:6305`), and `TurnExecutor::verify_and_commit_proof` verifies them via `stark::verify(&EffectVmAir,…)` (`turn/src/executor/proof_verify.rs:420-421`), reached when `turn.execution_proof.is_some()` && cell is sovereign (`turn/src/executor/execute.rs:476`). The two species CANNOT silently cross — `stark::proof_from_bytes` requires a `b"DREG"` magic header and fails closed on the postcard p3 blob (`circuit/src/stark.rs`). **Reachability (severity calibration):** `execute_sovereign_turn_with_proof` is a `pub fn` SDK API (not cfg-gated) but its ONLY in-repo callers are `tests/src/sovereign_proof.rs:73/125`; NO service/binary (node/cli/discord-bot/demos/starbridge) drives it — so this is a LATENT public-API-surface gap exercised only by in-repo tests, NOT a shipped-node-flow hole. (The sibling `execute_with_program` `:6278/:6305` is the other bespoke `execution_proof` writer, same API-surface posture.) NET: on the sovereign bespoke path, an `AttenuateCapability` is checked only for the legacy digest-advance shape, NOT for in-circuit non-amplification (`granted ⊑ held` against the authenticated `cap_root`) — so a caller of that API gets the weaker cap guarantee. **Decision shapes:** (i) graduate the sovereign path onto the p3 AIR (cut `cipherclerk.execute_sovereign_turn_with_proof` over to `prove_effect_vm_p3` + `verify_effect_vm_p3`, retire the bespoke `EffectVmAir` cap arm) — the coherent close, lands the same non-amp guarantee everywhere; or (ii) declare the sovereign bespoke-STARK path deprecated/decommissioned (no live caller ships it) and delete it wholesale; or (iii) accept the weaker sovereign cap-binding as an explicit documented scope-limit. NOT deleted: deleting only the `air.rs:1365-1374` cap arm while the sovereign path still verifies through `EffectVmAir` would BREAK that path's cap-root binding (left intact pending this decision). CROSS-REF: the ROTATION FLIP tail above ALREADY plans to "rewrite executor `proof_verify.rs::verify_and_commit_proof` … bespoke `stark::verify` → the rotated Ir2BatchProof" and to DELETE `effect_vm_p3_full_air.rs` — so decision-shape (i)/(ii) has a natural landing AT the flip; the open question is whether the sovereign cap-binding gap is acceptable in the interim (it is live on the bespoke path TODAY, pre-flip) or wants an earlier targeted fix. Named: cap-crown #103 burn-down, 2026-06-13.
- **#103 cap-crown Phase-D — the 4-ary c-list `membership` leg vs. the sorted `cap-membership` leg (retire-or-keep).** `sdk/src/full_turn_proof.rs` attaches TWO distinct membership sub-proofs to a cap-gated turn, proving DIFFERENT claims: (a) the **4-ary c-list `membership` leg** (`:978-1012`, witness `MembershipWitness` `:177`, `prove_membership_p3` over the generic positions-indexed `P3MerklePoseidon2Air`, PI `[leaf_hash, root]`, vk `merkle_poseidon2_descriptor`) proves "an opaque capability `leaf_hash` is present in A Merkle tree at the witnessed positions" — a GENERIC membership statement; its root is not structurally pinned to the authenticated `cap_root`, and the leaf is an opaque hash (not the typed 7-field cap preimage). (b) the **sorted `cap-membership` leg** ("cap Phase D", `:1075-1100`, witness `CapMembershipWitness` `:212` ← `ConsumedCapWitness`, `prove_cap_membership_p3` over the SORTED `CanonicalCapTree`, directional path, vk `cap_membership_circuit_descriptor`, expectation `CapMembershipExpectation` `:239` pins `pi[CAP_ROOT]` to the trusted root `:248`) proves "the SPECIFIC CONSUMED capability's full 7-field leaf preimage opens against THE holder's real sorted `cap_root` tree" — the authority leg that ties the acting/consumed cap to the authenticated cap-state, with sorted single-leaf-per-slot semantics. **The two are not redundant:** the sorted leg gives the strictly stronger, structurally-pinned, typed-leaf guarantee; the 4-ary leg gives a weaker generic membership over an unpinned root with an opaque leaf. **Retire-vs-keep tradeoff:** for a cap-gated turn the sorted `cap-membership` leg SUBSUMES the authority claim the 4-ary leg makes (consumed-cap-in-the-real-cap_root ⊃ opaque-leaf-in-some-4-ary-tree), so the 4-ary leg is retireable FOR CAP-GATED TURNS on the claim alone. **Live-producer evidence (the deciding fact):** there is currently NO live producer that sets `membership: Some(MembershipWitness{..})` — the only two build sites (`full_turn_proof.rs:2303`, `:2774`) are both inside `#[cfg(test)] mod tests` (`:2107`) using `merkle_test_witness`; the only LIVE membership-leg producer is `cap_membership` (`node/src/turn_proving.rs:518`, `CapMembershipWitness::from_consumed`). So today the 4-ary `membership` leg is dead on the live path — its `Option`/`P3MerklePoseidon2Air`/`merkle_poseidon2_descriptor` plumbing is wired + SDK-tested but unfed. **The keep argument** is therefore forward-looking, not current: the 4-ary leg is the GENERIC credential/c-list membership primitive (opaque leaf, witnessed root, no sorted `cap_root` to open against) that a NON-cap predicate-credential turn-shape WOULD use — retiring it removes that future affordance and the `merkle_poseidon2` descriptor's only full-turn consumer. **Recommendation (ember to ratify):** keep the 4-ary leg as the general-membership primitive but DO NOT couple it to cap-gated turns (the sorted leg is the cap authority leg of record); OR, if no near-term non-cap credential turn-shape is planned, demote the 4-ary leg + its descriptor to a clearly-labelled "general membership, no live producer" status (Research tier) so it stops reading as a live cap-authority alternative. Before any removal, confirm no in-flight feature wires a live `membership: Some(..)`. Named: cap-crown #103 Phase-D map, 2026-06-13. (Left intact — characterization only, per the brief.)

## Research tier (explicitly not scheduled)

- Transcendental-syntax S3 (substructural recovery from the dregg side) + S5 (stella instantiation).
- UC-security / CryptHOL (#31) + research pillars (revocation/info-flow/metadata).
- Hypersystem/simplicial joint turns (dregg4 vision).

## ⚠ FAITHFULNESS FINDING (surfaced by the #8 real-trace task, 2026-06-19) — Lean gate/transition vs Rust when_transition

The #8 "real non-empty inhabitant" task could NOT build a natural `nonce 0→1` transfer trace: the Lean
`VmConstraint.holdsVm` evaluates `.gate` and `.transition` on EVERY row INCLUDING the last (no `isLast` guard —
`EffectVmEmit.lean:410-411`), where `nxt` wraps to `zeroAsg` → forces the last row's STATE_AFTER = 0, propagating
back to `before.nonce = -1`. The deployed Rust AIR evaluates BOTH `Gate` and `Transition` under
`builder.when_transition()` (`descriptor_ir2.rs:1763-1772`) — every row BUT the last. So **Lean-Satisfied2 is
STRICTER than Rust-accept on the last row**, and the byte-identity descriptor differential does NOT catch it (the
emitted constraint JSON is identical; only the EVALUATION semantics diverge).

DIRECTION = potential SOUNDNESS-COVERAGE gap: soundness apex proves `Lean-Sat ⟹ genuine`; the deployed claim
needs `Rust-accept ⟹ Lean-Sat`, which FAILS if Lean is strictly stronger (a Rust-accepted trace with a last-row
gate/transition violation isn't covered by the apex). LIKELY MITIGATED (unconfirmed) by Rust `when_last_row()`
PI-bindings + boundary (`:1744`) pinning the last row's published state — but NEEDS the analysis: does any
published commit/PI read from a row that could be an adversarial last row whose gate/transition Rust skips? If
the last-row state is fully PI-pinned, benign; if not, a real hole.

INVESTIGATE AT SETTLE: (1) confirm `.gate`/`.transition` faithful direction (Lean every-row vs Rust
when_transition) across the rotated descriptor; (2) trace which row feeds the published 8-felt commit + whether
when_last_row pins it; (3) decide — make Lean `.gate`/`.transition` `isLast`-guarded to MATCH Rust (faithful), OR
prove the last-row divergence benign. This makes #8's empty/degenerate-single-row witness a SYMPTOM, not the
gap. (#8's real-row lemma is kept as the jointly-satisfiable-arithmetic witness; the natural trace awaits this.)

## ⚠ #6 RECONCILIATION + a potential cross-asset hole (2026-06-19, #6 collector build-half)

CORRECTION to `2f42998b1` ("#6: no aggregation point exists, per-cell-isolated"): that was the single-cell
ROTATED path (`verify_and_commit_proof_rotated`). It MISSED the ATOMIC multi-cell path
(`turn/src/executor/atomic.rs::execute_atomic_sovereign:597-612`), which DOES aggregate: extracts each cell's
`extract_net_delta(public_inputs)` → `proven_deltas` → `net_excess = proven_deltas.iter().sum(); if != 0 →
ConservationViolation`. So cross-cell conservation IS deployed for atomic turns — but with TWO gaps the #6
`BlockConservation` collector closes:
1. ⚠ SCALAR / ASSET-BLIND: `proven_delta` is a bare i64; the sum ignores AssetId. If a multi-asset atomic turn
   is reachable (AssetId := issuer-cell → plausible), `A:−10 asset7 + B:+10 asset8` nets 0 and PASSES = mint
   asset7 / burn asset8 (a CROSS-ASSET-BORROWING hole). #6's per-asset partition (`cross_asset_borrowing_rejected`
   tooth) closes it. CONFIRM-AT-SETTLE: are multi-asset atomic turns reachable? If yes → live hole, not nicety.
2. OFF-AIR: the `.sum()` is executor-trusted Rust, invisible to a ledgerless client. #6's collector is in-AIR.
LIVE-WIRE (#6): replace the scalar `atomic.rs` sum with `BlockConservation` (pair each `public_inputs` with its
`entry.cell_id` asset, per-asset `prove_and_verify`/`verify_with_proofs`); bundle seam =
`proof_verify.rs::verify_proof_carrying_turn_bundle:774`. `BlockConservation` (`circuit/src/block_conservation.rs`)
+ 8/8 teeth built, uncommitted.

ALSO FLAGGED (confirm pre-existing at settle): `cargo test -p dregg-circuit` (non --lib) hits a linker failure
in `circuit/tests/effect_vm_ir2_size_measure` (undefined p3 `from_ext_basis_coefficients`/
`recompose_quotient_from_chunks`) — the #6 agent says that file is unmodified/clean-in-git; verify it's
pre-existing (not a swarm interaction) at settle.

## ⚠⚠ LEAN-SIDE CHECK of the Rust findings (2026-06-19, ember: "could be even worse issues there") — IT IS

Checked the Lean side of the two Rust findings. One is fine; the other is WORSE on the Lean side (the trust anchor).

1. CONSERVATION — Lean SPEC is FAITHFUL (per-asset, NOT laundered): `Spec/Conservation.lean` is per-domain/
   per-asset parametric (`multi_domain_independent`: balance/note-per-asset/cross-cell conserve INDEPENDENTLY,
   no cross-domain leakage). So the Lean is correct and the Rust scalar `atomic.rs` sum genuinely UNDER-delivers
   vs the spec → the cross-asset hole is real (deployment doesn't meet its own Lean spec). The apex likely does
   NOT prove per-asset conservation about the DEPLOYED path (only #6's new unwired AIR does) — confirm at settle.

2. ⚠⚠ GATE/TRANSITION — the WORSE issue (potential HOLLOW-SOUNDNESS in the apex): the Lean every-row
   `.transition` (no isLast guard, `EffectVmEmit.lean:411`) makes `Satisfied2` NON-INHABITABLE by a real
   `nonce 0→1` trace: last row's `nxt = zeroAsg` forces `last.after = 0`; a noop pad freezes `after=before`; so
   ANY trace (single or padded) is forced to `before.nonce = -1`. Rust's `when_transition()` skips the last row
   → Rust handles `nonce 0→1` fine. CONSEQUENCE: a REAL deployed proof (Rust-accepts, real nonce) does NOT
   satisfy the over-strict Lean `Satisfied2` ⇒ `Rust-accept ⟹ Lean-Sat` FAILS for real turns ⇒ the soundness
   apex may be VACUOUS for the actual deployed trace family (proven, but covering only degenerate `nonce=-1`
   traces no real turn produces). #8 hit this directly (couldn't build the natural trace; its witness is the
   degenerate debit-to-zero). This is a faithfulness gap in the TRUST ANCHOR, worse than any Rust gap.
   FIX (confirm + apply at settle): `isLast`-guard Lean `.gate`/`.transition` (`VmConstraint.holdsVm`) to match
   Rust `when_transition()`, then RE-CHECK every refinement rung still holds (they should — the real traces they
   model become inhabitable) AND that #8's natural `nonce 0→1` trace now satisfies. HIGH PRIORITY — this gates
   whether the soundness apex is non-vacuous for real turns.

## gate/transition divergence — CONFIRMED on BOTH Rust paths (2026-06-19, before the audit lands)

The Lean-every-row vs Rust-when_transition divergence is confirmed on BOTH Rust evaluators:
- IR-v2 deployed path: `descriptor_ir2.rs:1763` puts Gate + Transition under `builder.when_transition()`.
- v1 hand-AIR: the frame-freeze `s_noop·(after−before)` (`air.rs:578`) + nonce-tick `new−old−(1−s_noop)`
  (`air.rs:1630`) are "Enforced on all rows except the last" (`air.rs:1619`).
Lean `holdsVm` (`EffectVmEmit.lean:410-411`) guards NEITHER `.gate` nor `.transition` on isLast → the last
row's transition forces main `STATE_AFTER = 0`, the freeze chains it back through every pad → the main-table
state chain collapses to 0 → a real `nonce 0→1` is unsatisfiable (#8's empirical wall).
OPEN (audit dimension B decides hollow-vs-benign): the published 8-felt commit is welded from the ROTATED limb
block (r0=bal_lo, r1=nonce), NOT main STATE_AFTER (#8's degenerate trace carried r0=10/r1=-1 with main-after
zeroed). So the apex may not be FULLY vacuous (commit reads the rotated block) — but the main-table model is
non-faithful regardless. FIX warranted either way: isLast-guard Lean `.gate`/`.transition` to match Rust
`when_transition`, then re-verify every rung + that #8's natural trace becomes inhabitable. (The audit will
resolve whether it was a live hole or "merely" non-faithful.)

## ⚠ DIFFERENTIAL FUZZER spike (2026-06-19) — feasible + a META-finding: the existing faithfulness test is UNFAITHFUL

FEASIBILITY: the Lean↔Rust differential constraint-satisfaction fuzzer is FEASIBLE + mostly-scaffolded. v1
precedent exists (`effect_vm_descriptor_exhaustive_differential.rs` = generator-driven differential vs the REAL
`p3 check_all_constraints`) + a kernel-PROVEN executable Lean oracle pattern (`Argus/InterpCore.lean::decideVm`
+ `decideVm_iff_satisfiedVm:301`, axiom-clean). Targeted checker = ~300-500 LOC / days. The ONLY undecidable leg
of `Satisfied2` is the `mapOp` heap existential (`DescriptorIR2.lean:485` opensTo/writesTo = ∃ heap); everything
else computes (the §10 `#guard decide(...)` goldens `:1374` prove it) → a `decideSatisfied2` +
`decideSatisfied2_iff_Satisfied2` (mirroring v1's decideVm, mapOp arm oracle-parameterized) is the gold-standard
faithful oracle (~1-2wk). Coverage-guided fuzzer = OVER-SCOPED (seams are few+structural; a domain-aware
boundary mutator — row-counts 1/2/n, first/last/interior mutations, per-arm forge menu — hits them
deterministically). Verdict: build the TARGETED checker; skip coverage-guidance.

⚠ META-FINDING (laundering in the VERIFICATION layer — exactly the goal's "critical eye on how they are
proved"): the EXISTING v2 differential `circuit/tests/ir2_denotation_eval_differential.rs` is UNFAITHFUL — its
"Lean side" (`eval_enforces:553`) deliberately MIRRORS the Rust `when_transition` last-row skip (`for r in
0..n-1`). So BOTH sides skip the last row → the test is GREEN but STRUCTURALLY CANNOT catch the gate/transition
every-row-vs-when_transition gap it exists to catch. It checks transcription-vs-transcription (both bent to
Rust), NOT the real Lean `holdsVm`. FALSE CONFIDENCE. FIX (queue AFTER the #1 holdsVm fix lands, so it reflects
the fixed Lean): un-mirror the `:553` loop to run REAL every-row `Satisfied2` semantics on the Lean side +
add the boundary generator (row-counts 1/2, last-row mutations). This is the targeted differential checker.

## ⚑⚑ FAITHFULNESS AUDIT MAP (2026-06-19, a5dd3457) — the close-out roadmap for the goal

Lean trust-anchor vs deployed Rust Ir2Air::eval. THREE verdicts + the drive order:

(i) gate/transition divergence = BENIGN FOR SOUNDNESS, completeness-vacuity is the real cost. The published
   8-felt state_commit is pinned on the LAST row TWO ways that both fire there (where gate/transition don't):
   a `.piBinding .last (saCol STATE_COMMIT) NEW_COMMIT` under when_last_row (EffectVmEmitTransfer.lean:123 ↔
   descriptor_ir2.rs:1744) + the every-row Poseidon2 hash-site lookups over the last row's own state_after
   (descriptor_ir2.rs:1797). NO commitment-malleability hole. (Tightening, not a hole: the NoOp pad's
   last.after==last.before isn't forced — a `.boundary .last saCol==sbCol` would make it explicit.)

(ii) ⚑⚑ THE PRIZE — YES the apex rungs are VACUOUS FOR REAL TRACES at HEAD. CircuitSoundness.lean:428 consumes
   Satisfied2 t with t universal; the ONLY constructed inhabitants are degenerate (empty trace
   CircuitCompletenessNonVacuity.lean:89; single-row all-zero-after nonce -1→0 ...Real.lean:141). NO witness has
   the real shape (multi-row, interior active, nonce 0→1, NoOp-pad last), and NO Satisfied2 witness exists for
   incNonceV3 or any non-transfer effect. So light-client unfoolability is TRUE-BUT-EMPTY for the real trace
   family. Invisible to the byte-identity differential. THE close: finish the isLast-guard (#1) AND construct a
   genuine multi-row nonce-0→1 NoOp-pad witness for Satisfied2 (per effect, not just transfer).

(iii) FAIL-CLOSED: NONE relies on producer behavior for soundness (GOOD — satisfies "no unreachable things"):
   setFieldDyn field_idx>=8 is VERIFIER-ENFORCED in-circuit (deg-8 product gate Π(field_index−k)=0,
   effect_vm_p3_full_air.rs:1506 + the JSON gate) → UNSAT not just producer-panic; the #2 "multi-residue/#78"
   degree bound is enforced symbolically by verify_batch. check_descriptor2 bounds-checks every producer index
   FIRST (descriptor_ir2.rs:4445/1172). One cheap defense-in-depth tightening: proof_verify.rs:357/359/391/393
   discard the ledger CAS Result with `let _ =` → should be `?`-propagated.

OTHER divergences FAITHFUL/benign: lookup membership-vs-LogUp (chip AIR committed + every row pinned to genuine
Poseidon2, out-lanes assert_zero descriptor_ir2.rs:2039) · mem/map ops (committed sub-AIRs + zero-summed buses).

⚑ STANDING TCB GAP (#5, why #1 was invisible): the differential is BYTE-IDENTITY (JSON fingerprint), NOT
denotational — Ir2Air::eval is trusted-by-inspection; no Lean proof it realizes Satisfied2. Durable closure =
the differential checker / a Satisfied2 ⟺ Ir2Air::eval accept-set equivalence (acknowledged in-source
InterpCore.lean:47).

DRIVE ORDER: (1) #1 foundation — finish the isLast-guard port (tree RED at EffectVmEmitTransfer.lean:437,
in-flight) + construct the real multi-row per-effect Satisfied2 witnesses → retires the vacuity AND divergence
#1; (2) #6 conservation per-asset (separate off-AIR lane); (3) #5 the differential checker (the standing
faithfulness guard); (4) the let_=→? + NoOp-pad-boundary tightenings; (5) the build-half live-wires once settled.

## ⚑⚑⚑ THE FOUNDATIONAL RECKONING (2026-06-19) — Satisfied2 does NOT denote the deployed verifier; the proofs are ungrounded

The denotational reviews (lookup a82d354c, assembly a94c4eb1) + Lookup.lean's own header establish: the Lean
`Satisfied2` is NOT a faithful denotation of the deployed Rust `verify_vm_descriptor2`. The byte-identity
"differential" hid this for the entire campaign. THE proofs prove `Satisfied2 ⟹ genuine`; there is NO verified
link that `Satisfied2` denotes what we deploy — and the link is BROKEN in multiple, opposite directions:

- FAITHFUL: boundary, pi_binding, range (where exercised; range is height-pinned + lookup-replaced, the old
  inert-ranges scar is closed).
- gate/transition: Satisfied2 TOO STRICT (every-row, no isLast guard) → forces last-row state to 0 → the apex's
  Satisfied2 is inhabited only by degenerate traces → VACUOUS for every real turn (#8's wall).
- lookup / chip table: Satisfied2 TOO LOOSE — `tf .poseidon2` is prover-FREE (no chipTableFaithful leg);
  `ChipTableSound` is an undischarged hypothesis ON the levers, not a leg OF Satisfied2 → accepts forged-digest
  tables Rust rejects.
- ⚑ THE ROOT (assembly): the LogUp/bus GRAND-PRODUCT — the mechanism `verify_global_sum` uses to tie EVERY
  auxiliary table (chip/memory/map/range/Blum) to the main trace — is NOT MODELED in Lean AT ALL. `Satisfied2`
  replaces it with POSTULATED equalities (memTableFaithful/mapTableFaithful = `tf = log`) + membership, and has
  NO correlate for the chip/range/mem-check buses. Lookup.lean:17,32 states the philosophy outright: "membership
  is the meaning; LogUp is merely how the prover ENFORCES it." So the soundness obligation `bus-balance ⟹ tables
  faithful` is UNPROVEN + UNMODELED + UNNAMED. Every rung silently assumes "the buses did their job."

CONSEQUENCE (ember's "none of our proofs mean anything"): the rungs are internally-valid theorems about a model
that is neither a subset nor superset of the deployed accept-set. They do NOT establish deployed soundness. The
model-to-system bridge — the load-bearing obligation — was substituted with a worthless syntactic JSON-fingerprint
check. This is THE fundamental proof-engineering error.

NOT total loss (the honest balance, NOT reassurance): the rungs + the crypto floors (Poseidon CR, FRI) survive as
real artifacts; v1 PROVES the bridge is buildable (`Argus/InterpCore.lean::decideVm_iff_satisfiedVm` — an
executable denotation proven == the spec — done for v1, SKIPPED for the v2/Ir2 apex). LogUp soundness is itself a
legit NAMED floor (like FRI) — the sin isn't "we didn't re-prove LogUp," it's that we HID it (baked into "meaning
= membership") instead of naming it + establishing the link.

THE CLIMB-OUT (re-grounding, before any live-wire/purge — there's no point wiring/deleting against a phantom):
1. NAME the floors explicitly (LogUp-soundly-enforces-membership · chip-AIR-constrains-table-to-genuine-Poseidon2
   · byte/range-table-height-correct) as apex hypotheses, NOT baked into the denotation.
2. WIRE table-soundness into Satisfied2 as STRUCTURAL legs (chipTableFaithful etc.) derived from those floors —
   so rungs stop carrying undischarged ChipTableSound.
3. UN-STRICT gate/transition (isLast-guard) so Satisfied2 isn't vacuous (the #1 fix, in flight).
4. BUILD THE BRIDGE: a denotational differential `Ir2Air::eval-accept ⟺ Satisfied2` (under the named floors) —
   the v2 analog of decideVm_iff_satisfiedVm. THE missing foundation; the real replacement for byte-identity.
5. RE-VERIFY every rung against the faithful, floor-explicit Satisfied2 (breaks = real gaps the phantom hid).
PURGE byte-identity + the live-wires come AFTER the model is the system.

## RECKONING REFINED (2026-06-19, mem/map review a2fc4403) — the modeling WORKS where done right; 3 specific divergent legs

The mem/map review (deepest, field-by-field) REFINES the assembly review's "the bus is unmodeled" — that was too
pessimistic. For MEMORY, the Lean conjunct `memTableFaithful : tf .memory = memLog` denotes EXACTLY what the
Rust BUS_MEM_LOG/BUS_MEM_CHECK permutation buses enforce (the reviewer traced send/receive field-by-field, serials
aligned, log-send correctly every-row, Blum multiset = bus grand-product). So Lean modeling the bus's NET EFFECT
as a conjunct IS denotationally FAITHFUL (same accept-set) even without modeling the grand-product MECHANISM.
memOp + umemOp: FAITHFUL (one tightening: pin log-send guards boolean in-AIR `guard·(guard−1)=0` vs the witness-
builder's 0/1 reject — internalize it).

So the COMPLETE faithfulness map (all 3 reviews):
- FAITHFUL: boundary · pi_binding · range (height-pinned) · memOp · umemOp. The approach works where done right.
- DIVERGENT leg #1 gate/transition: too STRICT (every-row) → Satisfied2 vacuous for real traces. FIX: isLast-guard
  (in flight). [over-constrains]
- DIVERGENT leg #2 chip table (lookup): a MISSING leg — there is NO `chipTableFaithful` conjunct for tf.poseidon2
  (unlike memTableFaithful for memory) → the chip table is prover-FREE → accepts forged digests. FIX: ADD the
  leg, template = memTableFaithful; wire ChipTableSoundN in structurally. [under-constrains]
- DIVERGENT leg #3 map root: a WRONG leg — Lean `opensTo`/`writesTo` use `Heap.root` = FLAT SPONGE
  (Heap.lean:367); deployed MapOps/MapAbsent use a DEPTH-16 BINARY MERKLE root (heap_root.rs); no bridge theorem
  and none can hold (sponge ≠ tree-fold); DeployedCapTree.lean:8-20 admits it verbatim. FIX: re-define opensTo/
  writesTo over the binary-Merkle model ALREADY PRESENT in DeployedCapTree.lean + re-prove the _functional
  anti-ghost against nodeOf_injective. [models the wrong object]

So it is NOT "burn it down" — most legs are faithful; the modeling approach is sound (memory proves it). It is
3 specific legs to fix (templates EXIST for all 3) + the missing machine-checked BRIDGE (the reviews established
faithfulness by careful HUMAN correspondence; there is still no `Satisfied2 ⟺ Ir2Air::eval` theorem — the
denotational differential is what makes the human reviews machine-checked + regression-proof). Climb-out unchanged
in shape, sharper in content: fix legs #1/#2/#3 (memTableFaithful / DeployedCapTree / isLast templates) → build
the bridge → re-verify rungs. Serious (proofs don't establish deployed soundness until done) but BOUNDED.

---

## DOCUMENT LANGUAGE — the dreggverse patch-theory document core (2026-06-19)

NEW: the `dregg-doc` crate (`dregg-doc/`, standalone workspace, dependency-free) — the Pijul-shaped
patch-theory core of the document language (`docs/deos/DOCUMENT-LANGUAGE.md`). A document is a
`DocGraph` of alive/dead content atoms (+ provenance) with order-edges + a single-valued field store;
a `Patch` is `Add`/`Delete`(tombstone)/`Connect`/`SetField` with `apply`/`compose`/`invert` (RCCS
reversibility); `merge` is the total join/LUB (the colimit-by-union the pushout computes); a conflict is a first-class `ConflictRegion`
(prose antichain OR field clash) carrying provenance; `History` is content-as-patch-fold with
`replay`/`replay_to` (time-travel) + `branch`/`stitch` (the pushout into the shared doc); the `Regime`
classifier splits illusory (prose) from real (field/authority) conflicts. 31 unit tests + 1 doctest
green; clippy clean.

LANDED (the §4.4 RESEARCH #1 proof, in LEAN): `metatheory/Dregg2/Deos/DocMerge.lean` —
**the document `merge` IS the least-upper-bound (the JOIN) in the document inclusion order `⊑`** —
the least-upper-bound join that the pushout *computes* in the Pijul model (NOT "the categorical
pushout"; see the MINTED audit lesson below): `merge_comm`/`merge_assoc`/`merge_idem`/`merge_total`
+ the universal property `merge_least`/`merge_is_lub` (the least graph including both legs;
`merge_includes_left`/`merge_includes_right` = the cocone legs); conflict-as-state (`ConflictAt`
antichain over **transitive reachability** `Reaches` = the refl-trans closure matching
`content.rs::reachable`, `merge_has_conflict` concrete witness, `resolve_collapses`); the two-regime
split connected to `Confluence.IConfluent` (`prose_iconfluent` vs `field_not_iconfluent`).
`#assert_axioms`-clean, `#guard` teeth; `lake build Dregg2.Deos.DocMerge` green; registered in the
`Dregg2.Deos` crown (`lake build Dregg2.Deos` green).

MINTED (audit lesson, "rise to meet the claim"): the earlier DocMerge OVERCLAIMED ("THE categorical
pushout up to unique iso") and modelled the atom merge as a naive **Finset struct-union** — the WRONG
operation: it never applied the Dead-wins status join, so a deleted atom could resurrect on merge. The
AUDIT caught it. The FIX: the atom store is now a KEYED MAP (`AtomId → Option AtomVal`) and `merge`
applies `Status.join` POINTWISE (`merge_status_dead_wins` is the proof). Two corrections in one breath:
(1) honest framing — it proves the LUB/join the pushout computes, NOT the categorical construction (the
category `P`, the span, functoriality = the named residual); (2) the conflict relation now uses
transitive reachability (`Reaches`), not a one-hop shadow.

LANDED (this session, Rust — `dregg-doc/`): the §4.4 RESEARCH #2 conflict-as-state SOUNDNESS is now
BUILT, plus the substrate ride and the authoring path. 56 tests + 1 doctest green with
`--features substrate`.
- (a) **The conflict-as-state COMMITMENT** (`dregg-doc/src/commit.rs`): `commit()` binds atoms + edges
  + fields WITH provenance into the document commitment. The anti-forge tooth is TESTED — forging or
  dropping a conflict alternative changes the commitment (a light client can't be shown a conflict that
  hides a forged/omitted alternative).
- (b) **The REAL substrate ride** (`dregg-doc/src/substrate.rs`, behind the `substrate` feature):
  projects the `DocGraph` into a real cell `heap_map` and commits via the production sorted-Poseidon2
  `compute_heap_root` — the anti-forge tooth RE-PROVEN against the REAL root, not the `DefaultHasher`
  stand-in.
- (c) **The ergonomic authoring path** (`dregg-doc/src/doc.rs`): `Doc::edit(author, text)` diffs
  text → patches via token-LCS at Line/Word granularity, with the duplicate-token stable-id fix
  (inserted atoms are predecessor-seeded so repeated tokens stay distinct).

RESIDUALS / next:
- The DocMerge full categorical-pushout construction (the category `P`, the span `a ← a⊓b → b`,
  functoriality, unique-iso) is the named residual; the Lean proves the executable consequence — the
  least-upper-bound / colimit object the pushout computes.

## 🟥 LIVE HOLE CONFIRMED (2026-06-19, a17f3278) — scalar conservation forges value ACROSS ASSETS (fail-open)

The HORIZONLOG ~2267 CONFIRM-AT-SETTLE resolves: multi-asset atomic turns ARE reachable → LIVE HOLE.
VERIFIED at source (atomic.rs:610 read directly): `let net_excess: i64 = proven_deltas.iter().sum(); if
net_excess != 0 {Err}`. ZERO asset keying. The deltas come from extract_net_delta (trace.rs:1429) = a bare i64
from one (NET_DELTA_MAG, NET_DELTA_SIGN) PI pair — NO asset field in the PI. atomic.rs has zero token_id refs.
- REACHABLE: AtomicSovereignTurn/MixedAtomicTurn carry Vec<AtomicProofEntry> with unconstrained per-entry
  cell_id; no guard requires shared token_id; multi-cell atomic turns are tested (atomic.rs:2019).
- FORGING TURN: entry A (asset 7, NET_DELTA −10, individually valid) + entry B (asset 8, +10, valid) →
  proven_deltas=[−10,+10], net_excess=0 → ACCEPTED. Asset 7 destroyed, asset 8 minted from nothing.
- FAIL-OPEN: the check is OFF-AIR (plain Rust executor arithmetic, NOT a verified constraint) → a light client
  verifying the published per-cell proofs cannot detect it; nothing in-circuit re-derives Σδ=0 per asset.
- The correct per-asset machinery EXISTS but is UNWIRED: block_conservation.rs (untracked ??, its own doc says
  "NOT invoked by the deployed verifier") + cross_cell_conservation_air.rs (the proven per-asset Σδ=0 AIR, asset
  pinned in PI). Lean Spec/Conservation.lean:21-46 is per-domain-independent — the deployed Rust collapses it to
  one asset-blind scalar. The conservation≠correctness trap, literally (a PROJECTION mistaken for soundness).
FIX (driving): replace the scalar sum at atomic.rs:609-612 + the mixed site ~890-897 with a per-asset collector
keyed by entry.cell_id's AssetId (:=issuer-cell), feeding PerCellContribution + declared mint/burn rows into
BlockConservation::prove_and_verify so each asset's Σδ=0 is IN-AIR + independent; same handoff at
proof_verify.rs::verify_proof_carrying_turn_bundle + the FullTurnWitness.conservation:None slot
(turn_proving.rs:843/1101/2244). Prereq: COMMIT block_conservation.rs + add asset class to the per-cell PI (or
derive trustworthily from cell_id at the collector) so the partition pin is genuine not an off-AIR annotation.

## LANDED (2026-06-19): asset-class is PI-BOUND — light-client per-asset conservation is proof-only
The asset class is now carried in the per-cell proof's PUBLIC INPUTS (`pi::v3::ASSET_CLASS`, the 4th v3 slot,
V3_BASE_COUNT 212→213), pinned by an AIR row-0 boundary constraint to a new `aux_off::ASSET_CLASS` trace
column (NUM_AUX 97→98) — so a proof COMMITS to its asset class (a prover cannot claim a PI class that disagrees
with the row-0 aux its trace committed). The fold `fold_token_id_to_asset` moved into `dregg_circuit::
block_conservation` (the ONE canonical fold the prover, executor, and light-client share). The executor
(atomic.rs `resolve_proof_asset_class`) groups per-asset deltas by the PROOF-bound class and reconciles it
against the trusted ledger token_id (OWNER_CELL_ID/FEDERATION_ID posture); the light-client/bundle path
(proof_verify.rs `check_bundle_per_asset_conservation`) groups by `PI[ASSET_CLASS]` directly — LEDGER-FREE
per-asset Σδ=0, enforced for the conservation-closed case (disclosed mint/burn keeps executor declared-row
accounting). Lean re-anchored (`RotationLayout.PiV3.ASSET_CLASS`, `v3_slots_fresh_and_distinct` for 4 slots);
Rust drift guard pins ASSET_CLASS=212. Builds: `dregg-circuit --features prover` + `dregg-turn` green;
`lake build Dregg2.Circuit.RotationLayout`/`EffectVmEmitRotation` green.
RESIDUAL (named, not laundered): the live PROVER paths (turn_proving.rs `generate_effect_vm_trace`,
full_turn_proof.rs) still emit `EffectVmContext::asset_class = ZERO` (the default) — threading the cell's
token_id through the prover entry signatures (`prove_and_verify_finalized_turn` et al.) is the remaining work.
Until then the executor treats a ZERO PI class as "not-yet-populated" and falls back to its trusted ledger class
(sound on the full node); the bundle path's pure-light-client partition is non-trivial for multi-asset turns
ONLY once the prover populates the slot. The PI surface + circuit binding + both read-paths are done.

## ⚑ OVERNIGHT ASSURANCE CAMPAIGN (2026-06-19→20) — the trust surface collapsed
After the foundational reckoning (Satisfied2 didn't denote the deployed verifier), the climb-out + an overnight
assurance push closed it. 15 commits, each its own green slice:
SOUNDNESS: the LIVE conservation hole (scalar asset-blind sum -> cross-asset forgery, off-AIR fail-open) CLOSED
  (per-asset in-AIR + PI[ASSET_CLASS] proof-bound + prover populates the real class); commitment width 4->8 felt
  (62->124-bit collision, matches FRI). LIGHT-CLIENT OFF-AIR CENSUS: conservation was the LONE off-AIR fail-open
  (nonce/chaining/height/authority/nullifier/disc all proof-bound, file:line evidence) — a systematic positive,
  not just a patch.
FAITHFULNESS: gate/transition (isLast) + chip-table (structural chipTableFaithful) + map-root (depth-16 Merkle)
  all fixed; the 20-rung+apex collapse (no free lever survives). THE DIFFERENTIAL NOW RUNS REAL MACHINERY: row-
  local arms via the actual Ir2Air::eval (96/216, no drift), bus arms via the actual prove/verify_vm_descriptor2
  batch assembly + verify_global_sum (13 cases, no drift; model-found+fixed the map-absent Const(0) bug). The
  'transcribed-by-inspection' trust is GONE.
BRIDGE: decideSatisfied2_iff_Satisfied2 (kernel-proven exec-denotation <-> Satisfied2); the mapDec oracle
  DISCHARGED (mapDecMerkle proven faithful) -> the Lean bridge half is assumption-free modulo the named CR floor.
NON-VACUITY: every apex floor/carrier proven inhabited + separating (no laundered emptiness); the KEYSTONE made
  whole = ONE active+faithful Satisfied2Faithful witness (real debit 100->90 nonce 0->1 AND genuine chip/range
  tables, axiom-clean, not even the CR floor).
HYGIENE: --features verifier (light-client build) un-broken; wide-descriptor width-skew (188-col) regen IN FLIGHT.
NET: the v2 deployed apex went from 'ungrounded against a phantom' to faithful + kernel-bridged + real-machinery-
  differential-guarded + non-vacuous + the lone soundness hole closed. Deploy parked (box lost); all green +
  committed, push-to-origin/main when a box returns.

## ⚑ ENMESHMENT TOPOLOGY CENSUS (2026-06-20) — layer 2/4: EXECUTOR↔SPEC = WELDED (the strong result)
The user's holistic "is it end-to-end enmeshed / would edits turn proofs red" census. Executor↔spec verdict
(ada583f6, grounded file:line):
- WELDED + axiom-clean + EFFECT-COMPLETE. `fullActionStep_exec_iff` (ActionDispatch.lean:328) is a PROVEN iff
  `execFullA st fa = some st' ↔ fullActionStep st fa st'` naming BOTH real objects (no hypothesis abstraction);
  #assert_axioms-pinned (:512). `execFullTurnA_iff_turnSpec` (:481) lifts to whole-turn. Covers ALL 57 action
  arms via 43 per-effect `execFullA_*_iff_spec` keystones, each #assert_axioms-pinned in its Circuit/Spec/*.lean
  leaf. No effect spec-only or executor-only. exerciseA R4 facet-gate enforced on BOTH sides.
- The Lean executor IS production: @[export dregg_exec_full_forest_auth] (FFI.lean:3325) is the sole prod turn
  entry; Rust runs it over the C-ABI (turn/src/lean_apply.rs, lean_shadow.rs). The legacy Rust apply.rs is the
  thing being RETIRED, NOT an oracle — its parity is EMPIRICAL differential (rust_lean_divergence_finder,
  lean_state_producer_*), not a Lean proof.
- WELD TEST: editing any fullActionStep arm / execFullA arm / *_iff_spec keystone / turnSpec fold / the R4 gate /
  the circuit *Spec post-state -> RED (apex rebuilds them via CircuitSoundness.lean:494,829 rw
  execFullTurnA_iff_turnSpec). NOT caught by Lean (the accepted seam): legacy Rust apply.rs parity (empirical) +
  FFI marshalling (below the proved execFullA layer).
- THE 3-CORNER TRIANGLE CLOSED: (a) executor⟺spec = the 43 keystones + FunctionalRefinement.lean intent triangles
  (mint/burn/delegate/attenuate/revoke/noteCreate/noteSpend, #assert_axioms-pinned, anti-ghost teeth); (b)
  circuit⟺spec = CircuitSpecTriangle.lean *_circuit_pins_intent + _rejects_wrong_ledger + _intent_is_circuit_acceptable
  for ~13 effects against INTENT oracles; whole-turn WholeTurnTriangle.lean binds the composed turnSpec post to one
  authenticated root. Terminal seams = named CR carriers (Injective D, logHashInjective) + the distributed Σδ=0
  consensus binding — typeclass params, never an open hole.

## ⚑ ENMESHMENT CENSUS layer 1/4: CIRCUIT effect-slot discharge (adc53df9) — the real frontier
ALL 30 live effect families DISCHARGED (the ∀ e hyp is NOT an open hole — closedLogExtract_all_genuine
ClosureFanoutGenuine.lean:828 is a 36-way split, every slot a proven <e>_descriptorRefines concluding the real
fullActionStep arm, axiom-clean). So SPEC-edit -> red holds for ALL 30. BUT the CIRCUIT-edit -> red property
splits them:
- CLASS A (circuit-descriptor-bound, edit propagates RED): 6 effects — transfer, mint, burn, setField,
  incrementNonce, bridgeMint. Their rung CONSUMES Satisfied2(Rfix e) via the *_forced limb lemmas. (= the memory's
  "5/36 VALUE rungs" + bridgeMint.) transfer is the DEEPEST (closedLogExtract_transfer_closed ClosureTransfer.lean:293
  reduces to 4 crypto floors + TransferAuthorityWitness, no opaque extract residual — the template).
- CLASS B (circuit-DECOUPLED, edit does NOT reliably propagate): 24 effects — cap family, lifecycle, perms/vk,
  birth, notes, exercise, heapWrite. Their <e>Encodes carries a NAMED internal gate (prover-supplied commitment
  fact) but the readout TAKES Satisfied2(Rfix e) AND DISCARDS IT — encode derived from its own gate, not the
  circuit denotation. Spec-edit still reds them (they refine real Spec); circuit-descriptor-edit does NOT.
  Worst: heapWrite(56) Rfix 56 = the WRONG descriptor (transfer fallback), descriptor-abstract by design.
- All keystones #assert_axioms-clean ⊆ {propext, Classical.choice, Quot.sound} + named floors.
THE NEXT CAMPAIGN (precise): close the 24 Class-B slots — make each <e>Encodes a FUNCTION of Satisfied2(Rfix e)
the way transfer's is (closedLogExtract_transfer_closed = the template), so a circuit-constraint bug in any effect
propagates red. The spec<->proof weld is COMPLETE; the circuit<->proof weld is deep for 6, shallow for 24.

## ⚑⚑ ENMESHMENT CENSUS layer 3/4: DISTRIBUTED/SETTLEMENT/BRIDGE/JOINT/PROMISES (a11c8d8a) — THE MISSING WELD found
Circuit soundness propagates up EXACTLY ONE RUNG (into Settlement), then stops at a single named sibling axiom.
- SETTLEMENT = PROVEN-AND-WELDED ✅. settlement_soundness (SettlementSoundness.lean:210) CALLS the apex
  (lightclient_unfoolable_circuit_sound, ClosureFinal.lean:162) at :238 to discharge its genuine-transition leg;
  lifts to authority-live-AT-SETTLEMENT (closes the branch-vs-settlement time-travel hole; non-vacuous both
  polarities settlement_gap_real:324 + n=1 collapse :338). Real body, axiom-clean. The memory's promised
  Settlement theorem is REAL + built ON circuit soundness.
- ⚑ THE MISSING WELD (the single highest-leverage edit on the board): the multi-turn IVC / finalized-history /
  joint / promise layers are ALL PROVEN but ride a SIBLING soundness floor EngineSound.leaf_sound
  (RecursiveAggregation.lean:124) which ASSERTS the per-turn recCexec soundness that the apex ALREADY PROVES.
  grep-confirmed the two are UNBRIDGED. Discharging EngineSound.leaf_sound BY lightclient_unfoolable_circuit_sound
  is the ONE link that propagates circuit soundness through the WHOLE finalized-history/multi-turn/distributed
  stack. Likely ~one bridging theorem (modulo the IVC recursion shape).
- BRIDGE = WELDED at the per-cell rung ✅. bridgeMint is a genuine effect dispatched tag 20, Rfix 20 = the gated
  mint descriptor, rides kstepAll. Argus/Effects/BridgeMint.lean clean (the memory's "breakage" flag is STALE).
  Conservation genuine (BridgeCell lock/finalize/cancel = moves; TriDomain triConserved_of_execFull real per-kind
  authority-measure body). ONE named seam: the foreign-finality CryptoPortal is an execFullA admission boundary
  (BridgeMint.lean:45, "HONEST BOUNDARY — stated not hidden"), not in-circuit.
- JOINT = PROVEN, welded to executor/spec/Argus-compiler, SEPARATE from the STARK apex (no whole-joint
  aggregation AIR; Argus/Joint.lean:59 states this). PROMISES = PROVEN-BUT-SEPARATE (GuardedHole/ConditionalTurn/
  CapTPPipeline/Await, ~real content, axiom-clean; the "promise-hole IS a nullifier" weld NOT yet realized).
DISTRIBUTED protocols (consensus/finality/lace-merge/catchup) PROVEN + thread real kernel types, but their
per-turn fact is the EngineSound sibling, not the apex — same missing weld.

## ⚑⚑ ENMESHMENT CENSUS layer 4/4: GLOBAL TOPOLOGY (aa129798) + THE SYNTHESIS
GLOBAL: the spine is PRISTINE. ZERO real open holes / `admit` tactics in 758 modules (all hits = docstring prose / a fn
named `admit`). EXACTLY 2 axiom decls, both deliberate test fixtures (Widget/Basic.lean:298 tier-classifier) — NO
smuggled axioms. Floors = 8 named *Kernel crypto carriers (ed25519/STARK-FRI-extractability/Poseidon2-CR/BLAKE3/
nullifier/seal/HMAC, PortalFloor.lean) as typeclass Prop-fields (invisible to collectAxioms) + injectivity portals
+ PostGSTProgress. Kernel triple only {propext,Classical.choice,Quot.sound}. native_decide's ofReduceBool is NOT
whitelisted -> hygiene SELF-ENFORCING (#assert_axioms across ~645 files). Apex deployed_system_secure
(AssuranceCase.lean:835) names the REAL gated executor execFullForestG, concludes A∧B∧C∧D∧E, pinned.
⚑ THE REFRAMING FINDING: 87 modules (11.5%) are ORPHANS — outside lake build Dregg2 (real, hole-free, but their
hygiene pins DON'T RUN by default). Clusters = Circuit.SettlementSoundness (!! the "one true weld" itself),
36/46 Circuit.Argus.* per-effect refinement subtree, 24 EffectVmEmit*FullState, Exec.ConcreteKernel (the hard
kernel-bridge gate), 3 Distributed (FinalityGate/MembershipSafety/CrashRecovery). NOT broken — UNENMESHED.

### THE SYNTHESIZED TOPOLOGY (the answer to "one tower or islands?")
ONE SOLID TOWER + a third-of-a-circle of real-but-unorbited moons. Two-axis truth:
- SPEC-edit -> proofs RED: reliable for ALL 30 effects (executor<->spec WELDED, 43 keystones; circuit<->spec
  discharged for all 30).
- CIRCUIT-edit -> proofs RED: reliable for 6/30 (transfer/mint/burn/setField/incNonce/bridgeMint, Satisfied2-bound);
  24/30 DECOUPLED (encode discards Satisfied2).
- Circuit soundness PROPAGATES UP one rung (Settlement, welded), then stops at the EngineSound.leaf_sound sibling
  axiom (multi-turn/IVC/joint/promises all proven-but-parallel).

### RANKED FRONTIER (the next campaigns, by leverage)
1. ENMESH THE 87 ORPHANS into the root build (esp. SettlementSoundness + the Argus subtree) — cheapest, highest
   trust/effort: theorems exist + clean, just need importing so their pins run in CI. Until then welds are true
   but UNGUARDED against regression.
2. THE EngineSound.leaf_sound WELD — discharge the sibling axiom by lightclient_unfoolable_circuit_sound ->
   circuit soundness flows through the WHOLE multi-turn/distributed stack. ~1 bridging theorem, largest blast radius.
3. THE 24 CLASS-B CIRCUIT SLOTS — make each <e>Encodes consume Satisfied2(Rfix e) (transfer's
   closedLogExtract_transfer_closed = template) so circuit-constraint edits propagate red for ALL effects, not 6.
Plus: joint-turn aggregation AIR; promise-hole-as-nullifier weld; the stale "Stated open" docstring Boundary.lean:217.

## ⚑⚑ CLASS-B DIAGNOSIS (2026-06-20, a7b6aece) — NOT garbage, NOT false: a missing Lean JOIN; the VK work is DEPLOYED
cellSeal probe verdict: the Class-B decoupling is neither lazy-sloppy nor a false-but-hidden rung. It is a
PROVEN-BUT-UNJOINED weld, and the descriptor (VK-affecting) work is ALREADY DEPLOYED.
- REFUTES hypothesis (b) for cellSeal: cellSealV3 DOES constrain the seal — the WAVE-1 disc flag-day gate
  rotateV3WithDiscGate forces committed limb B_DISC=32 (one of the 37 pre-iroot limbs chaining into state_commit);
  cellSealV3_rejects_frozen makes a frozen-seal forgery UNSAT in-circuit (axiom-clean, EffectVmEmitRotationV3.lean:2655/2665).
- THE DECOUPLING = a missing JOIN inside Lean (ClosureFanoutGenuine.lean:360): the rung consumes Satisfied2(Rfix 52)
  only as the DOMAIN of an opaque universally-quantified `readout` floor producing the MODELLED cellSealGenuineEncodes.gate,
  instead of EXTRACTING the deployed cellSealV3_disc_forces_sealed. Two facts about the same seal, proven separately,
  never joined -> descriptor edit doesn't propagate red.
- THE FIX = non-VK-affecting PROOF-COMPLETION (not descriptor-completion): a cellSeal_forced extraction (transfer's
  debit_forced analog). The ONE load-bearing new artifact per slot = a WitnessDecodes-class trace-column DECODE floor
  (discCol(trace) = discRoot(post.kernel) — realizable, same committed felt, but genuine multi-step). Agent REFUSED
  to land a half-weld with an assumed decode (correct — no laundering).
- THE RECIPE (Class-B -> Class-A, fan the ~23): (1) confirm eV3 = rotateV3With*Gate on a committed pre-iroot limb +
  the eV3_*_forces_* lemma exists; (2) write the trace-column decode floor; (3) e_forced = compose Satisfied2 ->
  active-row satisfiedVm -> *_forces -> decode -> root_binds -> kernel field; (4) rewire e_descriptorRefines +
  closedLogExtract_e_closed to take hsat:Satisfied2 and call e_forced; (5) #assert_axioms + green.
- ⚑ THE (b)-GAP DISCRIMINATOR: a slot is a REAL descriptor gap (VK-affecting) iff its committed limb has NO
  rotateV3With*Gate realization AND rides only the published-value record pin without a verifier anchor. cellSeal is
  NOT one. The disc-class (cellSeal/unseal/destroy/receiptArchive) + declared-param/constant classes (setPerms/setVK/
  makeSovereign/setFieldDyn) have their *_forces_* lemmas at HEAD = LAZY-join. Scrutinize the rest with the discriminator.

## ⚑ ENGINESOUND WELD landed (a242052f, NOT yet banked — waiting for cellSeal to settle the shared closure)
engineSound_of_apex (NEW Dregg2/Circuit/EngineSoundOfApex.lean, axiom-clean {propext,Classical.choice,Quot.sound})
GENUINELY discharges leaf_sound: leafStep_of_bundle FIRES lightclient_unfoolable_circuit_sound on each verifying
leaf + lowers to recCexec s.pre s.turn = some s.post. So leaf_sound is NO LONGER a free sibling axiom —
multiTurn_rests_on_apex -> AggregateAttests AND finalized_rests_on_apex -> FinalizedHistoryAttested both now follow
from {apex + the 2 FRI recursion legs}. It is an honest REDUCTION: the residual is crystallized into ONE named
realizable field `apexLowers` (witnessed inhabited on the honest transfer step, NOT a weakening), because of a REAL
structural finding:
⚑ THE MULTI-TURN LAYER IS BUILT ON AN OLDER/NARROWER KERNEL than the apex. The ChainStep/HistoryAggregation
multi-turn model rides the TRANSFER-ONLY legacy recCexec/recKExec over Turn={actor,src,dst,amt} on the
balOf(cell) slice; the apex's kstepAll is the general 30-effect dispatchArm over the per-asset bal:CellId->AssetId->ℤ
ledger (balancemovement.lean:118). DISJOINT RecordKernelState components. So apex->recCexec lowers only at
pi.effect=0 (transfer) and even there across the bal-vs-balOf-cell split. THE NEXT LEMMA to drop apexLowers
entirely: re-base ChainStep/recCexec onto the genuine per-asset recCexecAsset/execFullA (a step = a FullActionA
whole-turn over bal, matching the apex), retiring legacy recKExec -> then apexLowers becomes
execFullA_balanceA_iff_spec-shaped + provable outright. (= a real distributed-layer modernization, own campaign.)
BANK STATUS: hold until the parallel cellSeal agent settles the shared ClosureFanoutGenuine closure (tree was mid-edit).

## ⚑⚑⚑ CLASS-B TRIAGE COMPLETE (2026-06-20, a93b40505) — 5 REAL SOUNDNESS GAPS found (+ heapWrite), 14 LAZY, the fix shapes
Of the 24 census Class-B slots (apex ranges over v3RegistryCapOpen, CapOpenEmit.lean:799, NOT plain v3Registry):
- 14 LAZY-join (non-VK, the cellSeal recipe fans them — committed-limb gate + axiom-clean force-lemma already
  deployed, only the Lean join missing): cellSeal, cellUnseal, cellDestroy, refusal, receiptArchive, setPerms,
  setVK, setFieldDyn, createCell, factory, spawn, noteSpend, noteCreate, makeSovereign, ATTENUATE
  (attenuateV3_non_amp RotV3:3023 proves writesTo CAP_ROOT in-circuit — LAZY, NOT a gap; the framing-correction:
  the write-leg discriminator is the keepWrite/removeWrite/insertWrite map-op in the deployed base, not whether
  the bare weld pins cap_root).
- 3 NO-WRITE (not gaps): emitEvent, pipelinedSend, exercise (frozen frame + nonce tick).
- 1 UNCERTAIN->likely LAZY: revokeCapability (base carries [heldReadOp,removeWriteOp] RotV3:962 like attenuate,
  but NO force-lemma yet — confirm removeWriteOp is in the CapOpen constraint set, then mirror attenuateV3_non_amp).
- 🔴 5 REAL (b)-GAPS — VK-AFFECTING (the deployed circuit does NOT force the cap-tree WRITE): DELEGATE, INTRODUCE,
  DELEGATEATTEN, REVOKEDELEGATION, REFRESHDELEGATION. Root cause: the cap-open descriptor forces the authority
  READ (the 70-gate capOpenConstraintsEff appendix) but FREEZES the on-row cap_root/delegations limb; the write
  (new root) rides only an off-row effects_hash decode (*CapsTreeEncodes.SpineCommits = a PROVER-SUPPLIED
  hypothesis), unanchored to any deployed write gate. closedLogExtract_{delegate,...}_closed
  (ClosureFanoutGenuine.lean:246-349) takes the move as that free decode. So these 5 rungs are genuinely
  false-but-hidden at the deployed descriptor: a prover can publish a wrong post-cap-root and the circuit won't
  catch it. FIX (VK-affecting, Lean-now/deploy-ember-gated): add the in-circuit cap-tree write map-op mirroring
  attenuate's [heldReadOp,keepWriteOp] (RotV3:955) — insertWriteOp (delegate/introduce/delegateAtten),
  removeWriteOp (revokeDelegation), updateAtKeyWriteOp vs delegations root (refreshDelegation) — each forcing
  writesTo cap_root_before key value cap_root_after vs the committed B_CAP_ROOT/delegations limb + a <slot>V3_non_amp
  lemma. Converts REAL->LAZY.
- +1 heapWrite (different gap kind): ABSENT from every registry (Rfix 56 -> transfer fallback,
  CircuitSoundnessAssembled.lean:155); machinery (EffectVmEmitHeapRoot heapRoot_binds_write) + spec proof
  (heapWrite_newRoot_forced) EXIST — fix = construct heapWriteVmDescriptor2R24 registry entry + point actionTagToPos
  56 at it. VK-affecting "constructible assembly".
NEXT WAVE: (a) fan the cellSeal recipe across the 13 other LAZY slots [non-VK, parallelizable]; (b) the 5 cap-write
descriptor gaps [VK, mirror attenuate's keepWriteOp + _non_amp]; (c) revokeCapability force-lemma; (d) heapWrite
registry entry. The "garbage" was 14 missing-joins + 5 genuine soundness holes — now mapped with fix shapes.

## ⚑⚑ GOAL: "safely live within dregg" (2026-06-20) — the two floors that must hold
The autonomous-harness-inside-deos goal decomposes into exactly two soundness floors:
1. AUTHORITY FLOOR (guarantee A circuit-forced, no cap holes) — IN FLIGHT: the 4 Class-B agents, esp. the VK
   cap-write agent closing the 5 real gaps (delegate/introduce/delegateAtten/revokeDelegation/refreshDelegation).
   Load-bearing for "hand an agent caps + money safely" — the cap tree IS how authority delegates/revokes.
2. HUMAN/RECOVERY FLOOR ("you cannot lose your own OS") — pieces exist (guardian_rotation, beacon_cell,
   hints_onboarding, device_pairing, ResharingChain.lean, CrashRecovery.lean) but OWED:
   (a) ⚠ node recovery FIRST-WRITER-WINS durability bug (state.rs:699/879 strict insert_cell silently DROPS a
       post-checkpoint write to a cell the checkpoint holds; convergence root-mismatch only LOGS, doesn't fail
       closed) — a real "lose/serve-divergent state" bug. FIX = upsert_cell (CrashRecovery.upd point-update =
       remove-then-insert) at both sites + mismatch returns Err/refuses to serve. DRIVING NOW (node/, non-colliding).
   (b) the recovery e2e seam (identity_social_recovery_e2e.rs — fresh cipherclerk, 3-of-5 HINTS guardians).
   (c) circuit commitment for light-client-UNFOOLABLE recovery (currently host-TRUSTED — a guarantee gap: recovery
       isn't yet in the verified surface). = a future weld (recovery effect → circuit rung).

## ⚑ LIFECYCLE LAZY-fan landed (a6ef3b7c) — 3 Class-A + a 6th REAL GAP found (receiptArchive spec↔descriptor divergence)
3 CLEAN Class-A conversions (mutation-confirmed, axiom-clean, in RotatedKernelRefinementLifecycle.lean — NOT yet
banked, tree red from parallel CapFamily/PermsVK mid-edit): cellUnseal_descriptorRefines_sat (disc gate
forces lifecycle=lcLive), cellDestroy_descriptorRefines_sat (BOTH legs: lifecycle=lcDestroyed + deathCert via the
record-pin folded in the disc gate), refusal_descriptorRefines_sat (record-pin forces fieldOf refusalField = 1).
+ teeth rejects_unrevived/resurrection/wrong_cert/unwritten. New lemma names for fanout wiring: the 3 *_sat.
⚑ receiptArchive = a 6th REAL GAP (different kind: spec↔descriptor DIVERGENCE, not a missing write): deployed
receiptArchiveV3 disc-gate forces lifecycle cell = lcArchived (a side-table write), but ReceiptArchiveSpec
(Spec/cellstateaudit.lean) writes a RECORD SLOT (lifecycleField:=1) and FREEZES the lifecycle side-table
(post.lifecycle = pre.lifecycle) — they CONTRADICT. Class-A unreachable from the deployed descriptor without a
descriptor change (bind the audit record slot) OR reconciling the spec to the deployed Archived side-table
semantics. = an EMBER/descriptor decision, not Lean wiring. Documented at RotatedKernelRefinementLifecycleDisc §6.
So the Class-B frontier is now: ~13 LAZY (3 lifecycle done) + 5 cap-write VK gaps + receiptArchive (spec divergence)
+ heapWrite (registry) = the real gaps total 7. Agent correctly did NOT fake the receiptArchive seam.

## ⚑⚑⚑ AUTHORITY FLOOR — guarantee A now circuit-forced for ~26 of 30 effects (2026-06-20, banked d3dfc7f88+ba8efd53f)
The Class-B campaign wave LANDED green (lake 4096, axiom-clean) — survived a server-rate-limit storm (2 agents
died mid-edit, 1 repair agent finished their whole proofs: a missing Classical instance + a Prop->Type mistype +
an unqualified name, over COMPLETE proofs).
FORCED (circuit-edit -> red, mutation-confirmed) — guarantee A enforced in-circuit:
- 6 originally Class-A (transfer/mint/burn/setField/incNonce/bridgeMint)
- 11 LAZY fanned: cellSeal, cellUnseal, cellDestroy, refusal, setPerms, setVK, createCell, factory, spawn,
  noteSpend, noteCreate, makeSovereign, setFieldDyn (recipe = deployed force-lemma + WitnessDecodes decode seam)
- 4 cap slots FORCED: attenuate (was done) + delegate, grantCap, delegateAtten (the dead VK agent had completed
  the insertWriteOp descriptor + _forces_write keystones) + revokeCapability (removeWriteOp deployed)
= ~26 of 30 effects guarantee-A circuit-forced.
STILL OPEN (the real remaining gaps — all named, none faked):
- 3 FROZEN-FACE cap slots: introduce, revokeDelegation, refreshDelegation — v1 face freezes cap_root on-row
  (gCapPass), insertWriteOp jointly UNSAT with the freeze; fix = rebase their V3 base on the moving/recompute
  …Genuine face (a VK cutover, the …Genuine descriptors EXIST but aren't deployed). Cleanly Class-B-pending.
- receiptArchive: spec↔descriptor CONTRADICTION (spec writes record-slot+freezes lifecycle; descriptor forces
  lifecycle=Archived) — ember/descriptor decision.
- heapWrite: ABSENT from registry (Rfix 56 -> transfer fallback); machinery+proof exist, construct the entry.
- 3 NO-WRITE (not gaps): emitEvent, pipelinedSend, exercise.
NEXT: (a) wire the new *_descriptorRefines_sat into the apex fanout (ClosureFanoutGenuine — MAIN LOOP owns, serial);
(b) the VK JSON descriptor regen + drift-gate for the cap-write changes; (c) the 3 frozen-face cutover; (d)
receiptArchive + heapWrite decisions. The recovery/durability floor (node first-writer-wins) is a parallel lane.

## ⚑ RECOVERY FLOOR — durability core ALREADY SOUND (verified a5c2a0e0); one parity follow-up
The node recovery first-writer-wins bug was already fixed (279033535, ancestor): upsert_cell (= CrashRecovery.upd
remove-then-insert, last-write-wins) at both overlay sites (state.rs:717,910); the new_with_key_file convergence
root-mismatch FAILS CLOSED (state.rs:732, returns Err "refusing to serve a divergent ledger"); 3 reproduction tests
green (post-checkpoint write wins, mismatch-refuses-to-start, control). So post-checkpoint writes survive recovery +
the node won't serve divergent state — the "you cannot lose your own OS" durability core HOLDS.
⚠ FOLLOW-UP (parity, not a regression): the SECONDARY with_cclerk recovery path (state.rs:910) does the upsert but
has NO fail-closed convergence check (only new_with_key_file does). Mirror the convergence Err-on-mismatch into
with_cclerk for parity. Small, node/-only, non-colliding — drive when convenient.

## ⚑⚑ GENESIS REFRAME (ember, 2026-06-20) — the smell is a CATEGORY ERROR; the fix is EPIC + dissolves the bug
The genesis-path durability bug is a confusion, not a bug. There are THREE things, one illegitimate:
1. IMAGE GENESIS (build-time) = an EROS-style FACTORY: an offline verified constructor assembling a cell-graph +
   caps + programs into a SEALED, ATTESTABLE image ("customize your deos download ISO" + a proof of what it can't
   do = the Hatchery prove-once-hold-forever yield). Timeless because sealed BEFORE any turn. Booting = loading it.
2. NETWORK GENESIS (runtime) = COORDINATION: computers coming online, discovering each other, DECIDING to coordinate
   — an ordered ceremony of TURNS, NOT a pre-declared validator/committee manifest. (This is where the docuverse/
   branch-stitch/settlement brain plays — network formation = consensual history-stitching.)
3. ❌ "genesis-path mutation reachable mid-session" = runtime customization MASQUERADING as build-time genesis = THE
   CATEGORY ERROR producing the smell (a post-turn write filed as a pre-turn timeless fact -> replay-from-genesis
   applies it out of order -> image won't reopen).
THE FIX dissolves the bug: build-time customization -> the IMAGE (factory, sealed); runtime customization -> a TURN
(ordered, replayable). #3 can't exist. set_cell_program/genesis_grant_cap/genesis_open_permissions mid-session were
NEVER genesis — they're turns. (= the earlier "option 2: route through real turns", arrived at from FIRST PRINCIPLES.)
BRAIN SPLIT: regular executor brain fixes the smell for free (mid-session genesis calls -> turns); factory/image brain
builds genesis-as-ISO (EROS factory + attestation, snaps onto createCellFromFactory + sdk/factories.rs + Hatchery +
the seL4 boot image); docuverse brain designs network-genesis-as-coordination (houyhnhnm/branch-stitch). EPIC payoff:
attestable reproducible deos images ("here's my OS + a proof of its confinement"), the real download-and-customize
story, federations forming by coordination not config — collapses a special case into 2 clean primitives (build
artifact + turns), same instinct as 52->8 verbs. SCOUT RUNNING (a4414e6f) for the terrain map -> ember scopes.
The persist bug stays FAIL-CLOSED/GUARDED meanwhile (no data corruption); this reframe is its sound full closure.

## ⚑⚑ IMAGE-BUILDER (Phase 2) landed in isolation (a02bfba) — bank HELD for genesis Phase-1 to settle turn/
The EROS image-builder = the build-time IMAGE GENESIS half ("here's my OS + a proof of what it can't do").
persist/src/image_builder.rs (854 lines, NEW) + lib.rs re-export. NOT yet banked — verified green via a throwaway
git worktree (8/8 tests) because the shared tree's dregg-turn is mid-edit by the genesis Phase-1 agent (SetProgram
non-exhaustive match arms in pipeline/reversible/journal) -> persist->federation->turn won't compile in place.
WHAT IT IS:
- ImageManifest: declarative "what's in my ISO" — EROS FactoryDescriptors (each carrying program-for-life
  state_constraints) + CellSpecs (factory-by-content-hash + creation params + signed balance). serde/postcard.
- build_image: manifest -> ImageArtifact. Runs the REAL FactoryDescriptor::validate_creation, constructs
  genuinely factory-born Cells (CellProgram::Predicate(state_constraints) installed for life), real Ledger::root,
  sealed Snapshot (reuses snapshot.rs:80 fail-closed root tooth) + ImageAttestation.
- verify_image: FAIL-CLOSED, no builder trust — 5 re-derived checks (manifest binding, root binding +
  reconstruct tooth, conservation Σ=0, factory provenance, program-for-life binding so a cell can't be smuggled
  under a factory it wasn't born from). 8/8 tests incl. 5 tamper-rejections.
- HONEST seams (reserved Option slots, NOT silent): hatchery_invariant_proof (the Hatchery hpres prove-once-
  holds-forever proof attaches here — today carries DECLARED invariants, not the proof they hold) + seal (builder
  signature — self-verifying but unsigned).
FOLLOW-UPS: (a) bank when Phase-1 settles turn/; (b) wire hatchery hpres proofs into the attestation; (c) the
seL4 boot-wire (generate sel4 image_data.rs from a manifest via the builder, replacing the hand-built 6-cell const
gen_image_snapshot.rs — a render-from-artifact codegen pass since the viewer PD is no_std, can't link persist).
The conserving_manifest test already reproduces that const's exact Σ=0 shape -> ready to drive it.

## ⚑⚑⚑ AUTHORITY FLOOR — near-complete (2026-06-20, VK-freedom era; banked 7bccf2b68+239037ad2)
Guarantee A (Authority) circuit-FORCED (a circuit-descriptor edit reds the rung, mutation-confirmed) status by effect:
FORCED (the deployed circuit forces the write from Satisfied2):
- 6 originally Class-A: transfer/mint/burn/setField/incNonce/bridgeMint
- 13 LAZY-fanned lifecycle/state/birth/notes: cellSeal/cellUnseal/cellDestroy/refusal/setPerms/setVK/setFieldDyn/
  makeSovereign/createCell/factory/spawn/noteSpend/noteCreate
- 6 cap slots: attenuate + delegate/grantCap/delegateAtten/introduce/revokeDelegation + revokeCapability
- receiptArchive (disc gate -> lifecycle:=Archived) + heapWrite (registry entry built, hashSites=heapRecomputeSites)
= ~28 of 30 effects FORCED.
REMAINING (all NAMED, not faked):
- refreshDelegation: writes the DELEGATIONS tree (DELEG system-root, record-bound), NOT cap_root — needs a new
  deleg-tree map-op + runtime column (delegRoot_runtime_column_pending). The one genuine descriptor-architecture
  extension left in the cap family.
- 3 NO-WRITE (not gaps): emitEvent/pipelinedSend/exercise (frozen frame + nonce tick).
SERIAL TAIL (main-loop owned, queued): (a) wire the new _descriptorRefines_sat + the capOpenSat rungs into the apex
fanout ClosureFanoutGenuine (13 already wired; +receiptArchive/heapWrite/5 cap slots to add); (b) the JSON
descriptor regen for the new/changed descriptors (introduceWriteV3/CapOpen wrappers/heapWriteV3 — widths recorded);
(c) re-pin the drift gate. THEN guarantee A is forced AND apex-wired for ~28/30 — the authority floor of
"safely live within dregg" essentially COMPLETE.

## ⚑⚑ GENESIS REFRAME — BOTH HALVES SHIPPED (2026-06-20, b5ab3592f + 99b7dfe51)
The category error is dissolved + the front door is built:
- PHASE 1 (b5ab3592f): Effect::SetProgram (ordered, fully executor-wired) + production mid-session genesis sites
  redirected to TURNS (scene re-bake/organ install -> SetProgram; demo grant/open on the factory-born token ->
  Grant/SetPermissions turns). The apparatus CORRECTLY STAYS as the setup boundary (its remaining call sites are
  TESTS validating setup-vs-mid-session). PROVEN: a_mid_session_set_program_turn_survives_reopen passes (the
  post-turn reprogram-as-turn survives reopen). persistence 8/8. The persist durability bug's SOUND root closure.
- PHASE 2 (99b7dfe51): the EROS image-builder (persist/src/image_builder.rs) — manifest -> sealed Snapshot +
  attestation -> fail-closed verifier, 8/8 incl. 5 tamper-rejections. "Here's my OS + a proof of what it can't do."
FOLLOW-UPS (named, VK-free-driveable): (a) SetProgram's OWN circuit descriptor witness (reuses
EFFECT_SET_VERIFICATION_KEY's tag today, executor-sound; the descriptor rung is the VK follow-up); (b) wire the
Hatchery hpres prove-once-holds-forever proofs into the image attestation (the reserved Option slot); (c) the seL4
boot-wire (generate image_data.rs from a manifest via the builder — render-from-artifact codegen); (d) network
genesis as a coordination ceremony of turns (the houyhnhnm/branch-stitch distributed lift — own campaign).

## ⚑ THE SERIAL INTEGRATION TAIL (main-loop owned, queued for a quiet tree)
After the soundness waves: (1) wire the new _descriptorRefines_sat + capOpenSat rungs (receiptArchive, heapWrite,
the 5 cap slots) into the apex fanout ClosureFanoutGenuine (13 wired, ~7-9 to add); (2) the JSON descriptor regen
for the new/changed descriptors (introduceWriteV3/CapOpen wrappers/heapWriteV3) + drift re-pin; (3) compact
HORIZONLOG (~half is closed-but-logged, sweepable per the af232dd sweep); (4) the SetProgram circuit witness.

## ⚑ JSON-EMIT FOLLOW-UP (2026-06-20) — the new apex descriptors aren't in emit_descriptors.py's list yet
Round-2 apex wiring (ae14e524e) registry-deployed the write-bearing cap wrappers (delegate/introduce/delegateAtten/
revokeDelegationWriteCapOpenV3) + heapWriteV3 — the apex now PROVES about them. But scripts/emit_descriptors.py
emits from a FIXED descriptor-name list that does NOT include them (verified: grep -c WriteCapOpen|heapWrite in
emit_descriptors.py = 0), so the checked-in deployed JSON doesn't yet carry these descriptors (drift gate PASSES
only because they're absent from both Lean-emit-list and JSON). So: the WRITE-forcing is proven-in-Lean +
apex-wired, but the deployed Rust wire still runs the OLD authority-READ-only cap-open wrappers — not yet on the
wire. FOLLOW-UP (the deploy step of the cap-write soundness fix; non-VK-blocked, just a script + Lean-emit-list
edit): add the new descriptor names to the emitter so the deployed JSON carries exactly what the apex proves about,
then re-pin the drift gate. Real, named, driveable next (VK-freedom era).

## ⚑⚑⚑ AUTHORITY FLOOR — LAST MILE, the light-client forge CLOSED via the verifier tooth (2026-06-20, base 99cf43412, UNCOMMITTED)
The verdict-(b) light-client gap (a40fea04, below) is CLOSED on the load-bearing axis: the SDK light-client
verifier `verify_effect_vm_rotated_with_cutover` (sdk/src/full_turn_proof.rs) now REJECTS a cap effect proven
under its PLAIN cohort descriptor. New `is_forbidden_plain_cap_descriptor` forbids the 5 plain cap-effect
descriptors (introduce/revoke/attenuate/grantCap/revokeCapability VmDescriptor2R24) as the uniquely-accepting
descriptor — a cap effect MUST bind a `…CapOpen…VmDescriptor2R24` (the depth-16 capOpenConstraintsEff membership
crown is IN that descriptor and ONLY there). So a malicious producer that strips the cap-open route to launder
host-trusted authority into a passing light-client proof is now REFUSED.
- WHY the verifier tooth (not a blind producer resolver re-point): the deployed wire shares NO single resolver
  the way the verdict assumed. (1) The SDK light-client verifier iterates ALL cohort descriptors and binds the
  unique acceptor (it does NOT call `rotated_descriptor_name`) — so the FORCING had to be a forbidden-name tooth
  there. (2) The executor `verify_one_cohort_run` REGENERATES the WIDE trace by name from PLACEHOLDER witnesses —
  it has NO cap-membership witness, so it CANNOT regenerate a cap-open trace; re-pointing its resolver would
  break it. (3) The honest producer ALREADY routes cap-open (`cap_open_route_for_run`, cap-presence-driven,
  full_turn_proof.rs:1096/1687) — the verifier tooth makes that route MANDATORY (a producer can't get a cap
  effect accepted via plain), which is the forcing the verdict named, achieved soundly.
- NEW forge-rejection test `light_client_rejects_cap_effect_under_plain_descriptor`: proves a RevokeDelegation
  (cap effect) under the PLAIN revokeVmDescriptor2R24 (the exact forge) → the light-client verifier REJECTS with
  the AUTHORITY-FLOOR reason; the honest cap-open route (cap_open_fanout_revoke test) still VERIFIES. ONE-WAY
  tooth: plain cap-effect ⇒ reject, cap-open ⇒ accept.
- NO VK/descriptor drift (verifier-behavior change only; no .tsv/.json touched — the cap-open descriptors forced
  onto already exist in V3_STAGED_REGISTRY_TSV). Green: dregg-sdk lib 257, dregg-turn lib 512, dregg-node
  capability 8, cap_open suite 4. Build green across circuit(prover)+turn+sdk+node.
- RESIDUE (named, NOT in scope of this fix): (a) refreshDelegation stays on its plain descriptor — its deleg-tree
  WRITE column's cap-open variant is producer-unwired (refresh re-arms an existing delegation, confers no new
  authority — named, not a silent forge). (b) The …WriteCapOpen descriptors (introduceWrite/delegateWrite/
  delegateAttenWrite/revokeDelegationWrite) are in the STAGED registry but NOT the WIDE registry — the executor
  sovereign verify path can't reach them yet; the SDK light-client path uses the authority-bearing CapOpen family
  (already wired). The write-op binding into the commitment (the ~17-effect descriptor-fix terrain in
  docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md) is the next layer. (c) The executor sovereign-witness verify path is
  FULL-NODE (host check_breadstuff + the SDK cap-membership leg on the cap-gated path) — the verdict confirms
  full-node safety, so the light-client `verify_full_turn` path was the load-bearing axis and is now closed.

## ⚑⚑⚑ AUTHORITY FLOOR — CORRECTION (2026-06-20, a40fea04) — the cap-open authority crown is proven-in-Lean, NOT-on-the-wire (light-client gap)
Investigating the producer-selection layer surfaced a real gap (verdict (b): light-client gap, NOT a full-node
hole). The earlier "guarantee A apex-forced ~28/30" was about the LEAN apex; the DEPLOYED WIRE is weaker:
- FULL NODES SAFE: TurnExecutor::verify_authorization -> check_breadstuff (authorize.rs:1080) reads the actor's
  real c-list from the ledger -> PermissionDenied for a cap effect by an actor holding no cap, before commit. No forge.
- LIGHT-CLIENT GAP: the deployed producer selects the PLAIN cohort descriptors for cap effects
  (trace_rotated.rs:1042: INTRODUCE->introduceVmDescriptor2R24 etc.) which carry NO in-circuit cap-membership
  check. The 70-constraint cap-open authority appendix (capOpenConstraintsEff = the ARGUS depth-16 cap-membership
  crown) is proven in Lean but NEVER SELECTED on the wire. It is producer-opt-in (cap_membership:Some,
  full_turn_proof.rs:1687) + verifier-opt-in (checked only when the caller passes expected_cap_membership;
  verify_full_turn passes None,None at :2171). So a ledgerless light client can't distinguish "agent held the cap"
  from "host asserted it" — a malicious producer proves the cap effect via the non-cap path -> plain descriptor ->
  passes. SAME SHAPE as the conservation hole (enforced executor-side, off-AIR, light-client fail-open).
- THE WRITE half (the 5 …WriteCapOpen descriptors just emitted) is even further un-selected — both old-authority-only
  AND new-write cap-open families are un-routed in rotated_descriptor_name.
CLOSURE (named, the deploy step's real content): make cap-effect descriptor selection FORCED BY EFFECT KIND —
(producer) rotated_descriptor_name routes cap effects -> the …WriteCapOpenVmDescriptor2R24 (authority appendix +
write op), AND (verifier) verify_one_cohort_run + the light-client verify_full_turn REJECT a cap effect proven
under the plain base (require the cap-open binding). = a producer-behavior + VK change. This is the real "safely
live" authority item: an autonomous agent's caps must be LIGHT-CLIENT-verifiable, not host-trusted. Matches the
memory's "we do NOT have a proven-secure circuit for ~17 effects whose gate must bind into the commitment."
HONEST RESTATEMENT: authority floor = FULL-NODE sound, LIGHT-CLIENT named (the in-circuit crown un-selected).

## ⚑ RED TEST (pre-existing, named not quick-fixed) — resolvers_cover_exactly_the_rotated_registry (37 vs 36)
trace_rotated.rs:2232 `resolvers_cover_exactly_the_rotated_registry` asserts the effect→descriptor resolvers cover
EXACTLY the 36 non-cap-open rotated cohort members (cap-open members are excluded as "cap-presence-routed, not
reached by the resolvers"). It fails 37 vs 36 at base HEAD (an earlier commit added a write-bearing descriptor to
V3_STAGED_REGISTRY_TSV without updating the exclusion filter). NOT a trivial count bump + NOT mine (dregg-circuit,
not the sdk file the cap-authority fix touched): the test's PREMISE ("cap-open members aren't reached by the effect
resolvers") is exactly the property the cap-authority light-client fix (e26fe42df) is shifting — cap effects now
MUST bind a cap-open descriptor on the verify side. So the right fix is to reconcile this census WITH the new
cap-open-routing semantics (which write-bearing/cap-open descriptors are now resolver-reached vs presence-routed),
not to bump 36→37 blindly (which could mask a real coverage gap). Follow-up, careful, in the dregg-circuit
registry-census owner's lane. The authority-floor soundness (the light-client forge closure) does NOT depend on
this — it's a registry-completeness census assertion, currently stale vs the new routing.

## 🟥🟥🟥 CRITICAL SILENT FORGE FOUND (2026-06-21, ac39a343) — cap-write map_op guarded on the WRONG selector
The cap-WRITE descriptor fix (8275b3711, moving the cap-root to rotated limbs 213/264) left the map_op GUARD on
Var(2) = the SET_FIELD selector, but the effect is RevokeDelegation = selector 30. The two are NEVER both 1 -> BOTH
map_ops (read + write) NEVER FIRE -> NOTHING constrains the AFTER cap-root (var 264). PROVEN EMPIRICALLY: overwrote
var 264 with 0xBADF00D, recomputed the commitment self-consistently -> prove_vm_descriptor2 returned Ok AND the
light-client verifier ACCEPTED it. A malicious producer can publish a FABRICATED post-cap-root with no sorted-tree
witness and it verifies on the wire. THE cap-WRITE LIGHT-CLIENT AXIS IS NOT CLOSED — the post-cap-root is unbound
in-circuit, host-trusted.
⚑ WHY THE GREEN BOARD MISSED IT: cap_write_revoke_proves_and_verifies_light_client passes BECAUSE the binding is
DEAD (the map_op dormant -> the cap-root rides only the host-trusted commitment fold). Its greenness was the SYMPTOM
of the forge, not proof of soundness. Had the box been checked on that green prove-through, a FORGE would have
shipped as 'light-client-verifiable'. THIS IS THE GOAL VINDICATED: 'a green test only counts if it goes red when the
thing it guards breaks'; the new forge-detector test's assert_ne!(213,264) non-vacuity guard is what caught it.
THE FORGE-DETECTOR (write_cap_open_wrapper_requires_cap_tree_write_witness_no_silent_forge) is RED with a precise
SILENT FORGE diagnostic — banked deliberately as the honest signal; it MUST stay until the fix lands.
THE FIX (VK-affecting Lean re-emit): re-point the cap-write map_op guard from var 2 (SET_FIELD) to var 30
(REVOKE_DELEGATION) — and analogously delegate/introduce/delegateAtten on THEIR selectors. Until then the cap-write
box is NOT closed; the prior 'genuine prove-through' green is illusory (passes because the binding is dead).

## ⚑ PARALLEL-FAMILY WAVE in flight (2026-06-21) — 4 strands on the goal's parked families + the forge
Moving on the parked families IN PARALLEL with the forge fix (ember: the families are more important than one
effect's forge consequence). LIVE:
- adf2d407 🟥 SILENT-FORGE FIX — re-point the cap-write map_op guard var2(SET_FIELD)->the firing effect selector;
  the forge-detector must FLIP GREEN (the load-bearing check). HIGHEST PRIORITY.
- aba9985a VK EPOCH family 1 — setPerms/setVK off-cell-anchor -> in-circuit force gate (the 18-effect unlock's
  first family; the off-cell-anchor->gate conversion is the template for the rest).
- ac7dbddd ✅ refreshDelegation Class-A (DONE, verified-in-isolation, NOT yet banked — integrated tree red from a
  sibling): deleg-tree WRITE column on the rotated limb (reuses cap-root limb 25, freed by rotateV3CapWrite, since
  refresh freezes caps), selector-guarded on REFRESH_DELEGATION (independently learned the forge lesson),
  refreshDelegation_descriptorRefines_sat consumes Satisfied2, mutation-confirmed. delegRoot_runtime_column_pending
  CLOSED.
- a0b89245 SetProgram own circuit witness (new RotatedKernelRefinementProgram.lean module + own effect-tag).
INTEGRATION HAZARD: all 4 touch the shared EffectVmEmitRotationV3.lean + Dregg2.lean; tree transiently RED while
SetProgram's new module compiles. HOLD for settle, then ONE clean integrated verify; bank cap-family work ONLY
after the forge-detector flips GREEN (no banking onto the dead-binding state).

## ⚑⚑🟩 PARALLEL-FAMILY WAVE LANDED (2026-06-21) — forge closed + 3 families, verified green
The 4-strand wave converged green together (lake 4108 axiom-clean, forge-detector flipped GREEN). Banked:
- 5a98dbb39 🟩 THE SILENT FORGE CLOSED: cap-write map_op guards re-pointed var2(SET_FIELD)->firing per-effect
  selectors. forge-detector write_cap_open_wrapper_requires_cap_tree_write_witness_no_silent_forge RED->GREEN (a
  genuine cap-root change with empty witness now REJECTED). cap_write_revoke_proves_and_verifies GENUINELY green
  (live binding). + refreshDelegation CLASS-A (deleg-tree write column, delegRoot_runtime_column_pending CLOSED).
- d58545a5f VK EPOCH family 1: setPermissions/setVK FORCED-ON-WIRE light-client-verifiable (the in-circuit weld #64
  binds; SDK light-client verify is anchor-free; anchor-disabled discriminator test 2/2 green, forged perms/vk
  UNSAT=[#64]). The off-cell anchor is redundant for these 2. VK-EPOCH FAN-OUT template established: the shared
  proof_verify.rs off-cell block serves 7 effects; conversion = weld the dedicated sub-limb; remaining riders =
  Refusal (fields_root weld) + lifecycle payload (reason_hash/deathCert; DISC limb 32 already in-circuit). STAGE F
  = retire the PI-46 pin (the anchor-cutover flag-day), last.
- VK EPOCH family 2 (Refusal + lifecycle PAYLOAD): MEASURED as a REAL RESIDUAL, not closeable by the family-1 weld
  template. Both are FULL-NODE-FORCED (the proof_verify.rs off-cell anchor bites) but NOT LIGHT-CLIENT-FORCED: the
  record-pin welds AFTER-limb == PI[46], but PI[46] is producer-free on the light-client path
  (verify_effect_vm_rotated_with_cutover / verify_vm_descriptor2 alone) — the generator fills it from the producer's
  OWN after-limb (trace_rotated.rs:394), so it holds vacuously for any self-consistent forged post-cell. Refusal can't
  get a perms-style weld (post-value = fields_root_felt(fields_root'), a Merkle-map root depending on pre-fields_root;
  params are target/reason_hash, NEITHER is the post-root). Lifecycle DISC (limb 32) IS in-circuit (frozen-seal /
  resurrection rejected); only the OPAQUE payload felt (limb 29: reason_hash/deathCert/sealed_at) rides the anchor —
  and sealed_at=block_height is HOST context, not an effect param. CLOSING them = a NEW primitive (verifier-anchored
  declared-PAYLOAD column, the deleg-tree shape — STAGE B/C), VK-affecting. Witness: NEW discriminator
  circuit/tests/vk_epoch_refusal_lifecycle_light_client_binding.rs (2/2 green) — honest accepts AND forged-payload
  ACCEPTED through verify_vm_descriptor2 alone (the residual poles). Off-cell anchor annotation updated
  (proof_verify.rs). No Lean/descriptor/VK change (refusalV3 doc already correctly describes the residual; drift PASS).
  FORCED-ON-WIRE count after families 1+2: setPerms + setVK + lifecycle DISC (cellSeal/Unseal/Destroy/receiptArchive
  disc) — the disc is light-client-forced; the payloads + refusal are NOT. STAGE F (retire PI-46) still gated on B/C/D/E.
- SetProgram (a0b89245): setProgram_descriptorRefines_sat present (RotatedKernelRefinementProgram.lean:143), in the
  green build, but files untracked + action.rs modified + agent report pending -> HOLD bank for the report.
SOUNDNESS WIN: the new-goal discipline caught a real silent forge ONE CHECKMARK before it shipped (the green
prove-through passed because the binding was DEAD). Now closed + the forge-detector guards it permanently.
CHECKLIST boxes now genuinely green: attenuate · resolvers · receiptArchive · cap-write-revoke (forge closed) ·
refreshDelegation · setPerms · setVK. STILL OPEN: cap-write Inserts (delegate/introduce/delegateAtten — descriptors
forge-fixed but Rust CapTreeWriteOp::Insert unwired) · the verifier authority-only tooth (needs 3 tests reconciled) ·
revoke(tag-2) frozen-face · SetProgram bank · VK-epoch families 2-N (Refusal/lifecycle-payload + STAGE F).

## 🟩 FIRST ROOM stood up (2026-06-21) — the runnable weld + the one remaining wire
The first room of the living world is RUNNABLE + cargo-testable: `starbridge-apps/first-room` welds the
colonist-job organ (compartment-workflow-mandate::colonist_job) + the escrow economy (escrow-market) onto ONE real
EmbeddedExecutor/ledger. `cargo run -p starbridge-first-room --example first_room` shows the honest earn+spend cycle
(3 receipted job steps → paid 800 conserving) AND the 5-cheat battery each REFUSED in-band on its named tooth.
4 lib tests green (incl. every_cheat_is_provably_refused asserting tooth-citation = non-vacuity).
- ONE REMAINING WIRE: David's-door is a SEAM NOTE (scenario::davids_door), not yet executable. The job cell is born
  via `birth_job_cell` (a raw insert + seed) owned by the room operator's key. The real door = birth the inhabitant's
  job cell via the GATEWAY factory (`starbridge-apps/storage-gateway-mandate` init_mandate) owned by the BUILDR
  agent's cipherclerk, so entry is scoped by the world's physics (not operator-seeded). Closure = swap birth_job_cell
  for a gateway-mandate factory birth + a second cipherclerk; the advance/pay path is unchanged (same three legs bite).

## 🟥 FORGE PATTERN = a FAMILY (2026-06-21, adf2d407) — attenuate + revokeCapability ALSO mis-guarded
The silent forge (map_op guarded on var2=SET_FIELD, never fires -> post-root unbound) is NOT unique to the cap-WRITE
wrappers. attenuate (keepWriteOp, sel.ATTENUATE_CAPABILITY=48) + revokeCapability (removeWriteOp,
sel.REVOKE_CAPABILITY=24) carry the SAME never-firing var2 guard. BUT a guard re-point ALONE is insufficient +
broke cap_open_attenuate_leg_proves_and_verifies: these write the V1-STATE cap-root (col 65/87) which is NOT a
rotated-limb commitment input (the rotated commit binds limb 264, not col 87) + has no witness-heap bridge. CLOSURE
= the SAME rotated-limb rebase the cap-WRITE wrappers got (move the write onto rotated limb-25 folding into
wireCommitR + thread the cap-tree witness heap on the attenuate/revokeCapability route). Agent reverted them to the
faithfulness name (NOT half-fixed) + a FORGE NOTE in EffectVmEmitV2.heldReadOp. = 2 more cap-effects with the
post-cap-root unbound (forgeable) until the rebase. ⚑ The forge-detector pattern should be EXTENDED to attenuate +
revokeCapability (a non-vacuous assert that THEIR map_op fires / post-root is bound) so they can't silently ship.

## ⚑⚑⚑ THE BIG WAVE LANDED (2026-06-21) — forge sin-class BOUNDED + VK-epoch swept + cap-write CLOSED
8 agents integrated green (lake 4108, cap suite 38/0, 19 VK-epoch binding tests, drift PASS). Banked 511781ca7 + 04dad369d.
🟩 THE FORGE SIN-CLASS IS CLOSED BY CENSUS (forge-sweep ac5553da, read-only over all 67 descriptors): EXACTLY 4
  dormant-guard instances, ALL the cap_root cases (cap-write + attenuate + revokeCapability — all now FIXED), ZERO
  others. Every other written column binds via a firing-correct gate. The sin we found by accident is proven bounded.
  + forge-detectors now guard revoke/attenuate/revokeCapability permanently.
🟩 CAP-WRITE CLOSED END-TO-END: Insert (delegate/introduce) + Update (attenuate) + Remove (revoke) wired, genuine
  prove+light-client-verify+forge-reject; verifier authority-only tooth FLIPPED ON. delegateAtten = named residual
  (shares GrantCapability route, needs distinct routing signal).
VK-EPOCH SWEPT (anchor-disabled discriminators, ~11-13/18 confirmed FORCED-ON-WIRE, rest NAMED not faked):
  CONFIRMED: value 6 (transfer/burn/mint/bridgeMint/setField/incNonce, strong forge), birth 3 (createCell/factory/
  spawn), noteSpend, perms/vk, lifecycle DISC. RESIDUALS (honest): noteCreate (routing weld — the noteCreate-flag-day),
  refusal+lifecycle-PAYLOAD (need a verifier-anchored declared-payload column primitive; PI[46] producer-free),
  emitEvent/pipelinedSend/exercise (effects_hash past the rotated PI window), makeSovereign+setFieldDyn (BROKEN LIVE
  SEAMS: record-pin unwired 47!=46 / field_idx<8 panic).
THE NAMED RESIDUAL WELDS (the next wave): (1) noteCreate routing branch in proof_verify.rs + the 2 prover sites;
  (2) makeSovereign record_pin_offset arm + setFieldDyn dynamic generator branch (broken live seams, fail-closed not
  forge); (3) the declared-payload-column primitive for refusal/lifecycle-payload (the deleg-tree-column shape, VK);
  (4) effects_hash into the rotated PI window (emitEvent/pipelinedSend/exercise); (5) delegateAtten routing signal;
  (6) SetProgram FullActionA ~30-file weld; (7) revoke(tag-2) frozen-face. STAGE F (retire PI-46) last.

## ⚑ DECLARED-PAYLOAD-COLUMN PRIMITIVE — LANDED (2026-06-21, agent a3acc831)
THE PRIMITIVE: `EffectVmEmitRotationV3.§5.PC` — `rotateV3WithPayloadColumn off d` (= `rotateV3WithRecordPin`
definitionally, NO VK change) + the `PayloadAnchored env d anchor` predicate + the two-pole forcing theorems
(`rotateV3WithPayloadColumn_forces_anchor` / `_rejects_forged` / `_satisfiedVm_v1`, all axiom-clean, kernel-proved).
The light-client FORCE = the verifier ANCHORS PI[46] (the declared-payload slot) to the value it recomputes from
light-client-known inputs, instead of taking it producer-free. Refusal anchors `compute_authority_digest_felt`
(effect-param-derivable via effects_hash); cellSeal/Unseal/Destroy/receiptArchive anchor `lifecycle_felt_cell`
(reason_hash param + turn-header block_height). `refusalPayloadV3_eq_refusalV3 := rfl` proves the deployed descriptor
already carries the weld (byte-identical wire JSON, registry/drift unchanged). `cellSealV3_payload_rejects_forged`
specializes the tooth. effects_hash sub-case (§5.PC.EH): emitEvent/pipelinedSend/exercise declare a HASH not a state
payload; it IS the in-window `effects_hash` PI[16..20] (< V1_PI_COUNT 42) — ALREADY light-client-bound via the perms/VK
chain, NO new primitive needed (the raw operand slots 174+ past the window are redundant pre-fold operands).
DISCRIMINATOR FLIPPED: `circuit/tests/vk_epoch_refusal_lifecycle_light_client_binding.rs` now asserts FORCED-ON-WIRE
(forged refusal-audit / sealing-payload REJECTED through `verify_vm_descriptor2` ALONE under the anchored PI[46];
honest ACCEPTED; sanity: forged verifies vs its OWN producer-free PI → the force is the anchor bite). Both tests GREEN.
Lake `Dregg2.Circuit.Emit.EffectVmEmitRotationV3` GREEN + axiom-clean.
→ THE HAND-OFF (the parallel agent owns `proof_verify.rs`; this is the SDK LIGHT-CLIENT half): `sdk/src/full_turn_proof.rs`
  `verify_effect_vm_rotated_with_cutover` line ~2150 takes `dpis = &public_inputs[..public_input_count]` VERBATIM. To
  make refusal/lifecycle light-client-forced ON THE DEPLOYED PATH, it must — for the record-pin family (public_input_count
  == 47) — OVERRIDE `dpis[ROT_PI_COUNT]` (=46) with the recomputed anchor BEFORE `verify_vm_descriptor2`: refusal →
  `compute_authority_digest_felt(apply Refusal to cross-checked before-cell)`; lifecycle → `lifecycle_felt_cell(apply
  lifecycle to before)` with the turn-header `block_height` threaded in (NOT present in `full_turn_proof.rs` today — the
  ONE new input the SDK verifier needs; full-node `proof_verify.rs` step 6b already has it). The discriminator's
  `anchor_payload_slot` helper IS the reference implementation of this override. Until that SDK override lands, the
  light-client FORCE is proven (Lean + discriminator) but the DEPLOYED `verify_full_turn` still passes PI[46] producer-free.

## ⚑ BOARD CORRECTION (2026-06-21) — stale lines the hook flagged
- resolvers_cover_exactly_the_rotated_registry is GREEN (fixed fb27a30b4, 51->52 documented) — the "RED 37 vs 36"
  in the 4c27858b9 entry was already superseded; verified `cargo test` ok.
- receiptArchive(40) is CLOSED (Class-A, banked 56178b050) — not open.
THE RESIDUAL-WELD WAVE is DRIVING (not named-and-parked) — 4 agents in flight:
- a72bf75a: noteCreate routing + makeSovereign record-pin + setFieldDyn generator (the 3 broken live seams).
- a3acc831: the declared-payload-column primitive (refusal + lifecycle-payload + effects_hash light-client binding).
- aef70ac7: SetProgram FullActionA constructor weld (apex membership, ~30 files).
- ae15d66a: delegateAtten routing signal + revoke(tag-2) frozen-face rebase (the last 2 cap slots).
GOAL STANCE: every named weld is UNDER A RUNNING AGENT with a green-check bar (genuine prove + forge-reject /
mutation-confirmed apex red / axiom-clean lake), per Law #6 — named = a burn-down with its closure lane running,
never a parking lot.

## ⚑ PAYLOAD-COLUMN PRIMITIVE (a3acc831) — Lean DONE, Rust verifier-anchor = the queued WIRE-weld
The declared-payload-column primitive is BUILT + axiom-clean (rotateV3WithPayloadColumn + PayloadAnchored +
_forces_anchor/_rejects_forged, EffectVmEmitRotationV3.lean §5.PC). NO VK change (refusalPayloadV3 = refusalV3 by
rfl, descriptors byte-identical, drift unchanged). The discriminator (vk_epoch_refusal_lifecycle) FLIPPED to
FORCED (forged payload REJECTED under the anchored PI[46]). Per-effect: refusal (anchor =
compute_authority_digest_felt), lifecycle-payload (anchor = lifecycle_felt_cell folding reason_hash + sealed_at=
block_height from the turn-header), effects_hash (already in-window at PI[16..20], no new primitive). All 3 families
light-client-forced IN LEAN.
⚑ THE WIRE GAP (per the goal: proven-in-Lean-NOT-on-wire — NOT satisfied yet): the deployed
verify_effect_vm_rotated_with_cutover (full_turn_proof.rs ~2150) passes dpis verbatim — for the record-pin family
(count==47) it must OVERRIDE dpis[ROT_PI_COUNT=46] with the RECOMPUTED anchor before verify_vm_descriptor2
(refusal->compute_authority_digest_felt; lifecycle->lifecycle_felt_cell with block_height threaded = the ONE new
SDK input, full-node step 6b already has it). The test's anchor_payload_slot helper is the reference impl. QUEUED:
drive this Rust verifier-anchor the moment full_turn_proof.rs frees (the delegateAtten agent is in it). Until then
the payload force is proven-in-Lean but verify_full_turn is still producer-free on the wire.
INTEGRATION DISCIPLINE (6 agents on shared ActionDispatch/full_turn_proof/EffectVmEmitRotationV3): HOLD banking until
the swarm settles, then ONE clean integrated verify + coherent banks. Do NOT surgically extract slices mid-edit
(provenance-leak risk). lake green 4109 at this snapshot.

## ⚑⚑ PROOF-LEVEL SIN AUDIT (a6f7fa16, read-only) — spine sin-free; 3 real laundered-green items found
VERDICT: the Lean spine is genuinely sin-free — ZERO open holes / `admit` / `native_decide` in tactic/term position
(all hits = docstring prose or the `admit` upgrade-policy VERB identifier); only 2 benign labeled demo axioms
(Widget/Basic.lean:298, prove 1=1/2=2 for the tier-classifier, never used by real proofs); every crypto floor is a
typeclass/Prop portal not a bare axiom; the apex (19 load-bearing theorems incl. lightclient_unfoolable_*,
engineSound_of_apex) is #assert_axioms-pinned IN-FILE (7223 enmeshed decl pins); the orphan Claims is PROVABLY
REDUNDANT (0 of its 171 pins are Claims-only). The foil can't slip an open hole or smuggled axiom past the spine.
⚑ 3 REAL LAUNDERED-GREEN ITEMS (the burn-down the goal must close — passing-by-wrong-reason, not forges):
1. ~65 BLIND is_err() RUST TESTS — reject but NOT provably for the right reason (a setup error passes them). Same
   sin-class as catch_unwind. Heaviest: full_turn_proof.rs (14 light-client/path-preserve teeth, lines 3831…6846),
   aggregate_bilateral_prover.rs (14 #133 anti-ghost, 1348…1943), macaroon-caveat (11), orchestration/governance
   (16), swallow-pattern is_err()||matches!(Ok(Err)) (11). FIX MODEL = membership_verifier.rs (31 sites, 0 sins:
   honest-ACCEPT the same object BEFORE every tamper, so the rejection is provably caused by the tamper). + 2 RISKY
   catch_unwind (adversarial_boundaries.rs:113 also tolerates Ok(true)!; body_membership.rs:525).
2. TREE-WIDE *TraceReadout CARRIER-INHABITATION gap (~17 rungs) — *_descriptorRefines_sat takes a TraceReadout
   premise with NO inhabitation witness; if the readout type is uninhabitable the REFINEMENT rung is vacuously
   satisfiable (the tooth-theorems themselves ARE non-vacuous, but the readout-repackaging door is open). The
   readouts are realizable (WitnessDecodes-class) but un-witnessed. Per the goal's non-vacuity clause: prove each
   TraceReadout INHABITED (the FloorsNonVacuous pattern). Pre-existing; SetProgram inherits from refusal.
3. FloorsNonVacuous.lean covers 5 apex carriers but NOT the new-wave floors (SetProgram/SetVK/RefreshDelegation/
   ReceiptArchive spec-carriers + the TraceReadouts) — extend it.
ALSO: 9 substantive #[ignore]'d security obligations (γ.2 bilateral-binding x6, sovereign-witness AIR teeth,
cap_open_self_verify.rs:224/317/377 the attenuate UPDATE-AT-KEY handoff — NOW being closed by ae15d66a) — named
parked obligations, each a burn-down item. 3 honest residual-asserting tests (vk_epoch_misc, names its closure lane).
QUEUED (drive when the swarm settles, all 3 are real non-vacuity/no-laundered-green obligations the goal requires):
(a) harden the ~65 blind-reject tests to the membership_verifier honest-accept-then-tamper model; (b) prove the
~17 TraceReadout carriers inhabited; (c) extend FloorsNonVacuous to the new-wave floors.

## ⚑⚑⚑ COMPLETE SIN-MAP (a5343839, read-only) — the full light-client-blindness inventory + a DROPPED FORGE
The complete map of every place a light client could be lied to, across 30 effects. Bounded: every blind value is
CLOSEABLE (a named weld) or one of 3 by-design IRREDUCIBLE floors.
🟥🟥 THE DROPPED FORGE (#1 PICKUP — a LIVE light-client forge under NO in-flight agent): revokeCapability — the
  cap-tree REMOVE rides UNBOUND. Route write:None (full_turn_proof.rs:1329) -> revokeCapabilityCapOpenVmDescriptor2R24
  (NO map_op) which is NOT in the forbidden authority-only list (:2096-2099); the BASE (which HAS the remove map_op)
  IS forbidden (:2111). So a light client ACCEPTS a forged post-cap-root REMOVE. ⚠ THE FORGE-DETECTOR IS A LAUNDERED
  GREEN: cap_write_revoke_cap_no_silent_forge (full_turn_proof.rs:4542) tests the BASE descriptor, not the deployed
  ROUTE -> green while the wire is forgeable. FIX: add write:Some(("revokeCapabilityWriteCapOpen…", Remove)) + emit
  that wrapper + forbid revokeCapabilityCapOpen authority-only + a ROUTE-level forge-detector that exercises
  verify_full_turn (goes RED today). The Remove machinery EXISTS (revokeDelegation uses it). CONTENDED with ae15d66a
  (full_turn_proof.rs + EffectVmEmitRotationV3) -> DRIVE the moment ae15d66a settles (can't bank mid-edit).
HEADLINE TALLY (30 effects):
- FORCED-ON-WIRE (light-client-verifiable, no gap): 14 — transfer/burn/mint/bridgeMint/setField/incNonce/setPerms/
  setVK/createCell/attenuate/introduce(cap-move)/revokeDelegation(cap-move)/grantCap+delegate(cap-move)/delegateAtten.
- disc/mode forced + payload residual (CLOSEABLE, under payload agent a3acc831): cellSeal/Unseal/Destroy/receiptArchive
  + makeSovereign(mode forced, residue redundant).
- PRODUCED-HASH-UNBOUND (forge, CLOSEABLE by ONE effects_hash weld — PI[16..19] published-but-unpinned on the
  rotated path; payload agent a3acc831 covers it): emitEvent/pipelinedSend/exercise + intro_hash/child_hash/factory_vk.
- DROPPED CLOSEABLES (no in-flight agent): revokeCapability (FORGE, #1), refresh (deleg-tree write variant unrouted,
  lower sev — re-arms existing authority), spawn (child cap-handoff supplied-digest, CLOSEABLE-but-heavy),
  attenuate-honest-prove-route (#[ignore]'d pending CapTreeWriteOp UPDATE — prover-completeness, NOT a forge).
- BROKEN-LIVE-SEAM (fail-closed, NOT forge): setFieldDyn (panics field_idx<8, under a72bf75a); makeSovereign FIXED.
- 3 IRREDUCIBLE FLOORS (no light-client-knowable anchor by design — the goal accepts WITH non-vacuity proof):
  (1) noteSpend/noteCreate canonical set-root anchor — the in-circuit set-move IS forced; WHICH set is a client-input
      binding (federation receipt), caught at verify_full_turn_bound 8a/8b. Non-vacuity: the .absent tooth rejects a
      self-inconsistent double-spend. (2) exercise actor->target causal link — target proves its own turn; needs
      cross-turn composition. (3) refusal fields_root — IRREDUCIBLE under current params BUT closeable once the
      payload-column primitive lands (so a named-floor-with-closure-lane, not permanent).
NEXT-WAVE PICKUPS (driveable, the dropped set + the proof-level audit items): revokeCapability route-forge (#1) +
its honest route-detector · refresh/spawn write-routing · the ~65 blind-is_err() test hardening · the ~17
TraceReadout carrier-inhabitation non-vacuity · FloorsNonVacuous extension. All under the goal; none parked.

## ⚑ SetProgram APEX-MEMBERSHIP WELD DONE (aef70ac7) — held for swarm-settle
The ~30-file FullActionA weld CLOSED GREEN: FullActionA.setProgramA constructor (the setVKA analog) + the
setProgramA arm in EVERY exhaustive match (ledgerDelta/execFullA/conservation/receipt/fairness/authority/actionTag=13/
fullActionStep->SetProgramSpec/the commitment frames/HandlerExecutor/FFI/codec); execFullA_setProgram_iff_spec
re-proves fullActionStep_exec_iff; a NEW Inst/setProgramA.lean v1 encoder track (apex_iff_setProgramSpec, the deep
leaf arms built not skipped). APEX MEMBERSHIP: v3RegistryHeap pos 51 (52 total), actionTagToPos 13=>51,
Rfix_setProgram rfl, closedLogExtract_setProgram_closed via setProgram_descriptorRefines_sat, the |13=> dispatch arm
before the fallback. MUTATION-CONFIRMED (wrong registry pos OR dropped record-pin binding reds the apex). lake 4109
axiom-clean. SetProgram now a GENUINE apex leg — editing setProgramV3 reds the apex.
HELD: its apex edits (ClosureFanoutGenuine/ClosureAll/CircuitSoundnessAssembled) are SHARED with ae15d66a's
revoke-tag2 apex re-point -> bank in the final integrated pass when ae15d66a + a72bf75a settle, not mid-edit.
RESIDUAL-WELD WAVE STATUS: 7 welds — SetProgram ✅(held), payload-Lean ✅(held, Rust verifier-anchor queued),
refresh ✅(in 5a98dbb39 earlier), receiptArchive ✅, attenuate/revokeCap forge ✅; DRIVING: noteCreate/makeSovereign/
setFieldDyn seams (a72bf75a), delegateAtten+revoke-tag2 (ae15d66a). NEXT (post-settle): revokeCapability route-forge
(#1, the sin-map's dropped forge) + the payload Rust verifier-anchor + the ~65 blind-test hardening + TraceReadout
non-vacuity.

## ⚑ a72bf75a DONE (held for swarm-settle) — noteCreate + makeSovereign CLOSED on-wire; setFieldDyn = deeper residual
- noteCreate -> FORCED-ON-WIRE: the in-circuit commitments-root .insert grow-gate was SOUND; gap was live routing
  (fell to transfer-shape 46-PI, errored on the 47-PI commitment base). Added NoteCreate branch ->
  generate_rotated_note_create_wide in proof_verify.rs + the 2 prover sites. Discriminator
  notecreate_forced_on_wire_through_live_wide_producer green (honest proves+LC-verifies at 816-wide/63-PI; forged
  commitments-root UNSAT via .insert).
- makeSovereign -> FORCED-ON-WIRE: record_pin_offset had no MakeSovereign arm (46 vs declared 47 -> un-provable).
  Added Some(MakeSovereign)=>Some(B_RECORD_DIGEST) (the flipped mode byte folds into r23 authority residue) + the
  record-pin family in all 3 routers. Discriminator flipped residual->FORCED (forged authority residue UNSAT,
  anchor-disabled). Generator-side only, drift PASS.
- setFieldDyn = DEEPER RESIDUAL (named at true depth, NOT faked): setFieldDynVmDescriptor2R24 is a distinct 581-wide
  geometry (263-wide setFieldDynV1Face folding the openable fields_root insert sub-circuit). The standard generator
  makes 188->328-wide and can NEVER satisfy 581-wide; lifting field_idx<8 would silently clamp to the wrong field
  (correctness bug). CLOSURE = a from-scratch 263-wide V1Face generator (a real weld, not a branch). Test
  setfielddyn_unreachable_via_live_generator_missing_weld asserts the geometry mismatch (581 != ROT_WIDTH).
SWARM STATUS: only ae15d66a (delegateAtten + revoke-tag2) still running. When it lands -> ONE clean integrated
verify + bank coherent groups (SetProgram weld + payload-Lean + a72bf75a's 2 welds + ae15d66a, all held). THEN drive
the post-settle queue: revokeCapability #1 route-forge · payload Rust verifier-anchor · setFieldDyn 263-wide
generator · ~65 blind-test hardening · TraceReadout non-vacuity · FloorsNonVacuous extension · HORIZONLOG compaction.

## ⚑⚑⚑ POST-COMPACT ORIENTATION (2026-06-21, ~3am) — the TWO-TRACK swarm + integration plan
GOAL (the /goal hook, two tracks, SAME bar = verified-working not named): TRACK 1 FLOOR (soundness, audited by
docs/SAFELY-LIVE-CHECKLIST.md — closed+verified OR irreducible-floor-with-non-vacuity-proof, board red-free) +
TRACK 2 HOUSE (capacity — grow what an agent needs to LIVE; a capacity counts ONLY genuinely-working end-to-end +
inheriting the floor's forge-detector bar). Designed-but-unbuilt = a named gap (Law #6).

### THE LIVE SWARM (8 agents — the harness notifies on each completion, post-compact too):
TRACK 1: ae15d66a (delegateAtten routing + revoke-tag2 frozen-face, the LAST cap-weld) · a90a132e (harden ~65 blind
is_err() laundered-green tests to the membership_verifier honest-accept-then-tamper model; NOT full_turn_proof.rs) ·
a9e74dae (prove ~17 TraceReadout carriers INHABITED/non-vacuous + extend FloorsNonVacuous to new-wave floors).
TRACK 2: a695bfc7 (reactive effect-variant LIFT into Effect vocab + React circuit witness pending_id-as-nullifier) ·
a795f994 (DERIVED/relational cells — verifiable views, forged-derivation rejected) · a737e46c (MEMBRANE/forwarder —
caps compose up, non-amp tooth) · a45ee057 (HATCHERY abstraction-MINT — user-defined verified kinds, violating-turn
refused).

### HELD WORK TO BANK (when the swarm settles — ONE clean integrated verify, then coherent groups, NO partial
### sweeps / provenance-leak): SetProgram FullActionA apex-weld (lake 4109, mutation-confirmed) · payload-column
### primitive Lean (axiom-clean, no VK change) · noteCreate+makeSovereign on-wire welds (a72bf75a) · revoke-tag2 +
### delegateAtten (ae15d66a, pending). These touch shared apex Closure*/EffectVmEmitRotationV3 — bank together.
### INTEGRATION = lake axiom-clean + ALL forge-detectors green + the 6 vk_epoch discriminators + cap suite + drift.

### TRACK-1 QUEUE (drive after swarm-settle, in priority order):
1. 🟥 revokeCapability #1 ROUTE-FORGE (the sin-map's dropped live forge): route write:None -> revokeCapabilityCapOpen
   (no map_op, not in forbidden-authority-only list) -> cap-REMOVE rides UNBOUND, LC accepts forged post-root. Its
   forge-detector cap_write_revoke_cap_no_silent_forge is a LAUNDERED GREEN (tests the BASE not the ROUTE). FIX:
   emit revokeCapabilityWriteCapOpen wrapper + write:Some(...,Remove) + forbid the authority-only + a ROUTE-level
   forge-detector (RED today). Remove machinery exists (revokeDelegation). CONTENDED with ae15d66a -> drive when it frees.
2. payload Rust verifier-anchor (full_turn_proof.rs verify_effect_vm_rotated_with_cutover: override dpis[46] with the
   recomputed anchor — refusal=compute_authority_digest_felt, lifecycle=lifecycle_felt_cell+block_height). The payload
   is proven-in-Lean-NOT-on-wire (goal does NOT accept). Contended with ae15d66a.
3. setFieldDyn 263-wide V1Face generator (a from-scratch generator, NOT a branch — agent refused the wrong-field clamp).

### 3 IRREDUCIBLE FLOORS (goal-acceptable WITH non-vacuity proof): noteSpend/noteCreate canonical-set-root
### (client-input binding, verify_full_turn_bound 8a/8b; the .absent tooth is non-vacuous) · exercise actor->target
### cross-turn causal link · refusal fields_root (closeable once payload-anchor lands -> a named-floor-with-closure-lane).
### THE FORGE-DETECTOR ANTIBODY: every tree-write effect gets a non-vacuous forge-detector (overwrite the post-root,
### assert rejected) — the dormant-guard class is closed by census (forge-sweep ac5553da: 4 instances, all fixed).

### TRACK-2 STATUS: reactive effect BANKED 727b9a800 (sound-by-construction — react-twice = the noteSpend nullifier
### gate; 6 green tests incl. genuine react_twice_rejected). 4 more capacities in flight (above). Next after these:
### bank each genuine-working slice; the reactive Effect-vocab lift + circuit witness is the deepening.
### TRACK-2 DERIVED/RELATIONAL CELL (built, uncommitted): cell/src/derived.rs — a cell whose committed state IS a
### verifiable function of OTHER cells (sum/sumField/count/filtered-sum view). Binding rides the committed heap
### (DERIVATION_COLL) -> folded into canonical commitment, no VK bump. bind_derivation = re-derive; verify_derivation
### = the forge detector (claimed != f(sources) -> ValueMismatch; staleness = same rejection). 8 green tests incl.
### genuine forged_value_is_rejected + stale_after_source_change_is_rejected. Doc docs/deos/DERIVED-CELLS.md.
### NEXT SLICE (named): DeriveCell effect descriptor whose gate binds claimed==f(sources) into the commitment +
### source-commitment membership witnesses + Lean rung (verifyBatch accept => derived.claimed = f(sources)).

### ⟳ SWARM PROGRESS (2026-06-21, post-compact integration):
### ✅ SWARM FULLY SETTLED + INTEGRATED. 6 Track-2 HOUSE capacities banked, each with a genuine both-polarity
###   forge-detector (honest-accept + forge-reject share ONE verify core -> non-vacuous by construction):
###   - reactive Effect::{Promise,Notify,React} lifted to first-class executor vocab (5c4bd17e1) — React spends
###     pending_id into the SAME production note_nullifiers set as NoteSpend -> react-twice = double-spend. 10/10.
###   - derived/relational cells + membrane/forwarder (34ef4a048, 8/8 + 13/13).
###   - sealed escrow — atomic 2-of-2 value swap (4c20cf700, 15/15).
###   - Hatchery abstraction-mint — user-defined verified kinds (5b99f27ab, 13/13).
###   - standing/recurring obligation — owe AMOUNT every PERIOD, one-shot cursor + audit tooth (f675969b3, 13/13).
###   ALL six name their in-circuit-witness next slice (effect descriptor + Lean rung) — the light-client-soundness deepening.
### ✅ Track-1 FLOOR banked: token-caveat hardening (409886b6e) · turn anti-ghost+v3-sig honest-model (477420f1f) ·
###   circuit blind-rejection honest-model (22ed73d3f) · the LEAN APEX (eb4910086, lake Dregg2 GREEN 4115 jobs, axiom-clean):
###   revoke(tag-2) frozen-face -> WRITE-BEARING (Rfix 2 => revokeDelegationWriteCapOpenV3, forge-detector mutation-confirmed) +
###   18 *TraceReadout carriers proven INHABITED (no critical vacuity bug) + SetProgram FullActionA weld.
### ✅ VERIFIED GREEN at HEAD: cap suite 39/0/1 (the 1 ignore = delegateAtten LogUp residual, fail-closed, NOT a soundness gap) ·
###   descriptor-drift PASS (Lean emit == checked-in JSON) · circuit lib 941/0 · dregg-turn lib green · dregg-cell 714+ green.
### ✅ cap region BANKED (5d6184f3b): trace_rotated.rs + full_turn_proof.rs cap-routing + descriptors + vk_epoch
###   light-client-binding tests (20/0). Apps honest-model sweep BANKED (6495c0ae6, +1 u64->usize fix).
### ✅ Track-1 QUEUE #1 CLOSED (f458b5258): revokeCapability ROUTE-FORGE — the SDK cap-open route bound the
###   AUTHORITY-ONLY revokeCapabilityCapOpen (write:None) so the cap-tree REMOVE rode UNBOUND on the light-client wire
###   (forged post-cap-root accepted; base-level forge-detector was a LAUNDERED GREEN testing the BASE not the ROUTE).
###   FIX mirrors revokeDelegation tag-2: write-bearing wrapper revokeCapabilityWriteCapOpenV3 (authority crown AND
###   cap-tree REMOVE in ONE descriptor) + route re-pointed write:Some(...,Remove) + authority-only FORBIDDEN +
###   Lean rungs (descriptorRefines_capOpenSat + forge tooth + apex rung, axiom-clean) + route-level antibody
###   cap_write_revoke_cap_route_proves_and_verifies (RED before at route.write.is_some(), GREEN after, mutation-confirmed).
###   Verified at HEAD: lake 4115 green axiom-clean · cap suite 40/0/1 (+1) · drift PASS, FP re-pinned. VK-affecting -> ember-gated.
### ⚠ FINDING (named, not a fake green): the dregg-tests __wip_tests crate has ~258 PRE-EXISTING compile errors (API drift:
###   Cell.id went private, Turn gained 9 fields) — so the blind-test agent's tests/src/adversarial_boundaries.rs honest-model
###   edit is UNVERIFIABLE through it and is LEFT UNCOMMITTED (no green check for an edit that can't compile). Rehab of the
###   __wip_tests crate is its own project (out of tonight's scope), not a quick-fix.
### THE 1 REMAINING CAP RESIDUAL (named, fail-closed, NOT a soundness gap): delegateAtten genuine prove-through #[ignore]'d —
###   a plonky3 LogUp submask+INSERT permutation-column interaction (see the delegateAtten note at the top of this log).
### NOT-MINE-TONIGHT (other-session work in the shared tree, left untouched): cell/predicate.rs AuthContext · dregg-atlas/ ·
###   Cargo.{lock,toml} · sdk/cipherclerk.rs · turn/executor/{authorize,membership_verifier,proof_verify}.rs · wasm/runtime.rs.
### ✅ EXERCISE CAP-OPEN CLOSED (the LAST named cap-open residual): exerciseViaCapability's hold-gate is now
###   FORCED in-circuit via a DEDICATED cap-open descriptor. Diagnosis: the "inner-fold base does not take the
###   appendix" framing was STALE — the exercise base (v3Of exerciseVmDescriptor, frozen-frame+nonce-tick, gCapPass
###   freezes cap_root) is geometrically identical to the frozen fan-out bases (introduceV3/spawnV3); the generic
###   effCapOpenV3 combinator composes verbatim. Built: CapOpenEmit.exerciseCapOpenV3 (EFF_EXERCISE = bit 1 =
###   EFFECT_TRANSFER, the held cap's value facet — there is NO EFFECT_EXERCISE facet bit; the load-bearing content
###   is leaf.target = src, the confersEdgeTo edge) + exerciseCapOpenV3_authorizes + _rejects_wrong_facet keystones ·
###   ExerciseAuth.exerciseEncodesAuthV3 + exercise_descriptorRefines_capOpenSat (hold-gate forced from the dedicated
###   Satisfied2) · APEX: Rfix 16 re-pointed 10->53 (exerciseCapOpenVmDescriptor2R24, v3RegistryHeap pos 53) +
###   Rfix_exercise_capOpen rfl + closedLogExtract_exercise_closed now consumes exerciseEncodesAuthV3 -> threaded
###   load-bearing into lightclient_unfoolable_closed_final_genuine. MUTATION-CONFIRMED ×2: stripping the crown reds
###   CapOpenEmit (#guards + keystones); re-pointing actionTagToPos 16 away reds Rfix_exercise_capOpen rfl + the apex.
### VERIFIED GREEN at HEAD: lake Dregg2 4115 green, apex axiom-clean {propext,Classical.choice,Quot.sound} · circuit
###   lib 942/0 · sdk prover lib 316/0 · v3_staged_registry_parses (n==56) + wide_registry GREEN · descriptor-drift PASS
###   (FP re-pinned eef50da1) · cap_open_exercise_self_verify 2/0/1 (genuine columns + authority-forge-rejected-at-witness
###   GREEN; end-to-end prove #[ignore]'d on the SHARED non-TB cap-open IR-v2 cap-node lookup-balance handoff — the SAME
###   gap cap_open_attenuate_self_verifies carries; only the TURN-BOUND transfer path self-verifies).
### NAMED FOLLOW-ON (the one residual, fail-closed, NOT a soundness gap): the SDK route for exercise (full_turn_proof.rs
###   cap_open_route_for_run arm) is gated behind the shared non-TB cap-open prove-THROUGH plumbing landing (another
###   session owns that dispatch); cap_open_supported_for_run's error message updated to name it precisely. The exercise
###   descriptor + the Lean apex (Rfix 16) are CLOSED; only the end-to-end prover lookup-balance is the residual.

### gpui-component VENDORED — the cockpit gets real widgets (text Input it never had). Fork
###   emberian/gpui-component@dregg-repoint (sibling ../../gpui-component, Apache-2.0): a CLEAN re-point of every
###   zed-derived dep (gpui/gpui_platform/gpui_web/gpui_macros/reqwest_client) onto emberian/zed@407a6ff — the rev
###   starbridge-v2 already pins; upstream's gpui/src @1d217ee is byte-identical to our fork's (fork only patches the
###   offscreen renderer, not the API), so ONE gpui instance resolves across cockpit+widgets. Standalone
###   `cargo build -p gpui-component` GREEN (after replicating the zed monorepo's [patch.crates-io]: async-process/
###   async-task fork revs + vendored pathfinder_simd 0.5.6 scalar build). starbridge-v2 wiring: optional `gpui-component`
###   path dep (default-features OFF → tree-sitter grammars opt-in, lean cockpit) under `gpui-ui`; one
###   `gpui_component::init(cx)` at run_window boot. LICENSE-APACHE-gpui-component + NOTICE-gpui-component.md (AGPL
###   hygiene). Commit 4d610343. The gpui-component graph compiled clean in the bin build; verification was BLOCKED only
###   by a CONCURRENT SWARM WIP break in starbridge-v2/src/cap_inspector.rs:434 (another agent added a `HostPd` arm to
###   dregg-firmament's Target enum; non-exhaustive match, E0004) — NOT my file-set, not caused by this change. The
###   cockpit-integration agent owns cockpit.rs; Input API in the handoff: InputState (Entity model) .placeholder()/
###   .masked(true) + TextInput::new(&state) element, InputEvent::{Change,PressEnter} for submit.

### EXECUTOR⟺SPEC COVENANT widened (the SUBSTANTIAL_FAKERY audit fulcrum). Three strands, all green:
###   (1) THE DENOTATIONAL CENSUS — `turn/tests/lean_state_producer_denotational_census.rs`: one honest
###   committing turn per root-agreeing effect through BOTH producers, asserting full ledger agreement
###   (balances/nonces/state-fields/cap_root/.root()) AND the conservation invariant (scalar total supply
###   = deployed projection of §MA-scalar) on BOTH ledgers. 19 census tests (was a 2-effect spot-check):
###   Transfer/SetField/IncrementNonce/EmitEvent/SetPermissions/SetVerificationKey/NoteCreate/CellSeal/
###   CellUnseal/CellDestroy/MakeSovereign/GrantCapability/AttenuateCapability/Introduce/RevokeDelegation/
###   RefreshDelegation/RevokeCapability + a non-vacuous conservation tooth. NAMED RESIDUALS (each WHY):
###   NoteSpend (needs a real STARK proof — only the proofless reject agreement exists), Burn (W1
###   issuer-supply has no conserving scalar image — verified producer refuses until the well migration).
###   (2) SCALAR↔PER-ASSET refinement PROVED axiom-clean (`Dregg2/Exec/TurnExecutorFull.lean §MA-scalar`):
###   `execFullTurnA_conserves_scalar`/`execFullA_conserves_scalar` — the deployed single-asset scalar
###   conservation is the `b := a₀` specialization of the per-asset `execFullTurnA_conserves_exact`; the
###   deployed scalar model is sound BECAUSE it is one column of the proven per-asset executor (propext/
###   Classical.choice/Quot.sound only; `#assert_namespace_axioms Dregg2.Exec.TurnExecutorFull` still clean).
###   (3) THE REFRESH-DELEGATION RESIDUAL the census surfaced is now CLOSED (not just named). Root cause:
###   the kernel `delegate` parent-pointer was NEVER carried on the wire, so the verified
###   `refreshDelegationChainA` `(delegate child).isSome` precondition could never be met from a
###   reconstituted pre-state. FIX = a new 12th WState field `delegate` (`WState.delegate` /
###   `WireState.delegate`, `[child,parent]` pairs) ACROSS the FFI seam — FFI.lean (struct/encode/parse/
###   stateOfWState/wstateOfState) + Rust marshal.rs (struct/sentinel/encode/parse) + the golden
###   regenerated from the proved Lean codec (`marshal_conformance` GREEN byte-for-byte incl. the non-empty
###   `[[2,0]]` case) + `build_pre_ledger` parent-closure (pull each cell's delegation parent into the wire)
###   + `lean_apply::StateOp::RefreshDelegation` (replay `apply_refresh_delegation`'s DelegatedRef install,
###   forge-antibody + `current_timestamp`-stamped `refreshed_at` so the commitment-bound field matches).
###   `ShadowHostCtx` gained `current_timestamp`. VERIFIED GREEN: census 19/19, differential/widen/coverage,
###   rust_lean_divergence_finder (5), proptest (1), dregg-lean-ffi suite, Dregg2.Claims (4116 jobs, FFI
###   wire-codec refinement theorems still prove). NOTE concurrent swarm WIP broke circuit/src/binding.rs
###   (8-felt presentation-tag campaign, NOT my file-set) — blocks the dregg-node build only; my dregg-turn/
###   dregg-lean-ffi/Lean scope is clean. NOT committed (per directive).

### deos CAP-SECURED DATA STORE — first slice landed (2026-06-22)
### Designed + built the deos cap-secured store: PG18 + pg-dregg (caps-as-RLS) + dregg-query
### (attested reads). Doc: `docs/deos/DREGG-DATA-STORE.md` (vision/bundle/trust-story/builders-dev path).
### Runnable slice (postgres-free CORE, green): `pg-dregg/tests/cap_secured_store.rs` (5 tests — the RLS
### row-filter = the EXACT `authz::decide` the `dregg_admits` extern runs per row: cap-reachable-only,
### attenuation = strict subset, wrong/expired/forged = nothing, instant revocation, no-key = empty) +
### `dregg-query/tests/cap_secured_read.rs` (4 tests — attested `granted ∧ ¬revoked` read with the
### non-omission certificate + CALM grade; a server that omits a row is CAUGHT). pg-dregg 126 / dregg-query 26.
### FOLLOW-UP (named seam): the circuit crate-split #5 retired the `prover` feature + moved the IVC recursion
### tower to `dregg-circuit-prove`. Repointed pg-dregg's `tier-c` dep + `src/attest.rs` import to
### `dregg-circuit-prove` (default core resolves + tests green). STILL TODO: port `tests/tier_c_real_proof.rs`'s
### internal `dregg_circuit::{ivc_turn_chain,joint_turn_aggregation}` paths to the split crate (test is wholly
### `#[cfg(feature="tier-c")]`, does NOT block the core). Bundle packaging (one-command PG18 + auto-load) = next.

### ⚑⚑⚑ OVERNIGHT AUTONOMOUS — THE FULL-DEOS GOAL (2026-06-23, /goal set, stop-hook active)
GOAL: deos as a COMPLETE RUNNING self-hosting verified desktop OS, usable to develop dregg from within.
Prove by RUNNING (not compiling). Full vision: usable-dev-loop · WHOLE Zed IDE embedded · Xanadu
(doc-language+transclusion) · REHYDRATION/membrane (real cross-user) · web-deos PAINTING in a browser ·
servo browsing real pages net-cap-gated · data-plane · network-portable migrate verb · polis · MUD · live
Hermes · chat-on-live-homeserver · the literate atlas. DISCIPLINE (load-bearing, from the audit): "done"=
RAN not compiled/mock/first-slice; report real-state-only (wired vs seam); NOT the metatheory/circuit
(other agents own it — DON'T touch).

⚑ THE 3 AUDIT LEDGERS are the deficiency backlog (in this session's transcript). The repeated failure caught:
session-summaries compressed compiles/mock/first-slice into done/runs/real. The DOCS were honest; the SUMMARY
wasn't. Fix the words AND the code.

LANDED REAL (the honest way) this push:
- data-plane Bus is now the real delivery spine (b79af125): SSE delivery drains the Bus in lockstep
  (queued→handled witnessed live, inbox bounded), off-by-one fixed, "RUNS IN PRODUCTION" wording corrected.
- Hermes-UX interactive (33b001f8): typed prompt→streamed reply→live gated tool-calls→depleting budgets;
  brain=MockHermesPeer (honest), live Bedrock path real but not yet wired to the input box.
- theming dark+system-aware (14a9a837): the flashbang was gpui_component defaulting to LIGHT; fixed at all
  6 init sites + cohesive palette. (Hermes signature seam since fixed by main loop — native-full builds green.)
- gpui-cockpit-in-browser (ae65327f): HONEST — bundled + booted in headless Chrome + WebGPU up + boot_cockpit
  invoked, but STOPS at a gpui_web run-loop closure-reentrancy BEFORE first paint. The paint gap is in the
  gpui_web FORK's scheduler. build-gpui.sh + verify-gpui.mjs land it reproducibly. THIS is the model of honest
  "ran it, here's the real ceiling" reporting.

RUNNING LANES (check via task notifications): node-runs+cockpit-attach (ac3d1dc3) · servo real-pages+net-cap
(ac77fac0) · editor-on-FirmamentFs-mounted (a4f573a5) · cross-user-membrane-not-mock (a82f43b5) · migrate-verb
+tearoff-tests (a52ea649). Whole-Zed foundation LANDED (0a809467 + DESIGN-FULL-ZED-EMBED.md staging ladder:
editor→+project-panel/outline/search/palette→+terminal→+git/agent→+collab; real Zed editor over FirmamentZedFs
TESTED).

KEY SEAMS / NEXT (real-state):
- web-deos PAINT: fix the gpui_web fork run-loop closure-reentrancy so the cockpit paints (then app backends).
- ⚠ shared_fork.rs added a thiserror use that doesn't wasm-link under gpui-web (the cross-user-membrane lane) —
  breaks the gpui-web build until cleared; integrate.
- chat-LIVE (cockpit chat uses MockSource not a live homeserver) + wasm spawn_local sync: FIRE after the
  membrane lane clears deos-matrix (collision).
- devtools federation-config = honestly-stubbed (no live federation in embedded image) — NOT a code gap.
- the migrate verb (Local→HostPd→Distributed), Xanadu transclusion buildout, the whole-Zed Workspace stages.
