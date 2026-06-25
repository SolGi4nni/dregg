# THE FRONTIER BACKLOG — what is NOT finished, and what to swarm next

*A completeness map. This is the honest organized inventory of unfinished work
across EVERY lane, each line carrying its **closure lever** and a **rough size**,
followed by the payload: a proposed **ordering of the next 2–3 build waves**,
grouped for swarm-safety by disjoint file sets. It is a SYNTHESIS, not a restatement
of `HORIZONLOG.md` (the line-item burn-down) — it groups, prioritizes, and proposes
the waves. Present-tense, names every seam as work with a lever, never a wall.*

> Sources synthesized: `REORIENT.md` (current state), `docs/FRONTIER-ROADMAP.md`
> (the N/C/R tiers), `HORIZONLOG.md` (the burn-down), the six design-frontier docs
> (`ADOS.md`, `WEB-FORWARD.md` + `WEB-FORWARD-EVERYWHERE.md`, `EMBEDDED-WEB-SURFACE.md`
> + `DISTRIBUTED-SERVO.md`, `PG-DREGG-DX.md` + `PG-DREGG.md`, `AGENT-SWARM-UX.md`,
> `UNIFYING-STORY.md`), `docs/ROBIGALIA-ROADMAP.md` + `docs/SEL4-EMBEDDING.md`,
> `docs/DREGG-DESKTOP-OS.md` + `docs/STARBRIDGE-V2.md`, `docs/ASSURANCE-CRITIQUE.md`
> + `docs/STAGE5-CONSENSUS-DEVAC.md`.
>
> **Sizes** are rough, for sequencing only: **XS** ≈ hours · **S** ≈ a day ·
> **M** ≈ a few days · **L** ≈ a week+ · **XL** ≈ multi-week / quarter-scale.

---

## 0. The shape of "unfinished" in one breath

The spine is real and proven; the unfinished work falls into **seven families**,
and the single biggest fact about sequencing is the **cutover gate**:

1. **THE CUTOVER TAIL** (`circuit/` + `turn/` + `cell/` + node + the VK epoch) — the
   single largest in-flight engineering frontier. Most of the hard design is DONE
   (C1–C6 staged, walls A+B committed); what remains is the wide irreversible wire
   rewrite (wall C), two sibling hand-AIRs' Lean-emission, the regen/delete (C5/C7),
   and **the one VK epoch** that must batch the notify Step-2 felt-encoders. **This
   gate is why the swarm-safe NOW work lives in separate workspaces.**
2. **THE WIDE-SAFE PRODUCT SURFACE** (starbridge-v2, pg-dregg, wasm/web, site,
   additive-Lean apps) — the killer demos + handoff-readiness. NONE of it is blocked
   on the cutover (root-`exclude`d workspaces + static site + additive Lean). **This
   is the swarmable bulk of the next waves.**
3. **THE l4v BINARY BRIDGE** (`turn/` Stage 0, then spec→binary) — the Lean
   *composition* is strong; l4v-grade is the binary bridge. Research-tier, but Stage 0
   (executor authority) is "no new mathematics" and unblocks Tier-D pg + the seL4
   service executor.
4. **THE seL4 / ROBIGALIA SUBSTRATE** (`sel4/`) — the assembly boots, one verified
   turn has run in a PD; carrying it to a *service* is named, scoped work behind the
   Lean-runtime port residue.
5. **THE DISTRIBUTED / `n>1` FRONTIER** (`net/` + `node/` consensus + Servo-distributed)
   — an n=3 slice runs the ordering rule; the blocker is gossip dissemination (S5-1).
6. **THE FOUR-ASPECT AUTHORIZATION INTEGRATION** (`metatheory/` + macaroon/cap-crown)
   — the deepest open *design* thread: macaroon layer and cap-crown are unintegrated;
   integrate, do not reduce.
7. **THE LEAN RESEARCH PILLARS** — UC/CryptHOL, noninterference (the notify covert
   channel), transcendental-syntax, simplicial joint turns. Explicitly Research-tier.

---

## 1. THE CUTOVER TAIL — the live proof-path flip (the dominant gate)

*Where: `circuit/` + `turn/` + `cell/` + `node/` + the registry + the VK epoch.
Owner discipline: ONE lane (NEVER swarmed — it is one knot; `a4c7368ae` commissioned).
Docs: `ROTATION-CUTOVER.md §EXEC`, `REORIENT.md` CURRENT STATE.*

**DONE + committed** (`b0baf026c` + earlier): C1 (sovereign FLOW-A rotated), C2
(prover-free `verify_vm_descriptor2` split), C3 (the multi-table leaf-wrap + aggregate
— the recursion architecture is proven), C4 (the two recursion consumers + FLOW-B SDK
leg, WIP), C6 (cell commitment is v9 live), wall A (the bilateral Rust interpreter →
Lean-emitted `windowGate` descriptor, hand-AIR retired on the live path), wall B (node
FLOW-B producer threading for the self-sovereign turn). The rotated registry has all
**36** cohort members; the measured win is **−65.6% proof size, verify 3.4× faster**,
on top of the soundness win (multi-table batch verifier replaces the weak hand-AIR).

| # | Unfinished | Closure lever | Size |
|---|---|---|---|
| 1.1 | **Wall C — the ~70 plain-produce/verify + test/demo call-sites** (`sdk/full_turn_proof.rs` impl + `node/turn_proving.rs` ×27 + tests/perf/wasm/verifier). | Most need NO edit now — they pass `rotation: None` = byte-identical v1; the flip to rotated-default IS the C5 regen act. Audit each, edit only the live producers. | M |
| 1.2 | **The two SIBLING hand-AIRs** `CrossSideExistenceAir` + `BundleTreeFoldAir` (CG-5 cross-side-existence + proof-of-proofs, same file as the retired bilateral AIR; they do NOT read `effect_vm::pi`). | A Lean-emission lane for them (NEW IR2 constraint kinds, law #1) — **IN FLIGHT** per HORIZONLOG. Retiring the whole `bilateral_aggregation_air.rs` FILE is gated on emitting these two. | M |
| 1.3 | **C3 note-spend honest boundary** — the rotated 38-PI omits `NOTESPEND_NULLIFIER` (offset 198), so a note-spending turn with a freshness binding stays on v1. | Expose the nullifier in-PI on the rotated note-spend descriptor (a Lean re-emit), then drop the v1 freshness/capability arms. Until then it is a NAMED dual-path boundary, not degraded. | M |
| 1.4 | **`verify_sovereign_witness_stark`** (the OTHER live sovereign verify leg, `execute.rs:798`) stays on v1 `EffectVmAir` — no matched rotated producer. | Rotates WITH the FLOW-B / witness producer or retires at C7; NOT in isolation (verify-without-producer brick). | S |
| 1.5 | **C5 regen** — `EmitAllJson → v3Registry` default, re-pin ~58 artifacts/11 drift guards, re-emit the R=16 staged-probe → R=24, reseed FFI. | The regen recipe is in `ROTATION-CUTOVER.md §EXEC.3`; mechanical AFTER 1.1–1.3. | M |
| 1.6 | **C7 DELETE v1 + grep-zero** — `effect_vm_p3_full_air.rs`, `effect_vm/air.rs`, 186-col `generate_effect_vm_trace`, `ACTIVE_BASE_COUNT`, `CutoverFallback`, v1 `lean_descriptor_air.rs`, ~40 test harnesses. | `grep_zero_checklist` in `ROTATION-CUTOVER.md §EXEC`. End state = ONE path. | M |
| 1.7 | **THE ONE VK EPOCH** — the coordinated cutover-settle, **batched with the notify Step-2 felt-encoders** (`docs/NOTIFY-CASCADE.md`, `NOTIFY-STEP2-VK-CHECKLIST.md`). | The main-loop SETTLE act; a single VK bump carrying rotation regen + notify badge-mask + cap-leaf re-pin. | L |
| 1.8 | **#103 cap-crown sovereign-path graduation** (DECIDED: shape (i)) — cut `cipherclerk.execute_sovereign_turn_with_proof` + `proof_verify.rs::verify_and_commit_proof` off the bespoke `EffectVmAir` onto the rotated `Ir2BatchProof`, retire the legacy cap arm (`air.rs:1365-1374`). | Now a C5/C7 flip TASK — lands in-circuit non-amplification EVERYWHERE. (Latent: only in-repo tests drive the bespoke path today; not a shipped-node hole.) | M |

> **Why this is one lane, not a swarm:** `prove_full_turn` mints the very proof the
> recursion + aggregation + executor surfaces ingest. The wire shapes are ONE knot;
> parallel editors would collide irreversibly. The main loop drives it across
> relaunches until v1/v2 is gone and the tree is green.

---

## 2. THE WIDE-SAFE PRODUCT SURFACE — the swarmable bulk (NOT cutover-gated)

*All of §2 lives in root-`exclude`d workspaces (`wasm`, `pg-dregg`,
`sel4/dregg-firmament`), separate workspaces (`starbridge-v2/`, `sel4/` PDs), the
static `site/`, or additive-Lean modules that do not churn the VK. Each lands by its
own `cargo test` / `lake build` against the real embedded executor. **This is where
the next waves spend most of their swarm width.***

### 2a. starbridge-v2 (the native gpui master interface / the ADOS + desktop cockpit)

*Where: `starbridge-v2/` (own workspace). 183 lib tests green; the window opens via
gpui `runtime_shaders`. The `embedded-executor` feature compiles.*

| # | Unfinished | Closure lever | Size |
|---|---|---|---|
| 2a.1 | **The four-surface killer-demo cut** (`[headline]`, FRONTIER-ROADMAP N5) — wire mint → agent turn → notify handoff → the dual refusal as a `--headless` self-check + a SWARM-tab live path, + the N2 Tier-B read for step 5. | All in already-green crates; **the demo IS the pug evaluation artifact**. Depends on N1+N3+N4 (the budget meter + dispatch bar + notify coordinator). | M |
| 2a.2 | **The swarm budget meter + the Stingray ceiling weld** (N1 → N9) — per-member `spent`/`ceiling`, refuse a breaching dispatch BEFORE the turn; then replace the floor model with a real `dregg_coord::StingrayCounter` so "the swarm spent ≤ B" is *provable*. | Pure headless weld over `SwarmActionOutcome` computrons; N9 lifts it to a conservation bound. | S→M |
| 2a.3 | **The swarm dispatch bar** (N3) — generalize the 3 hardcoded demo verbs into a `SwarmDispatch` builder + `Swarm::can_reach(agent,target)` reading the live c-list (grey unreachable, predict the refusal) + ⌘K palette commands. | The keystone that turns the demo panel into a driving surface. | M |
| 2a.4 | **The notify-edge swarm coordinator, end-to-end** (N4) — widen the tested emit→inbox→async-drain shape to the full N-member coordinator loop. | `NotifyAuthority`/`NotifyOrgans` landed axiom-clean; keep this slice VK-free (badge-mask rides C1). | M |
| 2a.5 | **The narration-vs-truth panel** (N6) — a first-class view putting a member's CLAIMED action next to the executor's receipt (or its absence) and flagging divergence. | Pure UI over `Swarm::action_log` + dynamics. (Full claim↔turn correlation needs R1, the tool-call→effect compiler; the divergence panel ships now.) **The sharpest single ADOS feature.** | S |
| 2a.6 | **The surface op-verbs as turns / desktop R1** (N7) — a surface `FactoryDescriptor` + `present()` as a real turn with anti-ghost teeth (overpaint/label-spoof/double-focus REJECT) + `SurfaceDamaged` dynamics + a gpui panel; companion `Compositor` `AppSpec` via the `VerificationToolkit`. | T1–T4 are Lean theorems over the scene graph today, zero new axioms; the framebuffer last-hop is R5. | M |
| 2a.7 | **Per-member authorization boundary + coordination graph + cipherclerk lineage strip** (N16/N17/N18) — render each member's full held mandate + CAN/CAN'T boundary, the notify-arrow graph, the macaroon attenuation lineage. | Render welds over existing models (`agent.rs::AgentActivity`, the deposited `NotifyEdge`s). | M |
| 2a.8 | **Organ OPERATING verbs** (open/draw/repay/settle/close) — the live state is reflected; to DRIVE organ ops from the cockpit, bridge `World` → an `AgentRuntime`-shaped surface over the same ledger (no dregg-core change). | Both organs are embed-core; the lane is the World↔AgentRuntime bridge. | M |
| 2a.9 | **Live node connection + native federation panel** — move reads to gpui's async executor; wire `/api/events/stream` SSE into `ReceiptInspector` with `cx.notify()` (snapshot today); a `NodeClient::Http` panel (reqwest is sel4-thin-gated for now). | Makes the channel/mailbox/court organs LIVE reflections + an `n>1` window. | M |
| 2a.10 | **single-source wire types** — replace `starbridge-v2/src/model/` hand-mirrors with a shared `dregg-wire-types` crate depended on by both node + shell. | Anti-drift hygiene; a new tiny crate. | S |
| 2a.11 | **finish-the-window (HOST gap, not a crate defect)** — the runtime-shader path opens the window; the offline Metal Toolchain download is blocked by a damaged Xcode `DVTDownloads.framework`. | Provision the Metal Toolchain on a healthy Xcode (ahead-of-time shaders). Not a code lane. | XS |

### 2b. pg-dregg (postgres as the fifth surface)

*Where: `pg-dregg/` (standalone workspace, own target). Tier A/B/C + C-write live on
pg17/pg18; M2 mirror + the §11 write outbox landed. The range-attest SRF SHAPE + the
federation subscriber re-validation are BUILT (core green, 50 tests + 2 `#[pg_test]`s).*

| # | Unfinished | Closure lever | Size |
|---|---|---|---|
| 2b.1 | **The node-side queue drainer (close the C-write loop)** (S1, "highest leverage") — `dregg_submit_turn` enqueues into `dregg.submit_queue` but there is NO drainer; status never walks `pending → executed\|refused`. | A node `LISTEN/NOTIFY` loop tailing `submit_queue` → `execute_via_producer` → write back `status` + `receipt_hash`/`error`. A new node service module. **TOUCHES node/ — sequence in a node-touching wave, not the pure-pg lane.** | M |
| 2b.2 | **The proof-gate circuit-link S1–S3** — **S1** serialize `circuit::ivc_turn_chain::WholeChainProof` (holds plonky3 proof objects, NOT serde today — needs derives + a versioned envelope); **S2** a node-side proof PRODUCER folding finalized turns → a `dregg.turn_proofs` table; **S3** the `tier-c` `dregg-circuit` dep (Lean-FREE) flips `verify_serialized_proof` from the fail-closed stub to real `verify_turn_chain_recursive`. | Until S1–S3 the SRF attests NOTHING (safe direction). **S1 is the SHARED lever** with web items 4.2/4.3 (the recursion-proof serialization). TOUCHES circuit/ — co-sequence with the cutover-settle or after. | L |
| 2b.3 | **In-SQL dev minting + issuer-status discoverability** (S3/N19) — `dregg_dev_mint(subject, actions[], resource_prefix, ttl)` + a loud `dregg_issuer_status()` so "no key ⇒ everything denies" is discoverable not silent. | Standalone-workspace, dev path only; production mint-out-of-database stays default. | S |
| 2b.4 | **The cap-gated query cookbook + caps-as-rows explorer** (S4/N15) — parameterized RLS views + recursive queries (delegation tree `WITH RECURSIVE`, conservation check, time-travel, receipt-chain walk with in-SQL non-omission `prev_root = lag(ledger_root)`, no-amplification audit). | Pure SQL + static docs, zero build risk. Reframes `site/explorer` as "your caps, as the rows you may read." | S |
| 2b.5 | **The fresh-clone build story** (S6/N21) — `pg-dregg/scripts/setup.sh` (checks `cargo-pgrx` + managed pg18, prints exact install commands, installs the extension, sets the dev issuer key, runs `e2e-live.sh`). | Handoff-readiness; turns "we built a pile" into "a stranger can evaluate it." | S |
| 2b.6 | **Tier D spike: `dregg_submit_turn_inproc`** (S2 north star) — the executor as a pg function; one transaction mutating dregg kernel state AND app tables atomically. | Gated on linking the Lean executor into a postgres backend = the same FFI maturity as R0/the executor-PD. Decides feasibility (side-effect surface / palloc lifetime / proving stays off-txn). | XL |
| 2b.7 | **DreggDL node `POST /deploy` ingress** (HORIZONLOG) — a node endpoint accepting a DreggDL doc → `dregg-deploy::check` → lower + submit per-root turns → return receipt chain. | TOUCHES node/; the static check is the pre-submission gate, the executor stays the trust boundary. | M |

### 2c. web-forward (dregg in the browser)

*Where: `wasm/` (root-excluded) + `site/` (static) + `sdk-ts/`. The in-tab `DreggRuntime`
world, the in-tab light-client fold+verify, and the `@dregg/sdk/browser` door all ship.
The MV3 extension front door is largely DONE. Docs: `WEB-FORWARD-EVERYWHERE.md` (a–f).*

| # | Unfinished | Closure lever | Size |
|---|---|---|---|
| 2c.1 | **The web surface binding in `dregg-wasm`** (N10) — ~5 `#[wasm_bindgen]` fns mirroring `surface.rs`: `open_surface`/`present`/`share_surface` (a real `GrantCapability` turn; widening REJECTS)/`revoke_surface`/`surface_identity`. | Same shape as the ~80 bindings already in `bindings.rs`. Carries `Target::Surface` to the tab. | S |
| 2c.2 | **The browser compositor module** (N11) — a gpui-free DOM scene-graph: ordered surface list, each pane to a `<canvas>` with compositor-drawn identity chrome (T2 from N10, NEVER the page's), DOM focus/pointer routed to the focused pane (T3), T1 non-overlap on `present`. | The firmament-to-pixels weld in the browser; port the proven float/tile/stack layouts. | M |
| 2c.3 | **The proving Web Worker** (a) — move the ~150s prove off the main thread into a `prove-worker.js` + a `ProvingClient` promise wrapper. | Pure-frontend + build change; fixes RESPONSIVENESS (not latency — latency lever is #169 + threaded FRI behind COOP/COEP). | S |
| 2c.4 | **`verify_devnet_history` in-tab (the EXTERNAL-aggregate path)** (b/N12) — a tab verifies a history someone ELSE produced against a config-pinned anchor, no local proving. | **Blocked on the SHARED lever: a fork-side serialization of `WholeChainProof.root`** (an `Rc<CircuitProverData>` with no serde today). Same lever as pg 2b.2/S1 + the `n>1` half of (f). Until it lands, `light_client_demo` (fold+verify, no transport) is the runnable tooth. | L |
| 2c.5 | **The browser AS a light-client node** (c) — compose the SSE wire + `verify_devnet_history` into an in-tab object that tracks the chain head HAVING CHECKED it. | Gated on 2c.4's envelope; a browser is a verifying LEAF, never a gossip validator (the honest n-bound). | M |
| 2c.6 | **A PWA / installable web app** (d) — a `manifest.webmanifest` + a service worker precaching the app shell + wasm + playground sections (the local `n=1` world runs fully offline). | Pure-frontend; devnet reads degrade to "last attested checkpoint" offline (the outbox queues turns, never commits offline). | S |
| 2c.7 | **The SDK two-noun browser front door + `SurfaceClient`/`AttestedHistory` TS types** (N14/f) — finish `sdk-browser-ed25519-webcrypto`; a TS `SurfaceClient` over the wasm surface bindings; an `AttestedHistory` type over `verify_devnet_history`. | Bind, do not rebuild; authorization stays inescapable (no `Unchecked` in the public API). | M |
| 2c.8 | **The web killer-demo playground page** (N13) — wire N10+N11+N12 into `site/playground` as "two tabs, one surface, the share that REFUSES" + run `verify_history`. | The copy-paste end-to-end web story for the pug handoff, reachable from a URL. | S |
| 2c.9 | **Extension deepening + store distribution** (e) — a one-call `window.dregg.turn(builderSpec)` mirroring the SDK two-noun shape; bundle the surface bindings; Chrome Web Store submission (manual unpacked-load only today). | `.turn()` from a page stays MEDIATED through the clerk (the security property); store submission is packaging, not a code gap. | S |

### 2d. The integrator-wedge apps + the apps-polish lane (the lamesauce refutation)

*Where: `metatheory/` additive-Lean + `starbridge-apps/` + `sdk/`. The two crown
integrator apps (`AgentOrchestrationBudget`, `EscrowDeskCouncil`) landed; polis is real
(factory-born governance cells, executor-enforced, e2e teeth).*

| # | Unfinished | Closure lever | Size |
|---|---|---|---|
| 2d.1 | **The integrator-wedge apps as runnable SDK demos** (N20) — extend the two crown apps into copy-paste SDK demos exercising the cross-cell-import crown + the new cell-program atoms (`senderMemberOf`/`affineDeltaLe`/`balanceDeltaLe-Ge`). | The concrete proof real apps don't scream "toy"; additive-Lean + SDK. | M |
| 2d.2 | **Rebuild the weak toy apps on the new expressiveness** (apps-round-2, LIVE per REORIENT) — the language uplift (sender/context atoms, composite gates) lets the toy apps express real policy. | Per-app; uses the landed `Exec/Program.lean` atoms. | M |
| 2d.3 | **escrow-market follow-ups** — (a) no-burn equality is settle-scoped in `child_program_vk` but NOT in the flat installed `state_constraints` (teach factory-birth to use the cell's `Cases` program OR a settle-gated relational atom); (b) real ledger-balance binding (ESCROWED/RELEASED/REFUNDED are slot ints, not moved balance — wire settle to a real value transfer). | TOUCHES starbridge-apps/ + turn/ (post-flip). | M |
| 2d.4 | **userspace-verify as the app-level customer** — escrow's `released+refunded==escrowed` conservation is the first app customer for the static checks; lift to a published checker (same shape for agent-provenance `verify_chain` + bounty-board monotonicity). | Depends on the landed `dregg-userspace-verify` toolkit. | S |
| 2d.5 | **privacy-voting ballot unlinkability** (named in its README) — the app gives one-vote-per-ballot + monotone tallies, NOT ballot/voter unlinkability (no mixnet/nullifier-set). | A separate, stronger lane (true secrecy); named scope-limit today. | L |
| 2d.6 | **stub dirs decision** — `compute-exchange/` + `gallery/` carry only a `manifest.json` (no crate). | Build them or delete the stubs (ember-decision, HORIZONLOG). | XS |
| 2d.7 | **polis factory-birth co-location** — polis's executor-path teeth live in `sdk/tests/polis_*_e2e.rs`, not a `polis/tests/factory_birth.rs` like the other apps. | Co-locate a birth test to make it self-contained. | XS |

### 2e. The SDK polyglot + DreggDL + analyzer closures

*Where: `sdk-ts/`, `sdk-py/`, `dregg-deploy/`, `dregg-userspace-verify/`, `dregg-analyzer/`.*

| # | Unfinished | Closure lever | Size |
|---|---|---|---|
| 2e.1 | **sdk-ts organ-noun crypto closures** — three crypto ops stay node/wasm-side (pure TS has no Poseidon2/X25519/STARK): mailbox dequeue-proof verify, channel X25519→HKDF→ChaCha20-Poly1305 seal/open, `AttestedQuery` STARK+threshold-sig check (the light-client crown, likely waits on a wasm `verify_full_turn` export). | (a)+(b) are the first users of `@dregg/sdk/wasm`; (c) shares the wasm-verify lever. | M |
| 2e.2 | **userspace-verify TS/Py binding** — expose `analyze()` to TS/Py so the SDKs call it pre-submission (a cheap JSON-shell path or an integrated `#[no_mangle]` FFI cdylib). | `Assurance`/`Finding`/`Locus` are already Serialize+Deserialize; the lane is the glue + an SDK `analyze()` sugar at `.sign()`-time. | M |
| 2e.3 | **sdk-py self-contained wheel** — package the Py binding as a standalone wheel bundling libdregg. | Packaging (the FFI archive is the offender). | M |
| 2e.4 | **dregg-analyzer live-capture hooks + Studio binding** — a node trace-export mode emitting `BlocklaceCapture`/`ReceiptStrandCapture`/`WalCapture`; render the `AnalysisReport` in the shell. | The on-disk/wire types are already exact (a thin dump endpoint); the report is JSON-serializable. TOUCHES node/. | M |

### 2f. Handoff readiness (the pug bar — "works without ember in the loop")

*Where: docs + `QUICKSTART.md` + `site/` + `bootstrap.sh`. Judged by a stranger reaching
a useful, surprising, trustworthy result in minutes.*

| # | Unfinished | Closure lever | Size |
|---|---|---|---|
| 2f.1 | **FRESH-CLONE BUILD must be ONE documented command** — the FFI archive seeding (elan on PATH, lake build, seed-dregg2-closure.sh) is tribal-knowledge-heavy and bit us twice. | One documented command (or `build.rs` does it) with a loud, teaching failure mode. The single sharpest handoff blocker. | M |
| 2f.2 | **QUICKSTART re-verified POST-ROTATION** — it was verified pre-rotation; every command actually re-run after the organs + rotation. | Re-run + fix; gated on the cutover landing for the proof-path commands. | S |
| 2f.3 | **The evaluator's README** — what dregg IS / the guarantees (AssuranceCase in human terms) / the honest scope / the first ten minutes. | Stranger-usable, four questions up front. | S |
| 2f.4 | **The organs reachable as a STRANGER would** — SDK two-nouns + trustline/channel/mailbox/storage each with a copy-paste example that runs against a local node; error messages that teach. | Per-organ examples; the site/playground consistent with the shipped system. | M |
| 2f.5 | **One real end-to-end story pug can run start-to-finish** — two agents · trustline · channel · mailbox (money moves, messages flow, a removed member goes dark, every receipt checkable). | The demo IS the evaluation artifact (overlaps the four-surface demo 2a.1). | M |

---

## 3. THE l4v BINARY BRIDGE (the assurance frontier)

*Where: `turn/` (Stage 0) then spec→binary. Docs: `ASSURANCE-CRITIQUE.md §5`, Stages 0–6.
The Lean composition is strong (`deployed_system_secure` apex; unfoolability derives
conservation); the distance to l4v-grade is the binary bridge.*

| # | Unfinished | Closure lever | Size |
|---|---|---|---|
| 3.1 | **Stage 0 — make the verified executor authoritative** — invert `turn/src/lean_apply.rs:1143` so the Lean producer IS the executor, "no new mathematics." | The prerequisite for the binary bridge AND for Tier-D pg (2b.6) AND the seL4 service executor (§4). The highest-leverage l4v step. | L |
| 3.2 | **Stage 1 / CRITICAL-2 codec-in-TCB RESIDUAL (the RUST half)** — the Lean half is CLOSED (`Refine.lean` export-refines-model). Open: (1) translation-validation of `dregg-lean-ffi/src/marshal.rs` (a 2231-line hand-rolled mirror upheld by a differential, not yet a `marshal_turn_hosted = encodeWWire ∘ lift` THEOREM); (2) the Lean→C / `libdregg_lean.a` link boundary (no binary-correspondence statement). | Generate the Rust from Lean, or a verified-Rust mirror; the seL4 C-to-binary analogue. Disjoint from the proof-wire flip → post-rotation `dregg-lean-ffi/`. | L |
| 3.3 | **Stages 2–6** — discharge `leaf_sound` + empty the hand-AIR partition · tie the apex to one turn/history · native UC (CryptHOL-in-Lean) · `n>1` consensus that runs the ordering rule · config-pin the crypto floor. | Each a named stage; sequenced after Stage 0. Research-tier. | XL |
| 3.4 | **#93 proof-audit close** — declare `#assert_axioms` + non-vacuity-both-polarities + the Convergence gauntlet the successor to a separate harness. | WRITTEN UP as `docs/ASSURANCE.md §4`; awaiting ember's flip to close. | XS (decision) |

---

## 4. THE seL4 / ROBIGALIA SUBSTRATE (the deployment-shares-the-thesis frontier)

*Where: `sel4/` (its own workspaces) + `dregg-tui/`. The five-PD assembly BOOTS; a real
STARK is verified on-device; a real virtio NIC is brought up; one verified turn has run
inside a PD (`status:2 ok:1`, byte-identical receipt). Docs: `ROBIGALIA-ROADMAP.md`,
`SEL4-EMBEDDING.md`, `RBG-TO-SEL4.md`.*

| # | Unfinished | Closure lever | Size |
|---|---|---|---|
| 4.1 | **The Lean runtime bottom-half port residue → a SERVICE** — one turn boots; to become the `dregg.system` heart seat: (a) wire the real Poseidon2/BLAKE3/Ed25519 crypto floor (the demo stubs it); (b) the turn-stream service loop (block on `net→executor`, decode, step, stage `commit_out`, signal persist); (c) the runtime-shape decision (root-task today vs a Microkit-PD musl substrate — a project-lead call); (d) the GMP decision (full ELF-GMP vs a fixnum-only shim); (e) image shrink (285 MB → dead-data GC). | Named, scoped work, not mystery. Gated AFTER Stage 0 (3.1) for "authoritative." Blocks the executor PD ONLY — the verifier PD runs real STARK today. | XL |
| 4.2 | **sel4 cross-build tail** (verifier-PD scaffolded, `no-lean-link` PROVEN Lean-free) — the actual cross-build to `aarch64-sel4-microkit` (Microkit SDK + rust-sel4 toolchain) + `getrandom`-custom / `p3-maybe-rayon` serial-fallback for the bare target. | The verifier PD is UNBLOCKED — this is the toolchain wiring. | M |
| 4.3 | **persist PD over a raw block cap** — the device cap lands solely in the persist PD; `redb`'s `StorageBackend` over a block cap; then PD-checkpoint ↔ dregg-snapshot wiring on the already-verified `snapshot.rs` model. | The snapshot model is done + verified; the lane is the block-cap backend. | L |
| 4.4 | **The 2-PD net assembly** — a smoltcp client PD (DHCP/echo → turn ingress) + the shared-ring channel + the Ed25519 de-envelope boundary (parse the `SignedTurn`, verify the sig BEFORE the executor sees it). | The NIC is up; this turns "the NIC is up" into "a turn arrives over TCP." The rust-sel4 `http-server` example is the canonical assembly. | L |
| 4.5 | **The next rbg→seL4 cap ports** — SturdyRef→badged-endpoint, ScopedIntentPool→badged-endpoint (the first port `DirectoryFactory → seL4_Untyped_Retype` is DONE; M2 boots). | Additive, NOT gated on the Lean-runtime blocker; a `sel4/factory-pd/` sibling. | M |
| 4.6 | **A single-node devnet image** — `net → executor → persist` wired, verifier isolated, caps partitioned. | A legitimate milestone (the `n=1` target collapses the distributed bounds); gated on 4.1+4.3+4.4. | XL |
| 4.7 | **starbridge-v2 seL4 backends** — a gpui renderer targeting a framebuffer cap + a `NodeClient::Channel` over an seL4 endpoint (same contract over IPC not TCP). | The SEL4-EMBEDDING end state for the shell; gated on the framebuffer-cap story (R5). | L |

---

## 5. THE DISTRIBUTED / `n>1` FRONTIER (the bounds relax along n)

*Where: `net/` + `node/` consensus + the distributed-Servo design. An n=3 slice runs the
ordering rule; the single-machine `n=1` collapse is first-class and its bounds ARE honest
distributed bounds. Docs: `STAGE5-CONSENSUS-DEVAC.md`, `DISTRIBUTED-SERVO.md`.*

| # | Unfinished | Closure lever | Size |
|---|---|---|---|
| 5.1 | **S5-1 — the gossip-dissemination blocker (THE consensus blocker)** — the running node does NOT yet COMMIT a turn through the rule at n≥2: `latest_height` stays 0, `is_super_ratified` never fires, because eager/lazy Plumtree over unidirectional QUIC streams delivers blocks ASYMMETRICALLY at small N. NOT the rule (verified), NOT the Lean (non-vacuous) — a deployment-fidelity gap. | Make the eager set bidirectional / drive frontier-pull to drain orphans before each wave / eager-push to ALL committee peers. Acceptance test EXISTS (`three_node_ordering_rule.rs` [C] via `DREGG_TEST_REQUIRE_FINALITY=1`). TOUCHES net/gossip + blocklace + node/blocklace_sync. | L |
| 5.2 | **S5-2 … S5-6** — live commit refinement · #170 quorum-consumer migration · the consensus leg of the composed apex · equivocator Lean↔Rust differential pin · finality-on-demand. | Each sequenced after S5-1. | L |
| 5.3 | **#170 quorum unification** — ONE formula (blocklace supermajority vs federation `quorum_threshold`) + WAN peer fixes; the unified `supermajorityThreshold` Lean twin LANDED — migrate the consumers (`BlsQuorumCert.lean`/`EpochReconfig.lean`/`MembershipSafety.lean`). | Migrate onto `QuorumThreshold.lean`; the differentials pin the relations until migration. | M |
| 5.4 | **#171 remote `.turn()` submission** — agent/page turns route THROUGH a node (signed-envelope adoption), never straight to the wire. | The signed-envelope adoption seam; the extension already does page → clerk → node. | M |
| 5.5 | **Distributed-Servo (the web-of-cells)** — a link IS a sturdy ref, a fetch IS a verified turn (the `AttestedResource` envelope); co-presence (per-DOM-region caps); agent-driven federated history; render/display slid apart along `n`. | Most of the substrate ships (netlayer + sturdy refs + attestation + the distance param); the genuinely-new pieces are the `AttestedResource` envelope + the OCapN Syrup adapter (2–4 wk) + Willow range-reconciliation (a bounded build on the receipt-stream Merkle tree). Gated behind the single-node Servo embed (§2c / EMBEDDED-WEB-SURFACE). | XL |
| 5.6 | **Eclipse hardening at scale + Willow geometry** — peer_score buckets by SocketAddr today (add /24·/48 prefix + AS-diversity); Reed–Solomon erasure (swap the XOR prototype); real Merkle-path chunk proofs; range-based set reconciliation (the shared anti-entropy + storage partial-sync primitive). | Adopt the Willow geometry, keep our proofs; sequenced after S5-1. | L |

---

## 6. THE FOUR-ASPECT AUTHORIZATION INTEGRATION (the deepest open DESIGN thread)

*Where: `metatheory/` + macaroon/cap-crown. Docs: `AUTHORIZATION-MODEL.md`,
`CIPHERCLERK-AUDIT.md`.*

| # | Unfinished | Closure lever | Size |
|---|---|---|---|
| 6.1 | **R6 — integrate biscuit/macaroon/cap/zk into ONE proven arrow** — the agent MACAROON layer (federation-membership) and the kernel CAP-CROWN (in-circuit `granted ⊆ held`, #103) are UNINTEGRATED; non-amplification is told as two informal stories. | **Guardrail: integrate the four aspects, do NOT reduce them; the cipherclerk is a sovereign executor BY DESIGN.** Possibly extends #103. The deepest open thread. | XL |
| 6.2 | **#103 Phase-D 4-ary-vs-sorted membership-leg (retire-or-keep)** — the 4-ary c-list `membership` leg is DEAD on the live path (only `cap_membership` has a live producer); the sorted leg SUBSUMES the cap-authority claim. | ember-ratify: keep the 4-ary leg as the GENERAL-membership primitive but DON'T couple it to cap-gated turns; OR demote it to a labelled "no live producer" Research status. Characterization only today. | XS (decision) |

---

## 7. THE LEAN RESEARCH PILLARS (explicitly not scheduled)

| # | Unfinished | Closure lever | Size |
|---|---|---|---|
| 7.1 | **UC-security / CryptHOL** (#31) + the research pillars (revocation / info-flow / metadata). | Native CryptHOL-in-Lean; the l4v Stage 4. | XL |
| 7.2 | **R8 — noninterference (the notify covert channel)** — a badge-OR wake is a one-bit info-flow leak; dregg has no noninterference argument yet. Sound as coordination, leaky as isolation. | The cockpit shows the topic (the leaking bit); a real noninterference argument is the pillar (#31/#99). | XL |
| 7.3 | **R2 — token/dollar budget binding** — the executor meters computrons, not API dollars. | A declared-cost debit + a price oracle; the conservation machinery is there, the dollar mapping is honest-future. | M |
| 7.4 | **R1 — the tool-call → effect compiler** — the universal `ToolCall → Vec<Effect>` adapter (one per provider). | An audited per-provider adapter with a golden-corpus differential, named as the trust boundary (a wrong mapping yields a faithful receipt of the wrong thing). The genuinely-new ADOS SDK boundary. | M |
| 7.5 | **R5 — the graphics crypto-floor (the last hop)** — bind the scanned-out framebuffer to the cell's `contentDigest` (F1 frame attestation / F2 IOMMU-DMA confinement / F3 verified GPU compositing; in-browser narrows to trusted-chrome + the iframe sandbox). | T1–T4 are theorems over the scene graph today; the frontier is honestly the I/O edge. | XL |
| 7.6 | **Transcendental-syntax S3/S5 · hypersystem/simplicial joint turns** (dregg4 vision). | Named, not scheduled. | XL |
| 7.7 | **Private-participant Rust turn role** (design + Lean landed: `PrivateLeg.lean`) — to SHIP: a private-participant leg in `coord/src/atomic.rs` (commitPre/commitPost/proof not an applied action) + a commit-path verify-gate (MixedAdmissible) + state-root continuity. | Crypto floor = STARK extractability (no new assumption). TOUCHES coord/turn, post-flip. | L |

---

## 8. The standing node/runtime closures (post-rotation tails)

*Real but small debts named in HORIZONLOG; mostly post-flip, TOUCH node/turn/persist.
Listed so they are scheduled, not parked.*

- **node recovery overlay first-writer-wins bug** — `state.rs` recovery uses `insert_cell`
  (strict), silently dropping a post-checkpoint write to a checkpoint-held cell; the
  convergence root-mismatch only LOGS. Fix = `upsert_cell`. → node/persist. **S, real bug.**
- **persist snapshot wire half** — in-crate ship/apply landed; REMAINS the node `GET
  /snapshot/{from}` serve + joiner consume route. → node. **M.**
- **checkpoint-prune → commit-log compaction** — `prune_before` trims attested roots but
  commit-log records below a finalized checkpoint are never compacted (unbounded WAL). Add
  `CommitLog::compact_below(height)`. → persist. **S.**
- **storage put/get HTTP route weld** — the in-crate availability route (erasure+dedup) is
  closed; REMAINS the node put/get route (storage-gateway-mandate gated) calling it. → node. **M.**
- **stale-cap c-list sweep** (channels residue) — a real verb gap, NOT a quick fix: sweeping
  a departed member needs cross-cell `Delegate` authority the operator doesn't hold. Closure
  = a new verb shape (member-initiated self-revoke or group-scoped revoke). → node/turn. **M.**
- **trustline pureCredit HTTP lane** + channel close / one-factory collateral / `dregg_extend_trustline`
  + multilateral rippling. → turn/node. **M.**
- **divergence-ledger doc churn** — `rust_lean_divergence_finder.rs:684` overwrites a
  git-tracked file on every run, dirtying trees + blocking persvati pushes. One-line fix
  (emit to a build-artifact path). → turn/. **XS, tree-dirty NOW.**
- **CLI `config init` not path-injectable** — hardcodes `~/.dregg`; honor `DREGG_HOME`. → cli/. **XS.**
- **Crypto/protocol artifacts** (bounded, post-rotation): DKG transport · ECVRF gauntlet +
  ticket serde · KERI gauntlet + per-cell openings · OCapN Syrup adapter · MLS/TreeKEM
  fan-out swap · proactive resharing. → federation/captp/node. **M each.**

---

# THE PAYLOAD — the proposed next 2–3 build waves (swarm-safe ordering)

The organizing principle is **the cutover gate** + **disjoint file sets**. The cutover is
ONE lane the main loop drives alone; everything else is partitioned so concurrent lanes
never share a churning file. The waves front-load the **four-surface killer demo** (the pug
evaluation artifact) because it is the highest-leverage thing a stranger runs to judge the
substrate, and it is entirely wide-safe.

> **Swarm-safety law (from the build graph):** the root workspace `exclude`s `wasm`,
> `pg-dregg`, `sel4/dregg-firmament`; `starbridge-v2/` and the `sel4/` PDs are their own
> workspaces; `site/` is static; additive-Lean modules don't churn the VK. Lanes in
> DIFFERENT such buckets are swarm-safe concurrently. Lanes that TOUCH the shared root
> workspace's churning files (`circuit/`, `turn/`, `cell/`, `node/`, `metatheory/`'s
> apex modules) must be **sequenced** or scoped to disjoint files. The cutover lane owns
> `circuit/`+`turn/`+`cell/` proof-path files alone.

---

## WAVE 1 — "the killer demo + the cutover, in parallel" (front-load the pug artifact)

*Goal: a stranger can run the four-surface demo and the web demo end-to-end; the cutover
advances toward grep-zero. Six concurrent buckets, each its own workspace/target.*

| Lane | Bucket (swarm-safe) | Items | Why first |
|---|---|---|---|
| **L1 — the cutover** (main loop, ALONE) | `circuit/`+`turn/`+`cell/` proof-path | §1: wall C (1.1) · the two sibling hand-AIRs (1.2) · then C5/C7 (1.5/1.6/1.8) | The dominant gate; everything proof-path-touching waits on it. |
| **L2 — starbridge-v2 demo spine** | `starbridge-v2/` (own ws) | 2a.2 (budget meter) → 2a.3 (dispatch bar) → 2a.4 (notify coordinator) → 2a.5 (narration-vs-truth) → **2a.1 (the four-surface demo cut)** | The headline pug artifact; entirely wide-safe. |
| **L3 — web demo spine** | `wasm/` (excl) + `site/` (static) + `sdk-ts/` | 2c.1 (wasm surface binding) → 2c.2 (browser compositor) → 2c.8 (web killer-demo page) · 2c.3 (proving Worker) · 2c.6 (PWA) | The web evaluation artifact; the in-tab `n=1` world is already real. |
| **L4 — pg wide-safe** | `pg-dregg/` (own ws) + SQL/docs | 2b.3 (dev mint) · 2b.4 (query cookbook) · 2b.5 (fresh-clone setup) | Pure-pg + SQL, zero `./target` contention; makes step 5 of the demo a true query. |
| **L5 — apps + handoff docs** | `metatheory/` additive-Lean + `starbridge-apps/` + docs | 2d.1 (wedge apps as SDK demos) · 2d.2 (rebuild toy apps) · 2f.3 (evaluator README) · 2f.4 (organ examples) | Additive-Lean + docs; the lamesauce refutation + the handoff bar. |
| **L6 — node-touching closures** (ONE node lane) | `node/`+`turn/`+`persist/` (sequenced) | 8: the recovery upsert bug (real) · the snapshot serve route · the WAL compaction · the divergence-ledger one-liner | A SINGLE node lane (these share `node/`); the real recovery bug + the tree-dirty one-liner are the priorities. |

**Sequencing note:** L1 and L6 both touch `turn/` — L6 is scoped to node/persist/recovery
files DISJOINT from L1's proof-path files (`lean_apply.rs`/`full_turn_proof.rs`/
`turn_proving.rs` are L1's; `state.rs`/`snapshot.rs`/recovery are L6's). If a collision
risk is unclear, the main loop sequences L6 after L1's current commit.

---

## WAVE 2 — "the cutover settles + the surface deepens" (the VK epoch + the n=1 product)

*Goal: v1 is deleted, the VK epoch lands (batching notify), and the wide-safe surface
deepens to the full developer journey. Gated on WAVE 1's L1 reaching C5-readiness.*

| Lane | Bucket | Items | Gate |
|---|---|---|---|
| **L1′ — THE VK EPOCH** (main loop, ALONE) | `circuit/`+`cell/`+ registry + notify felt-encoders | §1.7 the ONE VK epoch · 1.3 (note-spend in-PI) · 1.4 (sovereign witness leg) · the cap-crown sovereign graduation (1.8 finish) · C1 notify badge-mask drop-in | The cutover-settle; the held notify Step-2 tail rides here. |
| **L2′ — starbridge-v2 desktop R1 + organs** | `starbridge-v2/` | 2a.6 (surface op-verbs as turns) · 2a.7 (auth boundary + coord graph + lineage) · 2a.8 (organ operating verbs) · 2a.9 (live node connection) · 2a.10 (wire-types crate) | Wide-safe; the desktop face deepens past the demo. |
| **L3′ — web light-client + SDK face** | `wasm/`+`site/`+`sdk-ts/` | 2c.7 (SurfaceClient + AttestedHistory TS) · 2c.9 (extension `.turn()` + store) · 2e.1 (sdk-ts organ crypto closures, the wasm-verify users) · 2e.2 (userspace-verify TS/Py) | Wide-safe; some items wait on the SHARED recursion-proof serde lever (see L4′). |
| **L4′ — the recursion-proof serde lever + pg proof-gate** | `circuit/` serde (post-L1′) + `pg-dregg/` + `node/` | 2b.2/S1 (serialize `WholeChainProof`) → unblocks 2c.4/2c.5 (in-tab external verify) AND the pg proof-gate S2/S3 AND the `n>1` half of 2c.7 · 2b.1/2b.7 (queue drainer + DreggDL ingress, node-side) | **ONE lever (the recursion-proof serialization) unblocks THREE consumers** — do it once, here, after the VK epoch settles `circuit/`. |
| **L5′ — apps polish + analyzer + sdk-py** | `starbridge-apps/`+`turn/`(post-flip)+`dregg-analyzer/`+`sdk-py/` | 2d.3 (escrow follow-ups) · 2d.4 (userspace-verify customer) · 2e.3 (sdk-py wheel) · 2e.4 (analyzer capture + Studio binding) | Mostly wide-safe; escrow's settle-binding is post-flip. |
| **L6′ — l4v Stage 0** (the assurance lever) | `turn/` (post-cutover) | 3.1 (invert `lean_apply.rs:1143` — executor authoritative) | "No new mathematics"; UNBLOCKS Tier-D pg (2b.6) + the seL4 service executor (§4). The single highest-leverage assurance step. |

---

## WAVE 3 — "distribution + the substrate + the deep research" (the n>1 + seL4 + l4v frontier)

*Goal: the bounds relax along `n` for real, the seL4 substrate carries a service, and the
deep research pillars open. These are the L/XL frontiers; sequence by their blockers.*

| Lane | Bucket | Items | Gate |
|---|---|---|---|
| **L7 — consensus n>1** | `net/`+`blocklace/`+`node/blocklace_sync` | **5.1 (S5-1 gossip dissemination — the blocker)** → 5.2 (S5-2…6) · 5.3 (#170 quorum migration) · 5.4 (#171 remote `.turn()`) | S5-1 is the keystone; the acceptance test EXISTS (`DREGG_TEST_REQUIRE_FINALITY=1`). |
| **L8 — the seL4 service executor** | `sel4/` (own ws) | 4.1 (Lean-runtime residue → service: crypto floor + service loop + runtime-shape + GMP + image shrink) · 4.2 (cross-build tail) | Gated AFTER L6′ Stage 0 for "authoritative"; the verifier PD is unblocked NOW. |
| **L9 — the seL4 node organs** | `sel4/` | 4.3 (persist block-cap) · 4.4 (2-PD net assembly) · 4.5 (rbg cap ports) → 4.6 (single-node devnet image) | Sequenced after L8's service loop. |
| **L10 — the authorization integration** | `metatheory/` (additive, then apex) | 6.1 (R6 four-aspect integration — the deepest DESIGN thread) · resolve 6.2 (4-ary leg) | An ember-steered design lane; possibly extends #103. |
| **L11 — distributed-Servo + Willow** | `wasm/`+`captp/`+`net/`+a new Servo embed | 5.5 (the `AttestedResource` envelope + OCapN Syrup adapter) · 5.6 (Willow range-reconciliation + eclipse hardening) · the single-node Servo embed (EMBEDDED-WEB-SURFACE) | Gated behind the single-node Servo `WebView`-as-cap embed; the envelope reuses the receipt-stream Merkle tree. |
| **L12 — the research pillars** | `uc-crypthol/`+`coord/`+`metatheory/` | 7.1 (UC/CryptHOL) · 7.2 (noninterference) · 7.4 (R1 tool-call compiler) · 7.7 (private-participant Rust role) · 7.5 (graphics floor) | Explicitly Research-tier; each named with its lever. |

---

## The honest sequencing summary

1. **The cutover is the spine of WAVE 1+2** and is driven by the main loop ALONE — it is
   one irreversible knot, NOT a swarm target. Everything proof-path-touching waits on it.
2. **The four-surface killer demo (L2/L3) is front-loaded** because it is the pug
   evaluation artifact and is entirely wide-safe (separate workspaces + static site).
3. **ONE lever — the recursion-proof serialization (2b.2/S1)** — unblocks the in-tab
   external verify, the pg proof-gate, AND the `n>1` SDK surface. It is scheduled ONCE in
   WAVE 2 (L4′), after the VK epoch settles `circuit/`.
4. **l4v Stage 0 (executor authoritative)** is the highest-leverage assurance step and the
   prerequisite for BOTH Tier-D pg and the seL4 service executor — scheduled at the end of
   WAVE 2 so WAVE 3's XL substrate frontiers can build on it.
5. **The deepest DESIGN thread (R6, four-aspect authorization)** and the deepest RESEARCH
   pillars (UC, noninterference) are WAVE 3 — named, levered, not parked, but honestly
   behind the product surface and the cutover.

*Every line above is WORK with a lever, never a wall. The spine is real and proven; the
frontiers are the two big bridges (the cutover wire rewrite, the l4v binary bridge), the
four-aspect authorization integration, the seL4 service executor, the `n>1` dissemination,
and the graphics / Servo last-hops — each named with its lane and its rough size, ordered
so the swarm never collides and the pug artifact ships first.*

> *and a small poem, as is our custom:*
>
> *one knot at the center the main loop unwinds,*
> *while six wide lanes braid the demo to glass —*
> *the cutover settles, one VK epoch binds,*
> *and the frontier is work, with a lever, not a wall.*
> *( ◕‿◕ )*
