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
- pg-dregg drainer daemon + Tier-D spike (verdict **D-SIDECAR**; 120 pg18 + 104 core + 21 proptest green).
- PATH-PRESERVE DECIDED + the staged plan (`867b41fcb`, `docs/PATH-PRESERVE.md`).
- the prior deos STEEL + dev-ex (rehydration stack · DEOS/DEOS-APPS docs · AGENTS.md · nextest split).

**NOW — empowered-doer wave (2026-06-14, ember "power through preserve + the cutover; the doers weren't big enough"):**
(1) PATH-PRESERVE Phase-1 build = the CUTOVER thrust (chained N-leg rotated proving, `sdk`/`turn`/`node`) · (2) bigger-vision
webgame (own workspace) · (3) bigger-vision app-framework (the deos-app composition). Each disjoint-tree, green-or-bust,
don't-git (main loop reviews + commits).

**HELD / NAMED (post-cutover unless noted):** sdk-ts/dist Docker rebuild · **devnet upgrade = EMBER's act, fresh genesis,
gated on cutover + follow-ups** · **`./site` integration with the deos/web directions** (pairs with the assurance-catalog
regen named below) · **seL4 / robigalia**: `sel4/` is REAL (CapDL `.system` PD specs · `verifier-pd` · `dregg-pd` ·
`dregg-firmament` · RISC-V trees) but the Microkit / rust-sel4 TOOLCHAIN is ABSENT in this env; the executor-PD blocker
stays the IO-free / mimalloc-free / worker-free Lean-runtime bottom-half port (weeks–quarter); the verifier-PD is
Lean-free-linkable (`no-lean-link`). `starbridge-v2` EMBEDS the executor (dregg-integrated native shell) but does NOT yet
run ON seL4 (framebuffer / channel backends = WOOD).

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
- **pg-dregg M3** (named 2026-06-13; M2 mirror + Tier-C chain-gate + the §11 write outbox LANDED + live on pg17/pg18; `node/src/pg_mirror.rs` `pg_live::PgSink` writes through over tokio-postgres incl. caps/memory in one txn). UPDATE 2026-06-13 (pg-dregg wide-safe lane, Opus): the **range-attest SRF SHAPE + the federation subscriber RE-VALIDATION are now BUILT** (`pg-dregg/src/attest.rs` + `mirror::revalidate_replicated_chain` + the `dregg_attest_range`/`dregg_attest_explain`/`dregg_install_federation`/`dregg_revalidate_replicated_chain` externs; core green, 50 `cargo test` + 2 new `#[pg_test]`s; docs/PG-DREGG.md §10.2.1 + §15 rewritten). What REMAINS — the genuinely NODE-/CIRCUIT-touching settle items (this lane does NOT touch node/ or circuit/): (a) **the outbox drainer** (§11.4): a node-side tokio task drains `dregg.submit_queue` as `dregg_kernel`, runs the submit gates + `execute_via_producer` (#171), resolves + mirrors back. (b) **the proof-gate circuit-link S1-S3** (§10.2.1): **S1** serialize `circuit::ivc_turn_chain::WholeChainProof` (it holds plonky3 proof objects, NOT serde today — needs derives + a versioned envelope); **S2** node-side proof PRODUCER (fold finalized turns via `prove_turn_chain_recursive`/`fold_two_turns` → write a `dregg.turn_proofs(lo,hi,genesis_root,final_root,proof bytea,vk)` table the SRF reads); **S3** the `tier-c` feature's `dregg-circuit` dep (`--features verifier`/`recursion`, **Lean-FREE** — §8.1) flips `attest::verify_serialized_proof` from the fail-closed stub to the real `verify_turn_chain_recursive`. Until S1-S3 the SRF attests NOTHING (safe direction, §10.3). Tier D (executor in-backend) stays the north star, gated on the pg/Lean process-model spike. The 4 §6/§13 ember-decisions now carry crisp recommendations (docs/PG-DREGG.md §13.1: instant-revocation default · typed-tables-lead/views-over-memory end-state · C-embed · spike-gated full-D else D-sidecar).

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
- **native federation/remote-node panel** (NodeClient::Http exists; reqwest gated to sel4-thin for now); the channel/mailbox/court organs become LIVE reflections once this connects a node.
- **live node connection** — move reads to gpui's async executor; wire `/api/events/stream` SSE into ReceiptInspector with `cx.notify()` (snapshot today).
- **seL4 framebuffer backend** — a gpui renderer targeting a framebuffer cap (SEL4-EMBEDDING end state) + **seL4 channel transport** (a `NodeClient::Channel` over an seL4 endpoint, same contract over IPC not TCP).
- **single-source wire types** — replace `starbridge-v2/src/model/` hand-mirrors with a shared `dregg-wire-types` crate depended on by both node + shell.
- **finish-the-window (HOST gap, not a crate defect)**: the runtime-shader path opens the window; the offline Metal Toolchain download is blocked by a damaged Xcode `DVTDownloads.framework`. The remaining ahead-of-time-shader option = provision the Metal Toolchain on a healthy Xcode.

## DREGG-ANALYZER (forensic/observability trace analysis)

*(New crate dregg-analyzer/ — ingests CAPTURED TRACES, ATTESTS via the REAL verifiers, 14 tests.
Build-out lanes:)*

- **live-capture hooks** — a node trace-export mode emitting `BlocklaceCapture`/`ReceiptStrandCapture`/`WalCapture` from the running node (the on-disk/wire types are already exact, so an export endpoint is a thin dump). → node.
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
