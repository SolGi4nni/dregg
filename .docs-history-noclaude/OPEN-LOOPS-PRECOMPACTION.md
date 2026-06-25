# OPEN LOOPS — pre-compaction snapshot (2026-06-14, ~83% ctx)

Durable capture so nothing is forgotten across the boundary. HEAD = `46c560fc5` (ember's "sel4 servo
checkpoint" — tree clean; bucket-F WIP + servo scaffold + loose WIP are IN it). Read order on resume:
this file → `docs/V1-DELETION-RUNBOOK.md` (the cutover endgame) → HORIZONLOG → cv-dig the in-flight lanes.

## ⚑ IN-FLIGHT lanes (running at snapshot — VERIFY green + COMMIT/integrate on report; `cv` them if lost)
- **bucket-F bug-#4 K-fold** (`bknft6l2p` = my persvati verify of the fix): the root-verify config fix
  (root verified at `ir2_leaf_wrap_config`, in `circuit/src/{ivc_turn_chain,joint_turn_recursive}.rs`,
  uncommitted on the checkpoint). ON `test result: ok` for `k_fold_turn_chain_proves_and_verifies` +
  `two_step_inductive_core` + `foreign_circuit_root_is_refused_by_vk_pin` → COMMIT the fix; bucket-F done.
  (The prior K-fold FAILED with `QueryProofCountMismatch{expected:38,got:19}` — that's the bug being fixed.)
- **Cutover STEP 1** (`a9dd74e7`): node `bespoke_air_accepts`/async-`EffectVmAir` attestation → rotated
  (`api.rs:2486/2540`, `prove_pool.rs:177`). THE real remaining wall. Verify `f_dos_1` + `api_` green.
- **Leptos deos-surface prototype** (`afed8355`): the reactive-surface fit verdict (signals↔Reactive rung).
- **servo Stage-A** (`a18b39be`): libservo+SWGL render — the build was progressing (659 crates deep).

## ⚑ THE CUTOVER ENDGAME (the LEAD — `docs/V1-DELETION-RUNBOOK.md` is the ordered plan to grep-zero)
STEP 1 running → STEPS 2-7: MCP attestation (`mcp.rs:260/479/4601/4650`) · executor secondary verify
(`atomic.rs:588/883`, `authorize.rs:1409`, `proof_verify.rs:845`) · circuit Silver/forest DELETES
(`per_action`, `proof_forest::DescriptorForestNode` = last EffectVmP3Proof field, `JointParticipant`) ·
5c mechanical fan-out (CutoverFallback → effect_vm_p3_full_air.rs → EffectVmAir struct → bilateral v1
block → v1 tests) · bucket-E fence · grep-zero. **⚑ EMBER-FLAG: the wasm `not(recursion)` prover floor**
(Option-A wasm-rotated decision) — does wasm build without recursion or need a rotated branch (doesn't
block NATIVE grep-zero). STAYS (NOT grep targets): `EFFECT_VM_WIDTH`, `ACTIVE_BASE_COUNT` (const),
`effect_vm_p3_air.rs`'s `EffectVmShapeAir`, `generate_effect_vm_trace`.

## ⚑ CONVERGENCE RESIDUE (green-the-tree; the checkpoint bundled non-building WIP)
- DELETE the orphan broken `metatheory/Dregg2/Deos/Flow.lean` (the killed flow-lane's partial — REDUNDANT
  with `Protocol/Workflow.lean`; never wired into the umbrella; was mid-development with open holes).
- servo scaffold: verify it compiles, then commit (or hold) — don't claim a render it didn't produce.
- `cargo check --workspace --tests` is RED with ~172 pre-existing dregg3-reduction test-corpus rot
  (protocol-tests/dregg-dsl-tests/test-modules) — the "green the corpus" lane.
- The **Collections Rust mirror** (`cell/src/program.rs` HeapAtom/HeapField — the layout-rotation gap
  7/11.1) — NOT done (delicate; the Lean rung landed + is umbrella-wired).
- ~~The **ObservedFieldEquals embedded-executor wiring**~~ — CLOSED 2026-06-14: `execute_tree.rs` now
  builds a real `FinalizedRootAuthority` from its committed peer view (`build_finalized_root_authority`,
  `finalized_roots: Some(...)`), so the §11.2 cross-cell atom ACCEPTS a genuine read + REJECTS the
  mismatch/forge teeth. Accept/reject pair in `coverage_state_constraints.rs`; ratchet `teasting` 10→9.
  Same gate also got `CollectionAggregate` (was missing from the classifier → RED) closed alongside.
- sdk-ts/dist Docker rebuild (npm-in-Docker policy; Docker unreachable this session).

## ⚑ DEOS / LANGUAGE
- The **Workflow ⟷ GatedAffordance/Reactive BRIDGE** (the choreography discovery: deos affordances are the
  SURFACE of `Protocol/Workflow.lean` + the choreography stack `Spec/Choreography`/`Projection`/`DSLChoreo`
  — BRIDGE, don't fork). Offered, not yet picked.
- Landed language rungs (Lean + umbrella-wired): GatedAffordance (cap∧state), Collections (data-model +
  council-N-lift), Reactive (transition/window/membrane). Rust mirrors: GatedAffordance (app-framework ✓),
  Reactive (starbridge-web-surface ✓), Collections (✗ — the cell layout work). MORE rungs possible:
  disclosure/privacy-dial as language; intent/coeffect predicate; named-actor/role.

## ⚑ THE DEEPEST OPEN THREAD — the authorization-model integration crown (`docs/AUTHORIZATION-MODEL.md`)
The macaroon/biscuit token layer (`token/` — macaroon_backend + biscuit_backend + datalog_verify +
dregg_caveats) vs the in-circuit cap-crown (#103) are "two informal stories welded by `&&`, not one proven
arrow." Close it ⇒ the biscuit-caveat an agent carries and the cell-program the circuit witnesses become
LITERALLY one predicate (offline biscuit-verify ≡ in-circuit proof). ember probed this twice (the two
language questions). The integration crown.

## ⚑ PG-DREGG FLAGSHIP
pg-Tier-D landed (executor runs in the pg backend). Residual: pg doesn't link `dregg-turn` → the producer
SYNTHESIZES a transfer rather than decoding the submitter's `SignedTurn→WForest` in-backend (node-side
`lean_apply`, #171). Flagship polish ember wants: benchmarks · fuzz · dummy loads · a horizontally-
integrated demo ("DBOS but way more powerful") · sdk-py/sdk-ts pg-native extensions.

## ⚑ SEL4 / DESKTOP OS
- servo Stage-A building; Stage-B (the `sel4-musl` Servo PD — the THREAD-PERSONALITY wall, not mozjs) =
  quarters (`docs/desktop-os-research/SERVO-ON-SEL4.md`).
- seL4 executor-PD productionization (crypto floor landed; the decomposed 5-PD Microkit assembly +
  elaborator import-trim remain) = weeks.
- boot deos on mac: blocked on the gpui Metal Toolchain (host Xcode `DVTDownloads` damaged; CI may link).

## ⚑ DEPLOY (ember's acts)
- `dregg.fg-goose.online` site/server redeploy (stale — site rewrite is on HEAD; the redeploy is the act).
- The fresh-genesis devnet redeploy — held post-grep-zero.

## ⚑ RESEARCH / FORWARD
- The **l4v binary bridge** Stage 0: invert `turn/src/lean_apply.rs:~1143` — make the verified executor
  authoritative ("no new mathematics"). Stages 1-6 = ASSURANCE-CRITIQUE §5.
- dregg4 (turn = guarded comodel/lens; the single-machine principle; simplicial joint turns).
- The frustum-snapshot deepening (the witness-graph REPLAY protocol; the membrane-negotiation semantics —
  "the unspecified continent"; liveness-type as a confinement READOUT, not just an honesty label).
- UC-security / CryptHOL (#31); the adjunction thesis (Lawvere hyperdoctrine).

## ⚑ STANDING DEBTS (task board, condensed)
#34 tidy legacy Rust crates · #93 proof-audit re-run · #101 nav docs · #103 cap-reshape phase-D · #150
non-revocation AIR depth · #155 census debt burn-down · #169 proving-modality dial · #170 quorum (Lean
twin + node consumer tail) · #171 remote `.turn()` submission.
