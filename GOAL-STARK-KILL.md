# GOAL — STARK-KILL: re-derive the hand-rolled Rust STARK engine + its ~45 AIRs from Lean

*(This goal's trail. The repo's `GOAL.md` belongs to the storage-in-lean lane — do NOT
touch it. Full plan: `docs/deos/LEGACY-STARK-DELETION-SCOPE.md`.)*

## The mission
Kill `circuit/src/stark.rs` (the O(n²) hand engine) + ~45 hand-authored Rust AIRs by
EMITTING every circuit from Lean as a byte-pinned `EffectVmDescriptor2` on the p3 IR2
prover (law #1). Then climb the semantic ladder as high as it goes — Rung 1 (functional
refinement) AND Rung 2 (semantic no-forgery) for EVERY family, Rung 3 (fold → light-client
verifiable) where there's a consumer, and beyond (cross-circuit composition + assurance-case
apex). Done = engine + AIRs deleted, every survivor Lean-emitted + Rung-1&2-proven.

## ⚑ WIRE-MIGRATION MAP (2026-07-07, "Grind it down" — ember lifted the hold + gave the phrase)
CUTOVER SURFACE LANDED (84 files, workspace-green, committed) → 35→**20** prod stark refs remain.
The 20 are the coupled wire-migration. WIRE SHAPE (grounded): predicate blobs (`cell/src/predicate.rs`
`WitnessedPredicate`, a small descriptor + `proof_idx` into a proof-witness table) carry a serialized
**`StarkProof`** (hand engine); TARGET = **`Ir2BatchProof`** (= `p3_batch_stark::BatchProof`, the return
of `prove_vm_descriptor2` at `descriptor_ir2.rs:4904`). Migrate producer→table→consumer in LOCKSTEP.
The 20, by cluster:
- **bridge** (present.rs producer + verifier.rs consumer) — SELF-CONTAINED, the PATHFINDER (build-gate just bridge).
- **turn** (action, aggregate_bilateral_prover, binding_proof, conditional, executor/apply, executor/membership_verifier) — the deep-prover core.
- **sdk** (cipherclerk, privacy, verify) · **chain** (main, lib, prove) · **cell/predicate.rs** (the blob table).
- **wasm** (lib, privacy) — SOFT wall (wasm already pulls p3 in its dep graph; a rewire, not a new prover).
- misc: wire/server.rs, storage/blinded.rs, circuit/examples/fri_from_scratch.rs (example — delete/migrate).
TWO descriptor-generalizations needed first: variable-depth membership (emit is depth-2), delegation-scope (no emit).
ORDER: bridge pathfinder → generalize membership → turn cluster → sdk/chain → cell blob table → wasm → delete hand AIRs → `git rm stark.rs` when grep==0.
NOTE: breaking old serialized StarkProof blobs is ACCEPTABLE (VK-epoch flip is a fresh-genesis act anyway).

### ⚑ REFINED PLAN (scout-mapped 2026-07-07, agent a9f1579a — supersedes the rough order above)
**PREMISE CORRECTED: the seam is OPAQUE `Vec<u8>` (witness_blobs table + `proof_bytes: &[u8]`), NOT a
typed StarkProof.** So `cargo build` catches only the ~9 TYPED sites; the byte-format flips + the
runtime AIR-name string dispatch are COMPILER-INVISIBLE. A big-bang builds green and fails at
RUNTIME. → runtime validation is mandatory, not optional.
FALSE POSITIVES (already done): `turn/aggregate_bilateral_prover.rs` (already Ir2BatchProof),
`turn/binding_proof.rs` (only hashes bytes) → **18 real files, not 20**.
- **PedersenEquality** predicate is genuinely off-STARK (Schnorr) — NO migration, NO descriptor.
- **Delegation descriptor ALREADY EMITTED** (EffectVmEmitDelegate/Atten/Refresh/Revoke) — the gap is
  only the Rust leg (`turn/action.rs:650 verify_stark_delegation_binding` does PI-binding + a
  cfg-gated v1 AIR being deleted; make it a full `verify_vm_descriptor2`).
- **Variable-depth membership = the ONE real descriptor-gen.** Emit is depth-2; production
  `prove_membership_dsl` is var-depth; executor PADS to depth-2 today (`membership_verifier.rs:865`).
  Plan: Rust runtime-parameterize depth for the cutover (viable, `check_descriptor2` gates
  well-formedness); Rung-2 proof stays depth-2 → OPEN a Lean lane to lift it (honest gap, don't block).
- **THE #1 DANGER: `circuit_for_air_name`** (runtime string→circuit dispatch, `descriptors.rs:686`) has
  NO descriptor-world equivalent (only a TEST-only registry). Must BUILD a production `descriptor_by_name`.
- **3 serialization dialects**: postcard (executor seam), serde_json (wasm), bincode (SP1 guest) — format
  mismatch = silent decode-fail→false.
- **SP1 chain leg** (`chain/program` RISC-V binary, hand-mirrored `GuestStarkProof` via bincode) — FENCE
  OFF, migrate as its own later gate; a Gate-2 format flip silently breaks the EVM-wrap. (Its guest struct
  is a SEPARATE copy, so fencing does NOT block `git rm circuit/src/stark.rs`.)
**GATES (2 build + 1 runtime, foundation-first):**
- GATE 1 (circuit + circuit-prove, fast per-crate): build `descriptor_by_name` production dispatch +
  variable-depth membership descriptor. These change signatures everything downstream needs.
- GATE 2 (one coordinated edit, `cargo check --workspace` iterate → one `cargo build --workspace`):
  migrate all 18 sites against Gate-1 foundations. Compiler catches ~9; MANUALLY handle the byte-opaque
  encoders + air_name call-sites. wasm rides along (deferrable sub-lane). SP1 FENCED.
- GATE 3 (runtime, mandatory): integration run — executor membership/adjacency discharge, bridge
  present→verify round-trip, wasm serde_json, SP1 decode (or confirm fenced).

## Current thrust — PARKED at a clean milestone (ember hold, 2026-07-07)
**Rung 0 + Rung 1 + Rung 2 ALL COMPLETE and committed.** Every one of the ~20 emitted
circuits is Lean-emitted, byte-pinned, functionally refined (Rung 1), AND no-forgery proven
(Rung 2): 10 DONE_AT_RUNG1 + 5 full Rung-2 (note_spending/quantified_absence/temporal/garbled/
effect_action) + DFA template + 4 honest PARTIAL. predicates-arithmetic → DONE_AT_RUNG1.
REMAINING (both HELD for the free tree / a fresh session):
- push the 4 honest PARTIALs → full (ivc, predicates-relational-compound, revocation are
  crypto-dischargeable additive proof; membership needs the emit-fix);
- Phase 2b CUTOVER (ember-confirm-gated) — the perf win + the Rust deletion.

## ⚑ EMBER DECISION (2026-07-07): Phase 2b is HELD
The CUTOVER (rewire 55 live `stark::prove` consumers onto `prove_vm_descriptor2` + delete the
hand AIRs + `git rm stark.rs`) — where the perf win lands + the unverified Rust dies — is
HELD until the tree is free of the other concurrent `/goal` lanes ("it won't be long before
the tree is free and ours"). Do NOT auto-fire it when the tree clears — CONFIRM with ember
first (it deletes deployed code, irreversible-ish). Same hold on the membership emit-fix
(byte-golden change). SAFE meanwhile: finish Rung 2 (pred-arith), push honest partials → full
(additive proof only). Preference when it goes: INCREMENTAL, one consumer family at a time,
whole-tree-build-gated, with a before/after perf benchmark wired into the first cutover.

## Next moves (both Rung-2 templates now committed; the rest is gated/polish)
- DONE: `DfaRoutingRung2` (hterm discharged via `route_commitment_binds_trace` + `CollisionFree`,
  cheatTrace necessity witness) — committed `87b5e8ec4`. `BilateralAggregationRung2`
  (no-double-spend, structural/carrier-free, cheat_double_spend necessity witness) —
  hand-verified + committed 2026-07-07 (workflows were killed by a process restart before
  recording verdicts; I'm the integration gate, verified on my own tree).
- ~~SAFE / additive: push the 3 Rung-2 PARTIALs → full (crypto-dischargeable)~~ **REFUTED
  2026-07-07 (workflow wf_40ec9ac2-272).** All 3 are EMIT-FIXES, not crypto-dischargeable:
  · **predicates-relational-compound → a FORMALLY PROVEN soundness gap** (committed
    `PredicatesRelationalCompoundRung2.lean` §5b, `fg_accepts_unequal_committed`): the `diff`
    column is never tied to `value_a − value_b`, so a Satisfied2 EQ proof accepts UNEQUAL
    committed values — in BOTH the emit AND the deployed Rust hand-AIR. The campaign's 2nd real
    deployed-circuit bug (cf. membership ordering gap `0f8d478b2`). CLOSE = in-AIR gate
    `diff = value_a − value_b` (emit-fix, byte-golden, HELD).
  · **ivc**: residuals are the two inter-row transition gates (`IvcContinuity`/`IvcStepIncrement`)
    the deployed StateTransitionAir OMITS for padding-safety — emit-fix, not a proof.
  · **revocation**: `DiffLowerRangeSound` (the strict-lower ordering bound) is re-assumed, not
    forced by the descriptor — emit-fix (a range gate).
  So the remaining Rung-2 partials are all downstream of the HELD emit-fixes (byte-golden), which
  ride Phase 2b. Nothing further is both safe-additive AND authorized until the cutover opens.
- HELD (ember-gated, confirm first): Phase 2b cutover (16 prod files still call hand
  `stark::prove`; rewire → `prove_vm_descriptor2` + delete hand AIRs + `git rm stark.rs`) and
  the membership emit-fix (byte-golden). Wait for the free tree + ember confirm; go INCREMENTAL,
  whole-tree-build-gated, perf-benchmarked.

## ⚑ Model-found finding (worth a fix, not a Rung-2 item)
The membership Rung-1 PARTIAL surfaced a REAL DSL→IR-v2 drift: `AdjacencyMembershipEmit`
maps the child-ordering gates to `.base (.gate …)`, which `holdsVm` makes VACUOUS on the
LAST row (when_transition). The deployed DSL (`dsl_plonky3.rs:225/240`) lowers them as
every-row `assert_zero` — so the emit UNDER-constrains the last Merkle level vs the hand AIR.
Fix = re-emit those ordering gates as an every-row IR-v2 form (moves the byte-golden + gate
test). Upgrades membership PARTIAL → full; same class may touch note_spending's Merkle fold.
Surfaced by the refinement proof itself — exactly what Rung 1 is for.

## Done-log
- Rung 0 (emit + real-prover gate) landed for all 20 families — `9c440d208` (+ merkle
  pathfinder `d7d3348fa`). Verified on my tree: 20 emit modules build, 21 gate tests pass.
- Rung 1 DFA bridge landed — `DfaRoutingRefine.lean` (`dfaRouting_refines_classify` +
  unconditional `dfaRouting_genuine_prefix`). Adversarially CONFIRMED non-vacuous,
  axiom-clean. Honest PARTIAL: `hterm` terminal-step = the first Rung-2 target.
- Scope doc + refinement ladder committed — `6716a3dcb`.
- Rung-1 swarm (other 20 families) resumed after a session-limit zombie — `w2hvgi0r4`
  (8 emits cached, remainder + all verifies re-running).
- Rung 1 — 16 whole-descriptor bridges landed + committed (verified on my tree, lake 3024
  jobs, adversarially CONFIRMED, non-vacuous, axiom-clean; bridge_action reaches IFF).
  13 GREEN + 3 honest PARTIAL (membership/note_spending/non_revocation residuals = Rung-2
  targets). Total Rung 1 = 17/20 (incl DFA). HELD unverified: multi_step + presentation
  (refute died on limit); temporal + garbled (refine died) — resume when limit resets.

- MEMBERSHIP SOUNDNESS GAP CLOSED (coordinated 4-file fix): the top-level ordering under-constraint
  the refinement proof caught is fixed (adjLastOrderFix, every-row enforcement); membership Rung-2 now
  FULL/unconditional. Verified my tree (3 Lean + 9 gate tests incl forged_top_level_ordering_refuses).

- ASSURANCE partials→full swarm (wf_31b63f12-9c7): all 3 STILL_PARTIAL, HONESTLY — ivc + revocation
  residuals are EMIT-LEVEL gaps (same class as membership: transition gates vacuous on last row → need
  every-row boundaries); predicates-relational already discharges its crypto slice. DEFERRED as polish
  (descriptors are Rung-1-full + honest-Rung-2-partial = correct); the CUTOVER is the priority, not this.

- ⚡ CUTOVER #1 LANDED + the PERF NUMBER (the loop-closer): zkOracle injection leg OFF stark.rs onto
  prove_vm_descriptor2. MEASURED 1KB 19.37s→1.87s = **10.4×**; 8KB 15.5s (was ~20min, ~80×). O(n log n)
  plonky3 replaces O(n²) hand engine. New DfaRoutingGeneralEmit.lean, grep stark==0, 42 tests green.
  Committed. This is the first consumer dead + proof the whole campaign's premise pays off.

- CUTOVER SWARM mapped the kill: 7 crates went stark-CLEAN (dsl-tests, demo-agent, tests, node,
  dsl-runtime, circuit, circuit-prove) — core crates BUILD GREEN together (1m54s). The deep provers
  (turn/sdk/bridge/misc, ~27 refs) are BLOCKED on a coordinated StarkProof→BatchProof WIRE MIGRATION:
  each carries hand-StarkProof in a serialized blob (cell predicate blobs, proof_bytes) that producer+
  consumer must switch in lockstep; + variable-depth membership descriptor + a NEW delegation-scope
  descriptor + wasm carve-out. That wire migration is the real remaining CAMPAIGN (not one swarm).
  Cutover working-tree changes build green; commit deferred to the wire-migration pass.

## Phase 2b — THE CUTOVER (ember approved 2026-07-07, "stark.rs dead ASAP")
Reality (grounded): ~35 real consumers + ~46 test/bench. TWO WALLS: (1) emitted descriptors
are MINIMAL INSTANCES (dfaRoutingDesc hardcodes the toggle transition; membership is depth-2)
→ each consumer needs its descriptor GENERALIZED to production shape (table-committed / var-depth)
before rewire; (2) WASM proves in-browser on `stark::MerkleStarkAir` (wasm/src/lib.rs:268) →
gates the final `rm` on a wasm-fittable prover (ember Option-A decision, pending). The seL4
`stark_core/stark.rs` ×2 are VENDORED copies, decoupled — NOT blockers.
PLAN: generalize-then-rewire, per consumer-family, whole-tree-build-gated + benchmarked.
- PATHFINDER (running, agent): zk_leg.rs — emit a GENERAL table-committed DFA descriptor,
  rewire off stark::try_prove onto prove_vm_descriptor2, measure before/after. Proves the
  pattern + the perf number. Then swarm the rest by family.
- kill order: (a) test/bench surface (delete/migrate to emit gate tests) · (b) rewire prod
  consumers per family (generalize descriptor + producer) · (c) delete hand AIRs · (d) wasm
  decision · (e) git rm stark.rs when grep circuit::stark (non-vendored prod) == 0.
