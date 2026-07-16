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

### ⚑ EMBER DECISIONS (2026-07-07) + EXECUTION STATUS
- SP1/EVM-wrap: **DELETE, rebuild later** (not fence). ✅ DONE — Gate 0: `git rm -r chain/` (332MB,
  leaf crate, 0 dependents; removes the bincode hazard + 3 files). Prod stark refs 20→17.
- Variable-depth membership: **do depth-general as GROUNDWORK** (not a depth-2 pad hack). → Gate 1.
- Breaks: **ALL breaks OK — discarding all pre-persisted things.** Full green light on serialization.
- GATE 1 RUNNING (workflow wf_67644971-9b9): production `descriptor_by_name` dispatch (the #1-danger
  air-name→descriptor analog) + depth-general membership descriptor builder. Round-trip-gated
  (name→desc→prove→verify per kind; depth-{2,4,8}), adversarially verified. On CONFIRMED: verify on my
  tree + commit, then Gate 2 (the coordinated ~15-site consumer swap).
- ✅ GATE 1 LANDED (commit pending-hash): `descriptor_by_name` (fail-closed dispatch, 9 goldens) +
  `membership_descriptor_of_depth` (genuinely var-depth, depth-8-load-bearing proven). 19 tests green
  on my tree, adversarially CONFIRMED. Residual: Rung-2 depth-general Lean lift (named follow-on).
- GATE 2 NEXT: coordinated swap of the 15 consumer sites (scout §2/§3 map) onto descriptor_by_name +
  the foundations. cargo check --workspace iterate → one build → Gate 3 runtime validation.
- ⚑ GATE 2 ATTEMPT (wf_7679d0c8) RETURNED PARTIAL — flipped ZERO prod sites by a SOUND judgment call,
  and REFUTED the scout's "one coordinated edit" optimism with 4 real foundation gaps (a "Gate 1.5"):
  1. **membership arity mismatch**: Gate-1 depth-general descriptor is BINARY (arity-2); production
     membership (`membership_verifier.rs` + ~8 app crates via registry_with_real_verifiers) is 4-ARY.
     Flipping changes every committed root + is FAIL-OPEN if wrong. → need a 4-ary depth-general variant
     to MATCH production (fresh-genesis lets us break roots, but the executor+apps must move together +
     run the app suites). **DECISION: match production arity (4-ary), don't force apps to binary.**
  2. **bridge `ProofVerifier` trait carries no predicate identity** (`verify(proof,action,resource,vk)`)
     → can't call descriptor_by_name(predicate_name); needs a trait-signature change (dregg-turn, ripples).
  3. **delegate descriptors are v1 parse_descriptor, NOT IR-v2** (scout was wrong) — delegation needs a
     new IR-v2 delegate EffectVmDescriptor2 + a descriptor_by_name arm before action.rs can migrate.
  4. **adjacency has no descriptor-witness builder** (only `membership_witness`) — needs one.
  DELIVERED: the Gate-3 runtime harness (turn/tests/stark_kill_wire_roundtrip.rs, 5 green) validating the
  consumer contract end-to-end. RESHAPED PLAN: **Gate 1.5** (close the 4 gaps: 4-ary depth-general
  membership + adjacency witness + IR-v2 delegate descriptor + the ProofVerifier trait threading predicate
  identity) → **Gate 2** (now-mechanical site flips against complete foundations, per-CLUSTER runtime-gated:
  bridge, turn-executor+8-apps, sdk, wire/storage, wasm). The membership cluster is the fail-open risk —
  do it its own cluster with the app suites run.
- ⚑ ARITY DECISION (ember "brave, 4-ary to match production"): production membership is 4-ARY
  (hash_4_to_1, siblings:&[[BabyBear;3]] = 3 sibs + node). Gate-1's depth-general was BINARY. →
  build a 4-ary variant whose root is BYTE-EQUAL to the production hash_4_to_1 root (apps don't move).
- GATE 1.5 RUNNING (wf_47cf9430-923): 2 lanes — (circuit) 4-ary depth-general membership +
  adjacency witness builder + IR-v2 delegate descriptor; (trait) thread predicate identity through
  ProofVerifier so descriptor_by_name is callable. Root-equality-gated + adversarially verified.

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

## ⚑ GATE 1.5 COMPLETE (2026-07-07) — foundations done, Gate 2 unblocked
All 4 gaps closed + committed (7e103edd2 trait, 3a65bb285 circuit), verified on my tree:
4-ary membership (root byte-equal to production, 6 tests) · adjacency witness (3) · IR-v2
delegate descriptor (4) · ProofVerifier::verify_with_predicate + DescriptorDispatchVerifier.
The adversarial verify CAUGHT the trait impl shipping a red test as green → corrected honestly.
NAMED RESIDUAL: Rung-2 depth-general soundness lift (depth is a name/VK label; the path is
root-bound via Poseidon2 CR; production is depth-2 → no regression; in-circuit depth-binding is
a Lean follow-on, NOT a migration blocker).
NEXT = GATE 2: flip the ~15 consumer sites against the now-complete foundations, per-cluster
runtime-gated (bridge · turn-executor+~8-apps [fail-open, run app suites] · sdk · wire/storage ·
wasm) → delete hand AIRs → git rm circuit/src/stark.rs.

## ⚑ DEPTH RESIDUAL CLOSED BY PROOF (2026-07-07, background Lean lane)
MembershipDepthGeneralRung2.lean (committed, lake green, axiom-clean): membership_depth_general_sound
— accept at ANY nominal depth + same committed root ⟹ same leaf/siblings/actual-depth (root binds
the path). REAL FINDING: CR alone does NOT suffice — cross-depth needs a 2nd carrier LeafNodeSep
(leaf/node domain separation, the Merkle depth-extension guard). The deployed Poseidon2 SATISFIES it
(poseidon2.rs:618 leaf-domain-sep). So depth-nominal is SOUND-BY-PROOF (2 named+realized carriers),
not just argued. Residual: mirror a per-depth emit descriptor to metatheory for the SAT⟹SEM lift at
actual height (additive follow-on; the functional-model soundness here governs it).

## ⚑ GATE 2 RESULT + THE REAL REMAINING SCOPE (2026-07-08, this instance OWNS the finish; others parked)
Gate-2 cluster workflow: 4/7 CONFIRMED + committed (via a broad "checkpoint commit" 4b19931b8 by a
concurrent instance — ref 17→14, HEAD builds green): bridge, turn-membership, turn-conditional-delegation,
wasm. The 3 BLOCKED (sdk, wire-storage, turn-executor-misc) validated the factoring: self-contained
producer+consumer PAIRS complete; thin consumers whose producers are elsewhere block.
⚑ DEEPER FINDING (the real gate): the blocked consumers are NOT just call-swaps. Each remaining
predicate family needs a DESCRIPTOR-WITNESS BUILDER (the Gate-1.5 pattern: a Rust fn producing a trace
that matches the EMITTED descriptor, since hand-DSL-circuit trace layout ≠ emitted-descriptor layout).
The confirmed clusters worked ONLY because membership got membership_witness_4ary in Gate 1.5.
  HAVE builders: membership, adjacency, delegate.
  MISSING (blocks the flip): non_revocation (sdk/privacy prove_not_revoked+verify), note_spend
    (storage/blinded), blinded-presentation (sdk verify_anonymous + wire/server + the bridge issuer path),
    predicate-arith (turn/executor/apply predicate leg).
REMAINING = per family {non-rev, note-spend, blinded-presentation, predicate-arith}: (a) build the
descriptor-witness builder [SELF-CONTAINED foundation, agent-able Gate-1.5 style, root/trace byte-match
gated] → (b) flip producer+consumer [COUPLED, main-loop, runtime-gated] → commit. Then strip additive
bridge residue + delete hand AIRs → git rm circuit/src/stark.rs. This is ~4 increments, not one turn.
The 14 refs also include comment-only/false-positives (aggregate_bilateral already Ir2, binding_proof
hashes-only, fri_from_scratch a self-contained example) that need no flip.

## ⚑⚑ REORIENTATION (2026-07-08, ember): ASSURANCE FIRST — the flip is GATED on argus-grade correctness
ember: "major bugs in the old Rust AIRs we ported over... carefully audit the new Lean for correctness
and expand our proofs; the assurance story vs primary argus is not very good." CORRECT — and the 3 bugs
we found (relational diff-unbound / membership ordering / non-rev forgery) are EVIDENCE: all found by
proving Rung-2 adversarially, all the SAME class (descriptor accepts a witness that doesn't satisfy the
intended semantic relation — a free column / missing gate; byte-identity does NOT catch it).
CENSUS (ground truth): assurance is UNEVEN — Rung-2 THIN on MembershipDepthGeneral(3)/NoteSpendingLeaf(5)/
GarbledEval(5)/EffectActionBinding(5); Rung-2 ABSENT on BridgeAction/CommittedThreshold/Derivation/Fold/
MerkleMembership/MultiStepChain/PredicatesArithmetic/Presentation; NONE tied into AssuranceCase.lean /
the argus adversary machinery (CoinductiveAdversary/CTLLiveness/Temporal).
NEW THRUST (supersedes flip-and-delete as the priority): (1) adversarial correctness AUDIT of every
security-critical emitted family, hunting the found-bug class [RUNNING wf_1b09d713-b46]; (2) Rung-2
COMPLETION — every family a real no-forgery proof w/ genuine cheat-witnesses, deepen the thin; (3) tie
the emitted descriptors into AssuranceCase.lean (argus citizens, not islands).
⚑ THE FLIP/DELETE IS NOW GATED: do NOT flip consumers onto a descriptor until it is audited-correct +
Rung-2-full. Replacing known-buggy Rust with unaudited Lean is a lateral move. The Gate-1.6 witness
builders (wrwj5nf6q) may finish (additive, needed post-audit) but the consumer flips WAIT on assurance.

## ⚑ UN-GATE (2026-07-08, ember): deletion and audit are ORTHOGONAL — DELETE FAST
ember: "we don't need to wait for that audit to rip out stark.rs / continue the purge. The new ones are
always going to be better than the old ones, and the faster we delete the old files the less confused
everything is." CORRECT — I over-gated. The new Lean-emitted descriptors are the go-forward path
REGARDLESS of the audit (byte-pinned + some proofs vs the old's zero-proofs + confirmed bugs); keeping
the old buggy Rust around is pure confusion. Any bug the audit finds is fixed IN THE LEAN EMIT, which
the deletion does not foreclose — it CLARIFIES (one impl to harden, not two).
CORRECTED THRUST: (a) CONTINUE the purge — finish the consumer flips (builders now exist), delete the
hand AIRs, git rm circuit/src/stark.rs. (b) The assurance audit (wf_1b09d713-b46) runs IN PARALLEL as
forward correctness on the KEPT Lean (Rung-2 completion + argus-case tie-in) — NOT a gate on deletion.

## ⚑⚑⚑ THE AUDIT PAID OFF (2026-07-08): 7 CONFIRMED forgery bugs in the emitted descriptors — 1 a REGRESSION
The assurance audit (wf_1b09d713-b46, 15 families) found the found-bug class is SYSTEMIC:
CONFIRMED_BUG (7): MerkleMembership, AdjacencyMembership, NonRevocation, NoteSpendingLeaf,
  PredicatesRelationalCompound, Derivation, Fold. SUSPECTED (3): GarbledEval, Presentation,
  CommittedThreshold. LOOKS_SOUND (4): DfaRouting, QuantifiedAbsence, TemporalPredicate, BridgeAction.
  (PredicatesArithmetic: suspected→REFUTED, sound.)
THE CLASS (nearly all of them): a semantic-binding constraint emitted as `.base (.gate body)` =
when_transition, VACUOUS on the last row (holdsVm .gate isLast=true = True) → a witness column FREE on
the last row (or a height-1 trace) → forgery. ⚑ AdjacencyMembership is a REGRESSION: the deployed RUST
AIR binds idx-step every row (assert_zero, is_transition=false) but the Lean EMIT dropped it — so
byte-identity was FAITHFULLY PORTING A HOLE THE RUST DIDN'T HAVE. This REFUTES "new is always better"
for these families and vindicates ember's audit-first instinct: byte-identity ≠ correctness; only
adversarial no-forgery proofs catch this.
FIX SWARM RUNNING (wf_be002563-213, ember "swarm fixes, improve the code + proof strategy"): per family
— add the every-row/last-row binding (the adjLastOrderFix precedent, match/exceed the deployed Rust),
regen the golden, PROVE the exact found-bug witness now UNSAT (regression), + PROOF-STRATEGY UPGRADE:
sweep the whole descriptor for sibling vacuous-.gate constraints.
⚑ META-LESSON (proof strategy): the `.gate` (transition-only) lowering of a semantic-binding constraint
is a SYSTEMATIC TRAP. Standing fix: every Rung-2 proof must construct the height-1/last-row cheat
witness and prove it UNSAT; consider a Lean lint flagging any semantic `.gate` without a last-row
counterpart. The consumer flips REMAIN GATED on their family's descriptor being FIXED (not just the
earlier audit — a fixed descriptor).

## ⚑ BUGFIX HARVEST + THE OOM LESSON (2026-07-08)
⚠ CAUSE OF DEATH: the 10-lane fix swarm ran ~10 concurrent `lake build`s → memory exploded →
HARD REBOOT (killed both the fix swarm + the final-flips workflow). STANDING RULE: NO concurrent
Lean-building swarms. Lean work is SEQUENTIAL main-loop, LEAN_NUM_THREADS capped. (The Rust flip
swarms are fine; it is Lean/lake concurrency that OOMs.)
HARVESTED (on-disk edits survived the reboot; verified sequentially, memory-capped):
- ✅ COMMITTED 3/10 (afb97de45), build-green + axiom-clean + real ¬Satisfied2 forge-reject:
  AdjacencyMembership (the REGRESSION — idx-step now every-row; fTrace/cTraceBad reject),
  NonRevocation (SIB1 bound; both poles prefix_carriers_admitted_forgery→fixed_forbids_the_forgery),
  NoteSpendingLeaf (merkle chain bound; broken_chain/wrong_root reject).
- ✅ COMMITTED 4/10 (+ Merkle 8f55a2ce7): + MerkleMembership (continuityLastFix binds CUR1=PARENT0 on
  last row; cTraceBadChain/cTraceBadRoot reject the height-1 forge). Built axiom-clean UNDER THE GUARD.
- ⚠ HELD 6/10 (on-disk, need sequential finishing UNDER `.bin/lean-safe` — NOT a swarm):
  · GarbledEval — has sorryAx (faked-green in garbled_lastRowFix_load_bearing); discharge the sorry.
  · Derivation — NOTHING on disk (lane died early); redo from the audit dossier (bodyHash cols 1..8 free).
  · PredicatesRelationalCompound — fix present, thin regression (and_intermediate free); complete.
  · Fold — fix present (REMOVAL_COUNT_PLUS_ONE free); build-verify + complete regression.
  · Presentation — fix present, NO regression (NOT_AFTER free); author the forge-reject.
  · CommittedThreshold — fix present, thin (FACT_COMMITMENT tautological pin); complete.
  Audit dossiers: /private/tmp/.../scratchpad/bugfix-seeds.json. Both swarms resumable by runId but
  DO NOT resume as concurrent Lean swarms — finish sequentially UNDER .bin/lean-safe.
  METHOD (proven): build each held family under `.bin/lean-safe lake build …` — a decide-bomb gets
  KILLED at 12GB (diagnostic: that family needs decide→== per the tractability rule); a clean build is
  harvestable. Fold/Relational/CommittedThreshold have `#guard decide(…)`/big-literal suspects; Garbled
  has a real sorryAx; Derivation must be redone from the dossier.
- final-flips (wf_0438144d-602) also OOM-died with consumer-crate edits on disk (uncommitted, GATED
  on the descriptors being fixed — do not commit until the 7 held fixes land).

## ⚑⚑ LEAN TRACTABILITY DISCIPLINE (2026-07-08) — the 80GB-per-process bug
ember: individual lean processes hit 80GB+ (NOT concurrency) → hard reboot. CAUSE: fix-lanes wrote
`#guard decide (…)` / `by decide` over HEAVY computation — Poly.eval over BabyBear field arithmetic and
26KB emitVmJson2 descriptor structures. `decide` forces the KERNEL to fully reduce the Decidable
instance → materializes enormous terms → 80GB. (Adjacency/NonRev/NoteSpend built fine: their decides
were small structural props.)
STANDING RULES:
1. NEVER `decide`/`native_decide` on heavy computation (emitVmJson2, descriptor structs, Poly.eval over
   field elements). Use COMPILED `#guard (a == b)` (a Bool, run by the compiler NOT the kernel) or `#eval`
   or a structural simp/rfl proof. `decide` is ONLY for small finite props that reduce trivially.
   FIX PATTERN: `#guard decide (X = 0)` → `#guard (X == 0)`.
2. EVERY build memory-capped: run via `.bin/lean-safe lake build …` (CAP_GB=12, RSS watchdog kills a
   runaway lean/lake before it reboots the box). NEVER a bare unbounded lake build.
3. Tractability review BEFORE build — a `#guard decide(bigterm)` / `by decide` over field arith is a
   red flag caught by READING, not at reboot.

## ⚑ BUGFIX HARVEST — 7/10 DONE + THE BOMB KILLED (2026-07-08, session 2)
The memory guard (.bin/lean-safe) WORKED: it caught the Presentation build at 20GB (KILL >12GB), which
IDENTIFIED the 80GB culprit → `#guard decide (v ∈ rangeRows 30)` = kernel membership in a 2^30 ≈
1-billion-element list. FIXED via the O(1) bound predicate (rangeRows_mem DescriptorIR2:1350). The
reboot cause is dead; every build now runs under the guard.
COMMITTED 7/10 (all axiom-clean under the guard, real ¬Satisfied2 forge-rejects):
  Adjacency (regression), NonRevocation (both poles), NoteSpendingLeaf, MerkleMembership (height-1),
  Fold, CommittedThreshold (suspected/hardened), Presentation (bomb + freshness hardening; NOT_AFTER↔
  derivation-leaf is a named Rung-3 composition residual).
REMAINING 3 (on-disk, HELD — delicate proof work, do FRESH under the guard, sequential):
  · GarbledEval — sorryAx in garbled_lastRowFix_load_bearing (the fix faked-green; discharge the sorry).
  · PredicatesRelationalCompound — sorryAx in relBad_not_satisfies (the and_intermediate fix faked-green;
    discharge). NOTE: the ORIGINAL relational diff-bug was already closed by another instance (0cfa85c82
    C2b weld); this is the SECOND (compound and_intermediate) bug's fix, which cheated.
  · Derivation — NOTHING on disk (lane died before writing); redo from the dossier (bodyHash cols 1..8
    free — bind to Merkle membership in pi[0] + hash_fact).
  bugfix-seeds.json has the dossiers. The 2 sorryAx families FAILED the axiom-hygiene gate → NOT shipped
  (the gate working as designed). Also still HELD: the final consumer-flips + git rm stark.rs, gated on
  these 3 landing.

## ⚑ BUGFIX CAMPAIGN — 9/10 DONE (2026-07-08, pushed through under the guard)
Finished the audit-confirmed forgery fixes SEQUENTIALLY under .bin/lean-safe (one build at a time — no
OOM). Both sorryAx cheats the axiom-hygiene gate caught were GENUINELY discharged (via fresh single
agents, verified on my tree):
- GarbledEval (8/10, 70bc33261): the sorryAx was Lean's error-RECOVERY injection (MemoryChecking.*
  unresolved); discharged with memCheck_nil. Axiom-clean.
- Derivation (9/10, 86d941d26): bodyHash 1..7 were slot-0-only bound → forgeable; c6c binds all body
  atoms (piCount 6→13); der_rejects_unexported_body_fact. Axiom-clean. Follow-up (ember-gated): the
  dsl/derivation.rs Rust lockstep + VK regen.
9/10 COMMITTED (all axiom-clean under guard, real ¬Satisfied2 forge-rejects): Adjacency, NonRevocation,
NoteSpendingLeaf, MerkleMembership, Fold, CommittedThreshold, Presentation(+bomb), GarbledEval, Derivation.
- 10/10 = PredicatesRelationalCompound: BLOCKED BY A LIVE CONCURRENT INSTANCE actively refactoring it
  (Emit descriptor 91→219 constraints + RelClassified extended with 4 unfilled fields → red). My agent's
  membership-lemma sorry-fix (the same error-recovery pattern) is ON DISK + correct + durable; it greens
  when the other instance finishes its value-bit range gates. NOT mine to commit — the parking didn't take
  on that lane. (The ORIGINAL relational diff-bug was already closed by another instance, 0cfa85c82.)
STILL GATED on Relational landing + the descriptor VK regens: the final consumer-flips + git rm stark.rs.

## ⚑ MACHINE-SYMPATHY + TRACTABILITY (2026-07-08, "go forth" — while blocked on the sdk red)
Did measured optimization + a proactive OOM sweep on the emissions code:
- ✅ PARSE-ONCE CACHE (6f9b9e3fe): descriptor_by_name re-parsed the byte-pinned JSON EVERY call on the
  per-verify path → LazyLock cache, ~10x dispatch (dfa 12.5x, non-rev 11.5x, adjacency 9.6x, note-spend
  4.9x). Zero signature change, legibility preserved, correctness green.
- ✅ MEASURED THE REAL COST (probe a4b389a4d): decode 14.8µs / prove 12.67ms / verify 2.54ms →
  decode is 0.097% of a cycle. The emissions/dispatch/decode layer is NOT the bottleneck; the STARK
  prove path is (log_blowup 6 = 64x + 19 FRI queries = a SECURITY param, not waste). For tiny predicate
  traces the fixed FRI/FFT overhead dominates → the real lever is BATCHING predicates (architectural,
  not an emissions fix). DO NOT chase further emissions-layer micro-opts (measure-before-a-lever result).
- ✅ TRACTABILITY SWEEP (read-only): NO active OOM bomb remains (Presentation's fix confirmed; all
  rangeRows membership uses the O(1) bound or stays opaque). TWO recorded follow-ups (NOT done — in
  shared/dirty files, fix when quiet):
  · `Exec/ConditionalTurn.lean:989` — the tree's ONLY `native_decide` (adds ofReduceBool, hygiene-gate
    violation). In a non-load-bearing `example`, tiny edge set → likely `decide` swaps clean. FILE IS
    DIRTY (another lane editing) — do NOT touch now.
  · `Circuit/DecideSatisfied2.lean:60` `checkLookup` — enumerates `tf l.table`; SAFE now (small tables)
    but the REINCARNATION VECTOR for the 80GB bomb if a witness's `.range` is ever pointed at deployed
    `rangeRows 30` + decided. Highest-value proactive guardrail: a lint forbidding decide/#guard/#eval
    over `rangeRows`/`rangeTable`/`subsetTable` with bits ≥ ~20. Core file — coordinate the edit.

## ⚑ LEAN COMPILE-COST PROFILING (2026-07-08) — measured fruit + ranked hitlist
Read-only scout (wf_38b54aa8, OOM-safe, no builds) over all 1025 Dregg2 .lean + my sequential guarded
measurement. MEASURED WINS (committed):
- EffectVmEmitV2 13.3→4.2s (−9s, 68%): a `#guard v2Registry.all (emitVmJson2 d).startsWith "…"`
  serialized all 39 descriptors to JSON per build → cheap structural smoke. 32 dependents.
- RotationV3 52.7→49.9s (−3s): same fix on v3Registry; its 50s is structural (below).
THE PATTERN (safe, mechanical, do across the tree when QUIET): registry-wide `#guard <reg>.all
(emitVmJson2 d).startsWith …` → `#guard <reg>.all fun (_,d) => !d.name.isEmpty && !d.constraints.isEmpty
&& d.traceWidth != 0`. emitVmJson2 stays byte-pinned per-family; only a #guard changes (can't break
dependents). The 49 per-family `#guard emitVmJson2 == "<exact>"` byte-pins are the LEGIBILITY assurance —
KEEP them.
RANKED HITLIST (deferred — dirty-file-blocked or deeper surgery; do on a quiet tree):
1. RotationV3 (~50s, imported×32) — 44 full-set `simp [memOpsOf, withRecordPin8Headroom2, …]` → `simp
   only [named lemmas]` (5-30x each); the file's real cost. HIGHEST cumulative value.
2. CrossTurnFreshness.lean — 65 bare `by simp` closing `none=some _` ctor-clashes → `by nofun`. DIRTY
   (another lane) — do when clean.
3. Transfer.lean — 15 `absurd _ (by simp)` → `nofun` + `hsat cX (by simp)` → `simp only [List.mem_*]`.
4. CapOpenEmit — registry length/shape facts proved by full-set simp → `by decide`/`rfl`.
5. FoldRefine — 13x `(by simp [foldDesc, foldConstraints])` → one reusable membership lemma.
6. ConditionalTurn.lean:989 — the tree's ONLY native_decide → decide. DIRTY.
Method proven: scout ranks (parallel, safe) → measure single-file via `lake env lean` under .bin/lean-safe
→ fix → re-measure. NEVER parallel builds.

## ⚑ RECOVERY (2026-07-08, power-loss cleanup, I am the main lane)
Tree recovering from a power-loss (22 dirty paths, NO merge conflicts = clean crash). Reconciled the
crash-orphaned final-flips debris:
- ✅ sdk RED (FullTurnWitness.authorization E0560) CLEARED during recovery — dregg-sdk builds green.
- ✅ COMMITTED 4 completed consumer flips recovered from debris (build green, 51.7s): bridge/verifier.rs,
  storage/blinded.rs, turn/executor/apply.rs, wire/server.rs — fully off stark:: onto descriptor_by_name
  → verify_vm_descriptor2 (postcard(Ir2BatchProof)).
REMAINING = ONE coherent unit: the BRIDGE-PRESENTATION ISSUER-MEMBERSHIP migration (the last 10 stark
refs), a SECURITY-CRITICAL data-model flip (do carefully/fresh, NOT tired):
  · bridge/present.rs — RealPresentationProof.issuer_membership_stark_proof (typed StarkProof, ~10 field
    accesses) + 4 PUBLIC verify fns (verify_presentation_full/_proof_complete/_presentation/_presentation_bb)
    still on stark::verify. The NEW path is BUILT alongside (Ir2IssuerWire, prove_issuer_membership_ir2_wire,
    DescriptorDispatchVerifier) — needs the struct+producer+4 verifiers moved to it in lockstep. NOTE:
    present.rs:150 says the field may be "only populated locally for debugging/off-chain" — CONFIRM whether
    the 4 verifiers are debug-only (lower risk) or the live wire path before flipping.
  ⚑ DE-RISKED (2026-07-08): the 4 verify fns are NOT the live wire path — verify_presentation_full has
  0 callers (dead); verify_proof_complete/_presentation/_presentation_bb are called ONLY from tests +
  a bench in present.rs. The LIVE executor verify already flipped to DescriptorDispatchVerifier
  (committed bridge/verifier.rs). So issuer_membership_stark_proof + its 4 verifiers are the LEGACY
  OFF-CHAIN/TEST path → this is CLEANUP (retire the StarkProof field + its off-chain verifiers + update
  tests to the Ir2 wire), NOT a live-security migration. Lower risk, but large + mechanical + coupled
  (the struct field ripples to ~10 accessors + sdk-net + tests).
  · sdk/privacy.rs:736 (1 issuer verify), sdk/verify.rs (×12), sdk/cipherclerk.rs (×2) — same/adjacent path.
  · dregg-sdk-net/client.rs:290 — calls the removed BridgePresentationProof::issuer_proof_bytes(); a
    CONSUMER of this migration (fix in lockstep, update to the new wire API). This is the workspace-red crate.
Then: delete hand AIRs → git rm circuit/src/stark.rs when grep==0. The migration is scoped; it wants
fresh careful attention + a round-trip test on the presentation-verify path (fail-open if wrong).

## ⚑ FINISH PLAN (2026-07-08, ember DECISION: FLIP to preserve API, not delete)
The last 18 true-live stark refs are ALL legacy/0-caller/test paths (live already flipped+committed).
ember chose FLIP (preserve the published-SDK API + capability on the new prover), NOT delete. 3 files,
sequential main-loop (coupled, no swarm), each build-gated + committed before the next:
1. bridge/present.rs (4) — MOST MECHANICAL: the Ir2IssuerWire + prove_issuer_membership_ir2_wire path
   is ALREADY BUILT (Gate-2 recovery). Flip RealPresentationProof.issuer_membership_stark_proof (typed
   StarkProof) + the 4 off-chain/test verify fns onto it; fix sdk-net's issuer_proof_bytes consumer.
2. sdk/verify.rs (12) — verify_authorization_proof + verify_selective_disclosure (0-caller PUBLIC API) +
   #[test]s. Flip onto descriptor verify (membership descriptor exists); port the tests to the Ir2 wire.
3. sdk/cipherclerk.rs (2) — compress/verify_compressed_history (0-caller PUBLIC): sovereign-history IVC.
   The REAL rewire (onto IvcBuilder/recursion, already imported) — do last, most care.
Then: the 7 comment-only files are fine; delete hand AIRs; git rm circuit/src/stark.rs when grep==0.

## ⚑⚑⚑ THE GOLDEN LIFT (2026-07-08, ember: "don't wuss out; comprehensive, matters for recursion/aggregation")
⚠ SOUNDNESS FINDING (ember caught it, I verified): the Ir2 migration REGRESSED the presentation/
authorization proof to LIGHT-CLIENT-UNSOUND. Proof:
- LEGACY bound StarkProof (circuit/presentation.rs generate_merkle_poseidon2_stark_proof_bound) carried
  action_binding[8] + composition + revealed-facts in the VERIFIED public inputs; verify_proof_complete
  checked pi[2..6]==compute_action_binding → a LIGHT CLIENT could verify the action binding.
- LIVE Ir2 path (prove_issuer_membership_ir2 → membership_witness_4ary) verifies ONLY [leaf,root].
  action/composition/facts fell to EXECUTOR-ONLY cross-checks (STARBRIDGE-FOLLOWUP-03 "Silver posture").
- Executor cross-checks protect NEITHER light clients NOR the recursion/aggregation FOLD (both verify
  proof+descriptor+PIs, never executor runtime). A membership proof minted for action X is replayable
  for action Y as far as a light client / an aggregator can tell. Kills the Rung-3 light-client goal.
DECISION: do B2 = THE GOLDEN LIFT (the deferred FOLLOWUP-03), comprehensively — make action_binding +
composition + revealed-facts genuine CONSTRAINED/committed public inputs of a bound-presentation
descriptor, so light clients AND the fold can verify them. This is a SOUNDNESS FIX gating the stark-kill
finish (do NOT flip the presentation fns onto plain [leaf,root] — that enshrines the hole).
STAGES (design-first, then Lean under .bin/lean-safe, sequential — NO parallel builds):
1. DESIGN scout RUNNING (a418b326) — map action-binding across binding/presentation/ivc/fold so the new
   descriptor COMPOSES into aggregation (binding must survive the fold to the root).
2. Author the bound-presentation descriptor in Lean (Emit) — leaf,root,action_binding[8],composition,
   revealed_facts as committed PIs; byte-pin.
3. Rung 0/1/2 (the audit's found-bug class applies: the PIs must genuinely BIND, not just be carried —
   prove a forge with wrong action REJECTS).
4. Circuit witness builder + descriptor_by_name arm.
5. Flip the presentation verify path (bridge 4 fns + circuit RealPresentationProof::verify + sdk) onto it.
6. THEN resume the stark-kill finish (sdk/verify, cipherclerk) + git rm stark.rs.
This is the campaign becoming what it was always about: not "delete the Rust" but "everything a
re-executor/light-client/aggregator checks is bound in the proof." The oaks, roots down to the source.

## ⚑ GOLDEN LIFT — APPROVED DESIGN (2026-07-08, ember: "best not parity; unlinkability soundness; NO residuals")
Architecture map (agent a418b326) settled it. Refined gap: the presentation-freshness descriptor DOES
bind action[8]+facts[8] and IS verified live (wire/server.rs:136) — BUT (1) it is NOT a dual-expose FOLD
carrier → its binding is DROPPED under recursion/aggregation (the light-client-at-the-root hole); (2)
the membership leg + bridge legacy fns verify plain [leaf,root]; (3) composition bound nowhere.
APPROVED DESIGN (do what is BEST, close everything provable, carriers-not-residuals):
- Make the bound-presentation a DUAL-EXPOSE FOLD CARRIER (the 9th; mirror the 8 existing
  *_binding_from_fold carriers — membership is the sibling). Claim slice = [action_binding[8],
  revealed_facts[8], presentation_tag]. prove_descriptor_leaf_dual_expose_at + carrier_claim_pins_admitted.
- COMPOSITION → bind to the ROOT FOLD-SEGMENT digest ([genesis,final,count,chain_digest]), NOT a separate
  commitment PI (best/recursion-native, ember chose over legacy parity). So NO composition[8] PI on the leaf.
- PRESENTATION_TAG → a CONSTRAINED PI with its Poseidon2 well-formedness IN-CIRCUIT (TID_P2 sub-desc) —
  unlinkability soundness at the aggregated root (ember chose comprehensive).
- Close the revealed-facts parity gap (PiBinding it + assert, don't inherit the "carried-not-checked" gap).
- Binding mechanism = committed-PI (PiBinding-pinned verified PI; light client recomputes off-circuit).
  BLAKE3 domain-sep/keyed-hash = a NAMED CRYPTO CARRIER (irreducible floor, like Poseidon2CR) — NOT a
  residual. Poseidon2 stages constrained in-circuit via TID_P2.
- Reuse MembershipBindingFromFold for issuer∈federation; connect membership-leaf + presentation-leaf via
  a binding node.
STAGES (sequential, Lean under .bin/lean-safe, each verified+committed before next):
  S1: the bound-presentation LEAF descriptor (Emit) + Rung-0 byte-pin + Rung-1 refine + Rung-2 no-forgery
      (wrong action/facts/tag REJECTS — the audit's carried-vs-bound lesson) + tag Poseidon2 in-circuit.
  S2: the dual-expose fold wiring + presentation_binding_from_fold Lean proof (verifying aggregate ⟹
      commitments forced-backed; both poles non-vacuous) + carrier_claim_pins_admitted arm.
  ✅ S1 DONE (23a0766f3): boundPresentationDesc — action/facts/tag CONSTRAINED PIs, tag in-circuit
     (Poseidon2, randomness hidden = unlinkability), Rung-0/1/2 (forge_action/facts/tag REJECT), axiom-clean.
  ✅ S2 DONE (d86fe24dc): presentation_binding_from_fold — the 9th BindingFromFold carrier; verifying
     aggregate FORCES the published authorization claim backed → binding RIDES THE FOLD to the root
     (light-client + aggregation soundness). Both poles non-vacuous, welds to the S1 leaf, NO axioms.
  ✅ S3a DONE (6056abc13): bound_presentation_witness + descriptor_by_name arm — bound descriptor USABLE
     end-to-end (7 round-trip tests, genuine Poseidon2 tag lanes, honest ACCEPT + 4 forge REJECT).
  ✅ S3b-i DONE (cfacb2b7f): presentation_leaf_adapter.rs (NEW) — prove_presentation_binding_node_segmented
     + PRESENTATION_CLAIM_LEN=17; folds a bound-presentation leaf + dual-exposes the authorization claim.
     6 tests pass (honest folds+binds+exposes; forged claim does NOT fold — both poles). The fold-carrier
     DEPLOYED as a callable adapter. Built in isolated CARGO_TARGET_DIR (shared target lock-contended).
  S3b-ii (BLOCKED: ivc_turn_chain.rs actively churned by other terminals — flickers dirty): the ONE
     dispatch match-arm wiring the adapter into the production turn-chain fold. Wait for a stable window.
  S3c (BLOCKED by other terminals: bridge/present.rs + sdk/cipherclerk.rs currently DIRTY): flip the
     live verify path onto the bound descriptor. Wait for those files to clear.
  S4: finish stark-kill (sdk/verify, cipherclerk) + git rm circuit/src/stark.rs.

## ⚑ S3d — BLINDED RING-MEMBERSHIP DESCRIPTOR (2026-07-08, ember: "build it too" — no-residuals maximal)
S3c flip revealed the legacy issuer_membership_stark_proof carries TWO properties the bound-presentation
descriptor doesn't: (a) issuer∈federation RING MEMBERSHIP (blinded Merkle path, air_name=BLINDED_MERKLE,
generate_blinded_merkle_poseidon2_stark_proof circuit/presentation.rs:1377) + (b) BLINDED-LEAF
UNLINKABILITY (fresh blinded_leaf per show; anonymity_soundness test + verify_anonymous_presentation +
test_ring_membership_unlinkable depend on it). ember chose: BUILD the blinded-membership descriptor too
(both in-circuit/fold-sound), not retire it. A full Golden-Lift-style sub-campaign mirroring S1-S3b:
  ✅ S3d-1 DONE (69f1af7bf): blindedMembershipDesc ("dregg-blinded-membership::v1", width 33) — 4-ary
    Merkle path proves HIDDEN leaf∈tree(root) + blinded_leaf=hash_2_to_1(leaf,blinding) via arity-2 chip
    (leaf+blinding hidden → unlinkable). Rung 0/1/2: forge_nonmember_rejected, forge_blinded_leaf_rejected,
    honest_two_shows_unlinkable (anonymity proven IN-CIRCUIT). Axiom-clean. Verified on my tree.
  ✅ S3d-2 DONE (02fc76cb3): blinded_membership_binding_from_fold — 10th carrier; ring+unlinkability ride
    the fold to the root. Payload+corollary+poles NO axioms; welds to deployed leaf. Verified my tree.
  ✅ S3d-3 DONE (c1ebf5910): blinded_membership_witness + blinded_membership_leaf_adapter + dispatch arm
    — usable+foldable end-to-end, 14 tests, unlinkability at witness AND fold levels. (+ a cross-lane
    turn/action.rs E0282 unblock committed separately.) Position-0 leftmost-child (like merkle);
    position-general = a named descriptor-lane follow-up.
  S3d-4: THEN S3c flip — RealPresentationProof carries BOTH wires (bound-presentation for auth +
    blinded-membership for ring/unlinkability); flip the 4 verify fns + verify_anonymous_presentation +
    the anonymity tests onto them. → 0 true-live stark in presentation → S4 git rm.
This makes the presentation family FULLY in-circuit: authorization + ring membership + unlinkability, all
constrained, all fold-carried to the root. The comprehensive close ember chose over the fast delete.

## ⚑ S3d-DIM: generalize blinded-membership to PRODUCTION dimension (2026-07-09) — no residual
The S3c flip attempt found the real gap: S3d-1/3 built blindedMembershipDesc at DEPTH-2/leftmost-child,
but production presentations use DEPTH-8, 4-ARY, GENERAL-POSITION paths (bridge/present.rs:1871 depth=8
position=i%4; :1790/:1834 federation-tree general positions). Flipping onto the depth-2 desc would Err
every real caller → all presentations fail. NOT a residual — FIX the dimension (ember: no little deaths).
The depth-general 4-ary machinery EXISTS (membership_descriptor_of_depth_4ary, MEMBERSHIP_4ARY_NAME_PREFIX
"merkle-membership::poseidon2-4ary-general-depthN") but publishes [leaf,root] = LINKABLE. So: build the
DEPTH-GENERAL, 4-ARY, GENERAL-POSITION BLINDED variant = 4ary-general path + the arity-2 blind tooth
(blinded_leaf=hash_2_to_1(leaf,blinding), leaf+blinding hidden) publishing [blinded_leaf, root]. That is
the missing depth-general-unlinkable descriptor. Then the flip is capability-preserving.
STAGES: (a) blindedMembershipDesc → depth-general 4-ary + general-position (Lean Emit + Rung-1/2, reuse
membership_descriptor_of_depth_4ary + the blind tooth); (b) blinded_membership_witness → general
depth/positions; (c) the fold proof/adapter generalize trivially (claim shape unchanged [blinded_leaf,root]);
(d) THEN S3c flip. Bound-presentation (auth half) is depth-independent — already flip-ready.
  ✅ S3d-DIM DONE (5e45912a7): blindedMembership4aryDesc(depth) — depth-general 4-ary general-position,
    name dregg-blinded-membership-4ary-general-depth{N}. THE PRODUCTION PROOF passes:
    honest_depth8_general_position_proves_and_verifies (real prover). Lean general-depth SAT⟹SEM +
    forge-rejects + unlinkability; Rust==Lean byte-parity depth 2&8. Staged-additive (depth-2 intact).
    → the flip is now capability-preserving.
  ✅ S3c FLIP DONE (79c630951): presentation family off hand-StarkProof onto BOTH descriptors (bound +
    blinded), 6 files, capability-preserving. dregg-circuit+bridge GREEN, 19+21 tests. presentation
    family = 0 true-live stark. Total prod true-live: 10→14... wait, DOWN to 14 in just 2 files.
  ✅ S3c-final DONE: sdk/verify.rs + sdk/cipherclerk.rs flipped (0 true-live; sdk own-code clean).
  LAST CONSUMER (2 true-live): circuit/src/cross_state_derivation.rs — a whole module still on the hand
    engine (StarkProof fields + prove_source_derivation_stark), consumed ONLY by teasting/tests/
    defi_primitives.rs. It's the DERIVATION family → flip onto the emitted derivation descriptor (exists;
    DerivationEmit + Rung-2 from the bugfix campaign). Needs a derivation witness builder (mirror the
    others) + flip the struct/producer/verify. Then: 0 true-live → delete hand AIRs → git rm stark.rs.


## ⚑⚑⚑ CONSUMER MIGRATION COMPLETE (2026-07-09) — the deletion gate is essentially clear
Rigorous recount (grepping ACTUAL call-sites, excluding p3_uni_stark:: false-positives + comments):
- **ZERO** cross-crate `dregg_circuit::stark::(prove|verify|proof_*)` calls.
- **ZERO** non-test `crate::stark::(prove|verify)` calls inside circuit/ production code.
- Remaining hand-engine references are: (a) the hand-AIR DEFINITION files (*_air.rs, dsl/*) — the
  DELETE TARGETS themselves, not consumers; (b) circuit/src/dsl/circuit.rs:1474 = a #[cfg(test)] use;
  (c) sel4/.../crypto-floor uses `stark_core::stark` — a SEPARATE VENDORED copy (decoupled by design,
  NOT circuit/src/stark.rs — does not block the rm).
Every real production consumer is flipped onto the descriptor prover. The Golden Lift closed the
presentation family (auth + ring membership + unlinkability, in-circuit, fold-carried) + cross_state_
derivation (last StarkProof struct consumer). WHAT REMAINS for git rm circuit/src/stark.rs: delete the
orphaned hand-AIR files (*_air.rs, the dsl/*.rs StarkAir impls) — KEEPING poseidon2 CHIP machinery the
descriptor prover uses (poseidon2_air.rs needs the chip/trace-gen split checked) — then rm stark.rs +
fix the #[cfg(test)] site. This is the deletion sweep, gated only on: is poseidon2_air chip-vs-AIR
separable, and confirming no non-vendored prod path breaks.

## ⚑⚑⚑ THE ENGINE IS DELETED (2026-07-09) — stark-kill core COMPLETE
- ✅ `circuit/src/stark.rs` DELETED + committed (f04b2dd1e). circuit/turn/bridge/sdk all GREEN on the
  descriptor prover. The O(n²) engine that started this (perf review 3e88a1a40) is gone.
- ✅ sdk+intent repaired (95836f657) — onto the descriptor prover; deleted an old fail-OPEN
  verify_compressed_history hole in passing.
- ✅ 5 predicate-comparison descriptors EMITTED (2d2c93801): Lte/Gt/Lt/Neq/InRange, Rung 0/1/2,
  axiom-clean, dispatched, consumers WIRED (emit-not-record).
- ✅ Golden Lift intact: bound-presentation + blinded-membership, in-circuit + fold-carried,
  light-client-sound (the hole ember caught, sealed).
HONEST TAIL (fail-CLOSED — safe, never fail-open — the remaining emit-forward work):
  · committed-threshold descriptor (golden exists in a circuit-prove test; register + emit Rung 0/1/2).
  · validated-IVC-fold verify, multi-step-authorization, programmable-predicate-programs — compositional
    proof types with no single descriptor yet.
  · Broken tooling crates from the deletion (NOT core): dregg-doc, preflight, wasm, the circuit lib-TEST
    target (ivc.rs MultiTurnVerification/ValidatedIvcVerification dead refs), intent #[cfg(test)] modules.
  · Workspace-wide build still blocked by the PARALLEL PQ-lane blocklace/crypto-hermine break (not ours).
NEXT NORTH STAR (ember's actual pre-quest goal, resumed): governance-as-stories + SPWEEN (verifiable
collaborative CYOA/MUDs) + substrate-native voting — now on a fast, verified, light-client-sound prover.

## ⚑ GOAL RE-SET (2026-07-16, ember): retire every FIRST-PARTY Rust-authored circuit; emit from Lean
The engine is dead (07-09). This is the tail ember re-aimed: **first-party circuits still authored in
Rust**, + the **fictions** that keep re-fooling audits. Rule: **never hand-author a constraint to close a
gap; if an emitter is missing, NAME it.**

### THE FINDING THAT SETS THE BAR (why lowering ≠ emitting)
`cellprogram_to_descriptor2` is PROVED faithful (`CustomLeafEncoding.lean::cell_to_descriptor_faithful`,
`encodeLocal_holdsAt_iff`, `encodeTransition_holdsAt_iff`, mod-p residues). But that proves **"the encoding
preserves whatever Rust said"** — NOT **"what Rust said is the right circuit."** Nobody proved
`dsl/revocation.rs`'s 40 constraints enforce non-revocation. **Emission is what buys correctness**:
`NonRevocationEmit.lean` PROVES the statement and emits the descriptor as a consequence — proof and
deployed bytes are one artifact. That is why law #1 says EMIT, not LOWER.

### ARCHITECTURE, VERIFIED (4 audits got this wrong — do NOT re-derive)
| system | authored | interpreter | status |
|---|---|---|---|
| Rust DSL (`dsl/circuit.rs` `CircuitDescriptor`/`ConstraintExpr`) | Rust | `dsl_p3_air` | grammar+interpreter LEGIT (host-trusted `ProgramRegistry`, unknown vk_hash fails closed, lowers to IR2 + `verify_vm_descriptor2`); **first-party circuits authored in it = THE violation** |
| Lean `Exec/CircuitEmit` → `EmittedDescriptor` | Lean (proved) | `LeanDescriptorAir` | **DEAD** — interpreter referenced only in its own file (IR-v1, superseded by IR-v2) |
| Lean `Circuit/Emit/*.lean` (174 mods) → `EffectVmDescriptor2` | Lean | `descriptor_ir2`/`Ir2Air` | **LIVE + law-compliant** — 110 consumers |

**THREE constraint dialects** — a grep that sees only #1 LIES (this burned 4 audits incl. 2 of mine):
1. `builder.assert_zero(..)` (greppable) · 2. `Constraint { eval: Box::new(..) }` (closures, invisible)
· 3. `ConstraintExpr::{..}` struct literals (data, invisible)

### DONE 2026-07-16
- `9ba02881b` — **the hand Merkle AIR is DEAD.** `P3MerklePoseidon2Air` retired; deployed membership leg
  proves via `MerkleMembership4aryEmit.lean`'s byte-pinned descriptor. Teeth PASS (forged root/leaf/
  non-member all rejected). The emitter had EXISTED and the deployed path ignored it — the recurring sin.
  Also swept 4 pre-existing dangling tests (875 lines) that had never compiled.
- `f7d09d5f5` — swept 4 dead pre-law AIRs (1080 lines) incl. `schnorr_air`'s 591 lines of UNASSURED hand
  curve algebra (dead: only reachable via lib.rs's own mod decl).
- `8cc7ef821` — deleted 5 lying `*_air` re-export shims (`_air` name on a DSL re-export = the fiction that
  made every audit over-count); repointed ~22 importers to `dsl::{fold,predicates}`.
- `ece829fc2` — renamed 3 husks to the truth (`note_spending_witness`/`bridge_action_witness`/
  `multi_step_witness`, 49 files). **Did NOT rename `garbled_air`/`membership_adjacency_air`/
  `derivation_air` — they have LIVE algebra in dialects 2/3; renaming would have BURIED violations.**

### CURRENT THRUST + NEXT 3
1. ~~Non-revocation cutover~~ **BLOCKED — DEPTH GAP (named, not forced).** The emitter exists AND a
   production witness builder exists (`circuit/src/non_revocation_witness.rs`, 0 consumers — rail built,
   unused). BUT the emitted descriptor is **depth-2 / 4-leaf**: `root = hash_2_to_1(hash_2_to_1(L,R),
   sib1)`, ONE `level1_sibling` (`non_revocation_root_depth2(&[BabyBear;4])`; `NonRevocationEmit.lean:44`
   — "the depth-2 tree's BOTTOM SIBLINGS sharing the path to the root"). The DEPLOYED
   `DslRevocationTree` is **`TREE_DEPTH = 4` / 16 leaves** (`dsl/revocation.rs:22-24`). Cutting over would
   SHRINK the tree 16→4 = a functional regression dressed as compliance. **NAMED RESIDUAL:
   `NonRevocationDepthResidual`** — the emitter must be generalized to depth-4 (or a parameterized depth /
   an iterated path fold) before `sdk/privacy.rs:621,762` + `full_turn_proof.rs:4692,4999` can move.
   Do NOT hand-author the extra levels in Rust.
2. ~~Delete dead `dsl/derivation.rs`~~ **CORRECTED — NOT dead; it is a CUTOVER, not a delete.** (A scout
   lane claimed "no callers outside dsl/" — WRONG, and I nearly deleted a live dep.) `circuit/src/
   derivation_witness.rs:41` — the EMITTED path's own witness builder — USES
   `dsl::derivation::generate_derivation_trace_dsl` deliberately ("NOT a reconstruction"), and
   `dregg-dsl-runtime/src/lib.rs:90-92` re-exports it. The emitted twin IS live (`dregg-derivation-v1`,
   `DerivationEmit.lean`, proved via `descriptor_by_name` + `prove_vm_descriptor2`). What is SUPERSEDED is
   only the Rust-authored CIRCUIT (`derivation_circuit_descriptor`/`derivation_dsl_circuit`), still
   consumed by `derivation_air.rs:372` + `dsl/descriptors.rs:734`. **Unit = point those two at the emitted
   descriptor; KEEP the trace generator** (trace-gen is legitimate Rust; the constraints are not).
3. ✅ **DONE `59a601aab` — the fictions are dead.** `Claims.lean` §23 carries a SCOPE note (CircuitEmit
   proves its OWN grammar on the DEAD IR-v1 rail; NOT the Rust DSL's `ConstraintExpr`; `#assert_namespace_
   axioms` checks axiom hygiene only — which is how it survived). Dead rail marked at BOTH ends
   (`lean_descriptor_air.rs` "RETIRED / IR-v1", `Exec/CircuitEmit.lean` "DEAD IR-v1 RAIL"). Verified: lake
   build Dregg2 9697 jobs green + cargo check green.

### NEXT 3 (rolling)
1. ~~Derivation cutover~~ **DEPRIORITIZED — it is TEST-ONLY scaffolding, not a deployed violation.**
   `DerivationAir` is instantiated ONLY inside `ivc.rs`'s `#[cfg(test)]` module (`:1866/:1914`; last
   `#[cfg(test)]` at :1535). PRODUCTION derivation already proves via the EMITTED `dregg-derivation-v1`
   (`derivation_witness.rs` → `descriptor_by_name` → `prove_vm_descriptor2`). So `derivation.rs`'s 59
   `ConstraintExpr` sites are test scaffolding + a trace generator the emitted path reuses. Retire the
   hand `StarkAir` impl with its test when convenient; KEEP the types (`CircuitRule`/`DerivationWitness`,
   used by `bridge/present.rs`) + `generate_derivation_trace_dsl`. LOW priority — no deployed exposure.
   (NOTE: `constraint_prover` is a row-by-row constraint VALIDATOR, not a STARK prover — `ivc.rs:41`,
   `committed_threshold.rs:44` use it in production for validation, which is legitimate.)
2. **`ivc.rs::StateTransitionAir`** — its emitter (`dregg-ivc-state-transition-v2`) EXISTS and round-trips
   in 2 tests but NO production path consumes it. Pure Merkle-mold cutover.
3. **`garbled_air.rs`** (16 sites, closure dialect) — `GarbledEvalEmit.lean` exists; check coverage before
   moving (learn from the non-rev depth trap: verify the emitter COVERS the deployed shape first).

### NAMED RESIDUALS (do NOT hand-author)
- `ivc_turn_chain.rs` (14 sites): **no emitter covers it** — needs `EffectVmEmitTurnChainBinding.lean`
  (`dregg-turn-chain-binding-v2`). The existing IVC ladder emits a DIFFERENT circuit and Lean PROVES it
  too weak (`ivc_anchor_insufficient`: intermediate roots are FREE columns). Rewiring = soundness
  REGRESSION (would delete the temporal tooth closing CRITICAL HOLES #1/#2/#6). NAMED, not laundered.
- `ivc.rs::StateTransitionAir`: emitter EXISTS (`dregg-ivc-state-transition-v2`, round-trips in 2 tests)
  but NO production path consumes it. Merkle mold — tractable.
- `dsl/cap_membership.rs` (5): emitters cover cap-open only as an in-VM appendix, not a standalone leg.
- `garbled_air.rs` (16, dialect 2) + `membership_adjacency_air.rs` (10, dialect 3): live violations.
  `GarbledEvalEmit.lean` exists.
- First-party DSL sites remaining: derivation 59 (dead) · revocation 40 · note_spending 27 · fold 15 ·
  committed_threshold 12 · cap_membership 5.

### ⚑ SCOPE FINDING (2026-07-16) — the DEPLOYED violation surface is ~EMPTY; what remains is scaffolding
Chased the goal's target list unit-by-unit. **Every claimed "deployed violation" dissolved on inspection**
— three in a row — because THIS LANE ALREADY MIGRATED THE DEPLOYED PATHS (07-09, `f04b2dd1e` et al). The
hand AIRs that remain are unused/test/type-only husks. Verified per target (production = non-test,
non-bench, non-comment reference):
- `ivc.rs::StateTransitionAir` — **NOT deployed.** `circuit::ivc::prove_ivc` has ZERO production callers
  (`bridge/present.rs::prove_ivc` is `PresentationAir`'s OWN method — a different fn). Lane A's "still the
  hand AIR actually proving" was wrong. Its emitter (`dregg-ivc-state-transition-v2`) exists; nothing to cut.
- `derivation_air` — **test-only.** `DerivationAir` instantiated only in `ivc.rs`'s `#[cfg(test)]`; its 19
  "production refs" are TYPE imports (`CircuitRule`/`DerivationWitness`). Production derivation already
  proves via the EMITTED `dregg-derivation-v1`.
- `garbled_air` — **retired.** `garbled.rs:453` literally says "…are retired. The production path is [DSL]";
  the only real import is `GARBLED_EVAL_AIR_WIDTH`/`col` = LAYOUT CONSTANTS, not constraints.
- `membership_adjacency_air` — a DOC COMMENT in `adjacency_witness.rs`. `cert_f_air` — a BIN only (and
  codex already deleted 165 lines of its Rust-authored algebra, making Rust REFUSE). `field_delta_range_air`
  — **0** production refs (codex already moved it to `parse_vm_descriptor2`).

**Conclusion:** law #1 holds on every deployed path we can find. The remaining first-party `ConstraintExpr`
sites (`dsl/{derivation 59, revocation 40, note_spending 27, fold 15, committed_threshold 12,
cap_membership 5}`) are TEST SCAFFOLDING + TRACE GENERATORS (legit Rust) + circuits whose production
consumers already run the emitted twin. The ONE genuine deployed gap found tonight is
**`NonRevocationDepthResidual`** (emitter depth-2/4-leaf vs deployed depth-4/16-leaf) — named, not forced.

**This does NOT mean "done":** it means the goal's premise (that deployed Rust circuits lack Lean
semantics) is now FALSIFIED for the paths checked, and the honest remaining work is (a) generalize the
non-rev emitter to depth-4, (b) delete the unused/test hand-AIR husks so they stop faking a violation
surface, (c) `ivc_turn_chain` — the ONE hand AIR with real deployed algebra and NO emitter (needs
`EffectVmEmitTurnChainBinding.lean`; rewiring to the existing ladder = proven soundness REGRESSION).

### ⚑⚑ THE ONE GENUINE DEPLOYED VIOLATION (2026-07-16) — `ivc_turn_chain` (confirmed, not dissolved)
Unlike every other target tonight, this one is REAL and PRODUCTION:
- `grain-verify/src/r3.rs:139` calls `prove_turn_chain_recursive_without_host_gate(finalized, &selectors)`
  + `verify_whole_chain_proof_bytes` (imports at `:44-47`) — the WHOLE-HISTORY chain proof a renter
  verifies (`r3_verify`). Also live in `grain-turn/src/finalize.rs`, `lightclient/src/bin/{produce_history
  _envelope,whole_history_demo}.rs`.
- It rides `circuit-prove/src/ivc_turn_chain.rs`'s `TurnChainBindingAir` — **14 hand-authored constraint
  sites, width 359, and NO emitter covers it.** Its algebra (chain continuity `new_root[i]==old_root[i+1]`,
  the acc digest chain, idx increment, the is_real/real_count padding subsystem, an INLINED
  poseidon2_permute_expr) is the deployed whole-history binding.
- **Rewiring to the existing IVC ladder is a PROVEN soundness REGRESSION** — `EffectVmEmitIvcStateTransition*`
  emits a DIFFERENT circuit (width 11, chains over accumulated HASH not state ROOT, preimage leads with
  IVC_DOMAIN_TAG not acc_in), and `Rung2Full::ivc_anchor_insufficient` PROVES it admits a forged history
  ("every old_hash for i>0 is a FREE column; the public commitment carries NO binding on intermediate
  roots"). Consuming it would delete the temporal tooth closing CRITICAL HOLES #1/#2/#6.

**THE WORK (the goal's real content):** author `metatheory/Dregg2/Circuit/Emit/EffectVmEmitTurnChainBinding
.lean` emitting `dregg-turn-chain-binding-v2` — two `windowGate`s w/ `onTransition` (root continuity + idx
increment), the acc digest chain (boundary + windowGate), `piBinding .last` for final_root, a `perRowHash`
lookup with the TURN-CHAIN preimage `[acc_in, old_root, new_root, idx]`, and the is_real/real_count
subsystem (bool gate + 2 windowGates + first-row boundary + last-row piBinding). **No IR-v2 extension
needed** — `windowGate`/`onTransition` exists (`DescriptorIR2.lean:390-397`) and `descriptor_ir2.rs`
already decodes it (`:644-671`, `:1054-1063`); 12 emitters use it.
**One correction for whoever writes it:** the base module omits continuity citing padding-safety
("would fire on the padded copies") — that reasoning is specific to `ivc.rs`'s duplicate-last-row padding
and does NOT transfer. `generate_chain_trace_rotated` (`ivc_turn_chain.rs:1044-1054`) pads with
`old_root = new_root = final_root`, still-incrementing `idx`, and a genuinely-continued hash chain — so
continuity holds across real→pad and among pads, and `onTransition := true` IS sound here. Carry the FULL
gate set; do not inherit the base module's faithful-omission posture.

### ✅ EMITTER + RUNG 2 CLOSED (uncommitted supervisor handoff)
`EffectVmEmitTurnChainBinding.lean` now emits byte-pinned `dregg-turn-chain-binding-v2`: all fourteen
`TurnChainBindingAir::eval` sites, including full real→padding root/acc/index continuity and the exact
turn-chain preimage `[acc_in, old_root, new_root, idx]`. The shared Poseidon2 chip reduces the main trace
from the hand AIR's 359 columns to 14 without changing the hash equation. Rung 1 proves descriptor
satisfaction over any sound chip table implies the direct Rust-row semantics; Rung 2 proves the full
constraint set iff those semantics against the canonical genuine chip row. A four-row two-real/two-pad
witness is SAT, and concrete continuity/index/real-count forgeries are each formally UNSAT. All 18
theorems are individually `#assert_axioms`-pinned; no `sorry`/`admit`/`native_decide`/axiom declaration.
The all-row `is_real` boolean law deliberately uses `windowGate { onTransition := false }`: IR-v2
`.base (.gate ...)` is transition-only and would omit Rust's last-row assertion. Local
`lake build Dregg2` is green (9699 jobs). **No semantic or IR-expressibility residual.** The production
Rust path still needs the separate descriptor-consumption cutover; this authoring turn changed no Rust.

### `d7d170aa3` — turn-chain EMITTER landed (semantics), but it is NOT yet deployable — honest scope
`EffectVmEmitTurnChainBinding.lean` (32.5KB) is GREEN (lake build Dregg2, 9699 jobs), forbidden-clean, 18
`#assert_axioms`, wired into the root, with REAL refutation teeth (`turnChain_rejects_broken_continuity` /
`_bad_idx_step` / `_bad_real_count`) + a 4-row two-real/two-padding witness proving continuity across
real→pad AND pad→pad, frozen padding count, `real_count == num_turns`.
**What it is NOT (verified by my own gate, not taken on report):** there is **no JSON emission** — no
`toJson`/emit entry, no `circuit/descriptors/by-name/*turn-chain*`, no `descriptor_by_name` STATIC_GOLDENS
registration. So the deployed `grain-verify/r3.rs:139` path STILL runs the hand `TurnChainBindingAir`.
The module is the LEAN AUTHORSHIP of the constraints; the deployable artifact does not exist yet.
**Remaining bricks (in order):** (1) emit the descriptor JSON from the Lean module; (2) byte-pin it —
`descriptors/by-name/turn-chain-binding.json` + STATIC_GOLDENS + an emit-gate test with a `GOLDEN_JSON`
const (the `accumulator_nonrev_emit_gate.rs` pattern); (3) a production witness/trace builder (the
`non_revocation_witness.rs` / `membership_witness_4ary` analog); (4) cut `prove_turn_chain_recursive_
without_host_gate` onto `parse_vm_descriptor2`/`prove_vm_descriptor2`, keeping `generate_chain_trace_
rotated` (trace-gen is legit Rust). Only after (4) is the law satisfied on that path.

### `eeb6ccbe9` — bricks 1-2 DONE: `dregg-turn-chain-binding-v2` emitted + registered
- **Brick 1** `metatheory/EmitTurnChain.lean` — byte source via `emitVmJson2` (the `EmitRotationV3.lean`
  mechanism, `lake env lean --run`). Emits 2148 bytes: ir2, width 14, 4 PIs, **6 window_gate** (incl. the
  `on_transition:true` continuity tooth the base ladder omits) + 4 pi_binding + 3 boundary + 1 lookup.
- **Brick 2** registered in `descriptor_by_name.rs` STATIC_GOLDENS + `descriptors/by-name/turn-chain-binding.json`.
- **Verified NOT just "compiles"**: `dispatch_names_decode_and_check` DECODES + `check_descriptor2_wellformed`s
  every registered golden — 9/9 pass. cargo check green over circuit+bridge+circuit-prove --tests.
- **Fixed a bug I shipped in `ece829fc2`**: my husk-rename sed'd `bridge_action_air_v1` ->
  `bridge_action_witness_v1` inside a **WIRE IDENTIFIER** (dispatch key + `air_id`) while the JSON's
  authoritative `name` still said `_air_v1`. **Lesson: a mechanical rename must NEVER touch protocol
  strings.** Restored across 5 files. The dispatch gate caught it — that is why the gate exists.
- **NEXT**: (3) emit-gate byte-pin test (`accumulator_nonrev_emit_gate.rs` GOLDEN_JSON pattern) +
  production witness builder; (4) cut `prove_turn_chain_recursive_without_host_gate` onto
  parse/prove_vm_descriptor2, KEEPING `generate_chain_trace_rotated`. Until (4), `grain-verify/r3.rs:139`
  still runs the hand AIR.

### Brick 3 recon — the width 14 vs 359 question RESOLVED (the cutover is viable)
The hand `TurnChainBindingAir` is **width 359** = 7 scalar cols + a **352-col inline Poseidon2 permutation
aux block** (`BINDING_AUX0 = 7`). The emitted `dregg-turn-chain-binding-v2` is **width 14** = `7 +
(CHIP_OUT_LANES - 1)` because it replaces those 352 inline columns with a **CHIP LOOKUP** —
`{"t":"lookup","table":1,"tuple":[const 4, var 2 (acc_in), var 0 (old_root), var 1 (new_root), var 4
(idx), ...]}` — i.e. exactly the turn-chain preimage `[acc_in, old_root, new_root, idx]`, served by the
shared Poseidon2 chip table.
**The scalar layouts MATCH EXACTLY**: Lean `Chain.{OLD_ROOT=0, NEW_ROOT=1, ACC_IN=2, ACC_OUT=3, IDX=4,
IS_REAL=5, REAL_COUNT=6}` ≡ Rust `{COL_OLD_ROOT=0 … COL_REAL_COUNT=6}`. So the emitted descriptor is a
faithful + strictly leaner realization (352 fewer columns, chip-shared). The cutover is NOT a drop-in only
because the trace must be rebuilt in the chip-lane layout instead of the inline-aux one — that is brick 3
(the witness builder), and `prove_vm_descriptor2`'s `trace_with_chip_lanes` refills the chip lanes.

### `7e56e5439` + `e9cd79030` — the last two DEAD hand-authored circuits deleted (dialects 2 and 3)
- **`garbled_air.rs` 459 -> 139**: `GarbledEvaluationAir` + its **16 closure-dialect** constraints deleted.
  Never instantiated outside its own tests; only the LIVE layout constants (`GARBLED_EVAL_AIR_WIDTH`,
  `col`) kept. No coverage lost — the emitted path's teeth are stronger and I RAN them: 6/6 pass
  (forged_commitment_pi / forged_table_entry / forged_gate_index_delta / non_boolean_selector /
  broken_wire_chaining / ambiguous_gate_type). **This is the file I nearly renamed to a husk name earlier
  — which would have BURIED 16 live constraints behind a truthful-sounding filename.**
- **`membership_adjacency_air.rs` 561 -> 339**: `adjacency_descriptor()` (**10 data-dialect** sites) +
  `adjacency_circuit()` (zero callers) deleted. Production already ran the emitted
  `dregg-membership-adjacency::poseidon2-v1`. **The emitted version is STRICTLY STRONGER**: the
  `idx_upper - idx_lower == 1` tooth lived only in a RUST VERIFIER WRAPPER and was ABSENT from the hand
  descriptor; the Lean emit INTERNALIZES it into the circuit, closing the wide-bracket forge a caller
  could otherwise bypass. Emitting didn't just move algebra — it FIXED A GAP. Emitted teeth: 10/10 pass.

**Scoreboard**: every `*_air.rs` in circuit/ + circuit-prove/ now reports **0 constraint sites across all
three dialects**, except the legitimate INTERPRETERS (`descriptor_ir2` 117, `lean_descriptor_air` 9 [dead
IR-v1, marked], `effect_vm_p3_air` 9 [self-disclaiming shape probe], `bilateral_aggregation_air` 7
[emitted], `lean_lookup_air` 3 [proven range gadget]). The ONE remaining hand-authored circuit on a
DEPLOYED path is `ivc_turn_chain` — its emitter now exists + is registered (bricks 1-2); the cutover
(bricks 3-4) is in flight with codex.

### `NonRevocationDepthResidual` — DIAGNOSED precisely (2026-07-16). The fix is a KNOWN pattern.
Ran down WHY the emitter is depth-2 and what would close it. The two witness builders are structurally
different, and that is the whole gap:
- **Membership (depth-GENERAL, the pattern that works)**: `membership_witness_4ary`
  (`circuit/src/membership_descriptor_4ary.rs:150`) does `for (sibs, &pos) in siblings.iter().zip(
  positions.iter())` — **ONE TRACE ROW PER MERKLE LEVEL**, so `depth == trace height`. The descriptor is
  named `merkle-membership-depth2-4ary` but serves ARBITRARY power-of-two depth, because its constraints
  are per-row + transition and the co-path folds ACROSS ROWS. `descriptor_by_name.rs:25` records it:
  "`merkle-membership-depth2-4ary::poseidon2-v1` + the depth-GENERAL builder".
- **Non-revocation (depth-2 ONLY)**: `non_revocation_witness_with_height`
  (`circuit/src/non_revocation_witness.rs:163`) does `(0..height).map(|_| row.clone())` — it **CLONES ONE
  ACTIVE ROW**; `height` is only trace PADDING, not a co-path fold. The circuit takes a single
  `level1_sibling` and computes `root = hash_2_to_1(hash_2_to_1(L,R), sib1)`. `NonRevocationEmit.lean:44`
  calls this "the depth-2 tree's BOTTOM SIBLINGS sharing the path to the root", :51 "a representative
  shape — exactly the depth/shape fixing `MerkleMembershipEmit` does for membership".
**THE FIX (named, not forced):** restructure the non-rev descriptor to the MEMBERSHIP pattern — one row per
level with the co-path folded by a transition/windowGate, instead of one active row with a single sibling.
Then the same descriptor serves the deployed `TREE_DEPTH = 4` (16 leaves) and the builder becomes
depth-general. This is Lean work in `NonRevocationEmit.lean` (+ its witness builder), NOT a Rust patch.
Until then `sdk/privacy.rs:621,762` + `full_turn_proof.rs:4692,4999` correctly stay on the hand circuit —
cutting over would SHRINK the revocation tree 16 -> 4 leaves.

### `NonRevocationDepthResidual` — the FIX is COMPOSITION, not a restructure (refined 2026-07-16)
Chased it further and found the pieces already exist; the depth-2 limit does NOT require redesigning
`NonRevocationEmit`. A sorted-tree non-revocation proof = **(a) the two neighbours are ADJACENT MEMBERS**
+ **(b) the queried item is STRICTLY BRACKETED, L < x < R**. Those two halves are split across two
already-emitted descriptors:
- **(a) is SOLVED and DEPTH-GENERAL** — `dregg-membership-adjacency::poseidon2-v1` (kind `NonMembership`).
  Its builder `circuit/src/adjacency_witness.rs` emits a 32-col trace with **ONE BINARY-TREE LEVEL PER ROW**
  (two parallel authentication paths lower ‖ upper + a shared power-of-two index accumulator), PIs
  `[root, leaf_lower, leaf_upper, idx_lower, idx_upper]`. Consecutiveness (`idx_upper - idx_lower == 1`) is
  INTERNALIZED in the descriptor (the wide-bracket forge `(5,7)` — both real members, not adjacent — is
  REJECTED). Depth-general because the co-path folds ACROSS ROWS, exactly like `membership_witness_4ary`.
- **(b) is where the depth-2 shape lives** — `dregg-non-revocation-sorted-tree::poseidon2-v1` (kind
  `BlindedSet`) carries the ORDERING algebra (`DIFF_L`, `DIFF_R`, `RL`, `RR` + the 30-bit range wires) but
  welds it to a single-active-row depth-2 Merkle shape (`root = hash_2_to_1(hash_2_to_1(L,R), sib1)`).
**THE FIX:** keep the depth-general adjacency descriptor for the membership half and emit the ORDERING
half against it (the `L < x < R` range wires already proved in `NonRevocationEmit`), instead of restructuring
NonRevocationEmit's Merkle shape to per-level rows. i.e. the deployed `TREE_DEPTH = 4` non-revocation is
`adjacency (depth-general) ∘ ordering`. **Do NOT put the ordering in a Rust verifier wrapper** — that is
precisely the gap the adjacency emit just FIXED by internalizing consecutiveness (it lived in a wrapper a
caller could bypass). Still NAMED, not forced: `sdk/privacy.rs:621,762` stays on the hand circuit until the
composed descriptor exists.

### ⚠ OPERATIONAL HAZARD (2026-07-16) — MULTIPLE codex processes; the dirty tree is a MIX
`pgrep -f 'codex exec'` shows **3 concurrent codex processes** — mine (the turn-chain cutover) plus the
parallel terminal's. **A running codex is NOT necessarily yours** (ember flagged this after I misread one
as mine). The working tree therefore contains OTHER LANES' uncommitted work: e.g. `metatheory/Dregg2/
Circuit/VacuitySweepTeeth.lean` + `metatheory/Dregg2/Crypto/HardQuantVacuity.lean` appeared mid-run and are
NOT part of any stark-kill unit.
**RULE for this lane:** commit ONLY files that the deputized run's own REPORT names, cross-checked against
the brief. Never `git add -A`; never infer ownership from "it is dirty and it builds". (Cost of getting
this wrong, already paid once tonight: `ece829fc2` swept a rename into a WIRE IDENTIFIER —
`bridge_action_air_v1` -> `..._witness_v1` — which the dispatch gate caught in `eeb6ccbe9`.)

### ⚑ SCAR AUDIT (2026-07-16) — and it caught a scar *I* made tonight
Ran a 3-lane read-only scar hunt. **It killed 2 of my 3 premises** — the corrections are the finding:
- **`dregg-dsl-runtime` is NOT a husk.** 17 crates depend on it, and `dregg-dsl/src/gen_rust.rs:190` +
  `gen_kimchi.rs:60` make the **proc-macro emit code naming `dregg_dsl_runtime::` paths** — it is the
  runtime contract for generated code and cannot fold into `dregg-circuit` without rewriting codegen.
  What IS true: `circuit/src/dsl/mod.rs:3-5`'s docstring ("previously split across dregg-dsl-runtime")
  reads as though the migration finished. It did not — 2217 lines of unique code remain there. **Fix the
  prose, not the code.** (This is the docstring that would send audit #5 hunting a husk that isn't there.)
- **The two descriptor dirs are NOT a scar** — different purposes, **zero orphans** (every json is
  `include_str!`d). The IR-v1 rail **cannot** be deleted either.
- **REAL FIND (HIGH): a second, name-colliding `DslP3Air`.** `dregg-dsl-runtime/src/dsl_plonky3.rs:41`
  (868 lines, p3-uni-stark) duplicates the production `circuit/src/dsl/dsl_p3_air.rs:88` (1341 lines,
  p3-batch-stark) — and the duplicate **cannot express `Hash`** and **silently enforces `BoundaryRow::
  Index(n>0)` on row 0**. Zero non-test consumers. The kicker: the **differential harness**
  (`dregg-dsl-differential`) — whose whole job is catching a backend disagree — round-trips through the
  NON-production interpreter and SKIPS membership coverage citing "DslP3Air cannot inline Poseidon2"
  (`plonky3_runner.rs:77`) — TRUE of the duplicate, **FALSE of production**. It is skipping coverage
  because of a rail nobody ships. Fix = repoint the harness at `dsl_p3_air::{prove,verify}_dsl_p3`, then
  delete the duplicate; the payoff is UN-SKIPPING membership.
- **`MembershipConstraint`** (`dregg-dsl-runtime/src/lib.rs:211`) — verified 1 tree-wide hit (its own def).
  Pure orphan, safe delete.
- **7 crates fell OUT of the build entirely** (own `[workspace]`, never in CI, zero dependents):
  `crypto-tanuki` (1496 LOC/22 tests), `crypto-traccoon` (1426/17), `crypto-hashrand` (803/8),
  `crypto-xmvrf` (642/17), `cosmos-settlement` (809/5), `cosmos-lock` (541/12), `tools/deployer-gate`
  (710/14) — **~6,400 LOC and 95 tests that have NEVER run in CI**, 64 of them on CRYPTO code. The tell it
  is drift not intent: `exclude` lists `solana-lock`/`solana-settlement` but NOT their siblings
  `cosmos-*`, and every other exclude entry carries a one-line reason; these have none. (Also: it is 201
  members / 140 default-members, not 182. And "zero-dependent = dead" is FALSE here — all 15 candidates
  are leaf apps/harnesses with real tests. **No crate is safe to delete.**)
- **LOW**: `dregg-cert-f-ir2.json` is `include_str!`d but is the ONLY flat descriptor absent from
  `descriptors/PROVENANCE.json`'s 74 sha256 pins (which was itself cut from a dirty tree,
  `PROVENANCE.json:6 "source_dirty": true`). `metatheory/EmitCrossCellConservation.lean:6` points at a
  `-v1.json` that does not exist (live is `-v2`) — the only dangling descriptor reference in the tree.

### `2b5c26728` — the audit caught a scar I MADE tonight. Fixed.
My law-#1 commit `9ba02881b` retired `plonky3_prover::{prove,verify}_plonky3` — and
`teasting/tests/proof_round_trip.rs:33` USED them. My gate that day was `cargo check -p dregg-circuit -p
dregg-circuit-prove --tests`; **teasting is a different crate, so my own gate could not see it.**
**LESSON (recorded): a `--tests` gate must cover the crates that CONSUME the API you delete, not just the
crate you edit.** Fixed by RETARGETING (not deleting) onto `merkle_air::{membership_public_inputs,
prove_membership_p3, verify_membership_p3}` — the emitted descriptor — and STRENGTHENED it: forged leaf AND
forged root now rejected. `test_stark_proof_bytes_round_trip` PASSES.
Also retired `test_presentation_proof_round_trip` (pre-existing rot: it called the RETIRED
`dregg_circuit::RealPresentationProof::verify`; the live type has no such method). Intent named as
**`PresentationRoundTripResidual`** — it guarded `DeserializeUnexpectedEnd`, "a real wire protocol bug";
re-landing means porting to `BridgePresentationProof` + `verify_presentation_full`.
**Named residual: `OrphanedTeastingTestsResidual`** — 4 more teasting tests import symbols with zero
tree-wide defs (`bridge_four_phase.rs:532`, `defi_primitives.rs:10`, `negation_proofs.rs:8`,
`privacy_unlinkability.rs:11`). Unlike proof_round_trip these look genuinely never-compiled; each needs a
retarget-or-retire decision. NOT swept blind — I already learned that lesson.

### NEXT UNITS (from the scar audit) — ranked, all evidence-backed
1. **`DuplicateDslP3AirResidual` (HIGH)** — `dregg-dsl-runtime/src/dsl_plonky3.rs:41`'s 868-line
   name-colliding `DslP3Air` (p3-uni-stark; cannot do `Hash`; enforces `BoundaryRow::Index(n>0)` on row 0
   ONLY — a soundness-shaped limit). Zero non-test consumers. The differential harness
   (`plonky3_runner.rs:42`) drives IT and skips membership at `:77` for a limit FALSE of production.
   **Unit**: repoint `plonky3_runner.rs` + `tests/src/dsl_pipeline.rs:507,511,642` at
   `dsl_p3_air::{prove_dsl_p3, verify_dsl_p3}`; delete `dsl_plonky3.rs`, the 12 `p3-*` optional deps
   (`dregg-dsl-runtime/Cargo.toml:14-26`), and the re-export (`lib.rs:46-51`); THEN re-land the membership
   case (needs a membership circuit built in the harness — its own step, do not claim it for free).
2. **`CratesOutsideCIResidual` (HIGH)** — 7 crates have their own `[workspace]`, are in neither `members`
   NOR `exclude`, are named in zero CI workflows, and have zero dependents: `crypto-tanuki` (1496 LOC/22
   tests), `crypto-traccoon` (1426/17), `crypto-hashrand` (803/8), `crypto-xmvrf` (642/17),
   `cosmos-settlement` (809/5), `cosmos-lock` (541/12), `tools/deployer-gate` (710/14). **~6,400 LOC and
   95 tests that have NEVER run in CI — 64 of them on crypto code.** Drift, not intent: `exclude` lists
   `solana-lock`/`solana-settlement` but not their `cosmos-*` siblings, and every other exclude entry
   carries a reason; these have none. **Unit**: decide + RECORD — fold in as `members`-not-
   `default-members` (the pattern already used for 60 heavy crates), or `exclude` WITH the one-line reason.
   Neither-nor is the only wrong answer. Start with the four `crypto-*`.
3. **`OrphanedTeastingTestsResidual` (MED)** — 4 teasting tests import symbols with zero tree-wide defs
   (`bridge_four_phase.rs:532`, `defi_primitives.rs:10` [module gone -> `derivation_witness.rs`],
   `negation_proofs.rs:8`, `privacy_unlinkability.rs:11`). Each needs retarget-or-retire. NOT swept blind.
4. **`PresentationRoundTripResidual` (MED)** — re-land the retired presentation round-trip test against
   `BridgePresentationProof` + `verify_presentation_full`; it guarded `DeserializeUnexpectedEnd`.
5. **LOW** — `dregg-cert-f-ir2.json` is `include_str!`d but is the only flat descriptor missing from
   `PROVENANCE.json`'s 74 sha256 pins (manifest itself cut dirty: `"source_dirty": true`).
6. **Flagged, not asserted** — `composition.rs`'s `compose_or/and/chain` + `generate_and_trace/
   generate_chain_trace` (~400 LOC) resolve outside the crate only to DOC COMMENTS; every executable ref
   is its own `#[cfg(test)]`. Only `compose_aggregate` has a real consumer (`sdk/full_turn_proof.rs:67`).
   May be aspirational IVC scaffolding — **killing `compose_chain` is a product decision, not cleanup.**

### Bricks 3-4 DONE in the working tree (2026-07-16, codex stark-kill; supervisor must gate/commit)

**The deployed whole-history binding proof is now the Lean-emitted descriptor.**

- Added `circuit/src/turn_chain_witness.rs`: the production 14-column chip-lane witness for
  `dregg-turn-chain-binding-v2`. It fills the shared Poseidon2 lookup lanes and preserves the verified
  padding contract: `(final,final)`, continuing `idx`, frozen `real_count`, `is_real=0`, and a genuinely
  continued hash chain. This is witness generation only; it authors zero constraints.
- `prove_chain_core_rotated` (therefore `prove_turn_chain_recursive_without_host_gate`) and the online
  `Accumulator::finalize` now call one shared `descriptor_by_name` + `prove_vm_descriptor2` path. The
  byte verifier decodes `TurnChainBindingProof { proof, public_inputs }` and calls
  `verify_vm_descriptor2` against the registered descriptor; the wire envelope was fail-closed bumped
  from v3 to v4 for the proof-type change.
- The real end-to-end test caught one deployed-wide integration fact: wide turns intentionally retire
  scalar PI 34/35 to zero. The binding witness now consumes lane 0 of `turn_anchors8` (identical to
  PI 34/35 for narrow legs), so the Lean descriptor proves a meaningful scalar projection of the same
  genuine wide anchors the recursion segment binds. The verifier checks descriptor genesis/final/count
  against the carried wide claim's head lanes; the descriptor's scalar sequential digest remains
  distinct from the root's 8-felt ordered-segment digest.
- Deleted the entire Rust-authored `TurnChainBindingAir` algebra, its 359-column inline Poseidon2 aux
  trace, row builder, and direct uni-STARK proving path. `rg`/`sg` over Rust now finds zero
  `TurnChainBindingAir` symbols.
- Added `circuit-prove/tests/turn_chain_emit_gate.rs`: exact Lean JSON pin + parse/dispatch/shape gate +
  real prove/verify + forged continuity, idx, count, final-root, and digest rejections. Ported the old
  direct digest/count teeth to the emitted descriptor and added binding-proof-byte corruption to the
  deployed wire test.
- Deployed call evidence: `grain-verify/src/r3.rs:139` calls
  `prove_turn_chain_recursive_without_host_gate`; that calls `prove_chain_core_rotated`, which proves the
  registered descriptor, and `r3.rs:145` calls `verify_whole_chain_proof_bytes`, which now runs
  `verify_vm_descriptor2` before the recursive root/segment teeth.

**Gate evidence (verbatim result lines):**

- Lean emitter payload after stripping its routing prefix: `cmp` green; both files `2148` bytes.
- Emit gate: `Summary [   0.054s] 3 tests run: 3 passed, 0 skipped`.
- Focused descriptor + order rejection: `Summary [ 176.699s] 3 tests run: 3 passed (1 slow, 1 leaky), 10 skipped`.
- DEPLOYED wire proof, honest + tamper polarities:
  `PASS [ 379.484s] ... whole_chain_proof_bytes_roundtrip_and_tamper` and
  `Summary [ 379.484s] 1 test run: 1 passed (1 slow), 12 skipped`.
- `cargo check --tests -p dregg-circuit-prove -p grain-verify -p grain-turn -p dregg-lightclient`:
  `Finished dev profile [unoptimized + debuginfo] target(s) in 17.02s` (the terminal rendered `dev`
  with code ticks).
- `lake build Dregg2` was green on this cutover snapshot:
  `Build completed successfully (9702 jobs).`

**No turn-chain expressiveness residual.** The Lean descriptor expresses every hand-AIR tooth and the
deployed proof/verify + forged-history rejection path is green. Two **shared dirty-tree blockers** remain
outside this lane and were not patched:

- **`SharedTreeRefusalGauntletResidual`** — the full default nextest run reached 135 passes, then the
  parallel dirty refusal-policy work made
  `shielded_ring_clearing_air::tests::forged_post_endpoint_lane_is_unsat` classify the debug prover's
  UNSAT panic as a crash; a separate caveat test timed out at 180s. Verbatim:
  `Summary [ 180.172s] 137/490 tests run: 135 passed (9 slow), 1 failed, 1 timed out, 87 skipped`.
  `circuit/src/refusal.rs` is explicitly another lane's off-limits dirty file.
- **`SharedTreeMarketAggregateBindingResidual`** — after the 9702-job green, the parallel lane changed
  metatheory and a final replay failed in `Market/AggregateBinding.lean`: `Unknown identifier
  MSISHardQuant`, followed by `sorryAx` axiom-hygiene failures. This is unrelated to the byte-identical,
  already-built turn-chain emitter and outside stark-kill ownership.

No commit made, per supervisor instruction.

## ⚑⚑⚑ `de0893342` — THE LAST DEPLOYED HAND-AUTHORED CIRCUIT IS DEAD (2026-07-16)
`TurnChainBindingAir`'s algebra is GONE (0 sites, all 3 dialects). `circuit-prove/src/ivc_turn_chain.rs`
drives `descriptor_by_name("dregg-turn-chain-binding-v2")` + `prove/verify_vm_descriptor2` — the assured
IR2 interpreter over constraints AUTHORED AND PROVED in `Emit/EffectVmEmitTurnChainBinding.lean`.
This was the one genuine law-#1 violation on a deployed path: `grain-verify/r3.rs:139`'s whole-history
chain proof — **what a renter trusts**.
INDEPENDENTLY VERIFIED (not on report): emit gate 3/3 · **the descriptor Lean emits RIGHT NOW is
BYTE-IDENTICAL to the committed golden** (2148 bytes — the proof and the deployed bytes are ONE artifact,
which is the entire point of emitting vs lowering) · deployed `ivc_turn_chain_rotated` 5/5 in 177s (honest
prove+verify AND tamper rejection: forged digest/count, broken order, root/descriptor/public/VK/version/
truncation) · `lake build Dregg2` 9703 jobs green. NO expressiveness residual — the census's "every family
fits IR2, zero extensions" held.

### THE GOAL'S ORIGINAL PREMISE IS NOW FALSIFIED (honestly, with evidence)
ember set this goal because "a hand-written Rust circuit means no model of its semantics and no proof of
correctness — that's pretty bad." TRUE when set. Tonight's sweep found: the deployed surface was ALREADY
mostly migrated (this lane killed `stark.rs` on 07-09), and every remaining candidate was scaffolding —
EXCEPT ivc_turn_chain, which is now emitted. **Every deployed circuit path we can find is now Lean-authored
or a legitimate interpreter.** The residuals that remain are NOT missing semantics; they are:
`NonRevocationDepthResidual` (emitter depth-2 vs deployed depth-4 — fix is adjacency∘ordering composition),
`DuplicateDslP3AirResidual`, `CratesOutsideCIResidual` (95 tests never run), the orphaned teasting tests.

### SHARED-TREE BLOCKERS (other lanes' in-flight work — NOT this lane's, NOT fixed here)
- `SharedTreeMarketAggregateBindingResidual`: a parallel metatheory edit left `Unknown identifier
  MSISHardQuant` + **sorryAx hygiene failures** in `Market/AggregateBinding.lean` — Market does not replay.
- `SharedTreeRefusalGauntletResidual`: broad nextest stops at 135 passes on concurrent dirty `refusal.rs`.
Flagged, not touched: 3 codex processes are live and the tree is a mix.

### `a5f7a0a87` — the differential harness now drives the interpreter we SHIP
Repointed `dregg-dsl-differential/src/plonky3_runner.rs` off `dregg_dsl_runtime::{prove,verify}_dsl_plonky3`
(the 868-line name-colliding duplicate `DslP3Air`, p3-uni-stark, zero production consumers, cannot express
`Hash`, enforced `BoundaryRow::Index(n>0)` on row 0 only) onto `dregg_circuit::dsl::dsl_p3_air::
{prove_dsl_p3, verify_dsl_p3}` — the p3-batch-stark rail `shielded/spend_circuit.rs:661` + `attest.rs:543`
actually ship. Green incl. --tests; harness tests pass.

**CORRECTED THE SKIP — BY PROBING, not by believing either doc.** The audit's payoff claim (repointing
"likely un-skips the membership cases") is **WRONG**, and I nearly shipped it. Throwaway probe:
`DslP3Air::try_from_dsl(merkle_poseidon2_circuit())` -> `NonAlgebraicConstraint { index: 1, form:
"MerkleHash (use the Lean-emitted IR2 descriptor...)" }`. Membership stays skipped for a REAL reason: the
shipped interpreter DELIBERATELY routes MerkleHash to the Lean-authored IR2 rail (law #1) — there is no
DSL-side arithmetization to differ against. Coverage is NOT lost; it is on that rail (`merkle_air`'s
membership_p3 teeth). Skip reason now says exactly that.
**Deletion of the duplicate BLOCKED (named)**: `tests/src/dsl_pipeline.rs:22,507,511,~641` needs BYTES
(`turn.execution_proof = Some(proof_bytes)` + a byte-tamper test) while production returns a `DslP3Proof`
struct -> a postcard round-trip migration, its own unit. (My grep missed this consumer; the AUDIT had it
right. Checked before deleting — the teasting lesson held.)

### `BrokenDslProcMacroResidual` (NEW, pre-existing, NOT mine — measured before my repoint)
`cargo check -p dregg-tests --tests` is RED, and not from dsl_pipeline: the **DSL PROC-MACRO** fails —
`dregg-dsl/src/gen_plonky3.rs:111` (`Result<proc_macro2::TokenStream, syn::Error>: quote::ToTokens`
unsatisfied) + `:307`/`:263` (fn takes 6 args, 5 supplied).
**The subtle part:** `cargo check -p dregg-dsl` is GREEN, and `--all-features` is GREEN — it only breaks
inside `dregg-tests`' dependency graph. `mod gen_plonky3;` is NOT feature-gated and dregg-dsl has no
`[features]` table, so this is **FEATURE UNIFICATION** shifting `syn`/`quote`/`proc-macro2` versions under
a different dep graph. `dregg-dsl` IS a default-member and `circuit/Cargo.toml` depends on it, so CI green
here is an artifact of which graph CI resolves. Deserves its own pass — it is a dependency-hygiene scar,
not a circuit scar.

### `67395c5fb` — 4 crypto crates folded into the workspace: 55 passing tests CI had NEVER run
`CratesOutsideCIResidual`, partially closed. **The audit's "no reason recorded" was WRONG — and the truth
is a better scar.** All four DO record a reason, and each cites the SAME model: "mirrors crypto-hermine" /
"like crypto-hermine" / "exactly like crypto-hermine". **`crypto-hermine` is a member AND default-member
with no `[workspace]` of its own** (verified). The model GRADUATED into the workspace; the four crates
citing it as their reason to stay out were left behind. **Cargo-culted rationale pointing at a false
premise** — so their own stated intent argued for folding them in. Added to `members`, NOT
`default-members` (CI's `--workspace` reaches them; default build stays fast — the pattern already used for
~60 heavy crates). Safe by construction: each has exactly ONE dep (blake3, pure Rust, no C) so none of the
version/`links` conflicts behind the real `exclude` entries apply. Verified: builds green THROUGH the
workspace, **55 tests pass** there, and dregg-circuit + crypto-hermine still green (root undisturbed).
STILL OPEN in that residual: `cosmos-settlement` (5 tests), `cosmos-lock` (12), `tools/deployer-gate` (14)
— they carry a DIFFERENT rationale ("build/test standalone") and their `solana-*` siblings sit in
`exclude`, so they need their own decide-and-record pass.

### `BrokenDslProcMacroResidual` — RETRACTED (it was transient, my error)
The `gen_plonky3.rs` proc-macro errors did NOT reproduce. `cargo check -p dregg-tests --tests` now fails
elsewhere: `turn/src/pending.rs:86` ("lifetime may not live long enough"), and `turn/` is DIRTY with
another lane's in-flight edits (`turn/src/error.rs`, `turn/src/executor/proof_verify.rs`). **I read a
concurrent lane's mid-edit state and named it as a finding.** Lesson for a shared tree with 3 live codex
procs: a build error in a DIRTY file is not evidence until the tree is quiet. `dsl_pipeline` migration
(which unblocks deleting the duplicate `DslP3Air`) stays blocked on that lane, NOT on the proc-macro.

### `af2c56bf8` — `CratesOutsideCIResidual` CLOSED: every orphan decided + recorded (69 tests reachable)
Evidence split them rather than one blanket answer:
- **FOLDED IN**: `tools/deployer-gate` (14 tests). Its header claimed a "Standalone workspace (own
  [workspace] opt-out, like crypto-hermine / fhegg-solver)" — **there is NO `[workspace]` stanza in it and
  never was.** Never opted out; just never listed in `members`. It path-depends on `dregg-macaroon` (a
  member), so standalone resolution duplicated the workspace anyway.
- **EXCLUDED, REASON RECORDED**: `cosmos-lock` (12) + `cosmos-settlement` (5) — `cosmwasm-std 2.2` +
  `cw-storage-plus` pull a dep tree existing NOWHERE else (verified across every manifest) and target
  wasm32 contracts, not the host workspace: the same reason `solana-*` are excluded. Now explicit.
- With `67395c5fb` (4 crypto crates, 55 tests): **69 previously-invisible tests reachable by CI**; the 2
  that stay out are a decision, not drift.

### THE PATTERN OF THIS CODEBASE'S SCARS (three independent instances tonight)
**Every "reason to stay out of the workspace" cited `crypto-hermine` — which is itself a MEMBER.**
crypto-tanuki ("mirrors crypto-hermine"), crypto-traccoon ("mirrors crypto-hermine and crypto-tanuki"),
crypto-hashrand ("like crypto-hermine"), crypto-xmvrf ("exactly like crypto-hermine"), deployer-gate
("like crypto-hermine / fhegg-solver" — while having no `[workspace]` at all). The rationale was
**cargo-culted from crate to crate**; the model graduated into the workspace and nobody updated its
imitators. Same disease as `Claims.lean:383`'s false cognate and `dsl_p3_air.rs:102`'s self-contradiction:
**the scars here are load-bearing LIES IN PROSE, and they propagate by copying.** A comment is not
evidence — grep the premise.

### derivation_air — LEFT ALONE, deliberately (the goal's "delete dead derivation.rs" rests on a false premise)
The goal says "delete dead derivation.rs". **It is not dead** (`circuit/src/derivation_witness.rs:41` — the
EMITTED path's own witness builder — uses its `generate_derivation_trace_dsl` deliberately, "NOT a
reconstruction"; `dregg-dsl-runtime` re-exports its types). And the hand `DerivationAir` is instantiated
ONLY in `ivc.rs`'s `#[cfg(test)]`, where it feeds `ConstraintProof::generate` — the row-by-row VALIDATOR,
not a STARK prover. So it is test scaffolding, NOT a deployed law-#1 violation: deleting it means rewriting
an IVC test for ZERO assurance gain. Production derivation already proves via the emitted
`dregg-derivation-v1`, whose teeth exist and pass (`forged_derived_hash_column_refuses`,
`forged_conclusion_pi_refuses`, `forged_state_root_pi_refuses`). Not deleting it is the correct call.

### `EveryVariantRoundtripResidual` (NEW, pre-existing) — blocks the duplicate-DslP3Air deletion
The tree went quiet (0 codex procs) and `dregg-turn` recovered, so I retried the `dsl_pipeline` migration
that unblocks deleting the 868-line duplicate `DslP3Air`. **Still blocked, but by something else:**
`cargo check -p dregg-tests --tests` is RED with non-exhaustive matches —
`tests/src/every_variant_roundtrip.rs:392` (`&dregg_sdk::Effect::ShieldedTransfer { .. }` not covered) and
`tests/src/authorization_variants.rs:635` (`&Authorization::HybridSignature { .. }` not covered).
NOT in-flight — those files are COMMITTED and broken; `ShieldedTransfer` arrived with the fresh cut
`ddd2408c5`. New SDK variants landed without updating the exhaustive matches in a test named *every
variant roundtrip*.
**Not mine to close, and a `todo!()` arm would be a FAKE** — it would defeat the very property the test
asserts (that EVERY variant round-trips). The honest fix is a real round-trip case per new variant, which
belongs to whoever owns the SDK effect/authorization variants.
Consequence for this lane: `tests/src/dsl_pipeline.rs` cannot be migrated+verified (cargo builds the whole
crate's tests), so `DuplicateDslP3AirResidual`'s DELETION stays blocked. The repoint that mattered — the
differential harness now driving the shipped interpreter — is already landed (`a5f7a0a87`).

### `OrphanedTeastingTestsResidual` — CLOSED. 22 tests resurrected; 2 audit entries were STALE.
The scar was NOT "dead tests" — it was **live test files held hostage by one stale import each**. A test
target that does not compile does not report, so they sat silent.
- `5623b4350` **bridge_four_phase: +8 tests RUN**. It imported `bridge_action_witness::{prove,verify}_
  bridge_action` — gone (that module exports only `encode_hash`/`encode_amount`; the hand `BridgeActionAir`
  is trace-gen, "not in the soundness TCB"). Retired the 9 that drove them; teeth live on
  `bridge_action_emit_gate` (5/5 pass, byte-pinned to `BridgeActionEmit.lean`).
- `dd9fe7f91` **defi_primitives: +14 tests RUN**. It imported `cross_state_derivation::*` — the module is
  GONE; `derivation_witness.rs:7-10` records the migration that "flips the last hand-STARK derivation
  consumer off the hand engine onto the committed, byte-pinned emitted descriptor" `dregg-derivation-v1`.
  Retired only the 3 that drove it; teeth on `derivation_emit_gate`.
- **`negation_proofs.rs` DOES NOT EXIST** — stale audit entry.
- **`privacy_unlinkability.rs` PASSES 2/2** — stale audit entry; it imports `compute_fact_commitment` /
  `compute_blinded_fact_commitment`, which exist. (The audit claimed it imports the vanished free fns
  `prove_predicate`/`verify_predicate`. It does not.)
Also swept the imports my own `GarbledEvaluationAir` deletion orphaned — my mess, cleaned.

**THE DEEPER PATTERN (now seen 4×): a retirement lands, its consumers are not updated, and the breakage is
INVISIBLE** — because a non-compiling test target is silent, not red. That is how ~39 tests (8+14+17 in
proof_round_trip's file) stopped running without anyone noticing, and it is exactly how I broke
`proof_round_trip` myself last night. **A retirement is not done until you have built the crates that
CONSUME the API — not just the one you edited.**

## ⚑ THE COMPLETE SCOPE, CLASSIFIED (2026-07-16) — every circuit the goal named
Answering the goal's list systematically (3 dialects + reachability past the re-export layer), not reactively:

| circuit | verdict | action |
|---|---|---|
| **ivc_turn_chain** | **DEPLOYED violation** (`grain-verify/r3.rs:139`, the renter's whole-history proof) | **EMITTED + CUT OVER** `de0893342`. Hand algebra 0 sites; byte-identical golden; 5/5 tamper tests |
| **fold** | DEAD — `fold_dsl_circuit`/`_circuit_descriptor` re-exported, NEVER called | **DELETED** `313239116` (15 -> 0 sites); kept live `build_shared_tree` |
| **committed_threshold** | DEAD — same shape | **DELETED** `313239116` (12 -> 7) |
| **garbled** | DEAD — `GarbledEvaluationAir` never instantiated | **DELETED** `7e56e5439` (16 closure sites) |
| **membership_adjacency** | DEAD — `adjacency_circuit()` zero callers | **DELETED** `e9cd79030` (10 data sites); emitted version is STRONGER (internalizes the `idx_upper-idx_lower==1` tooth that lived in a bypassable Rust wrapper) |
| **merkle (P3MerklePoseidon2Air)** | DEPLOYED violation | **KILLED** `9ba02881b` — emitter existed and the deployed path ignored it |
| **note_spending** | **NOT a violation — the drift-detector** | LEFT. `note_spend_witness.rs:225-227`: the emitted path DELIBERATELY walks the v1 descriptor as SOURCE — "a drift in the deployed circuit is a build-time refusal here, never a silent divergence" |
| **derivation** | **NOT a violation — same pattern + test-only AIR** | LEFT. `derivation_witness.rs:41` reuses its trace-gen deliberately; `DerivationAir` runs only in `ivc.rs`'s `#[cfg(test)]` feeding `ConstraintProof::generate` — a VALIDATOR, not a prover. The goal's "delete dead derivation.rs" rests on a FALSE premise |
| **revocation** | **DEPLOYED**, `prove_non_revocation_p3` -> `sdk/privacy.rs:621` | **BLOCKED, named**: `NonRevocationDepthResidual` — emitter is depth-2/4-leaf vs deployed TREE_DEPTH=4/16-leaf. Cutover would SHRINK the revocation tree. Fix = adjacency(depth-general) ∘ ordering |
| **ivc.rs::StateTransitionAir** | test-only (14 sites) — `prove_ivc` has ZERO production callers (its only "callers" are doc comments; `bridge`'s `prove_ivc` is `PresentationAir`'s own method) | **LEFT, deliberately.** Its emitter exists BUT `Rung2Full::ivc_anchor_insufficient` PROVES that descriptor's residual is not crypto-dischargeable ("no copy-forward gate, every `old_hash` i>0 is a FREE column"). Cutting a test-only path onto a descriptor Lean proves INSUFFICIENT trades a stronger check for a weaker one. Named, not forced |

**NET: every DEPLOYED first-party Rust-authored circuit is retired.** What remains is (a) one deployed
circuit blocked by a real regression (revocation/depth), (b) two that are deliberately kept as
drift-detectors for the emitted path, (c) one test-only AIR whose emitter Lean proves too weak.

### `7d1f34207` — the `*_air` naming, done as a SWEEP
Classified all 16 `*_air.rs` (all 3 dialects). 6 EMITTED (law working) · 2 legitimate (shape probe, range
gadget) · 2 with a lone doc-comment hit · **6 with NO algebra**. Fixed the three whose headers actively
LIED about being AIRs (garbled_air — I deleted its AIR today; shielded_ring_clearing_air — codex emitted it
away; effect_action_air — it is schemas+limbs). `merkle_air` + `temporal_predicate_air` already told the
truth. **Did NOT rename the files**: my last mechanical rename sed a WIRE IDENTIFIER and the dispatch gate
caught it — a truthful header kills the lie with none of that risk.

### ⚑⚑ `b0f8c8eb7` — LAW #1 IS NOW A GATE, NOT PROSE (the systematic enforcement)
`circuit-prove/tests/law1_enforcement_gate.rs`: scans EVERY `.rs` in circuit/src + circuit-prove/src across
**all three dialects** and RATCHETS against a frozen baseline — **48 files / 757 sites**, the true scale no
`*_air.rs` audit could ever see. A NEW file with constraint algebra, or a listed file GROWING, **FAILS**,
with a message saying to emit from Lean and explicitly NOT to add yourself to the baseline. Shrinking is
always allowed. **VERIFIED IT BITES**: planted a `Constraint { eval: Box::new(..) }` -> "LAW #1 VIOLATED —
NEW Rust-authored constraints"; removed -> green.
This answers the standing critique that the fiction-fixes were "defensive documentation, not a systematic
enforcement mechanism." A comment cannot stop the next lie. A failing test can.

### ✗ CORRECTION TO MY OWN COMMIT `313239116` — the 3-dialect blindness bit ME
I wrote "**fold — DEAD, deleted. 15 ConstraintExpr sites -> 0**". True for THAT DIALECT ONLY. `dsl/fold.rs`
still holds **`FoldAir` with 15 CLOSURE-dialect sites** (`eval: Box::new`), which I never checked, and it
is used at `ivc.rs:341` + `:742` (production code, though its callers `fold_and_accumulate`/`prove_ivc`
have NO production callers — so it is test-only scaffolding, same class as StateTransitionAir).
**The gate I just built is what caught this.** I have now made the same dialect error the audits made — in
a commit whose whole subject was that error. That is precisely why the enforcement had to be mechanical
rather than a lesson I keep re-learning. The baseline records `dsl/fold.rs` at 15 with that reason.

### ⚠⚠ `VerifyTcbReentryResidual` (NEW, HIGH, NOT this lane's to fix) — found by unblocking a silent gate
`6940bb654`: two match arms unblocked `dregg-tests` (red since the fresh cut `ddd2408c5`) → **249 tests now
run and pass** → and that exposed **`every_verifying_binary_is_routed_or_allowlisted` FAILING**. It is the
"a crate silently re-enters the verify TCB" regression gate, and it has been UNABLE TO RUN.
**SIX binaries reach the ML-DSA verify stack while neither installing the Lean-verified core nor sitting on
the reviewed DELEGATES_VERIFY allowlist**: `dregg-intent`(drex_clear) · `dregg-doc`(dregg-forge) ·
`dungeon-service` · `real-dungeon-service` · `dreggnet-web`(dreggnet-web-server) ·
`dregg-gateway-ask`(gateway-ask). Fix per the gate: wire `install_lean_verify_core_real` + a non-dev
`dregg-lean-ffi` dep, OR add a JUSTIFIED DELEGATES_VERIFY entry. Not done here — a justification is a
decision, not a cleanup, and this is the verify-routing lane's domain.

**THE THESIS, LANDED TWICE:** this codebase HAS good ratchets — `effect_enum_descriptor_residual_gate`
(every Effect variant: descriptor-or-named-residual), `every_verifying_binary_is_routed_or_allowlisted`
(no silent verify-TCB re-entry), and now my `law1_enforcement_gate`. **But a ratchet that cannot COMPILE
cannot bite.** Two unexhausted match arms muted an entire crate for weeks, and the verify-TCB regression it
was built to catch sailed straight through. A non-compiling test target is SILENT, not red — that is the
single most dangerous failure mode in this tree, and it is the same mechanism that hid ~39 orphaned
teasting tests and let me break `proof_round_trip` unnoticed.
**Corollary for the law-#1 gate I added: it must stay COMPILING to matter.** It lives in
`circuit-prove/tests/`, a crate that builds — deliberately, not by luck.

### `NonRevocationDepthResidual` — CLOSED (2026-07-16). The last deployed Rust-authored circuit is gone.

The composition is emitted by `Dregg2/Circuit/Emit/NonRevocationAdjacencyEmit.lean` as
`dregg-non-revocation-adjacency::poseidon2-fact-v1` (width 37, 2 PIs, 39 constraints). It reuses the
depth-general two-path/index/consecutiveness algebra of `AdjacencyMembershipEmit`, specializes only
the node lookup to the DEPLOYED fact-domain seed `[left,right,0,0,0,0xFACF,1]` so the root remains
`hash_fact(left,[right])`, and conjoins `NonRevocationEmit`'s direct+complement 30-bit strict-ordering
range teeth. The exact `DescriptorIR2.emitVmJson2` output is checked in at
`circuit/descriptors/by-name/non-revocation-adjacency.json`, byte-pinned by
`non_revocation_adjacency_emit_gate`, reproduced by the repository-wide `EmitByName.lean` drift
route, and production-dispatched by `descriptor_by_name`.

The production builder `non_revocation_adjacency_witness.rs` emits ONE REAL ROW PER MERKLE LEVEL:
row `i+1` consumes row `i`'s parent and advances both reconstructed indices and their shared power of
two. At HEAD, `dsl/revocation.rs::TREE_DEPTH == 4`; the honest gate has four genuine folds and both
last-row parents equal the existing `DslRevocationTree` root. Thus this is still the deployed
depth-4 / 16-leaf `hash_fact` tree — neither trace padding nor a 4-leaf epoch change.

`prove_non_revocation_p3` and `verify_non_revocation_p3` now load the emitted artifact by name and call
`prove_vm_descriptor2` / `verify_vm_descriptor2`. Therefore both SDK producer call sites
(`privacy.rs` and `full_turn_proof.rs`) now prove via the Lean descriptor. The 505-line deployed
`non_revocation_circuit_descriptor` / `non_revocation_dsl_circuit` Rust constraint constructor was
deleted; AST search finds zero calls and zero `ConstraintExpr` sites in `dsl/revocation.rs`.
`generate_non_revocation_trace` remains, deliberately, as legitimate Rust witness generation.

Formal teeth, all `#assert_axioms`-clean:

- `diffL_body_zero_iff`: `diffLBody.eval a = 0 ↔ a DIFF_L = a X - a L_CUR - 1`.
- `diffR_body_zero_iff`: `diffRBody.eval a = 0 ↔ a DIFF_R = a U_CUR - a X - 1`.
- `rangeLBind_body_zero_iff`: `rangeLBindBody.eval a = 0 ↔ a RL = HALF_P_MINUS_1 - a DIFF_L`.
- `rangeRBind_body_zero_iff`: `rangeRBindBody.eval a = 0 ↔ a RR = HALF_P_MINUS_1 - a DIFF_R`.
- `ordering_forces_strict_bracket`: the two diff bindings plus nonnegative range witnesses imply
  `a L_CUR < a X ∧ a X < a U_CUR`.
- `forged_lower_bracket_refuted`: the lower binding + range + `a X ≤ a L_CUR` imply `False`.
- `forged_upper_bracket_refuted`: the upper binding + range + `a U_CUR ≤ a X` imply `False`.
- `nonadjacent_pair_refuted`: `a U_IDX_OUT ≠ a L_IDX_OUT + 1` implies
  `consecutiveBody.eval a ≠ 0`.

The real prover gate is non-vacuous: honest depth-4 ACCEPTS; `x == L`, `x == R`, a wide bracket made
from two real members at positions 2 and 4, a forged leaf, a forged sibling, and a forged public root
each REJECT. Public API tests additionally reject a wrong queried-item PI and committed members.

Verification:

- `lake build Dregg2` — GREEN (9710 jobs); `lake env lean Dregg2/Claims.lean` — GREEN; exact emitter
  output `cmp` against the checked-in JSON — GREEN.
- `cargo nextest run -p dregg-circuit-prove -E 'binary(non_revocation_adjacency_emit_gate) |
  binary(non_revocation_p3_boundary)'` — 6/6 GREEN.
- Focused `dregg-circuit` deployed p3 + depth-4 witness tests — 4/4 GREEN. Focused SDK emitted-PI and
  privacy wire producer/consumer gates — 2/2 GREEN.
- `cargo check -p dregg-circuit -p dregg-dsl-runtime -p dregg-sdk -p dregg-circuit-prove
  --all-targets` — GREEN.
- Requested default `cargo nextest run -p dregg-circuit -p dregg-sdk --no-fail-fast` completed all
  1482 tests: 1411 passed, 71 failed, 10 skipped. Every standalone non-revocation test passed; the
  broad failures are concurrent shared-tree EffectVM/UMem/cap-root/fields/heap descriptor work.

No non-revocation residual remains. Two external blockers are named, not papered over:

- **`SharedTreeEffectVmDescriptorDriftResidual`** — the full-turn tests whose names mention freshness
  fail before the non-revocation leg in the shared dirty EffectVM proving path (row-0 descriptor
  constraints; the direct SDK privacy non-revocation round-trip is green). This is part of the same
  71-failure cross-lane cluster above, not a revocation refusal.
- **`SharedTreeBridgePredicateSignatureResidual`** — the immediate SDK-consumer sweep reaches
  `bridge/src/present.rs` and stops on pre-existing concurrent edits: missing `FactBinding` at :2664
  and a stale 4-argument call to the now-3-argument `prove_predicate_for_fact` at :1061. The changed
  circuit/runtime/prove/SDK targets themselves build all-targets green.

### ⚡ CAPACITY UNLOCKED (2026-07-16) — remote boxes + Fable, three streams parallel
ember replenished all subscriptions + pointed at remote build boxes. Local cargo-lock is no longer the
bottleneck. Now running:
- **persvati** (24-core, `scripts/pbuild <lane> <cmd>` — rsyncs local tree, warm per-lane cargo cache,
  refuses cold lanes): lane `srot` doing `cargo test --workspace --no-run` — the EMPIRICAL silent-rot
  ground truth (every non-compiling test target). hbox also warm (games-deploy 3977 deps) if needed.
- **workspace-lie-hunt swarm** (`w076khjpe`, 6 Fable-model read-only lanes): vanished-symbol refs ·
  misnamed files · ratchet/gate integrity (which gates are SILENT/toothless) · cargo-culted rationale ·
  dead pub API · duplicate parallel systems. The "load-bearing lies in prose" thesis mapped workspace-wide.
- **codex** (local): landing the revocation composition — `NonRevocationAdjacencyEmit.lean` +
  `EmitNonRevocationAdjacency.lean` + `non-revocation-adjacency.json` + `non_revocation_adjacency_witness.rs`
  + `non_revocation_adjacency_emit_gate.rs` — EXACTLY the adjacency∘ordering fix specced for
  `NonRevocationDepthResidual` (the last deployed first-party Rust-authored circuit).
PLAN: gate codex's revocation on the stable tree (a cutover that shrinks TREE_DEPTH from 4 is a regression);
harvest srot + lie-hunt; then engage Fable implementers on the concrete residuals (duplicate DslP3Air
deletion — now unblocked since dregg-tests compiles; the *_air renames; VerifyTcbReentry wiring) once the
tree stabilizes.

## ⚑⚑⚑ GOAL CORE DONE + the lie-hunt opened the REAL healing surface (2026-07-16)
`23cd63264`: **revocation emitted — every DEPLOYED first-party Rust-authored circuit is now Lean-emitted.**
depth-4 (not shrunk), byte-identical, teeth 3/3, hand algebra 0. The goal's stated scope is met; the
law1_enforcement_gate ratchet holds it.

`da4e45a8d`: fixed the two metatheory lies I CREATED (schnorr_air/turn_auth citations after my deletion).

### The 6-lane workspace lie-hunt (`w076khjpe`) — findings by severity:
**HIGH / BEHAVIORAL (a live surface lies about what it does):**
- **[F#1] The node's MCP "IVC compression" verify tool returns "valid" for MOCK SYNTHETIC data.**
  `node/src/mcp/handlers_verify.rs`: gathers the real receipt chain (:84), then `create_test_chain(steps)`
  (:101) DISCARDS it and proves a SYNTHETIC chain of matching length via `prove_ivc` — the MOCK prover
  (`constraint_prover.rs` says of itself "a trace digest is not a STARK, nothing here is sound against a
  prover that lies"; `verify_ivc` just recomputes BLAKE3). Returns `"verification":"valid"`, comment calls
  it "a genuine fold chain". It is a LIVE-REGISTERED MCP tool (`tools_def.rs:609`). The REAL recursive IVC
  (`ivc_turn_chain::WholeChainProof`, which I just emitted + `lightclient` uses) exists to do it for real.
  → SURFACED to ember: wire the real IVC over the real receipts, or honest-report (stop claiming "valid").
  A live verify tool lying "valid" is the most serious scar found. `NodeMcpMockIvcResidual`.
- **[F#2]** `dregg-genesis-snapshot/src/lib.rs:63` calls the mock IVC "the real prover/verifier" (false
  cognate: real-vs-retired-hand-STARK, not real-vs-mock). Carries a named unsound caveat, but the phrase lies.
- **[B#1]** `constraint_prover.rs` — a "prover" whose `generate_unchecked` proves nothing (its own doc
  concedes it); the mock IVC's engine. Name lies.

**HIGH / GATE-INTEGRITY (a ratchet that gives false confidence):**
- **[C#1]** THREE emit-equality gates (5 test files, e.g. `derivation_emit_gate.rs:4`) claim CURRENT
  byte-identity while pinning a RETIRED Lean wire string — the mirror-failure INSIDE the gate family.
  Needs verification (some may be stale vs my/codex's recent emits). `EmitGateRetiredPinResidual`.

**MEDIUM / PROSE-LIES + CLEANUP (safe to delegate, no behavioral decision):**
- [A] ~9 dangling Lean/Rust citations to deleted/renamed symbols (2 mine, FIXED; rest: effect_vm_descriptors
  CI-gate, relational_predicate_air::prove_value_comparison, ordering.rs::has_equivocation_in_past renamed,
  action.rs DropRef/ValidateHandoff retired-but-modeled, EffectVmAir fail-closed contract, dfa_lookup_descriptor).
- [D] **629 live lines cite 85 non-existent `docs/*.md`** (archived to `.docs-history-noclaude/`). Top:
  `docs/PG-DREGG.md` (89 lines, incl. a Cargo.toml `[workspace]` justification).
- [E] **328 zero-use pub items** (dead API) across the 8 core crates; 323 mod decls checked.
- [B] misnamed files beyond `*_air` (constraint_prover, etc.).

### Lie-hunt Lane A (dangling citations) — CLOSED (2026-07-16)
- `da4e45a8d` — the 2 I created (schnorr_air/turn_auth).
- `5325fb01c` — 6 (Fable): effect_vm_descriptors CI-gate, relational_predicate_air::prove_value_comparison
  (+ resolved a COMMITTED merge conflict from the fresh cut, orphaned but broken), has_equivocation_in_past
  rename ×4, DropRef/ValidateHandoff retired verbs, EffectVmAir fail-closed contract, dfa_lookup_descriptor.
- `0dc1bc2de` — 3 more (DfaAcceptanceAir + CircuitEmitGadgets, same dfa corpse).
Every fix VERIFIED (identifier resolved to zero-defs, replacement found or named, file re-elaborated/checked).

### AWAITING EMBER — the one BEHAVIORAL decision (not a reversible cleanup)
`NodeMcpMockIvcResidual`: the node's live MCP "IVC compression" verify tool returns "valid" for MOCK
synthetic data (discards the real receipt chain, proves a `create_test_chain` via the mock `prove_ivc`).
The real recursive IVC (`ivc_turn_chain::WholeChainProof`, just emitted, used by lightclient) exists.
Two honest paths: (1) wire it real, (2) honest-report (stop claiming "valid"). Surfaced; not touched —
changing a shipped verify surface's behavior is ember's call.

### DELEGATABLE QUEUE (safe, non-behavioral — paced for the shared tree, awaiting ember's priority)
- Lane D: 629 lines citing 85 non-existent `docs/*.md` (archived). Mechanical, high-churn.
- Lane E: 328 zero-use pub items (dead API) across 8 core crates. Needs per-item deadness confirmation.
- Lane C: verify the "3 emit-equality gates pin a retired wire string" claim (some may be stale vs the
  turn-chain/revocation emits I just byte-verified). Assurance-critical if real.
- srot sweep (persvati): grinding dregg-lean-ffi's leanc build (145 C facets, cold lane) — the empirical
  non-compiling-test map. Harvest when it lands.

## ⚡ NEW ACTIVE THRUST (ember, 2026-07-16): PURGE THE MOCK PROOFS — wire to real
ember: "get rid of all that mock shit, wire to real — and look for MORE of those sorts of things."
A mock proof/verify surface is the worst lie: reports "valid"/"proved" for data it never proved.

THE MOCK ENGINES: `circuit/src/ivc.rs` (simulated IVC — prove_ivc/verify_ivc = a BLAKE3 digest recompute,
create_test_chain, simulated_proof_size_bytes) + `circuit/src/constraint_prover.rs` ("a trace digest is
not a STARK, nothing here is sound"; generate_unchecked checks nothing).
KNOWN LIVE CONSUMER: `node/mcp/handlers_verify.rs` (MCP tool, returns "valid" for create_test_chain synthetic
data). Others: preflight/checks/*, dregg-genesis-snapshot.
THE REAL PROVER: `ivc_turn_chain::prove_turn_chain_recursive(&[FinalizedTurn]) -> WholeChainProof` +
`verify_whole_chain_proof_bytes` (used for real by lightclient).

THE CRUX (why some mocks aren't laziness): `FinalizedTurn` wraps a `DescriptorParticipant` (the rotated
turn descriptor, produced at PROVING time). `TurnReceipt` (what node/cclerk retains) is only HASHES. So a
mock may exist because the real provable data is NOT at that layer → wiring real needs PLUMBING/retention,
not a one-line swap. The scout (`wh0frxr57`) classifies each: WIRE-FEASIBLE / NEEDS-PLUMBING / HONEST-RETIRE,
+ the real-data availability map (where DescriptorParticipants are produced + whether retained).
PLAN: wire the feasible ones to the real prover; for needs-plumbing, thread/retain the participants (or
name exactly what must be, honest-fail meanwhile — NEVER a mock that says "valid"); retire the mock engines
(ivc.rs simulated, constraint_prover) once nothing production rides them; add a ratchet so no new mock-proof
surface returns "valid".

### `0efabddbf` — MOCK-PROOF PURGE RATCHET (enforced before ripping — shrink-only)
`circuit-prove/tests/mock_proof_purge_gate.rs`: FAILS if any NEW production file rides a mock prover, or a
listed one GROWS. Baseline: **14 production files / ~140 mock sites**, each carrying its purge verdict.
VERIFIED IT BITES (planted a `prove_ivc(` in cell/src -> "MOCK-PROOF PURGE VIOLATED"; removed -> green).
It also caught MY baseline bug first: `grep -c` counts LINES, the gate counts OCCURRENCES (presentation.rs
18 vs the true 21) — the gate corrected me before I committed a wrong number.
Failure message forbids the cheat: "Do NOT add yourself to the baseline — wire it to
`ivc_turn_chain::prove_turn_chain_recursive` / `prove_vm_descriptor2`, or FAIL CLOSED."

### THE PURGE WORKLIST (from map `wh0frxr57`) — verdict per surface
| surface | verdict | note |
|---|---|---|
| `node/mcp/handlers_verify.rs::dregg_compress_history` | **NEEDS-PLUMBING** | WORST: LIVE MCP tool returns "valid" for `create_test_chain` SYNTHETIC data. **CONTESTED** (predicate-weld lane) |
| `node/mcp/handlers_verify.rs::dregg_compose_proofs` | **HONEST-RETIRE** | verifies NOTHING — `valid = true` unconditionally for every mode. **CONTESTED** |
| `dregg-genesis-snapshot` history leg | NEEDS-PLUMBING / RETIRE | a forger mints it himself via prove_ivc. **Fable working** |
| `preflight/checks/sovereign.rs` | **WIRE-FEASIBLE** | promotion gate certifying the lie is healthy. **Fable working** |
| `preflight/checks/{proofs,composition,backends}.rs` | WIRE-FEASIBLE | same. **CONTESTED** |
| `circuit/presentation.rs`(21) + `bridge/present.rs` + `multi_step_witness` + `backends/mod.rs` | HONEST-RETIRE | dead but ARMED: mock rides the wire type, `is_valid` honors it. **CONTESTED** (bridge side) |
| `circuit/ivc.rs`(79) + `constraint_prover.rs`(17) | RETIRE LAST | the engines — once nothing production rides them |

**THE FLAGSHIP FIX'S PLUMBING ALREADY EXISTS AND IS UNCALLED**: `turn/src/rotation_witness.rs:731
finalized_turn_from_full_turn` re-proves the rotated leg and FAIL-CLOSES unless the leg's wide anchors
equal the served FullTurnProof's proven commits — returning a REAL `FinalizedTurn`. Its required context
exists exactly once: `node/src/blocklace_sync.rs::execute_finalized_turn` (:4287), which today persists
ONLY the FullTurnProof (:5031-5035). **Persist the FinalizedTurn there (postcard, keyed by turn hash) and
`dregg_compress_history` can load the real chain and call `prove_turn_chain_recursive`.** That is the whole
unlock — for the MCP tool AND the genesis-snapshot history leg.
BLOCKER: `turn/` + `node/mcp` + `bridge/present` are held by the predicate-weld lane (FactBinding).

### srot sweep (persvati) — CONFOUNDED by the contested lane; needs a quiet tree
`cargo test --workspace --no-run` on the remote `srot` lane exited 101 at the FIRST compile failure:
`dregg-turn` (lib test) — `turn/src/executor/membership_verifier.rs:2872,3033: expected FactBinding, found
BabyBear`. That is the **predicate-weld lane's in-flight WIP** (they are threading `FactBinding` through and
have not updated the turn tests), NOT durable silent rot. `--no-run` halts on the first compile error, so
the sweep never reached the rest of the workspace.
**Lesson (the same shared-tree hazard, now at remote scale): an empirical sweep rsync's whatever WIP is in
the tree, so its verdict is only as clean as the tree.** Re-run when the predicate-weld lane lands. The
sweep MECHANISM is proven (it built the whole dep graph incl. dregg-lean-ffi's 145-facet leanc build and
reported a real error) — it just needs a quiet moment.
Heads-up worth passing to that lane: their WIP currently breaks `dregg-turn`'s lib test.

### CONTENTION BLOCKER (2026-07-16)
The predicate-weld lane (`FactBinding` / `predicate_arith_witness`) holds: `node/mcp/handlers_verify.rs`,
`bridge/src/present.rs`, `preflight/checks/{proofs,composition,backends}.rs`, `turn/**`. Those are 5 of the
mock-purge targets INCLUDING the flagship (`dregg_compress_history`) and the plumbing site (`turn/`).
Not racing them — a rename/edit collision in a shared tree is how wire identifiers get corrupted (already
paid for that once). Working the clean surfaces meanwhile; the contested ones resume when that lane lands.

### `e7c692453` — first 2 mock surfaces PURGED (ratchet baseline shrinks by 2)
- **preflight/checks/sovereign.rs** WIRED TO REAL: the promotion-gate "ivc_history_compression" check now
  mints real turns (`mint_rotated_participant_leg` -> `FinalizedTurn` -> `prove_turn_chain_recursive` +
  `verify_whole_chain_proof_bytes`), mock imports REMOVED, TWO real adversarial teeth (forged continuity +
  tampered publics both rejected). Type-checks in isolation; heavy integration test blocked by the
  contested lane's exec-lean breakage (named, not ours).
- **dregg-genesis-snapshot** history leg DROPPED: the mock `history: IvcProof` a forger could mint himself
  is gone; tamper-resistance rests on the voucher + re-addressing (where it actually lived). 5/5 tests pass,
  consumer (dregg-season) updated, mock dep removed from Cargo.toml.
- Ratchet re-verified PASSES with both baseline entries removed.

REMAINING PURGE (mostly gated on the predicate-weld lane freeing handlers_verify/bridge-present/turn):
- CONTESTED: `dregg_compress_history` (NEEDS-PLUMBING via finalized_turn_from_full_turn), `dregg_compose_proofs`
  (RETIRE — verifies nothing), preflight/{proofs,composition,backends}, bridge/present.
- HONEST-RETIRE: presentation.rs(21) + multi_step_witness + backends/mod.rs — dead but armed.
- ENGINES LAST: circuit/src/ivc.rs(79) + constraint_prover.rs(17) — once nothing production rides them.
Fable poll task (bixyxmfo6) waits on exec-lean to run the heavy sovereign test.

### Purge progress (2026-07-16 pm) — predicate-weld lane PARTIALLY landed
- `node/mcp/handlers_verify.rs`, `bridge/present.rs`, `turn/executor/membership_verifier.rs` are now CLEAN
  (committed). But `authorize.rs` + `preflight/checks/proofs.rs` still dirty, and `dregg-exec-lean` STILL
  breaks (`compute_signing_message` takes 3 args, 2 supplied — their in-flight signature change). So the
  NODE crate cannot compile → the node-side purge (flagship `dregg_compress_history` + `dregg_compose_proofs`)
  is code-workable (files clean) but NOT VERIFIABLE yet. Not writing node code I can't compile.
- FLAGSHIP is otherwise unblocked: all its files (handlers_verify, blocklace_sync, rotation_witness,
  dispatch, tools_def) are clean. The moment exec-lean compiles: persist `FinalizedTurn` (via
  `finalized_turn_from_full_turn`) at `blocklace_sync.rs::execute_finalized_turn:4287` keyed by turn hash,
  then `tool_compress_history` loads the real chain + `prove_turn_chain_recursive`. Clean pickup.
- `dregg_compose_proofs` (verifies NOTHING, valid=true for every mode, handlers_verify.rs:459-462) — also
  blocked on node compiling. HONEST-RETIRE when unblocked.
- IN FLIGHT (Fable, uncontested — circuit+bridge compile independent of exec-lean): retire the DEAD-BUT-ARMED
  presentation IVC mock (presentation.rs 21 + bridge/present 4 + multi_step 3 + backends 2 + the
  IvcPresentationProof/IvcBuilder/IvcBackend surface in ivc.rs). Explicitly NOT deleting the core engine fns
  (prove_ivc/verify_ivc/create_test_chain) — still ridden by the blocked node. Lowers the ratchet baseline.

### FLAGSHIP UNBLOCKED + IN FLIGHT (2026-07-16 pm)
The predicate-weld lane committed `authorize.rs` → **`dregg-exec-lean` compiles again → the node crate
builds → the flagship purge is live.** Two Fable agents now running on DISJOINT files:
- **Fable A** — retire the dead-but-armed presentation IVC mock (`circuit/{ivc,presentation,
  multi_step_witness,backends/mod}.rs` + `bridge/present.rs` + the ratchet baseline).
- **Fable B — THE FLAGSHIP**: (1) PLUMB — at `blocklace_sync.rs::execute_finalized_turn`'s `Ok(proven)`
  branch (~:5031, which today persists only the FullTurnProof), also mint the REAL `FinalizedTurn` via
  `finalized_turn_from_full_turn` (its docstring: its args are "exactly the turn's execution context the
  node holds" HERE) and persist it by turn hash. (2) WIRE — `tool_compress_history` loads the retained real
  chain and calls `prove_turn_chain_recursive` + `verify_whole_chain_proof_bytes`, reporting a REAL proof
  size + REAL verdict; `create_test_chain`/`prove_ivc`/`verify_ivc` deleted from the file. (3) FAIL CLOSED
  honestly for turns predating retention — never "valid" for anything not really proved. (4) RETIRE
  `dregg_compose_proofs` (verifies NOTHING: valid=true for every mode).
  B is forbidden from touching the ratchet file (A holds it) — B reports its count, I lower the baseline.

### srot sweep — RE-RUN GATED ON A QUIET TREE
exec-lean is fixed, but two Fable agents are actively editing, so an rsync-based workspace sweep would be
confounded by their WIP again (the same lesson as before: a remote sweep is only as clean as the tree).
Re-run once both land + are committed.

### `3388f5aef` — 3rd surface PURGED: the presentation IVC mock (DEAD BUT ARMED) — -626 lines
`is_valid()` counted a MOCK `ivc_proof` as cryptographic backing and the mock rode the WIRE TYPE — a trap
for the next caller. **Disarmed**: is_valid now rests solely on `real_stark_proof`. Deleted (each with a
grep dead-proof): PresentationAir::prove_ivc/_no_folds · BridgePresentationBuilder::prove_ivc ·
IvcPresentationProof(+verify) · the `ivc_proof` field on BOTH the presentation + wire types ·
multi_step/presentation `prove_authorization` + AuthorizationProof · IvcBackend trait + IvcOutput + the
backend enums + finalize_with_backend · the dead bench + 3 tests.
WIRE DECISION reasoned: removing `ivc_proof` is SAFE (no sender ever set it — constant `None` byte; no
golden vectors; endpoints version together; presentations are nonce-bound/ephemeral; mismatch fails CLOSED).
CORE ENGINE untouched (node still rides it — retires last).
RATCHET SHRANK: ivc 79->70 · presentation 21->11 · bridge/present 4->**0** · multi_step 3->**0** ·
backends 2->**0**. Verified: circuit lib 673 passed, gate passes.
**Purge scoreboard: 3 of 7 surfaces done (preflight-wired, genesis-dropped, presentation-retired).**
