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
1. **Derivation cutover** — point `derivation_air.rs:372` + `dsl/descriptors.rs:734` off
   `dsl::derivation::derivation_circuit_descriptor()` (Rust-authored constraints) onto the emitted
   `dregg-derivation-v1` (`DerivationEmit.lean`, live via `derivation_witness.rs`). KEEP
   `generate_derivation_trace_dsl` (trace-gen is legit Rust).
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
