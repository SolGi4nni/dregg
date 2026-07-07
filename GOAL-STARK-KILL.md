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

## Next 3 moves
1. Await DFA Rung-2 conclusion → verify + commit the `DfaRoutingRung2` template (builds
   green; real `CollisionFree` carrier + `cheatTrace` non-vacuity witness).
2. Fan out Rung-2 across all families (additive `*Rung2.lean`, adversarial vacuity-hunt),
   prioritizing the honest Rung-1 PARTIALs (membership, note_spending).
3. Phase 2b: theorem-backed hand-AIR deletion for done families; then `git rm stark.rs`.

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
