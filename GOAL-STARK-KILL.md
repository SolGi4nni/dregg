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

## Current thrust
**Rung 0 + Rung 1 COMPLETE; Rung 2 essentially COMPLETE** (`464c34b8d`): 10 DONE_AT_RUNG1
(Rung 1 already = no-forgery) + 4 full Rung-2 (note_spending/quantified_absence/temporal/
garbled) + 4 honest PARTIAL (membership/ivc/predicates-relational/revocation) + DFA template.
Pending: predicates-arithmetic (StructuredOutput cap — re-run). Next real milestone = Phase 2b
CUTOVER (⚠ ember-steer: high-risk shared-file change; the perf win lands here).

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
