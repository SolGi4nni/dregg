# automatafl (n=2) — verified Custom-VK build spec (2026-07-14)

The reasonable, tractable model for a VERIFIED n=2 automatafl, from the scholar-architect-visionary pass. THE ARCHITECTURE
IS SETTLED: a hand-authored Custom AIR checking `new == applyTurn(old, moves)`, gated by StateConstraint::Custom — NOT
mechanics-as-teeth (that was a rejected drift). Targets the committed contract metatheory/Dregg2/Games/Automatafl.lean.

## THE n=2 COLLAPSE (why this is tractable)
The general resolution is petgraph + Tarjan SCC + 4 MergeResolutionModes + cycle-rotation + empty-cycles. At n=2 (exactly two
moves) ALL of that is dead weight: the resolution is a FINITE SWITCH on the equality pattern among the 4 coordinates
{frm_a,to_a,frm_b,to_b} + the 2 source-vacuum bits. Enumerated:
- source-fork conflict (frm_a==frm_b, to_a!=to_b) -> both dropped; (to_a==to_b == identical move, NOT a conflict).
- dest-collision (to_a==to_b, both sources non-vacuum) -> both dropped.
- independent (disjoint) -> each moves iff its ray unoccluded.
- 2-chain/caterpillar (to_b==frm_a): B->A's-vacated-cell, A->A'; if A's source is vacuum, B flows THROUGH to A'.
- 2-swap (to_a==frm_b AND to_b==frm_a): the only nontrivial 2-edge SCC -> ALWAYS STASIS (no rotation).
- merge -> pin the mode to DetectAndConflict -> a two-real-piece merge is just a conflict -> DELETE all 4 merge modes +
  rotation + empty-cycles from the AIR.
=> NO Tarjan, NO SCC, NO merge machinery. The whole Phase 2-4.5 machine becomes ~10 boolean gates over 6 advice bits. The only
continuous residue: OCCLUSION (interior ray scan, sources passable) + the AUTOMATON RAYCAST — both board random-access reads.

## THE CUSTOM AIR (single-row, hash-free, translation-validation)
A single-row DSL CellProgram (circuit/src/dsl/circuit.rs CircuitDescriptor / ConstraintExpr) lowered by cellprogram_to_
descriptor2 (circuit-prove/src/custom_leaf_adapter.rs:670) -> IR-v2 -> prove_custom_leaf_with_commitment. TRANSLATION
VALIDATION: the prover WITNESSES the resolution (which move survives, dests, the 4 raycast hits/dists, the offset), the AIR
CHECKS it is the correct function of (old, moves) and that `new` is exactly the applied board.
WITNESS COLUMNS (board NxN, K=N^2 cells, one BabyBear felt/cell in {0=vac,1=rep,2=att,3=auto}): old[0..K], new[0..K] (2K);
the 2 moves as cell-index+(x,y) (~10); auto location (pinned old[auto]==3); advice: 6 pattern bits + is-zero inverse cols;
per-move valid/occluded/dest; 4 raycasts (what,dist); per-axis Decision; offset (dx,dy); auto_new; win. For N=11: ~282 cols
<< MAX_TRACE_WIDTH=1024; PIs << 64.
CHECKS (as clean algebraic teeth): validity x2 (MoveValid conjunction — frm!=to, rook-align, endpoint!=auto, in-bounds); the
n=2 SELECTION truth-table (~10 Gated/Polynomial identities over the 6 pinned pattern bits -> survive/dest keys — the WHOLE
conflict+SCC+merge apparatus); occlusion x2 (AtLeastOne over the <=N interior cells, sources passable); the AUTOMATON STEP
(the fully-Lean-proven fragment — raycast bounded axis scan + evaluateAxis's truth table with dist>1 guards + decisionCmp/
chooseOffset via the bit-decomposition range gadget compiler.rs:17-40 for the <=4-bit compares + in-bounds/vacuum guard +
win = [auto_new in goals]); output equality (K teeth: each new[c] = selected-sum keyed on dest_a/dest_b/auto_new/cleared-
source==c, else old[c]). ~240 constraints, degree <=8, HASH-FREE / Merkle-free / Lookup-free (dodges every leaf-adapter
residual). Only clean algebraic + bit-decomposition + optionally TableFunction/grid-indicator for board reads.
BOARD CELL + GATE: the board is a dregg cell (a heap enum-grid via dregg-schema); the move method carries StateConstraint::
Custom{ir_hash, descriptor, reads}; the executor demands a custom_program_proof verified against ir_hash (cell/program/eval.
rs:1732). FOLD PLUG (all existing, now Lane-D-green): prove_custom_leaf_with_commitment -> the dual-expose leg + prove_custom_
binding_node_segmented (joint_turn_recursive.rs:595) -> prove_turn_chain_recursive -> verify_turn_chain_recursive; a match =
a chain of these turns. SECRECY (n=2 simultaneous SECRET moves): reuse the sealed-auction commit-reveal wholesale (WriteOnce
seal = BLAKE3(who||frm||to||nonce) + StrictMonotonic(PHASE) commit->reveal->resolve + PreimageGate reveal); the RESOLVE turn
fires the Custom AIR on the revealed moves. Tighter cut (seal-binding into the Custom-AIR PIs) is a labeled follow-up.

## STAGED BUILD + SIZING
1. automaton-step-only AIR (~80 constraints — the richest already-Lean-proven+#guard'd fragment; the first leaf that proves->
   folds->verifies; refines automatonStep/automatonMove).
2. +single-move apply (validity + occlusion + place; refines applyMoves for |ms|=1).
3. +the 2-move resolution (the ~10-gate selection truth-table — the only genuinely-new logic; refines full n=2 applyTurn;
   matches the fork-conflict #guard).
4. +commit-reveal secrecy (the sealed-auction executor teeth + optional seal-binding PIs).
HARDEST PART: NOT the resolution (it evaporated) — the in-circuit RANDOM-ACCESS BOARD READS (occlusion scans + raycasts read
old[witnessed-coord] as low-degree gates under degree 8 -> favor a small board N<=9 or a segmented indicator; ONE gadget,
reused). Second: the concrete Lean Refines discharge (Automatafl.lean:573 states it vs an ABSTRACT AIR; proving the CONCRETE
DSL AIR refines applyTurn is the long pole). SIZING: steps 1-3 to driven-green (proves->folds->verifies, refinement-tested
vs the Lean #guards) = a few weeks; the full machine-checked Lean Refines = ~a quarter (the honest long pole).

## REUSE vs NEW
REUSE (green): the reference engine (the witness oracle); Automatafl.lean applyTurn + its proven properties (the refinement
target); cellprogram_to_descriptor2 + prove_custom_leaf_with_commitment; the whole fold (dual-expose + prove_custom_binding_
node_segmented + prove/verify_turn_chain_recursive); StateConstraint::Custom + the executor binding; the bit-decomposition
range gadget; TableFunction/grid-indicator; the commit-reveal rails (sealed-auction WriteOnce+PHASE+PreimageGate); dregg-schema.
NEW: the board-transition DSL CellProgram (validity + n=2 selection + occlusion + automaton + output-equality); its witness
generator (drives the reference engine, emits advice); the board-cell schema + ir_hash registration; the concrete Lean Refines;
(tighter) the seal-binding PIs.
