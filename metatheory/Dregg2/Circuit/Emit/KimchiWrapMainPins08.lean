/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins08 — §18b — W-PREV

⚑ **ONE MODULE OF THE `KimchiWrapMain` SPLIT.** The namespace is unchanged
(`Dregg2.Circuit.Emit.KimchiWrapMain`), so nothing here is renamed and no consumer moves; the file
boundary exists only so a pin re-elaborates without the emitter's 5,000 lines of `def` behind it.
The in-file rule that keeps it stable is the step side's: **a `def` goes in `…Core`/`…Fixture`, a
pin goes in its section's `…PinsNN`.**

⚠ The `set_option` block below is VERBATIM `KimchiWrapMain`'s and must stay that way. `set_option`
does not cross an import, and `KimchiWrapFinalizeSpongeGate` shipped four proofs as `sorryAx` --
each still landing in the environment with the right statement -- because a split dropped it.

Pins only. Every `def` this section had is in `…Fixture`; the namespace-wide axiom pin is in the
`KimchiWrapMain` umbrella, which imports every one of these.

-/
import Dregg2.Circuit.Emit.KimchiWrapMainFixture

namespace Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams rcsQ mdsQ)

set_option autoImplicit false
set_option maxRecDepth 100000
-- ⚠ §12/§14b reduce whole sponge trajectories IN THE KERNEL (`rfl`/`decide`), which is strictly
-- stronger than the `#guard`s they replace and correspondingly slower to elaborate.
set_option maxHeartbeats 4000000

/-! ### §18b — ⚑ **W-PREV'S PINS, AS NAMED THEOREMS.**

⚠ Same discipline as §17b: nothing here reduces a ladder. The rows are `Generic` halves and one
probe, and every value pin is over `Nat`s.

⚑ **AND THE HARDEST ONE TO WRITE HONESTLY IS THE LAST.** A rung whose own row count is nine is easy
to oversell; what these say is exactly what §18's header says — the checks upstream emits, the σ
identities that make the MSM read the statement, and the census entry that did NOT move. -/

/-- ⚑ **`prev_step_accs` ARE REAL VESTA POINTS.** `Inner_curve.typ`'s check is `assert_on_curve`, so
the rung is only satisfiable if the values the transcript already absorbs as `sg_old` lie on
`y² = x³ + 5` over Fq. They do — `PastaPoseidonFq.PREVCOMM_XY` are the two `RecursionChallenge`
commitments of a proof `kimchi::verifier::verify` ACCEPTED — so `w9_prev` adds a real check WITHOUT
moving the transcript. Had they not been on the curve, this rung would have had to re-fixture
`sg_old` and every challenge below the absorb would have moved. -/
theorem prev_step_accs_are_on_vesta :
    (List.range shapeSmoke.prevs).all (fun p =>
      onCurveQ (itemVal T_SGOLD (2 * p), itemVal T_SGOLD (2 * p + 1))) = true
    ∧ (List.range shapeWrap.prevs).all (fun p =>
      onCurveQ (itemVal T_SGOLD (2 * p), itemVal T_SGOLD (2 * p + 1))) = true := by
  refine ⟨rfl, rfl⟩

/-- ⚑ **AND THE ON-CURVE CHECK RUNS ON THE ABSORBED CELLS, NOT ON COPIES.** `wrap_main.ml:412` hands
`incrementally_verify_proof` the same `prev_step_accs` that `wrap_verifier.ml:538` absorbs, so both
`assert_on_curve` chains here name the transcript's own `wordV` for `sg_old`. A version that
allocated fresh coordinate cells would have checked a curve point the sponge never saw. -/
theorem prev_on_curve_runs_on_the_absorbed_cells :
    (List.range shapeSmoke.prevs).all (fun p =>
      hasHalf prRows [some (sgOldVar tPrev p 0), some (sgOldVar tPrev p 0),
                      some (prevSq shapeSmoke tPrev.sp p 0)] cMul
      && hasHalf prRows [some (prevSq shapeSmoke tPrev.sp p 0), some (sgOldVar tPrev p 0),
                         some (prevSq shapeSmoke tPrev.sp p 1)] cMul
      && hasHalf prRows [some (sgOldVar tPrev p 1), some (sgOldVar tPrev p 1),
                         some (prevSq shapeSmoke tPrev.sp p 1)] cOnCurveQ) = true
    ∧ (List.range shapeSmoke.prevs).all (fun p =>
        (sgOldVar tPrev p 0) == ((tPrev.sp.evs.getD (1 + 2 * p) default).wordV)) = true := by
  refine ⟨rfl, rfl⟩

/-- ⚑ **THE ONE CHECK THE 57-WORD `typ` EMITS, AND IT IS EMITTED TWICE BECAUSE THERE ARE TWO
`B Bool`s.** Everything else in `Types.Step.Proof_state.typ` is check-free at source (§18), so a
third `Boolean` half here would mean this file invented a constraint `wrap_main` does not have. -/
theorem prev_should_finalize_is_boolean_constrained :
    (List.range XHAT_PREVS).all (fun p =>
      let v := prevW shapeSmoke tPrev.sp (PREV_PER_PROOF_WORDS * p + PREV_SHOULD_FINALIZE)
      hasHalf prRows [some v, some v, some v] cBool) = true
    ∧ ((prevRows tPrev true).filter (fun r => r.kind == KGateType.generic)).length = 5
    ∧ ((prevRows tPrev true).filter (fun r => r.probe)).length = 1
    ∧ ((prevRows tPrev true).filter (fun r =>
         r.kind == KGateType.poseidon || r.kind == KGateType.varBaseMul
         || r.kind == KGateType.completeAdd)).length = 0 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ **§10 SLOT 12 CLOSES HERE.** `Field.Assert.equal messages_for_next_step_proof
prev_proof_state.messages_for_next_step_proof` (`wrap_main.ml:350-351`) as the tie between the rung's
own public word and packed statement word `PREV_MSG_NEXT_STEP` — and the rung's public size is one
more than every rung below it. -/
theorem prev_ties_messages_for_next_step_proof_to_a_public_word :
    hasHalf prRows [some (.external shapeSmoke.pubWords : PVar),
                    some (prevW shapeSmoke tPrev.sp PREV_MSG_NEXT_STEP), none] cEq = true
    ∧ rungPub shapeSmoke .prev = shapeSmoke.pubWords + 1
    ∧ rungPub shapeSmoke .ftcomm = shapeSmoke.pubWords
    ∧ (exposedVarsAt tPrev .prev).getD shapeSmoke.pubWords (.external 0)
        = prevW shapeSmoke tPrev.sp PREV_MSG_NEXT_STEP := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ **…AND THAT PUBLIC WORD IS NOT A PUBLIC FIXTURE.** The cell it ties is packed word 54, which
the MSM reads as entry 64 — at the committed wrap shape by construction, and at the SMOKE shape
because `xhatSel` selects it. A shape that exposed the word without selecting the entry would tie a
public word to a cell no other row constrains, which is the defect class this rung would otherwise
have introduced. -/
theorem prev_public_word_is_read_by_the_msm :
    (xhSel shapeSmoke).contains (XHAT_PER_PROOF * XHAT_PREVS) = true
    ∧ (xhSel shapeWrap).contains (XHAT_PER_PROOF * XHAT_PREVS) = true
    ∧ (List.range (xhN shapeSmoke)).any (fun k =>
        xhAt shapeSmoke k == XHAT_PER_PROOF * XHAT_PREVS
        && xScal shapeSmoke tPrev.sp k == prevW shapeSmoke tPrev.sp PREV_MSG_NEXT_STEP) = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚑ **THE MSM READS THE STATEMENT, AND THE TIE IS A σ IDENTITY RATHER THAN A ROW.**
`wrap_main.ml:404-411` passes `pack_statement … prev_statement` straight into
`incrementally_verify_proof`, so entry `i`'s scalar and its packed word are ONE `Cvar` and cost no
constraint. `xScal` is that: every non-split entry's scalar cell IS `prevW (xhatWordOf i)`, and only
the two `split_field` halves keep cells of their own. Emitting `Field.Assert.equal` rows instead
would have been stricter than `wrap_main` and would have had to be declared in §13's list. -/
theorem prev_msm_scalars_are_the_statement_words :
    (List.range (xhN shapeSmoke)).all (fun k =>
      let i := xhAt shapeSmoke k
      if xhatIsSplitHi i || xhatIsSplitLo i then
        xScal shapeSmoke tPrev.sp k
          == (PVar.external (baseXh shapeSmoke tPrev.sp + XH_STRIDE * k + 4))
      else xScal shapeSmoke tPrev.sp k == prevW shapeSmoke tPrev.sp (xhatWordOf i)) = true
    ∧ ((List.range (xhN shapeSmoke)).filter (fun k =>
        xScal shapeSmoke tPrev.sp k
          == prevW shapeSmoke tPrev.sp (xhatWordOf (xhAt shapeSmoke k)))).length = 3 := by
  refine ⟨rfl, rfl⟩

/-- ⚑ **AND `w7_split`'s `x` IS THAT SAME WORD** — the sentence §16's header had been carrying as a
promise since `w7_split` landed. The `cSplit 1` half now names three cells the circuit uses
elsewhere: the statement word, and the two MSM entry scalars its halves feed. -/
theorem split_x_is_the_statement_word :
    (List.range (splitPairs shapeSmoke).length).all (fun a =>
      xSplitW shapeSmoke tPrev.sp a
        == prevW shapeSmoke tPrev.sp
             (xhatWordOf (xhAt shapeSmoke ((splitPairs shapeSmoke).getD a (0, 0)).1))) = true
    ∧ (splitPairs shapeSmoke).length = 1
    ∧ hasHalf (splitRows tPrev true)
        [some (xSplitW shapeSmoke tPrev.sp 0),
         some (xScal shapeSmoke tPrev.sp ((splitPairs shapeSmoke).getD 0 (0, 0)).1),
         some (xScal shapeSmoke tPrev.sp ((splitPairs shapeSmoke).getD 0 (0, 0)).2)]
        (cSplit 1) = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- The `w9_prev` rung is a strict superset of `w8_ftcomm`, its length is the sum of its parts, and
the WIRED and UNWIRED emissions differ ONLY in the probe rows' permutation columns. -/
theorem prev_rung_extends_ftcomm :
    (rungRows tPrev .prev true).length
      = (rungRows tPrev .ftcomm true).length + (prevRows tPrev true).length
    ∧ (rungRows tPrev .ftcomm true).length < (rungRows tPrev .prev true).length
    ∧ (((rungRows tPrev .prev true).zip (rungRows tPrev .prev false)).filter
        (fun p => p.1.perm != p.2.perm)).length
        = ((rungRows tPrev .prev true).filter (fun r => r.probe)).length := by
  refine ⟨rfl, by decide, rfl⟩

/-- `placeChecked` ACCEPTS the `w9_prev` rung at its LARGER public size and no public word is inert
— including the new one. ⚑ And the rung below it is refused at that size: `w8_ftcomm`'s gates read
no cell for slot `pubWords`, so `inertPublicWord` fires. That is the leg that makes the reservation
a gate rather than a comment. -/
theorem prev_rung_places_and_the_rung_below_it_does_not :
    refusalOf shapeSmoke (rungPub shapeSmoke .prev) (wrapGates (rungRows tPrev .prev true)) = none
    ∧ inertPublicWords (rungPub shapeSmoke .prev)
        (wrapGates (rungRows tPrev .prev true)) = []
    ∧ inertPublicWords (rungPub shapeSmoke .prev)
        (wrapGates (rungRows tPrev .ftcomm true)) = [shapeSmoke.pubWords] := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚠ ⚑ **THE CENSUS DID NOT MOVE, AND THE ENTRY IS REWRITTEN RATHER THAN DELETED.** W-PREV names
the MSM's scalars and constrains three of the 67 — one to a public word, two to bits. The other 64
are free witnesses, HERE and UPSTREAM, so an MSM over them still spans the group and the prover's
reach into the transcript is unchanged in size. `sg_old` likewise: it is on-curve now and still
consumed by nothing, because its consumer is `Split_commitments.combine`'s `~init` (W-COMBINE).
Striking either entry on the strength of "a sub-circuit now reads it" is the metric-gaming this
census exists to refuse. The count stays **8**. -/
theorem prev_does_not_move_the_unconsumed_census :
    WRAP_UNCONSUMED.length = 8
    ∧ WRAP_UNCONSUMED_KEYS.getD 1 "" = "x_hat"
    ∧ WRAP_UNCONSUMED_KEYS.getD 0 "" = "sg_old" := by
  refine ⟨rfl, rfl, rfl⟩

end Dregg2.Circuit.Emit.KimchiWrapMain
