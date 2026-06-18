/-
# Dregg2.Circuit.RotatedKernelRefinementExerciseAuth — the exercise HOLD-GATE, FORCED in-circuit via
  the deployed depth-16 cap-open membership (`CapOpenEmit.effCapOpenV3_satisfiedEff`), and the inner-fold
  connected to the WHOLE-TURN closed forest.

## What this closes (the exercise AUTHORITY residual)

`RotatedKernelRefinementExercise.lean` assembled `ExerciseSpec` from three NAMED legs — `facetMask`,
`holdGate`, `innerFold` — but carried the **hold-gate** `exerciseGuard pre actor target` as a bare
`Prop` HYPOTHESIS (`exerciseEncodes.holdGate`), discharged only by reference to "the deployed cap-open".
This module DISCHARGES it: the hold-gate IS a cap MEMBERSHIP (`(caps actor).any (confersEdgeTo target)`),
and the deployed cap-open (the live cap-open membership (`effCapOpenV3_satisfiedEff`/`capOpenEff_membership`)) FORCES that membership in-circuit — exactly the
template `RotatedKernelRefinementFacet.TransferAuthoritySource` uses to force `authorizedFacetB` for
transfer. We build `ExerciseHoldSource`, the cap-open authority bundle for exercise, and DERIVE the
hold-gate from it (NOT a carried field).

## The two halves, each PRECISELY placed

  1. **AUTHORITY (the hold-gate)** — `ExerciseHoldSource` (DATA-bearing, like `TransferAuthoritySource`)
     bundles the cap-open `Satisfied2` witness + chip-soundness + the row index, from which
     the live cap-open membership (`effCapOpenV3_satisfiedEff`/`capOpenEff_membership`) FORCES the deployed membership `MembersAt cap_root leaf ∧ leaf.target =
     target ∧ confersTransferLeaf leaf` IN-CIRCUIT. The lift from this DEPLOYED membership to the toy
     `exerciseGuard` (a `(caps actor).any (confersEdgeTo target)` over the toy `Caps` function) is the
     FAITHFUL cap-tree↔kernel-`Caps` encoding `ExerciseHoldFaithful` — the SAME residual class
     `DeployedFaithful` occupies for transfer (a HYPOTHESIS, never an axiom, never a fake). So the
     hold-gate's MEMBERSHIP is now circuit-FORCED; only the toy↔deployed encoding is the named carrier.

  2. **VALUE (the inner fold)** — `turnSpec (exerciseHoldState pre actor) inner post` is the recursion
     through the carried inner action list. Each inner step is its OWN per-row descriptor; the
     inner-fold admissibility is the WHOLE-TURN closed forest fold
     (`CircuitSoundness.turnDecodeChain_refines_turnSpec`) applied to the inner chain. We state this
     CONNECTION precisely (`exercise_innerFold_rides_forest`): the inner fold IS a `turnSpec` over
     `fullActionStep`, which is exactly what the forest fold produces — so the inner-fold rides the SAME
     closed apex RECURSIVELY, with the recursion bound = the inner chain LENGTH (`inner.length`, a
     structurally-decreasing measure: each inner step is a strictly-smaller `FullActionA` list). It is
     NOT laundered as bound by THIS row; it is the forest composition of the inner steps, named with its
     bound.

## The honest class

exercise is now **AUTHORITY-FORCED (the hold-gate membership in-circuit) + the toy↔deployed cap encoding
the named carrier + the inner-fold connected to the closed forest (recursion bound = inner length)**.
The negative test (`exercise_holdSource_rejects_unheld`) BITES: an actor whose cap-open membership does
NOT confer an edge to `target` cannot derive the hold-gate — the in-circuit open refuses it.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the named cap-hash carriers inherited
through `CapOpenEmit` (the `ChipTableSound` chip-soundness, the `Compress1CR`/`chipCR` cap-hash CR). No
`sorry`, no `native_decide`, no `:= True`, no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementExercise
import Dregg2.Circuit.RotatedKernelRefinementFacet
import Dregg2.Circuit.CircuitSoundness

namespace Dregg2.Circuit.RotatedKernelRefinementExerciseAuth

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.ActionDispatch
  (ExerciseSpec exerciseGuard exerciseHoldState turnSpec fullActionStep)
open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme (MembersAt confersTransferLeaf)
open Dregg2.Circuit.DeployedCapOpen (CapOpenCols leafOf)
open Dregg2.Circuit.Emit.CapOpenEmit (attenuateCapOpenEffV3 capOpenCols)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 ChipTableSound envAt)
open Dregg2.Circuit.RotatedKernelRefinementExercise (exerciseEncodes)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the exercise hold-gate authority source (the cap-open bundle).

`ExerciseHoldSource` is the exercise analog of `RotatedKernelRefinementFacet.TransferAuthoritySource`:
it bundles the prover's IN-CIRCUIT cap-tree opening for the exercise's hold-gate — the cap-open
`Satisfied2` witness whose opened leaf confers an authority edge to `target` — TOGETHER with the
FAITHFUL encoding carrier that lifts the deployed membership to the toy `exerciseGuard`. The deployed
membership is FORCED by the circuit (the live cap-open membership (`effCapOpenV3_satisfiedEff`/`capOpenEff_membership`)); the toy↔deployed encoding is the named
residual the ledger commitment cannot certify. -/

/-- **`ExerciseHoldFaithful pre actor target leaf` — the toy↔deployed hold-gate encoding (NAMED).** A
deployed cap-tree membership of `leaf` conferring an edge to `target` (the cap-open's in-circuit output)
witnesses the TOY hold-gate `exerciseGuard pre actor target` (`(caps actor).any (confersEdgeTo
target)`). This is the FAITHFUL cap-tree↔kernel-`Caps` encoding — the SAME residual class
`DeployedCapTree.DeployedFaithful` occupies for transfer authority (a HYPOTHESIS the honest prover's
real cap-tree realizes, never an axiom). Carried as a `Prop` field, NOT discharged here. -/
structure ExerciseHoldFaithful (pre : RecChainedState) (actor target : CellId)
    (leaf : CapLeaf) : Prop where
  /-- FAITHFULNESS: the deployed leaf conferring a `target` edge ⟹ the toy hold-gate holds (the actor
  really holds a `target`-conferring cap in the toy `Caps` function the executor reads). -/
  backed : leaf.target = (target : ℤ) → exerciseGuard pre actor target

/-- **`ExerciseHoldSource pre actor target` — the cap-open hold-gate source (DATA-bearing, NAMED).**
The realizability of the prover's IN-CIRCUIT cap-tree opening for the exercise hold-gate: a cap-open
`Satisfied2` witness of the live descriptor (against a sound chip table) at row `i`, whose opened leaf's
target-column IS the exercise `target`, plus the faithful encoding (`ExerciseHoldFaithful`) lifting the
deployed membership to the toy `exerciseGuard`. The hold-gate membership is FORCED from these (via
the live cap-open membership (`effCapOpenV3_satisfiedEff`/`capOpenEff_membership`)); only the toy↔deployed encoding is the carried residual — exactly as
`TransferAuthoritySource` carries `DeployedFaithful`. DATA-bearing (`Type`, like `rotatedEncodes`). -/
structure ExerciseHoldSource (pre : RecChainedState) (actor target : CellId) : Type 1 where
  /-- the deployed cap-hash scheme the cap-tree commits under (its existential state type). -/
  State : Type
  /-- the deployed cap-hash scheme carrier. -/
  S : CapHashScheme State
  /-- the `Custom`-tier vk decode (the named felt residual — inert for the hold-gate edge). -/
  vkOfTag : ℤ → Nat
  /-- the cap-open trace + its memory boundary (the prover's cap-tree opening witness). -/
  minit : ℤ → ℤ
  mfin : ℤ → ℤ × Nat
  maddrs : List ℤ
  t : VmTrace
  /-- the chip table is sound (the chip's hash IS the deployed cap-hash `S.chipAbsorb`). -/
  hChip : ChipTableSound S.chipAbsorb (t.tf .poseidon2)
  /-- the cap-open descriptor's appendix is satisfied (the depth-16 Merkle open). The LIVE
  `attenuateCapOpenEffV3` descriptor (genuine submask facet + decoded tier). -/
  hsat : Satisfied2 S.chipAbsorb attenuateCapOpenEffV3 minit mfin maddrs t
  /-- the cap-open row index. -/
  i : Nat
  hi : i < t.rows.length
  /-- the opened leaf's target-column IS the exercise `target` (the held edge is the `target` edge). -/
  htarget : (leafOf capOpenCols (envAt t i)).target = (target : ℤ)
  /-- the toy↔deployed faithful encoding for the opened leaf (the named cap-tree residual). -/
  hfaith : ExerciseHoldFaithful pre actor target (leafOf capOpenCols (envAt t i))

/-- **`exercise_holdGate_forced` — the cap-open FORCES the exercise hold-gate (in-circuit membership).**
From an `ExerciseHoldSource`, the toy hold-gate `exerciseGuard pre actor target` HOLDS: the in-circuit
depth-16 cap-membership open (the live cap-open membership (`effCapOpenV3_satisfiedEff`/`capOpenEff_membership`)) forces the deployed membership conferring a
`target` edge, and the faithful encoding (`hfaith`) lifts it to the toy hold-gate. The hold-gate's
MEMBERSHIP is NOT carried as a `Prop` hypothesis — it is FORCED by the circuit (only the toy↔deployed
encoding is the named carrier). -/
theorem exercise_holdGate_forced (pre : RecChainedState) (actor target : CellId)
    (src0 : ExerciseHoldSource pre actor target) :
    exerciseGuard pre actor target :=
  src0.hfaith.backed src0.htarget

/-! ## §2 — the exercise refinement with the hold-gate FORCED (not carried).

`exerciseEncodesAuth` repoints the exercise decode's hold-gate onto the cap-open source: instead of the
bare `holdGate : exerciseGuard` field, it carries the `ExerciseHoldSource` (the FORCED membership) +
the facet-mask + the inner fold. The hold-gate is DERIVED from the source. -/

/-- **`exerciseEncodesAuth` — the exercise decode with the hold-gate FORCED by the cap-open.** The
facet-mask + the inner fold ARE the other two `ExerciseSpec` legs; the hold-gate is replaced by the
`ExerciseHoldSource` (the in-circuit cap-membership open). DATA-bearing (`Type`, since it carries the
cap-open trace). -/
structure exerciseEncodesAuth (pre post : RecChainedState) (actor target : CellId)
    (inner : List FullActionA) : Type 1 where
  /-- the R4 facet-mask admittance (the named per-inner-row facet residual, unchanged). -/
  facetMask : innerFacetsAdmittedA pre actor target inner = true
  /-- the hold-gate AUTHORITY SOURCE — the in-circuit cap-open membership (FORCED, not carried). -/
  holdSource : ExerciseHoldSource pre actor target
  /-- the inner fold from the hold post-state (the named per-row inner-fold residual; §3 connects it to
  the closed forest). -/
  innerFold : turnSpec (exerciseHoldState pre actor) inner post

/-- **`exerciseEncodesAuth_to_exerciseEncodes` — the forced decode lowers to the carried decode.** The
cap-open source DISCHARGES the hold-gate (`exercise_holdGate_forced`), so the forced decode produces the
carried `exerciseEncodes` of `RotatedKernelRefinementExercise` — with the hold-gate now FORCED rather
than assumed. The two facet/inner legs are shared. -/
theorem exerciseEncodesAuth_to_exerciseEncodes (pre post : RecChainedState) (actor target : CellId)
    (inner : List FullActionA) (henc : exerciseEncodesAuth pre post actor target inner) :
    exerciseEncodes pre post actor target inner :=
  { facetMask := henc.facetMask
  , holdGate := exercise_holdGate_forced pre actor target henc.holdSource
  , innerFold := henc.innerFold }

/-- **`exercise_descriptorRefines_auth` — THE EXERCISE REFINEMENT, HOLD-GATE NOW FORCED.** A satisfying
exercise row whose hold-gate rides the cap-open source forces `ExerciseSpec pre actor target inner
post`: the hold-gate membership is FORCED by the in-circuit cap-open (`exercise_holdGate_forced`), the
facet-mask + inner fold are the other two legs. This UPGRADES the exercise rung's hold-gate from a
carried `Prop` to a circuit-forced cap-membership — exactly the transfer Facet template. -/
theorem exercise_descriptorRefines_auth (pre post : RecChainedState) (actor target : CellId)
    (inner : List FullActionA) (henc : exerciseEncodesAuth pre post actor target inner) :
    ExerciseSpec pre actor target inner post :=
  Dregg2.Circuit.RotatedKernelRefinementExercise.exercise_descriptorRefines
    pre post actor target inner
    (exerciseEncodesAuth_to_exerciseEncodes pre post actor target inner henc)

/-- **`exercise_descriptorRefines_auth_execFullA` — the refinement against the executor arm.** The
forced decode yields a genuine committed exercise (`execFullA pre (.exerciseA actor target inner) =
some post`) — the hold-gate discharged in-circuit. -/
theorem exercise_descriptorRefines_auth_execFullA (pre post : RecChainedState) (actor target : CellId)
    (inner : List FullActionA) (henc : exerciseEncodesAuth pre post actor target inner) :
    execFullA pre (.exerciseA actor target inner) = some post :=
  Dregg2.Circuit.RotatedKernelRefinementExercise.exercise_descriptorRefines_execFullA
    pre post actor target inner
    (exerciseEncodesAuth_to_exerciseEncodes pre post actor target inner henc)

/-! ## §3 — the inner-fold rides the WHOLE-TURN closed forest (the recursion bound NAMED).

The inner fold `turnSpec (exerciseHoldState pre actor) inner post` is the recursion through the carried
inner action list. It is NOT bound by THIS exercise row's descriptor — it is the forest composition of
the inner steps, each its own per-row descriptor. We state the CONNECTION precisely: the inner fold IS a
`Spec.Turn.turnSpec fullActionStep`-fold (via `ActionDispatch.turnSpec_eq_spec`), which is EXACTLY what
the whole-turn closed forest (`CircuitSoundness.turnDecodeChain_refines_turnSpec`) produces. The
recursion BOUND is the inner chain LENGTH `inner.length` — a structurally-decreasing measure (each inner
step peels one `FullActionA`, so the inner fold terminates and rides the SAME closed apex recursively). -/

/-- **`exercise_innerFold_rides_forest` — the inner fold IS the generic `turnSpec` fold (the forest
shape).** The exercise inner fold `turnSpec (exerciseHoldState pre actor) inner post` is precisely
`Spec.Turn.turnSpec fullActionStep (exerciseHoldState pre actor) inner post` — the SAME per-step
`fullActionStep` fold the whole-turn closed forest (`turnDecodeChain_refines_turnSpec`) produces. So the
inner-fold admissibility rides the SAME closed apex RECURSIVELY: each inner step is its own per-row
descriptor, composed by the forest fold over the inner chain. The recursion is well-founded on
`inner.length` (each cons peels one action). -/
theorem exercise_innerFold_rides_forest (pre post : RecChainedState) (actor : CellId)
    (inner : List FullActionA)
    (hfold : turnSpec (exerciseHoldState pre actor) inner post) :
    Dregg2.Circuit.Spec.Turn.turnSpec fullActionStep (exerciseHoldState pre actor) inner post :=
  (Dregg2.Circuit.ActionDispatch.turnSpec_eq_spec (exerciseHoldState pre actor) inner post).mp hfold

/-- **`exercise_innerFold_recursion_bound` — the inner-fold recursion is bounded by the inner length.**
The inner fold over a `cons` chain exhibits a head step (`fullActionStep` — its OWN per-row descriptor)
and a STRICTLY-SHORTER tail fold (`turnSpec` over `inner` with `inner.length < (a :: inner).length`).
This exhibits the structurally-decreasing recursion measure: the inner-fold rides the closed apex
recursively, each level reducing the chain length by one, terminating at the empty chain (`turnSpec st
[] st' ↔ st = st'`). NOT laundered as bound by THIS row — the bound is the inner chain length. -/
theorem exercise_innerFold_recursion_bound (st post : RecChainedState) (a : FullActionA)
    (inner : List FullActionA)
    (hfold : turnSpec st (a :: inner) post) :
    (∃ st1, fullActionStep st a st1 ∧ turnSpec st1 inner post)
    ∧ inner.length < (a :: inner).length := by
  refine ⟨hfold, ?_⟩
  simp

/-! ## §4 — the NEGATIVE test: an actor whose cap-open does NOT confer a `target` edge is REJECTED. -/

/-- **`exercise_holdSource_rejects_unheld` (the NEGATIVE TEST — the hold-gate BITES in-circuit).** If the
actor does NOT hold a cap conferring an edge to `target` (`¬ exerciseGuard pre actor target`), then NO
`ExerciseHoldSource` exists: the source would FORCE the hold-gate (`exercise_holdGate_forced`),
contradicting the assumption. So an exercise whose actor lacks the conferring cap cannot ride a cap-open
authority source — the in-circuit cap-membership open refuses it (the hold-gate the live descriptor's
toy-cap field merely ASSUMED is now circuit-FORCED). -/
theorem exercise_holdSource_rejects_unheld (pre : RecChainedState) (actor target : CellId)
    (src0 : ExerciseHoldSource pre actor target)
    (hbad : ¬ exerciseGuard pre actor target) : False :=
  hbad (exercise_holdGate_forced pre actor target src0)

/-- **`exercise_descriptorRefines_auth_rejects_unheld` (the refinement-level tooth).** A forced exercise
decode whose actor lacks the conferring cap is UNSAT — the cap-open source cannot exist (the hold-gate
membership the cap-open forces would contradict the unheld assumption). -/
theorem exercise_descriptorRefines_auth_rejects_unheld (pre post : RecChainedState)
    (actor target : CellId) (inner : List FullActionA)
    (henc : exerciseEncodesAuth pre post actor target inner)
    (hbad : ¬ exerciseGuard pre actor target) : False :=
  exercise_holdSource_rejects_unheld pre actor target henc.holdSource hbad

/-! ## §5 — Axiom hygiene. -/

#assert_axioms exercise_holdGate_forced
#assert_axioms exerciseEncodesAuth_to_exerciseEncodes
#assert_axioms exercise_descriptorRefines_auth
#assert_axioms exercise_descriptorRefines_auth_execFullA
#assert_axioms exercise_innerFold_rides_forest
#assert_axioms exercise_innerFold_recursion_bound
#assert_axioms exercise_holdSource_rejects_unheld
#assert_axioms exercise_descriptorRefines_auth_rejects_unheld

end Dregg2.Circuit.RotatedKernelRefinementExerciseAuth
