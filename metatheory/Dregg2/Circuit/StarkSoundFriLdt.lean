/-
# `Dregg2.Circuit.StarkSoundFriLdt` — THE NAMED STARK APEX, CUT OVER off the proved-empty bundle.

## What changed (2026-07-25)

`starkSound_of_friLdtExtract_transferV3` used to be conditioned on
`AlgoStarkSoundTransferV3.FriLdtExtractV3` at the deployed `cfg*` arguments. That premise is PROVED
EMPTY: `FriLdtExtractDeployed.friLdtExtractV3_makes_verifyBatch_reject_everything` shows it forces
`CircuitSoundness.verifyBatch` to return `Verdict.reject` on EVERY key/public-input/proof triple,
because the bundle concludes `oodPoint = [ood]` — one base felt — while acceptance forces four
extension lanes. The apex therefore quantified over an empty accepting set.

The premise is now `FriLdtExtractDeployed.FriLdtExtractV3Faithful` at the same arguments: the same
extraction payload, indexed by `ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt` (the predicate
`verifyBatch` actually evaluates), with the singleton conjunct replaced by what the deployed verifier
forces (`oodPoint = ood :: oodRest`, equal to the continued transcript's `ζ`, of `params.extDeg`
lanes). NO deprecated twin at the old shape is retained HERE — a twin would duplicate a statement
already proved empty. The old statement survives in exactly one place, deliberately and labelled:
`StarkSoundFriLdtCorrected.starkSound_of_friLdtExtract_transferV3_via_corrected`, which re-proves it
VERBATIM through the corrected chain as the RECEIPT that the cutover cost consumers nothing. That is
the tree's one remaining `StarkSound`-shaped conclusion drawn from the empty premise, and it exists
to record the subsumption, not to be consumed.

## What discharges the migration obligation (that the new premise is not ALSO empty)

  * `apexPremise_ood_conjuncts_come_from_acceptance` — the three OOD conjuncts the corrected bundle
    adds are supplied by the bundle's own antecedent, so they can never be the reason it is empty.
  * `apexPremise_adds_no_strength` — the corrected premise is EQUIVALENT, at the deployed arguments,
    to itself with those three conjuncts DELETED.
  * `starkSound_of_friLdtExtract_transferV3_noOodShape` — ★ the sharper form: the apex follows from a
    premise MENTIONING NO OOD-SHAPE CONJUNCT AT ALL. A premise cannot be emptied by a conjunct it
    does not contain.
  * `deleted_apex_premise_was_empty` — the receipt for what was removed.

## ⚠ What this cutover does NOT close

`apexPremise_false_of_accepting_run_without_tableOpenings`: the corrected bundle RETAINS
`topen ∈ (view pi π).1.tableOpenings`, and that conjunct is NOT supplied by acceptance. At any
arguments admitting an accepting run whose mapped proof opens no table, the migrated premise is
FALSE. `FriLdtExtractDeployed.deployed_accepting_pole_has_no_tableOpenings` exhibits exactly such a
run — but it is `Nat`-typed at concrete arguments, while this file's premise is `ℤ`-typed at the
`opaque` `cfg*` ones. So what is refuted is the SCHEMA where anything is exhibitable, NOT the
deployed instance, which nobody has decided in either direction. The cutover replaces a premise empty
EVERYWHERE with one whose emptiness is CONDITIONAL and UNDECIDED — an improvement, not a closure.

Unchanged underneath: the FRI-LDT soundness floor, and the fact that `StarkSound` is a statement
about the verifier's ACCEPTANCE of a SUPPLIED proof, not about a witness generator.
-/
import Dregg2.Circuit.AlgoStarkSoundTransferV3
import Dregg2.Circuit.StarkSoundDischarge
import Dregg2.Circuit.FriLdtExtractDeployed

namespace Dregg2.Circuit.StarkSoundFriLdt

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.FriVerifierBridge
open Dregg2.Circuit.AlgoStarkSoundTransferV3
open Dregg2.Circuit.StarkSoundDischarge
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.FriLdtExtractDeployed
  (ExtProofView FriLdtExtractV3Cons FriLdtExtractV3Faithful FriLdtExtractV3FaithfulNoOodShape
   friLdtExtractV3Cons_imp_faithful friLdtExtractV3Faithful_iff_noOodShape
   faithfulExt_accept_gives_cons_shape starkSound_of_friLdtExtractFaithful_transferV3
   friLdtExtractV3_makes_verifyBatch_reject_everything)

/-! ## §1 — THE APEX, over the corrected deployed-verifier bundle. -/

/-- **StarkSound for deployed transferV3 from the CORRECTED deployed-verifier extraction bundle.**

Floors, unchanged from the retired version: `Poseidon2SpongeCR sponge` (genuinely used in the
commitment binding) and the FRI-LDT extraction bundle itself. What changed: the bundle is indexed by
`verifyAlgoUnifiedFaithfulExt`, the predicate `CircuitSoundness.verifyBatch` evaluates, and its OOD
conjunct is the deployed four-lane transcript squeeze rather than a base-felt singleton — so this
premise does NOT force `verifyBatch` to reject every input, whereas the retired one did
(`deleted_apex_premise_was_empty`). -/
theorem starkSound_of_friLdtExtract_transferV3
    (sponge : List Int → Int) (hash : List Int → Int)
    (hfri : FriLdtExtractV3Faithful sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore
      cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView) :
    StarkSound hash (fun _ => Dregg2.Circuit.RotatedKernelRefinement.transferV3) :=
  starkSound_of_friLdtExtractFaithful_transferV3 sponge hash hfri

/-- **★ THE SHARPER FORM: the apex from a premise that MENTIONS NO OOD SHAPE AT ALL.** The strongest
available discharge of the migration obligation — whatever residual emptiness the premise may carry
is inherited ENTIRELY from the FRI-LDT / Merkle / Fiat–Shamir conjuncts (the floor), and none of it
from the OOD repair, because the OOD repair does not appear in this statement. Interderivable with
the apex above through `apexPremise_adds_no_strength`. -/
theorem starkSound_of_friLdtExtract_transferV3_noOodShape
    (sponge : List Int → Int) (hash : List Int → Int)
    (hfri : FriLdtExtractV3FaithfulNoOodShape sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk
      cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView) :
    StarkSound hash (fun _ => Dregg2.Circuit.RotatedKernelRefinement.transferV3) :=
  starkSound_of_friLdtExtract_transferV3 sponge hash
    ((friLdtExtractV3Faithful_iff_noOodShape sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk
      cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView).mpr hfri)

/-! ⚑ **DELETED 2026-07-28 — `retiredPremise_imp_apexPremise`.** It rode
`FriLdtExtractDeployed.friLdtExtractV3_imp_cons`, deleted in the same commit: the corrected bundles
now carry the per-run opening residual `¬ OpeningColl` (the honest replacement for the refuted
`Poseidon2SpongeCR` floor) and the LANDED bundle never did. WHAT WAS LOST: a free transport from a
premise PROVED empty at the deployed arguments (`deleted_apex_premise_was_empty`, below) — nothing
that ever transported. -/

/-! ## §2 — THE MIGRATION OBLIGATION: the installed premise is not ALSO empty. -/

/-- **The migrated premise's OOD conjuncts are supplied BY ITS OWN ANTECEDENT.** On every run the
bundle's antecedent accepts — at the deployed arguments, with no hypothesis beyond acceptance — the
OOD point already decomposes as `ood :: oodRest`, already IS the continued transcript's out-of-domain
squeeze, and already has `cfgParams.extDeg` lanes. Those are exactly the three conjuncts the
corrected bundle adds over an OOD-silent one, so they cannot be the reason it is empty. Contrast the
retired singleton conjunct, which acceptance REFUTES
(`FriLdtExtractDeployed.faithfulExt_forces_oodPoint_ne_singleton`). -/
theorem apexPremise_ood_conjuncts_come_from_acceptance
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : Dregg2.Circuit.ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt cfgPerm cfgRATE cfgToNat
      cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN
      (cfgView pi π).1 (cfgView pi π).2 (cfgExtView pi π) = true) :
    ∃ (ood : Int) (oodRest : List Int),
      (cfgView pi π).1.oodPoint = ood :: oodRest
        ∧ ood :: oodRest = (Dregg2.Circuit.FriChallengerUnified.deriveTranscript cfgPerm cfgRATE
            cfgToNat cfgParams cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2).ζ
        ∧ (ood :: oodRest).length = cfgParams.extDeg :=
  faithfulExt_accept_gives_cons_shape cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
    cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2
    (cfgExtView pi π) hacc

/-- **The migrated premise adds EXACTLY ZERO strength**, at the deployed arguments the apex is stated
at: it is EQUIVALENT to itself with the three OOD conjuncts deleted. The `mpr` direction is the whole
point — the conjuncts come from acceptance, so adding them cannot shrink, let alone empty, the set of
accepting runs the premise must cover. -/
theorem apexPremise_adds_no_strength (sponge : List Int → Int) (hash : List Int → Int) :
    FriLdtExtractV3Faithful sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
        cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView
      ↔ FriLdtExtractV3FaithfulNoOodShape sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk
        cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView :=
  friLdtExtractV3Faithful_iff_noOodShape sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk
    cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView

/-! ## §3 — THE RECEIPT for what was replaced. -/

/-- **THE RECEIPT: the premise this apex used to carry was EMPTY.** Under
`AlgoStarkSoundTransferV3.FriLdtExtractV3` at the deployed `cfg*` arguments — verbatim the retired
hypothesis of `starkSound_of_friLdtExtract_transferV3` — `CircuitSoundness.verifyBatch` returns
`Verdict.reject` on EVERY key/public-input/proof triple. So the retired apex quantified over an empty
accepting set: it was vacuously true, and would have been for any registry whatsoever
(`StarkSoundFriLdtCorrected.landedPremise_gives_starkSound_for_ANY_hash_and_registry` states that
collapse in its sharpest form). That is what the cutover removed, and why no deprecated twin at the
old shape is retained here. -/
theorem deleted_apex_premise_was_empty
    (sponge : List Int → Int) (hash : List Int → Int)
    (h : FriLdtExtractV3 sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView)
    (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof) :
    verifyBatch vkey pi π = Verdict.reject :=
  friLdtExtractV3_makes_verifyBatch_reject_everything sponge hash h vkey pi π

/-! ## §4 — ⚠ THE CAVEAT THIS CUTOVER INHERITS, AS A THEOREM RATHER THAN A NOTE. -/

/-- **⚠ The migrated premise is refutable at an accepting run with no table openings.**
`FriLdtExtractV3Faithful` RETAINS `topen ∈ (view pi π).1.tableOpenings`, and acceptance does NOT
supply it: at ANY arguments admitting an accepting run whose mapped proof opens no table, the
migrated premise is FALSE. The condition is not hypothetical —
`FriLdtExtractDeployed.deployed_accepting_pole_has_no_tableOpenings` exhibits a `decide`-backed
accepting run with `tableOpenings = []`.

That pole is `Nat`-typed at CONCRETE arguments while §1's premise is `ℤ`-typed at the `opaque` `cfg*`
ones, so what is refuted is the SCHEMA at the arguments where anything is exhibitable — NOT the
deployed instance, which nobody has decided in either direction. Stated as a theorem so the residual
travels with the apex that carries it: this cutover trades a premise empty EVERYWHERE for one whose
emptiness is CONDITIONAL and UNDECIDED. -/
theorem apexPremise_false_of_accepting_run_without_tableOpenings
    (sponge : List Int → Int) (hash : List Int → Int)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (core : FriCore Int) (A : FieldArith Int)
    (extCore : Dregg2.Circuit.ExtFieldChallenge.ExtFriCore Int)
    (extA : Dregg2.Circuit.ExtFieldChallenge.ExtFriArith Int) (W : Int)
    (initState : List Int) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : Dregg2.Circuit.ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk
      core A extCore extA W initState logN (view pi π).1 (view pi π).2 (extView pi π) = true)
    (hnil : (view pi π).1.tableOpenings = []) :
    ¬ FriLdtExtractV3Faithful sponge hash perm RATE toNat params vk core A extCore extA W
        initState logN view extView := by
  intro h
  obtain ⟨_t, _ζ, _Λ, _qp, _topen, _ood, _vC, _root, _oodRest, _idx, _sib,
    _hcap, _hoodPt, _hzeta, _hlen, hmem, _⟩ := h pi π hacc
  rw [hnil] at hmem
  simp at hmem

#assert_axioms starkSound_of_friLdtExtract_transferV3
#assert_axioms starkSound_of_friLdtExtract_transferV3_noOodShape
#assert_axioms apexPremise_ood_conjuncts_come_from_acceptance
#assert_axioms apexPremise_adds_no_strength
#assert_axioms deleted_apex_premise_was_empty
#assert_axioms apexPremise_false_of_accepting_run_without_tableOpenings

end Dregg2.Circuit.StarkSoundFriLdt
