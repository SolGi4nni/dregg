/-
# `Dregg2.Circuit.StarkSoundFriLdtCorrected` — the NON-VACUOUS replacement for the RETIRED shape of
`StarkSoundFriLdt.starkSound_of_friLdtExtract_transferV3`.

⚑ 2026-07-25 STATUS UPDATE. This module was written while `StarkSoundFriLdt`'s apex still carried the
singleton-shaped `FriLdtExtractV3`. That apex has since been CUT OVER in place: it now carries
`FriLdtExtractDeployed.FriLdtExtractV3Faithful`, i.e. exactly this module's
`starkSound_of_friLdtExtractFaithful_deployed`. So wherever the text below says "the landed apex",
read "the RETIRED shape of the apex" — the statement no longer exists in the tree, and §2's
`starkSound_of_friLdtExtract_transferV3_via_corrected` is now a RECEIPT that the retired shape's
conclusion was never lost, not a parallel replacement for a live theorem. Everything proved here is
unaffected; only the relation to `StarkSoundFriLdt` changed.

## §A why the retired apex shape had nowhere to go

The retired `starkSound_of_friLdtExtract_transferV3` was conditioned
on `AlgoStarkSoundTransferV3.FriLdtExtractV3` at the deployed `cfg*` arguments. That bundle concludes
`oodPoint = [ood]` — ONE base felt — on every accepting run, and
`FriLdtExtractDeployed.friLdtExtractV3_makes_verifyBatch_reject_everything` PROVES that at those
arguments the premise forces `CircuitSoundness.verifyBatch` to return `reject` on EVERY
key/public-input/proof triple. The landed apex therefore quantifies over an empty accepting set.

`landedPremise_gives_starkSound_for_ANY_hash_and_registry` (§3) states that collapse in its sharpest
form: under the landed premise alone — no `Poseidon2SpongeCR`, no descriptor, no registry — one gets
`StarkSound hash' R` for EVERY `hash'` and EVERY `R`. A premise that proves the apex for descriptors
nobody wrote is proving nothing about `transferV3`.

## §B what this module delivers

The replacement apexes, over the CORRECTED bundles of `Dregg2.Circuit.FriLdtExtractDeployed`:

  * `starkSound_of_friLdtExtractCons_transferV3` — `StarkSound hash (fun _ => transferV3)` from
    `FriLdtExtractV3Cons` (the bare-verifier bundle at the `ood :: oodRest` shape
    `FriVerifier.batchTablesCheck` actually matches).
  * `starkSound_of_friLdtExtractFaithful_deployed` — the same conclusion from
    `FriLdtExtractV3Faithful`, the bundle indexed by `verifyAlgoUnifiedFaithfulExt`, the predicate
    `verifyBatch` really evaluates. This is the migration target with the smallest gap to reality.
  * `starkSound_of_noOodShape_transferV3` — the same conclusion from a premise that mentions NO OOD
    shape at all.

Relation to the RETIRED apex shape (§2): `FriLdtExtractV3 → FriLdtExtractV3Cons →
FriLdtExtractV3Faithful`, so `starkSound_of_friLdtExtract_transferV3_via_corrected` re-proves the
retired statement VERBATIM through the corrected chain. The corrected premise is thus weaker; the
retired apex is subsumed, not contradicted — which is exactly why cutting `StarkSoundFriLdt` over cost
its consumers nothing. The converse transport does not exist as an acceptance argument
(`FriLdtExtractDeployed.bundles_are_not_interchangeable`).

## §C the inhabitability argument — why this repair is not a second vacuity

The apex-level analogue of `FriLdtExtractDeployed`'s §6, in the same currency as the vacuity theorem
(statements about `verifyBatch` at the deployed arguments), and PROVED despite `cfg*` being `opaque`:

  * `verifyBatch_accept_gives_cons_shape` — on EVERY `verifyBatch`-accepting triple, at the DEPLOYED
    arguments, with NO hypothesis whatsoever, the corrected OOD conjuncts already hold: the OOD point
    is `ood :: oodRest`, it IS the continued transcript's `ζ`, and it has `cfgParams.extDeg` lanes.
  * `verifyBatch_accept_refutes_singleton` — on the same runs the singleton conjunct is FALSE.
  * `correctedPremise_iff_noOodShape` — at the deployed arguments the corrected premise is
    EQUIVALENT to itself-with-the-three-OOD-conjuncts-deleted, so the repair adds exactly zero
    strength, and `starkSound_of_noOodShape_transferV3` derives the apex from that OOD-free premise.

Together: the conjuncts this module's premise adds relative to an OOD-silent bundle are THEOREMS of
the deployed verifier, so they cannot be the reason any premise is empty — whereas the landed
singleton conjunct is REFUTED by the deployed verifier, which is exactly why the landed one is.

## §D what is NOT established (the floor that remains)

Not claimed here, and not claimable by anyone at present: that `FriLdtExtractV3Faithful` (or
`FriLdtExtractV3Cons`, or `FriLdtExtractV3FaithfulNoOodShape`) is SATISFIABLE at the deployed
arguments. `cfgPerm`, `cfgParams`, `cfgView`, `cfgExtView`, `cfgExtra`, … are `opaque`, so no
accepting run at those arguments can be exhibited, and the bundle's remaining conjuncts (the FRI-LDT
extraction, the Merkle-opening layout, the two Fiat–Shamir non-exceptionality clauses) ARE the
undischarged FRI floor. What §C establishes is strictly narrower and exact: the OOD component of the
corrected premise is implied by acceptance, hence contributes no emptiness; the OOD component of the
landed premise contradicts acceptance, hence contributes total emptiness. The residual floor is
unchanged in content by this repair — `correctedPremise_iff_noOodShape` says precisely that.

Also unchanged: the FRI soundness floor under it all, and the fact that `StarkSound` is a statement
about the verifier's ACCEPTANCE of a SUPPLIED proof, not about a witness generator.
-/
import Dregg2.Circuit.FriLdtExtractDeployed
import Dregg2.Circuit.StarkSoundFriLdt

namespace Dregg2.Circuit.StarkSoundFriLdtCorrected

open Dregg2.Circuit.CircuitSoundness
  (BatchPublicInputs BatchProof Registry StarkSound Verdict VerifyKey verifyBatch vkOfRegistry
   cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW
   cfgInitState cfgLogN cfgView cfgExtView cfgExtra)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.AlgoStarkSoundTransferV3 (FriLdtExtractV3)
open Dregg2.Circuit.ExtFieldChallenge (verifyAlgoUnifiedFaithfulExt)
open Dregg2.Circuit.FriLdtExtractDeployed
  (FriLdtExtractV3Cons FriLdtExtractV3Faithful FriLdtExtractV3FaithfulNoOodShape
   friLdtExtractV3_imp_cons friLdtExtractV3Cons_imp_faithful friLdtExtractV3Faithful_iff_noOodShape
   faithfulExt_accept_gives_cons_shape faithfulExt_forces_oodPoint_ne_singleton
   friLdtExtractV3_makes_verifyBatch_reject_everything)

/-! ## §1 — the deployed acceptance unfolding, shared by everything below. -/

/-- `verifyBatch` accepted ⇒ the predicate it evaluates, `verifyAlgoUnifiedFaithfulExt` at the
deployed arguments on the deployed view, returned `true`. (`verifyBatch` ignores its key argument;
the acceptance branch is the conjunction of the extension-faithful verifier and `cfgExtra`.) -/
theorem verifyBatch_accept_imp_faithfulExt
    (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyBatch vkey pi π = Verdict.accept) :
    verifyAlgoUnifiedFaithfulExt cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN
      (cfgView pi π).1 (cfgView pi π).2 (cfgExtView pi π) = true := by
  unfold verifyBatch at hacc
  by_cases h :
      (verifyAlgoUnifiedFaithfulExt cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
            cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN
            (cfgView pi π).1 (cfgView pi π).2 (cfgExtView pi π)
        && cfgExtra (cfgView pi π).1 (cfgView pi π).2) = true
  · exact ((Bool.and_eq_true _ _).mp h).1
  · rw [if_neg h] at hacc
    exact absurd hacc (by decide)

/-! ## §2 — the REPLACEMENT apexes, and their relation to the landed one. -/

/-- **`StarkSound` for the deployed `transferV3` slice from the CORRECTED deployed-verifier
bundle.** The migration target with the smallest gap to reality: the premise is indexed by
`verifyAlgoUnifiedFaithfulExt`, the predicate `verifyBatch` evaluates, and its OOD conjunct is the
transcript's four-lane `ζ` rather than a base-felt singleton. Floors: `Poseidon2SpongeCR sponge`
(used in the commitment binding) and the FRI-LDT extraction bundle. -/
theorem starkSound_of_friLdtExtractFaithful_deployed
    (sponge : List Int → Int) (hCR : Poseidon2SpongeCR sponge) (hash : List Int → Int)
    (hfri : FriLdtExtractV3Faithful sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore
      cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView) :
    StarkSound hash (fun _ => transferV3) :=
  Dregg2.Circuit.FriLdtExtractDeployed.starkSound_of_friLdtExtractFaithful_transferV3
    sponge hCR hash hfri

/-- **`StarkSound` for the deployed `transferV3` slice from the CORRECTED BARE-verifier bundle** —
the drop-in replacement for the RETIRED shape of
`StarkSoundFriLdt.starkSound_of_friLdtExtract_transferV3`: same
conclusion, same floors, and a premise differing from the landed one in exactly one conjunct
(`oodPoint = ood :: oodRest` instead of `oodPoint = [ood]`). -/
theorem starkSound_of_friLdtExtractCons_transferV3
    (sponge : List Int → Int) (hCR : Poseidon2SpongeCR sponge) (hash : List Int → Int)
    (hfri : FriLdtExtractV3Cons sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView) :
    StarkSound hash (fun _ => transferV3) :=
  starkSound_of_friLdtExtractFaithful_deployed sponge hCR hash
    (friLdtExtractV3Cons_imp_faithful sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore
      cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView hfri)

/-- **The RETIRED apex shape is SUBSUMED, not contradicted.** This is the RETIRED statement of
`StarkSoundFriLdt.starkSound_of_friLdtExtract_transferV3` VERBATIM, re-proved through the corrected
chain `FriLdtExtractV3 → FriLdtExtractV3Cons → FriLdtExtractV3Faithful → StarkSound`. It is the
RECEIPT that the 2026-07-25 cutover of that apex cost its consumers nothing: anything the retired
shape gave, the migrated one gives. -/
theorem starkSound_of_friLdtExtract_transferV3_via_corrected
    (sponge : List Int → Int) (hCR : Poseidon2SpongeCR sponge) (hash : List Int → Int)
    (hfri : FriLdtExtractV3 sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView) :
    StarkSound hash (fun _ => transferV3) :=
  starkSound_of_friLdtExtractCons_transferV3 sponge hCR hash
    (friLdtExtractV3_imp_cons sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView hfri)

/-- **The premise-level relation, at the deployed arguments**: the landed bundle DISCHARGES the
replacement's premise (`[ood] = ood :: []`, then acceptance supplies the transcript identity and the
lane count). This is the fact a migration rides: a consumer currently holding `FriLdtExtractV3` can
hand it to the corrected apex unchanged. The converse transport does not exist —
`FriLdtExtractDeployed.bundles_are_not_interchangeable` exhibits a concrete run the bare verifier
accepts and the unified/extension-faithful verifier rejects, so a bundle indexed by the deployed
verifier carries obligations on strictly fewer runs and cannot be pushed back to the bare one. -/
theorem landedPremise_imp_correctedPremise
    (sponge : List Int → Int) (hash : List Int → Int)
    (hfri : FriLdtExtractV3 sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView) :
    FriLdtExtractV3Faithful sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView :=
  friLdtExtractV3Cons_imp_faithful sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore
    cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView
    (friLdtExtractV3_imp_cons sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView hfri)

/-! ## §3 — the landed premise, in its sharpest collapsed form. -/

/-- **The landed premise proves the apex for descriptors nobody wrote.** Under
`FriLdtExtractV3` at the deployed arguments — with NO commitment-collision-resistance floor, NO
descriptor, NO registry — `StarkSound hash' R` holds for EVERY `hash'` and EVERY `R`, because
`verifyBatch` rejects everything (`friLdtExtractV3_makes_verifyBatch_reject_everything`). That a
premise about `transferV3`'s FRI extraction yields soundness for an arbitrary registry is the
signature of vacuity, and it is why the landed apex needs a replacement rather than a restatement. -/
theorem landedPremise_gives_starkSound_for_ANY_hash_and_registry
    (sponge : List Int → Int) (hash : List Int → Int)
    (hfri : FriLdtExtractV3 sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView)
    (hash' : List Int → Int) (R : Registry) :
    StarkSound hash' R where
  extract := by
    intro pi π hacc
    rw [friLdtExtractV3_makes_verifyBatch_reject_everything sponge hash hfri
      (vkOfRegistry R) pi π] at hacc
    exact absurd hacc (by decide)

/-! ## §4 — THE INHABITABILITY ARGUMENT for the replacement (apex-level, at the DEPLOYED args). -/

/-- **The corrected OOD conjuncts are a THEOREM of the deployed verifier.** On every triple
`verifyBatch` accepts — no hypothesis, at the `opaque` deployed arguments — the OOD point is
`ood :: oodRest`, it IS the continued transcript's out-of-domain squeeze, and it has
`cfgParams.extDeg` lanes. These are exactly the three conjuncts `FriLdtExtractV3Faithful` adds over
an OOD-silent bundle, so those conjuncts can never be the reason the replacement premise is empty. -/
theorem verifyBatch_accept_gives_cons_shape
    (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyBatch vkey pi π = Verdict.accept) :
    ∃ (ood : Int) (oodRest : List Int),
      (cfgView pi π).1.oodPoint = ood :: oodRest
        ∧ ood :: oodRest = (Dregg2.Circuit.FriChallengerUnified.deriveTranscript cfgPerm cfgRATE
            cfgToNat cfgParams cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2).ζ
        ∧ (ood :: oodRest).length = cfgParams.extDeg :=
  faithfulExt_accept_gives_cons_shape cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
    cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2
    (cfgExtView pi π) (verifyBatch_accept_imp_faithfulExt vkey pi π hacc)

/-- **The landed singleton conjunct is REFUTED on the very same runs.** The exact contrast with the
theorem above: what the replacement asserts, acceptance supplies; what the landed bundle asserts,
acceptance forbids. -/
theorem verifyBatch_accept_refutes_singleton
    (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyBatch vkey pi π = Verdict.accept) (ood : Int) :
    (cfgView pi π).1.oodPoint ≠ [ood] :=
  faithfulExt_forces_oodPoint_ne_singleton cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
    cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2
    (cfgExtView pi π) (verifyBatch_accept_imp_faithfulExt vkey pi π hacc) ood

/-- **The replacement premise adds ZERO strength**, at the deployed arguments the apex is stated at:
it is EQUIVALENT to itself with the three OOD conjuncts deleted. Instantiation of
`FriLdtExtractDeployed.friLdtExtractV3Faithful_iff_noOodShape` at `cfg*`. -/
theorem correctedPremise_iff_noOodShape
    (sponge : List Int → Int) (hash : List Int → Int) :
    FriLdtExtractV3Faithful sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
        cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView
      ↔ FriLdtExtractV3FaithfulNoOodShape sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk
        cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView :=
  friLdtExtractV3Faithful_iff_noOodShape sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk
    cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView

/-- **The apex from a premise that never mentions the OOD shape.** The strongest form of "the repair
is not a second vacuity": the replacement apex is available under a bundle carrying no OOD conjunct
at all, so whatever residual emptiness the premise may have is inherited ENTIRELY from the FRI-LDT /
Merkle / Fiat–Shamir conjuncts — the floor — and none of it from the OOD repair. -/
theorem starkSound_of_noOodShape_transferV3
    (sponge : List Int → Int) (hCR : Poseidon2SpongeCR sponge) (hash : List Int → Int)
    (hfri : FriLdtExtractV3FaithfulNoOodShape sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk
      cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView) :
    StarkSound hash (fun _ => transferV3) :=
  starkSound_of_friLdtExtractFaithful_deployed sponge hCR hash
    ((correctedPremise_iff_noOodShape sponge hash).mpr hfri)

/-- **The apex-facing predicate accepts something** (re-exported here so the migration record is
self-contained): a concrete run `verifyAlgoUnifiedFaithfulExt` accepts, by `decide`. It is at
CONCRETE arguments, not the `opaque` deployed ones — see §D of the header for what that does and does
not license. -/
theorem apexFacing_predicate_accepts_something :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat)
      (params : Dregg2.Circuit.FriVerifier.FriParams)
      (vk : Dregg2.Circuit.FriVerifier.RecursionVk Nat)
      (core : Dregg2.Circuit.FriVerifier.FriCore Nat)
      (A : Dregg2.Circuit.FriVerifier.FieldArith Nat)
      (extCore : Dregg2.Circuit.ExtFieldChallenge.ExtFriCore Nat)
      (extA : Dregg2.Circuit.ExtFieldChallenge.ExtFriArith Nat) (Wres : Nat)
      (initState : List Nat) (logN : Nat)
      (proof : Dregg2.Circuit.FriVerifier.BatchProofData Nat)
      (pub : Dregg2.Circuit.FriVerifier.WrapPublics Nat)
      (view : Dregg2.Circuit.ExtFieldChallenge.ExtVerifierView Nat),
      verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA Wres
        initState logN proof pub view = true :=
  Dregg2.Circuit.FriLdtExtractDeployed.deployed_accepting_pole_nonempty

#assert_axioms verifyBatch_accept_imp_faithfulExt
#assert_axioms starkSound_of_friLdtExtractFaithful_deployed
#assert_axioms starkSound_of_friLdtExtractCons_transferV3
#assert_axioms starkSound_of_friLdtExtract_transferV3_via_corrected
#assert_axioms landedPremise_imp_correctedPremise
#assert_axioms landedPremise_gives_starkSound_for_ANY_hash_and_registry
#assert_axioms verifyBatch_accept_gives_cons_shape
#assert_axioms verifyBatch_accept_refutes_singleton
#assert_axioms correctedPremise_iff_noOodShape
#assert_axioms starkSound_of_noOodShape_transferV3
#assert_axioms apexFacing_predicate_accepts_something

end Dregg2.Circuit.StarkSoundFriLdtCorrected
