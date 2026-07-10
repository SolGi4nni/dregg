/-
# Dregg2.Circuit.DeployedRefinesProof — DEBT-A obligation #5: the deployment-refinement half.

**The honest scope, first sentence.** `verifyBatch` is `opaque`
(`CircuitSoundness.lean:353` — `opaque verifyBatch : VerifyKey → BatchPublicInputs →
BatchProof → Verdict`, NO body), therefore `FriVerifierBridge.DeployedRefines` (`:92`,
`verifyBatch (vkOfRegistry R) pi π = accept → verifyAlgo … = true`) is
**UNPROVABLE-AS-STATED**: from an uninterpreted `verifyBatch … = accept` nothing can be
derived, because `verifyBatch` has no computational content to case on. This file does the
strongest honest thing that is NOT laundering: it MODELS the deployed p3 batch verifier
faithfully — as running the SPECIFIED `verifyAlgo` (the FRI fold-chain + Merkle recompute
+ batch-table quotient + PoW checks, `FriVerifier.verifyAlgo`) conjoined with any
deployment-specific `extra` validation — proves the refinement for that model
(`deployedRefines_model`), proves the both-truth teeth (a tampered quotient the model
REJECTS and the algorithm also rejects; a model acceptance that FORCES algorithm
acceptance), and states the residual gap PRECISELY as a reduction lemma
(`deployedRefines_of_matchesModel`): the committed `DeployedRefines` follows exactly from
`DeployedMatchesModel` — "the opaque Rust `verify_batch` computes the model verdict". That
byte-level Rust↔Lean correspondence is the one thing no Lean object here can provide while
`verifyBatch` stays opaque; it is named, not faked. No new `…Sound` carrier, no assumed
hypothesis standing in for the refinement, no `sorry`.

**Why the model is faithful, not a stub.** The deployed p3 `verify_batch` IS, by
construction, the algorithm the batch-STARK verifier runs: the same Fiat-Shamir transcript
(`deriveFri`/`deriveQueryIndices`), the same per-query fold/Merkle checks, the same OOD
quotient identity `C(ζ)=Z_H(ζ)·q(ζ)`, the same grinding PoW — all specified in
`FriVerifier.verifyAlgo` with PROVEN reject-teeth. Modelling the deployed verdict as
`verifyAlgo && extra` (deployment MAY check MORE, never less) is the honest superset
refinement: acceptance of the deployed model forces `verifyAlgo` acceptance because the
model CONJOINS the algorithm's checks. That is exactly the shape `DeployedRefines`
requires, and it is where the two accept-conditions can only DIVERGE in the safe
direction (deployed stricter), never the unsafe one.

`#assert_axioms` stays `⊆ {propext, Classical.choice, Quot.sound}`: the model is a plain
`def`, the refinement a `theorem`, the gap a named `Prop`; no `axiom`, no carrier class.
-/
import Dregg2.Circuit.FriVerifierBridge
import Dregg2.Tactics

namespace Dregg2.Circuit.DeployedRefinesProof

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.FriVerifierBridge

/-- **The faithful model of the deployed p3 batch verifier.**

The deployed Rust `verify_batch`, modelled: it ACCEPTS exactly when the SPECIFIED
`verifyAlgo` accepts the mapped proof data (the FRI fold-chain + Merkle recompute +
batch-table quotient identity + grinding PoW — all of `FriVerifier.verifyAlgo`) AND any
deployment-specific `extra` validation passes. The `&&` is the honest superset direction:
the deployment MAY perform additional checks (version pins, param bindings), never fewer.
The `VerifyKey` argument is present to match `verifyBatch`'s type; the algorithm's own
`vk : RecursionVk` (the shape pin, checked inside `verifyAlgo`) carries the key content. -/
def verifyBatchModel
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (extra : BatchProofData Int → WrapPublics Int → Bool) :
    VerifyKey → BatchPublicInputs → BatchProof → Verdict :=
  fun _vk pi π =>
    if (verifyAlgo perm RATE toNat params vk checks initState logN
          (view pi π).1 (view pi π).2
        && extra (view pi π).1 (view pi π).2) = true
    then Verdict.accept else Verdict.reject

/-- **The refinement, PROVED for the model (the acceptance tooth).** Model acceptance
FORCES algorithm acceptance — because the model verdict conjoins `verifyAlgo` with `extra`,
an `accept` can only occur when `verifyAlgo` itself returned `true`. This is the
deployment-refinement half `DeployedRefines` asks for, discharged for the faithful model
instead of the opaque `verifyBatch`. -/
theorem deployedRefines_model
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (extra : BatchProofData Int → WrapPublics Int → Bool)
    (vk0 : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof)
    (h : verifyBatchModel perm RATE toNat params vk checks initState logN view extra
          vk0 pi π = Verdict.accept) :
    verifyAlgo perm RATE toNat params vk checks initState logN
      (view pi π).1 (view pi π).2 = true := by
  unfold verifyBatchModel at h
  by_cases hcond :
      (verifyAlgo perm RATE toNat params vk checks initState logN
          (view pi π).1 (view pi π).2
        && extra (view pi π).1 (view pi π).2) = true
  · exact ((Bool.and_eq_true _ _).mp hcond).1
  · rw [if_neg hcond] at h
    exact absurd h (by decide)

/-- **The both-truth REJECTION tooth.** A batch whose mapped proof carries a tampered
quotient on some opened table (`C(ζ) ≠ Z_H(ζ)·q(ζ)`) is REJECTED by the deployed MODEL —
proved from the algorithm's proven tooth (`verifyAlgo_full_rejects_tampered_quotient`), no
appeal to the FRI floor. The refinement fires on a rejection: the algorithm rejects, so the
model rejects. Uses the FULL checks (`fullChecks` = FRI core + concrete batch-table +
PoW). -/
theorem model_rejects_tampered_quotient
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (core : FriCore Int) (A : FieldArith Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (extra : BatchProofData Int → WrapPublics Int → Bool)
    (vk0 : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof)
    (ood : Int) (hood : (view pi π).1.oodPoint = [ood])
    (t : TableOpening Int) (hmem : t ∈ (view pi π).1.tableOpenings)
    (htamper : t.constraintEval ≠ A.mul t.vanishingAtZeta t.quotientAtZeta) :
    verifyBatchModel perm RATE toNat params vk (fullChecks core A toNat params.powBits)
      initState logN view extra vk0 pi π = Verdict.reject := by
  have hrej := verifyAlgo_full_rejects_tampered_quotient
      perm RATE toNat params vk core A initState logN (view pi π).1 (view pi π).2
      ood hood t hmem htamper
  unfold verifyBatchModel
  rw [hrej, Bool.false_and, if_neg (by decide)]

/-- **The precise residual gap, as a named `Prop`.** The one thing that must hold for the
COMMITTED `DeployedRefines` to follow: the opaque deployed `verifyBatch` computes exactly
the model verdict. This is the byte-level Rust↔Lean-spec correspondence — the analogue of
`FriVerifier.GnarkRefines` for the deployed verifier — that cannot be discharged in Lean
while `verifyBatch` stays `opaque`. Named, not assumed as a soundness carrier. -/
def DeployedMatchesModel (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (extra : BatchProofData Int → WrapPublics Int → Bool) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyBatch (vkOfRegistry R) pi π
      = verifyBatchModel perm RATE toNat params vk checks initState logN view extra
          (vkOfRegistry R) pi π

/-- **The reduction: `DeployedRefines` ⟸ `DeployedMatchesModel`.** The committed
deployment-refinement obligation follows EXACTLY from the residual gap plus the proved
model refinement. This does NOT prove `DeployedRefines` unconditionally (impossible while
`verifyBatch` is opaque); it proves the obligation reduces to the single named
byte-correspondence `DeployedMatchesModel`, isolating precisely what remains. -/
theorem deployedRefines_of_matchesModel
    (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (extra : BatchProofData Int → WrapPublics Int → Bool)
    (hmatch : DeployedMatchesModel R perm RATE toNat params vk checks initState logN
                view extra) :
    DeployedRefines R perm RATE toNat params vk checks initState logN view := by
  intro pi π hacc
  rw [hmatch pi π] at hacc
  exact deployedRefines_model perm RATE toNat params vk checks initState logN view extra
    (vkOfRegistry R) pi π hacc

#assert_all_clean [deployedRefines_model, model_rejects_tampered_quotient,
  deployedRefines_of_matchesModel]

end Dregg2.Circuit.DeployedRefinesProof
