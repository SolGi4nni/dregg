/-
# `Dregg2.Circuit.CollaborativeTensorCode` — a Dregg-native tensor-code foundation.

This file is a deliberately small, proof-complete model of the algebra needed by a
share-native distributed PCS.  It is inspired by collaborative tensor-code proving,
but the definitions and proofs here are ours:

* `encode` is a finite linear code given by a generator matrix;
* `tensorEncode` applies two such codes on independent axes;
* `tensor_encode_order_independent` proves the two encodings commute;
* `fold_tensorEncode` proves that a linear fold of encoded rows is exactly the
  remaining-axis encoding of the induced message fold;
* `below_threshold_support_privacy` proves a finite-observation privacy statement:
  any fewer-than-threshold collection of complete encoded rows is consistent with
  every candidate secret vector;
* `threshold_rows_pin_secret` proves the matching boundary: `t` raw rows pin every
  degree-`< t` secret component.

The privacy theorem is intentionally an **information-theoretic support statement**.
It says the same finite view has witnesses for both secrets.  It does not yet claim a
uniform sharing distribution, malicious-prover security, query privacy, or a Fiat–Shamir
compiler.  Those require explicit protocol/adversary distributions above this algebra.
-/
import Dregg2.Circuit.LowDegreeUniqueness
import Dregg2.Crypto.ShamirPrivacy
import Mathlib.Data.Fin.VecNotation

namespace Dregg2.Circuit.CollaborativeTensorCode

open Polynomial
open scoped BigOperators

/-! ## §1 — Finite linear and tensor encodings. -/

section TensorAlgebra

variable {F K L I J : Type*} [CommRing F]
variable [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- A finite linear code described by its generator matrix `G : I → K → F`.
`K` indexes message symbols and `I` indexes codeword symbols. -/
def encode (G : I → K → F) (message : K → F) : I → F :=
  fun i => ∑ k, G i k * message k

/-- Encode the left axis of a message tensor. -/
def encodeRows (G : I → K → F) (message : K → L → F) : I → L → F :=
  fun i l => encode G (fun k => message k l) i

/-- Encode the right axis of a message tensor. -/
def encodeCols (H : J → L → F) (message : K → L → F) : K → J → F :=
  fun k j => encode H (message k) j

/-- The separable tensor code `G ⊗ H`, written as left encoding after right encoding. -/
def tensorEncode (G : I → K → F) (H : J → L → F)
    (message : K → L → F) : I → J → F :=
  encodeRows G (encodeCols H message)

omit [DecidableEq K] [DecidableEq L] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] in
/-- **Tensor encodings commute.** Applying `H` then `G` gives exactly the same
codeword as applying `G` then `H`.  This is the finite Fubini/bilinearity law that
lets workers encode either axis independently. -/
theorem tensor_encode_order_independent (G : I → K → F) (H : J → L → F)
    (message : K → L → F) :
    tensorEncode G H message = encodeCols H (encodeRows G message) := by
  funext i j
  simp only [tensorEncode, encodeRows, encodeCols, encode]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Fold one tensor axis by a finite linear functional `weight`. -/
def foldRows (weight : K → F) (message : K → L → F) : L → F :=
  fun l => ∑ k, weight k * message k l

omit [DecidableEq K] [DecidableEq L] [Fintype J] [DecidableEq J] in
/-- Folding the left axis commutes with encoding the independent right axis. -/
theorem foldRows_encodeCols (weight : K → F) (H : J → L → F)
    (message : K → L → F) :
    foldRows weight (encodeCols H message) = encode H (foldRows weight message) := by
  funext j
  simp only [foldRows, encodeCols, encode]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A codeword-row fold induces this linear functional on the message-row axis. -/
def inducedMessageWeight (weight : I → F) (G : I → K → F) : K → F :=
  fun k => ∑ i, weight i * G i k

omit [DecidableEq K] [Fintype L] [DecidableEq L] [DecidableEq I] in
/-- Folding an encoded left axis is the induced fold of the underlying message axis. -/
theorem foldRows_encodeRows (weight : I → F) (G : I → K → F)
    (message : K → L → F) :
    foldRows weight (encodeRows G message) =
      foldRows (inducedMessageWeight weight G) message := by
  funext l
  simp only [foldRows, encodeRows, encode, inducedMessageWeight]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Fold the first axis of an encoded tensor. -/
def foldEncodedRows (weight : I → F) (word : I → J → F) : J → F :=
  fun j => ∑ i, weight i * word i j

omit [DecidableEq K] [DecidableEq L] [DecidableEq I]
  [Fintype J] [DecidableEq J] in
/-- **Encode/fold commutation.** A linear fold of the fully encoded tensor is exactly
the right-axis encoding of the message tensor folded by the induced functional.

No code-distance or cryptographic assumption enters: this is an equality in every
commutative ring.  A concrete FRI/collaborative-PCS backend only needs to prove that
its transcript-derived codeword weights induce the intended message weights. -/
theorem fold_tensorEncode (weight : I → F) (G : I → K → F) (H : J → L → F)
    (message : K → L → F) :
    foldEncodedRows weight (tensorEncode G H message) =
      encode H (foldRows (inducedMessageWeight weight G) message) := by
  change foldRows weight (tensorEncode G H message) = _
  rw [tensor_encode_order_independent, foldRows_encodeCols, foldRows_encodeRows]

omit [DecidableEq K] [DecidableEq L] [DecidableEq I]
  [Fintype J] [DecidableEq J] in
/-- User-facing form: if the codeword weights induce a requested message fold `rho`,
then folding the codeword commutes with the remaining tensor encoding at exactly `rho`. -/
theorem fold_tensorEncode_of_induces (weight : I → F) (rho : K → F)
    (G : I → K → F) (H : J → L → F) (message : K → L → F)
    (hweight : inducedMessageWeight weight G = rho) :
    foldEncodedRows weight (tensorEncode G H message) =
      encode H (foldRows rho message) := by
  rw [fold_tensorEncode, hweight]

end TensorAlgebra

/-! ## §2 — Finite observed-row privacy for a Shamir × linear tensor code. -/

section FiniteObservationPrivacy

variable {F K J : Type*} [Field F] [DecidableEq F]
variable [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]

/-- Evaluate one sharing polynomial per secret component at a party point. -/
def evalSharingRow (sharing : K → F[X]) (point : F) : K → F :=
  fun k => (sharing k).eval point

/-- The observable row after applying the public right-axis code. -/
def encodedSharingRow (H : J → K → F) (sharing : K → F[X]) (point : F) : J → F :=
  encode H (evalSharingRow sharing point)

/-- A polynomial family fits a finite raw observation and a candidate secret vector. -/
def FitsObservedRows (t : ℕ) (T : Finset F) (shares : F → K → F)
    (secret : K → F) (sharing : K → F[X]) : Prop :=
  (∀ k, (sharing k).degree < (t : ℕ)) ∧
  (∀ k, (sharing k).eval 0 = secret k) ∧
  (∀ point ∈ T, evalSharingRow sharing point = shares point)

omit [Fintype K] [DecidableEq K] in
/-- Every candidate secret vector admits componentwise degree-`< t` sharings matching
the same strictly-fewer-than-`t` observed raw rows.  Internally we interpolate at
`T.card + 1` nodes (the observed points plus `0`) and weaken the degree bound to `t`. -/
theorem exists_sharing_fitting_observed_rows (t : ℕ)
    (T : Finset F) (hcard : T.card < t) (h0 : (0 : F) ∉ T)
    (shares : F → K → F) (secret : K → F) :
    ∃ sharing : K → F[X], FitsObservedRows t T shares secret sharing := by
  classical
  have hcomponent : ∀ k : K, ∃ p : F[X],
      p.degree < (t : ℕ) ∧ p.eval 0 = secret k ∧
        ∀ point ∈ T, p.eval point = shares point k := by
    intro k
    obtain ⟨p, hdeg, hsecret, hshares⟩ :=
      Dregg2.Crypto.ShamirPrivacy.shamir_t_privacy
        (T.card + 1) (by omega) T (by omega) h0
        (fun point => shares point k) (secret k)
    refine ⟨p, ?_, hsecret, hshares⟩
    exact hdeg.trans_le (by exact_mod_cast (Nat.succ_le_iff.mpr hcard))
  choose sharing hsharing using hcomponent
  refine ⟨sharing, ?_, ?_, ?_⟩
  · exact fun k => (hsharing k).1
  · exact fun k => (hsharing k).2.1
  · intro point hpoint
    funext k
    exact (hsharing k).2.2 point hpoint

omit [DecidableEq K] [Fintype J] [DecidableEq J] in
/-- **Finite-observation support privacy.** For arbitrary candidate secret vectors
`secret0` and `secret1`, the same set of fewer than `t` observed complete rows is
consistent with both.  Consequently the corresponding publicly encoded rows are
byte-for-byte equal.

This is the exact unconditional privacy fact available at this layer: the finite view's
support does not determine the secret.  Probability-distribution equality is deliberately
not claimed until a randomized sharing protocol is modeled. -/
theorem below_threshold_support_privacy (t : ℕ)
    (T : Finset F) (hcard : T.card < t) (h0 : (0 : F) ∉ T)
    (shares : F → K → F) (secret0 secret1 : K → F) (H : J → K → F) :
    ∃ sharing0 sharing1 : K → F[X],
      FitsObservedRows t T shares secret0 sharing0 ∧
      FitsObservedRows t T shares secret1 sharing1 ∧
      (∀ point ∈ T,
        evalSharingRow sharing0 point = evalSharingRow sharing1 point ∧
        encodedSharingRow H sharing0 point = encodedSharingRow H sharing1 point) := by
  obtain ⟨sharing0, hfit0⟩ :=
    exists_sharing_fitting_observed_rows t T hcard h0 shares secret0
  obtain ⟨sharing1, hfit1⟩ :=
    exists_sharing_fitting_observed_rows t T hcard h0 shares secret1
  refine ⟨sharing0, sharing1, hfit0, hfit1, ?_⟩
  intro point hpoint
  have hraw : evalSharingRow sharing0 point = evalSharingRow sharing1 point :=
    (hfit0.2.2 point hpoint).trans (hfit1.2.2 point hpoint).symm
  exact ⟨hraw, congrArg (encode H) hraw⟩

omit [DecidableEq F] [Fintype K] [DecidableEq K] in
/-- **The threshold boundary bites.** If two componentwise degree-`< t` sharing families
agree on at least `t` distinct raw rows, then their secret vectors (evaluation at `0`) are
equal.  The below-threshold theorem above is therefore sharp at the level of polynomial
interpolation: every collection of `< t` rows admits every secret, while `t` rows pin it. -/
theorem threshold_rows_pin_secret (t : ℕ) (T : Finset F) (hcard : t ≤ T.card)
    (sharing0 sharing1 : K → F[X])
    (hdeg0 : ∀ k, (sharing0 k).natDegree < t)
    (hdeg1 : ∀ k, (sharing1 k).natDegree < t)
    (hagree : ∀ point ∈ T,
      evalSharingRow sharing0 point = evalSharingRow sharing1 point) :
    (fun k => (sharing0 k).eval 0) = fun k => (sharing1 k).eval 0 := by
  funext k
  have hpoly : sharing0 k = sharing1 k :=
    Dregg2.Circuit.LowDegreeUniqueness.lowDegree_agree_forces_eq
      (sharing0 k) (sharing1 k) T (hdeg0 k) (hdeg1 k) hcard
      (fun point hpoint => congrFun (hagree point hpoint) k)
  rw [hpoly]

end FiniteObservationPrivacy

/-! ## §3 — Concrete teeth over `ZMod 5`. -/

section Teeth

abbrev F5 := ZMod 5

def secret0 : Fin 2 → F5 := ![1, 2]
def secret1 : Fin 2 → F5 := ![3, 4]
def oneObservedRow : F5 → Fin 2 → F5 := fun _ => ![0, 1]
def identityGenerator2 : Fin 2 → Fin 2 → F5 := fun i k => if i = k then 1 else 0

/-- The two candidate secrets in the privacy tooth are genuinely distinct. -/
theorem secret0_ne_secret1 : secret0 ≠ secret1 := by decide

/-- **FIRE.** At threshold `2`, the one observed row `{1}` is consistent with the two
distinct secret vectors above, and their publicly encoded observations are identical. -/
theorem below_threshold_privacy_fires :
    ∃ sharing0 sharing1 : Fin 2 → F5[X],
      FitsObservedRows 2 ({1} : Finset F5) oneObservedRow secret0 sharing0 ∧
      FitsObservedRows 2 ({1} : Finset F5) oneObservedRow secret1 sharing1 ∧
      (∀ point ∈ ({1} : Finset F5),
        evalSharingRow sharing0 point = evalSharingRow sharing1 point ∧
        encodedSharingRow identityGenerator2 sharing0 point =
          encodedSharingRow identityGenerator2 sharing1 point) := by
  exact below_threshold_support_privacy 2 ({1} : Finset F5)
    (by decide) (by decide) oneObservedRow secret0 secret1 identityGenerator2

/-- A nontrivial 2×2 tensor/codeword used to execute the encode/fold law. -/
def message2 : Fin 2 → Fin 2 → F5 := fun i j =>
  ![![1, 2], ![3, 4]] i j

def mixGenerator2 : Fin 2 → Fin 2 → F5 := fun i k =>
  ![![1, 1], ![1, 2]] i k

def foldWeight2 : Fin 2 → F5 := ![2, 3]

/-- **FIRE.** The generic encode/fold theorem evaluates on a genuinely mixed tensor code,
not only the identity matrix. -/
theorem fold_tensorEncode_fires :
    foldEncodedRows foldWeight2 (tensorEncode mixGenerator2 mixGenerator2 message2) =
      encode mixGenerator2
        (foldRows (inducedMessageWeight foldWeight2 mixGenerator2) message2) :=
  fold_tensorEncode foldWeight2 mixGenerator2 mixGenerator2 message2

#assert_axioms tensor_encode_order_independent
#assert_axioms foldRows_encodeCols
#assert_axioms foldRows_encodeRows
#assert_axioms fold_tensorEncode
#assert_axioms fold_tensorEncode_of_induces
#assert_axioms exists_sharing_fitting_observed_rows
#assert_axioms below_threshold_support_privacy
#assert_axioms threshold_rows_pin_secret
#assert_axioms secret0_ne_secret1
#assert_axioms below_threshold_privacy_fires
#assert_axioms fold_tensorEncode_fires

end Teeth

end Dregg2.Circuit.CollaborativeTensorCode
