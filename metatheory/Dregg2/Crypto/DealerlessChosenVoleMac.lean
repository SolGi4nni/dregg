/-
# Dealerless chosen-input VOLE composition for authenticated shares

This file isolates the algebra needed to replace the test-only ideal OT in
`mpc_distributed_mac.rs` with a LogVOLE/C-VOLE-shaped adapter.  For every
ordered `(sender, receiver)` pair, the sender holds a mask `q` and the receiver
holds `t`, with the chosen-input relation

  `t - q = alpha_sender • x_receiver`.

The diagonal entry is a local synthetic correlation (`q = 0`,
`t = alpha_i • x_i`); only distinct-party entries require a network VOLE.
Summing every sender contribution `-q` and receiver contribution `t` covers
every term in

  `(sum_i alpha_i) • (sum_j x_j)`.

In characteristic two, `-q = q`, so this is exactly the runtime convention in
which both OT endpoints add their outputs.  The theorems are generic over a
commutative scalar ring and module, then specialized to a field for the
existing authenticated-opening equation.

No theorem here asserts chosen-input privacy, malicious VOLE security,
selective-failure resistance, correlation robustness, authenticated routing,
uniform sampling, liveness, or a post-quantum reduction.  A live adapter must
establish those cryptographic and transport premises separately.  The sole
adapter premise consumed by the algebra is the explicit per-pair relation
`Valid`; it is not manufactured by an axiom.
-/

import Mathlib
import Dregg2.Tactics
import Dregg2.Crypto.AuthenticatedBitMac

namespace Dregg2.Crypto.DealerlessChosenVoleMac

open scoped BigOperators

/-! ## Chosen-input VOLE relation over a commutative ring/module -/

/-- Endpoint-local outputs of one ordered chosen-input VOLE correlation. -/
structure ChosenVoleShare (M : Type*) where
  senderMask : M
  receiverMasked : M
  deriving DecidableEq, Repr

/-- Exact algebraic adapter contract.  Cryptographic security is deliberately
not part of this equality. -/
def Valid {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (alpha : R) (input : M) (c : ChosenVoleShare M) : Prop :=
  c.receiverMasked - c.senderMask = alpha • input

/-- The product share reconstructed from the two endpoint outputs. -/
def residual {M : Type*} [AddCommGroup M] (c : ChosenVoleShare M) : M :=
  c.receiverMasked - c.senderMask

theorem valid_residual {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {alpha : R} {input : M} {c : ChosenVoleShare M}
    (h : Valid alpha input c) : residual c = alpha • input := h

/-- GF(2^k) runtime form: subtraction is addition, hence the sender can add
`q` while the receiver adds `t`, exactly as the current chosen-message OT
substrate does. -/
theorem runtime_endpoint_add_eq_residual
    {F : Type*} [CommRing F] [CharP F 2] (c : ChosenVoleShare F) :
    c.senderMask + c.receiverMasked = residual c := by
  simp [residual, CharTwo.sub_eq_add, add_comm]

/-! ## Complete ordered-pair expansion -/

/-- Sum of every ordered sender/receiver cross term, diagonals included. -/
def completeCrossTermSum {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {parties : Nat} (alpha : Fin parties → R) (input : Fin parties → M) : M :=
  ∑ i, ∑ j, alpha i • input j

/-- The complete ordered-pair sum is exactly the product of reconstructed
global key and reconstructed input. -/
theorem completeCrossTermSum_eq_global
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {parties : Nat} (alpha : Fin parties → R) (input : Fin parties → M) :
    completeCrossTermSum alpha input = (∑ i, alpha i) • (∑ j, input j) := by
  unfold completeCrossTermSum
  calc
    (∑ i, ∑ j, alpha i • input j) = ∑ i, alpha i • (∑ j, input j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.smul_sum (s := Finset.univ) (f := input) (r := alpha i)).symm
    _ = (∑ i, alpha i) • (∑ j, input j) := by
      exact (Finset.sum_smul (s := Finset.univ) (f := alpha)
        (x := ∑ j, input j)).symm

/-! ## Party-local tag assembly -/

/-- One full ordered-pair matrix.  The diagonal is interpreted as a local
synthetic correlation; distinct indices are the actual C-VOLE calls. -/
abbrev CorrelationMatrix (parties : Nat) (M : Type*) :=
  Fin parties → Fin parties → ChosenVoleShare M

/-- Contribution of one matrix edge to one party.  The sender receives `-q`
and the receiver receives `t`; when sender = receiver both pieces land in the
same local diagonal tag. -/
def edgeContribution {M : Type*} [AddCommGroup M] {parties : Nat}
    (corr : CorrelationMatrix parties M) (party : Fin parties)
    (edge : Fin parties × Fin parties) : M :=
  (if party = edge.1 then -(corr edge.1 edge.2).senderMask else 0) +
  (if party = edge.2 then (corr edge.1 edge.2).receiverMasked else 0)

/-- Canonical local MAC-tag share assembled from every incident VOLE edge. -/
def localTagShare {M : Type*} [AddCommGroup M] {parties : Nat}
    (corr : CorrelationMatrix parties M) (party : Fin parties) : M :=
  ∑ edge : Fin parties × Fin parties, edgeContribution corr party edge

theorem sum_edgeContribution {M : Type*} [AddCommGroup M] {parties : Nat}
    (corr : CorrelationMatrix parties M) (edge : Fin parties × Fin parties) :
    (∑ party, edgeContribution corr party edge) = residual (corr edge.1 edge.2) := by
  classical
  simp [edgeContribution, residual, Finset.sum_add_distrib, sub_eq_add_neg, add_comm]

/-- All endpoint-local tag shares cancel masks and expose exactly the sum of
the per-pair VOLE residuals. -/
theorem sum_localTagShare_eq_residuals
    {M : Type*} [AddCommGroup M] {parties : Nat}
    (corr : CorrelationMatrix parties M) :
    (∑ party, localTagShare corr party) =
      ∑ edge : Fin parties × Fin parties, residual (corr edge.1 edge.2) := by
  unfold localTagShare
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  exact sum_edgeContribution corr edge

/-- An exact relation for every ordered pair turns the residual fold into the
complete key/input cross-product expansion. -/
theorem valid_residuals_eq_completeCrossTermSum
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {parties : Nat} (alpha : Fin parties → R) (input : Fin parties → M)
    (corr : CorrelationMatrix parties M)
    (hvalid : ∀ i j, Valid (alpha i) (input j) (corr i j)) :
    (∑ edge : Fin parties × Fin parties, residual (corr edge.1 edge.2)) =
      completeCrossTermSum alpha input := by
  rw [Fintype.sum_prod_type]
  unfold completeCrossTermSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact valid_residual (hvalid i j)

/-- Complete pairwise chosen-input VOLE correlations therefore authenticate
the reconstructed global input under the reconstructed global key. -/
theorem all_local_tags_authenticate_global
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {parties : Nat} (alpha : Fin parties → R) (input : Fin parties → M)
    (corr : CorrelationMatrix parties M)
    (hvalid : ∀ i j, Valid (alpha i) (input j) (corr i j)) :
    (∑ party, localTagShare corr party) =
      (∑ i, alpha i) • (∑ j, input j) := by
  rw [sum_localTagShare_eq_residuals corr,
    valid_residuals_eq_completeCrossTermSum alpha input corr hvalid,
    completeCrossTermSum_eq_global]

/-! ## Exact interface to the existing authenticated opening equation -/

open Dregg2.Crypto.AuthenticatedBitMac

/-- Per-value pairwise VOLE formation composes directly into the existing
party-major batched MAC check.  This theorem supplies that module's `htag`
premise from the explicit VOLE relation rather than assuming a trusted tag
dealer. -/
theorem chosenVole_batch_check_identity
    {F : Type} [Field F] {parties values : Nat}
    (keyShare : Fin parties → F)
    (inputShare : Fin parties → Fin values → F)
    (corr : Fin values → CorrelationMatrix parties F)
    (opened coeff : Fin values → F)
    (hvalid : ∀ value sender receiver,
      Valid (keyShare sender) (inputShare receiver value)
        (corr value sender receiver)) :
    batchCheck coeff keyShare
        (fun party value => localTagShare (corr value) party) opened =
      (∑ party, keyShare party) *
        (∑ value, coeff value * ((∑ party, inputShare party value) - opened value)) := by
  have htag : ∀ value,
      (∑ party, localTagShare (corr value) party) =
        (∑ party, keyShare party) * (∑ party, inputShare party value) := by
    intro value
    simpa [smul_eq_mul] using
      (all_local_tags_authenticate_global keyShare (fun party => inputShare party value)
        (corr value) (hvalid value))
  exact batch_check_identity
    (∑ party, keyShare party)
    (fun value => ∑ party, inputShare party value)
    opened coeff keyShare
    (fun party value => localTagShare (corr value) party)
    rfl htag

/-! ## Executable omission and diagonal-only teeth -/

namespace Demo

abbrev F := ZMod 2

def alphaOmit : Fin 2 → F := ![1, 0]
def inputOmit : Fin 2 → F := ![0, 1]

/-- Canonical zero-mask correlation matrix. -/
def fullOmitCorrelation (i j : Fin 2) : ChosenVoleShare F :=
  ⟨0, alphaOmit i * inputOmit j⟩

/-- Drop precisely the only nonzero cross term `(sender=0, receiver=1)`. -/
def omitted01Correlation (i j : Fin 2) : ChosenVoleShare F :=
  if i = 0 ∧ j = 1 then ⟨0, 0⟩ else fullOmitCorrelation i j

theorem fullOmitCorrelation_valid (i j : Fin 2) :
    Valid (alphaOmit i) (inputOmit j) (fullOmitCorrelation i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [Valid, fullOmitCorrelation, alphaOmit, inputOmit]

/-- Omitting one load-bearing ordered pair breaks the global MAC product. -/
theorem omitted_pair_can_break_global_authentication :
    (∑ party, localTagShare omitted01Correlation party) ≠
      (∑ i, alphaOmit i) * (∑ j, inputOmit j) := by
  decide

def alphaDiagonal : Fin 2 → F := ![1, 1]
def inputDiagonal : Fin 2 → F := ![1, 0]

/-- Keep only local `alpha_i*x_i` diagonals and erase every cross-party edge. -/
def diagonalOnlyCorrelation (i j : Fin 2) : ChosenVoleShare F :=
  if i = j then ⟨0, alphaDiagonal i * inputDiagonal j⟩ else ⟨0, 0⟩

/-- Diagonal-only tags need not authenticate the reconstructed key/input pair. -/
theorem diagonal_only_can_break_global_authentication :
    (∑ party, localTagShare diagonalOnlyCorrelation party) ≠
      (∑ i, alphaDiagonal i) * (∑ j, inputDiagonal j) := by
  decide

#guard (∑ party, localTagShare omitted01Correlation party) !=
  (∑ i, alphaOmit i) * (∑ j, inputOmit j)
#guard (∑ party, localTagShare diagonalOnlyCorrelation party) !=
  (∑ i, alphaDiagonal i) * (∑ j, inputDiagonal j)

end Demo

#assert_axioms runtime_endpoint_add_eq_residual
#assert_axioms completeCrossTermSum_eq_global
#assert_axioms sum_localTagShare_eq_residuals
#assert_axioms valid_residuals_eq_completeCrossTermSum
#assert_axioms all_local_tags_authenticate_global
#assert_axioms chosenVole_batch_check_identity
#assert_axioms Demo.fullOmitCorrelation_valid
#assert_axioms Demo.omitted_pair_can_break_global_authentication
#assert_axioms Demo.diagonal_only_can_break_global_authentication

end Dregg2.Crypto.DealerlessChosenVoleMac
