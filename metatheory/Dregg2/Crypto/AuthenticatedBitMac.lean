/-
# Authenticated binary shares: SPDZ-style batch-check algebra

The runtime carries binary values but authenticates them in a large
characteristic-two field.  This file states the field-generic algebra.  A
global MAC key `alpha` is additively shared as `alpha_i`; a secret value `x_j`
is additively shared and its tag shares reconstruct to `alpha*x_j`.  When the
parties claim the public opening `y_j`, party `i` contributes

  `gamma_ij - alpha_i*y_j`.

Random field coefficients batch all opened values.  The theorem below proves
that the aggregate check is exactly

  `alpha * sum_j r_j * (x_j - y_j)`.

Thus honest openings accept.  A changed batch is rejected whenever both the
hidden global key and the random linear-combination difference are nonzero.
The cryptographic step—an adversary committing its check share before learning
an honest key/check share and hitting zero only with field-sized probability—is
an explicit protocol premise, not smuggled into this algebra theorem.
-/

import Mathlib
import Dregg2.Tactics

namespace Dregg2.Crypto.AuthenticatedBitMac

open scoped BigOperators

variable {F : Type} [Field F]

/-- One party's local check contribution for one opened value. -/
def localCheck (tagShare keyShare opened : F) : F :=
  tagShare - keyShare * opened

/-- The runtime order: each party batches its values, then the verifier sums
the committed party check shares. -/
def batchCheck {parties values : Nat}
    (coeff : Fin values → F)
    (keyShare : Fin parties → F)
    (tagShare : Fin parties → Fin values → F)
    (opened : Fin values → F) : F :=
  ∑ i, ∑ j, coeff j * localCheck (tagShare i j) (keyShare i) (opened j)

/-- One opened value: distributed checking exposes precisely the global MAC
key times the opening error. -/
theorem aggregate_single_check {parties : Nat}
    (alpha actual opened : F)
    (keyShare tagShare : Fin parties → F)
    (hkey : (∑ i, keyShare i) = alpha)
    (htag : (∑ i, tagShare i) = alpha * actual) :
    (∑ i, localCheck (tagShare i) (keyShare i) opened) =
      alpha * (actual - opened) := by
  simp only [localCheck, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hkey, htag]
  ring

/-- Load-bearing batch identity.  It is independent of how many parties or
values are present and matches the party-major runtime computation exactly. -/
theorem batch_check_identity {parties values : Nat}
    (alpha : F)
    (actual opened coeff : Fin values → F)
    (keyShare : Fin parties → F)
    (tagShare : Fin parties → Fin values → F)
    (hkey : (∑ i, keyShare i) = alpha)
    (htag : ∀ j, (∑ i, tagShare i j) = alpha * actual j) :
    batchCheck coeff keyShare tagShare opened =
      alpha * (∑ j, coeff j * (actual j - opened j)) := by
  unfold batchCheck
  calc
    (∑ i, ∑ j, coeff j * localCheck (tagShare i j) (keyShare i) (opened j)) =
        ∑ j, coeff j * (∑ i, localCheck (tagShare i j) (keyShare i) (opened j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ j, coeff j * (alpha * (actual j - opened j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [aggregate_single_check alpha (actual j) (opened j) keyShare (tagShare · j) hkey
        (htag j)]
    _ = alpha * (∑ j, coeff j * (actual j - opened j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Completeness of the batched MAC check. -/
theorem honest_batch_accepts {parties values : Nat}
    (alpha : F)
    (actual coeff : Fin values → F)
    (keyShare : Fin parties → F)
    (tagShare : Fin parties → Fin values → F)
    (hkey : (∑ i, keyShare i) = alpha)
    (htag : ∀ j, (∑ i, tagShare i j) = alpha * actual j) :
    batchCheck coeff keyShare tagShare actual = 0 := by
  rw [batch_check_identity alpha actual actual coeff keyShare tagShare hkey htag]
  simp

/-- Deterministic soundness core.  Probability enters only in establishing
that a post-commit random linear combination of a nonzero opening-error vector
is itself nonzero. -/
theorem changed_batch_rejected {parties values : Nat}
    (alpha : F)
    (actual opened coeff : Fin values → F)
    (keyShare : Fin parties → F)
    (tagShare : Fin parties → Fin values → F)
    (hkey : (∑ i, keyShare i) = alpha)
    (htag : ∀ j, (∑ i, tagShare i j) = alpha * actual j)
    (halpha : alpha ≠ 0)
    (hdiff : (∑ j, coeff j * (actual j - opened j)) ≠ 0) :
    batchCheck coeff keyShare tagShare opened ≠ 0 := by
  rw [batch_check_identity alpha actual opened coeff keyShare tagShare hkey htag]
  exact mul_ne_zero halpha hdiff

/-- If a nonzero-key check accepts, the random linear combination of all
opening errors must be zero.  This is the exact residual an adversary must hit. -/
theorem accepting_batch_forces_zero_combination {parties values : Nat}
    (alpha : F)
    (actual opened coeff : Fin values → F)
    (keyShare : Fin parties → F)
    (tagShare : Fin parties → Fin values → F)
    (hkey : (∑ i, keyShare i) = alpha)
    (htag : ∀ j, (∑ i, tagShare i j) = alpha * actual j)
    (halpha : alpha ≠ 0)
    (haccept : batchCheck coeff keyShare tagShare opened = 0) :
    (∑ j, coeff j * (actual j - opened j)) = 0 := by
  rw [batch_check_identity alpha actual opened coeff keyShare tagShare hkey htag] at haccept
  exact (mul_eq_zero.mp haccept).resolve_left halpha

#assert_axioms aggregate_single_check
#assert_axioms batch_check_identity
#assert_axioms honest_batch_accepts
#assert_axioms changed_batch_rejected
#assert_axioms accepting_batch_forces_zero_combination

end Dregg2.Crypto.AuthenticatedBitMac
