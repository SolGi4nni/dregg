/-
# Honest size limits of finite-field polynomial-function models

`FinitePolynomialFunctions` proves the positive result: over a finite field,
every map between finite field powers is represented by polynomials, and the
table object supplies an exponential.  This file records the matching limits.

The limits concern *extensional* polynomial functions.  There are infinitely
many polynomial expressions, but after quotienting by agreement on the finite
field there are only finitely many maps.  Consequently, a faithful encoding of
a hom-set into a fixed `F^n -> F^m` function space has an exact cardinal bound;
in particular, it cannot encode an infinite hom-set.  The table exponential is
exact, but its coordinate dimension grows exponentially.
-/
import Dregg2.Metatheory.FinitePolynomialFunctions

namespace Dregg2.Metatheory.FinitePolynomialFunctionLimits

open Dregg2.Metatheory.FinitePolynomialFunctions

variable {F : Type*} [Field F] [Fintype F]
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

/-- Extensional polynomial maps from `F^σ` to `F^τ`.

By finite-field interpolation this is exactly the image of vectors of formal
polynomials under evaluation, but using the function type makes extensional
equality explicit and avoids counting syntactically different representatives.
-/
abbrev ExtensionalMap (σ τ F : Type*) := (σ → F) → (τ → F)

/-- There are exactly `q^(m * q^n)` extensional maps `F^n -> F^m`.

This is also the exact number of extensional vector-polynomial denotations,
because `vector_polynomial_representation_surjective` proves that every such
map has a polynomial representative.
-/
theorem card_extensionalMap :
    Nat.card (ExtensionalMap σ τ F) =
      Nat.card F ^ (Nat.card τ * Nat.card F ^ Nat.card σ) := by
  rw [show Nat.card (ExtensionalMap σ τ F) =
      (Nat.card F ^ Nat.card τ) ^ (Nat.card F ^ Nat.card σ) by
    simp only [ExtensionalMap, Nat.card_fun]]
  exact (Nat.pow_mul _ _ _).symm

/-- The coordinate dimension of the table exponential is
`m * q^n`: one output coordinate for every input point and output coordinate.
-/
theorem card_expCoord :
    Nat.card (ExpCoord σ τ F) =
      Nat.card τ * Nat.card F ^ Nat.card σ := by
  simp only [ExpCoord, Nat.card_prod, Nat.card_fun]
  exact Nat.mul_comm _ _

/-- The point set of the table exponential has exactly as many elements as the
function space it represents.  Thus the table construction is exact, while
making the exponential coordinate blowup visible rather than hiding it.
-/
theorem card_tableObject :
    Nat.card (ExpCoord σ τ F → F) =
      Nat.card F ^ (Nat.card τ * Nat.card F ^ Nat.card σ) := by
  rw [Nat.card_fun, card_expCoord]

/-- Any faithful encoding of a finite hom-set into maps `F^n -> F^m` obeys the
same exact upper bound. -/
theorem finite_hom_bound {H : Type*} [Finite H]
    (encode : H → ExtensionalMap σ τ F) (hinj : Function.Injective encode) :
    Nat.card H ≤ Nat.card F ^ (Nat.card τ * Nat.card F ^ Nat.card σ) := by
  calc
    Nat.card H ≤ Nat.card (ExtensionalMap σ τ F) :=
      Nat.card_le_card_of_injective encode hinj
    _ = Nat.card F ^ (Nat.card τ * Nat.card F ^ Nat.card σ) :=
      card_extensionalMap

/-- An infinite hom-set cannot inject into a fixed finite-field function
space.  This is the precise cardinality obstruction behind the statement that
one fixed finite polynomial model cannot faithfully represent an arbitrary
cartesian closed category. -/
theorem no_injective_infinite_hom {H : Type*} [Infinite H]
    (encode : H → ExtensionalMap σ τ F) :
    ¬ Function.Injective encode := by
  intro hinj
  letI : Finite H := Finite.of_injective encode hinj
  exact not_finite H

/-- A concrete cartesian-closed counterexample: in `Type` (and hence in the
usual set model), the exponential `Bool^Nat` is already an infinite hom-set.
It cannot be faithfully represented inside any one fixed `F^n -> F^m`
polynomial-function space over a finite field. -/
theorem no_injective_nat_predicates
    (encode : (ℕ → Bool) → ExtensionalMap σ τ F) :
    ¬ Function.Injective encode :=
  no_injective_infinite_hom encode

/-- Data for a faithful, extensional encoding of a chosen hom-set into a fixed
finite-field polynomial-function space. -/
structure FaithfulEncoding (H σ τ F : Type*) where
  encode : H → ExtensionalMap σ τ F
  injective : Function.Injective encode

namespace FaithfulEncoding

variable {H : Type*}

/-- Equality of encoded polynomial functions reflects equality in the source
hom-set. -/
theorem encode_eq_iff (E : FaithfulEncoding H σ τ F) (f g : H) :
    E.encode f = E.encode g ↔ f = g :=
  E.injective.eq_iff

/-- If field equality is decidable, a faithful finite-field encoding gives a
concrete decision procedure for equality in the represented hom-set: enumerate
the finite input space and compare the output tables. -/
def reflectedDecidableEq [DecidableEq σ] [DecidableEq τ] [DecidableEq F]
    (E : FaithfulEncoding H σ τ F) : DecidableEq H :=
  fun f g => decidable_of_iff (E.encode f = E.encode g) (encode_eq_iff E f g)

/-- Every faithfully encoded hom-set is finite, even when no `Fintype` instance
for the source was supplied in advance. -/
theorem finite (E : FaithfulEncoding H σ τ F) : Finite H :=
  Finite.of_injective E.encode E.injective

/-- Hence an infinite hom-set admits no faithful encoding of this fixed shape. -/
theorem not_nonempty_of_infinite [Infinite H] :
    ¬ Nonempty (FaithfulEncoding H σ τ F) := by
  rintro ⟨E⟩
  exact no_injective_infinite_hom E.encode E.injective

end FaithfulEncoding

#assert_all_clean [card_extensionalMap, card_expCoord, card_tableObject,
  finite_hom_bound, no_injective_infinite_hom, no_injective_nat_predicates,
  FaithfulEncoding.encode_eq_iff, FaithfulEncoding.finite,
  FaithfulEncoding.not_nonempty_of_infinite]

end Dregg2.Metatheory.FinitePolynomialFunctionLimits
