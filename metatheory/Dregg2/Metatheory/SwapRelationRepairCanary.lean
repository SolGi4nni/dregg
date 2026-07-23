/-
# Dregg2.Metatheory.SwapRelationRepairCanary

The armed regression for the published-swap forgery, plus its repair.

`Dregg2.Metatheory.FOLArithmetizationCounterexamples` proves that the swap
relation printed in the public ModulusZK/BitLogic PDF (§4.1, p. 6; transcription
pinned at `tools/direct-logic-bench/README.md:56-60`) accepts a
transaction-shaped witness that violates both the quoted-output factor and the
constant-product factor, and that the bypass is a *polynomial identity* rather
than a lucky evaluation point.  That file exhibits the attack and stops.  This
file states the repair, proves the repaired relation rejects the exact forged
witness, and arms both facts as executable teeth so neither can rot.

## Scope, stated plainly

The attacked object is a THIRD-PARTY published relation, not a dregg relation.
The shipped dregg analogue is `dark-amm-private-v1`, which is Lean-authored AIR:
`Market/DarkAmmPrivateDescriptor.lean:94-101` lists the swap conditions as
`semanticBodies`, and line 146 maps EACH body to its OWN `.gate` constraint
(line 147 repeats them as last-row boundaries).  The emitted
`circuit/descriptors/by-name/dark-amm-private-v1.json` accordingly carries them
at constraint indices 3-8, and `circuit-prove/src/dark_amm_private.rs:25`
`include_str!`s that JSON rather than rebuilding constraints in Rust.  The four
swap gates read

    v23 - (v19 + v21) = 0        -- x' = x + dx
    v20 - (v24 + v22) = 0        -- y  = y' + dy
    v19 * v20 - v2   = 0         -- x  * y  = k
    v23 * v24 - v2   = 0         -- x' * y' = k

each of which must vanish on its own.  A conjunction of independent residuals
admits no erasable factor (`conjunctive_encoding_has_no_erasable_factor`), so
the published bypass does not apply to it.  Checked directly at the source: `Market/DarkAmmPrivateDescriptor.lean`
maps EACH swap body to its own `.base (.gate body)`, so the shipped dark-amm
descriptor carries no product-of-residual gate. (An earlier draft of this header
claimed a mechanical scan of all 52 by-name descriptors found zero such gates
anywhere -- that claim was FALSE and is retracted: other descriptors do contain
product-shaped gate bodies, see the residual below. The immunity established here
is about dark-amm's own construction, not a tree-wide absence.)  This file therefore records a REFUTED-ON-PAPER
design, not a live dregg vulnerability, and the teeth below are what keep the
distinction true rather than merely asserted.

Residual, named not hidden: other shipped descriptors DO contain
product-of-residual gate bodies. Verified instance: `note-spend-leaf.json`
(selector-gated `(1 - s) * (a - b)` shapes). The `merkle-membership-*` family was
cited in an earlier draft WITHOUT verification -- treat that half as UNCHECKED
until someone reads those descriptors; do not repeat it as established.  Those are conditional constraints, sound exactly when the selector is
itself pinned; they are the known stapleable-slot class, not this one, and are
out of this file's scope.

The two encodings are built from the *same three residuals*
(`published_swap_is_product_of_the_same_residuals`); only the fold differs —
product versus conjunction.  That is the entire finding, and it is exactly the
connective reversal audited in `papers/direct-logic-arithmetization`.

The Lean transcription of the shipped gate list below is a MODEL of the JSON,
not a certificate about it; it states which relation the descriptor is claimed
to encode and pins the forged witness against it.  Reproving the descriptor
itself is the emit path's job, not this file's.
-/

import Dregg2.Metatheory.FOLArithmetizationCounterexamples

namespace Dregg2.Metatheory.SwapRelationRepairCanary

open Dregg2.Metatheory.FOLArithmetizationCounterexamples

set_option autoImplicit false

/-! ## The hole class, stated once and generically -/

/-- **The bug, generically.** Under zero-means-true, folding a constraint list
with multiplication makes ANY one satisfied residual erase every other one. -/
theorem product_encoding_erases_every_other_residual {R : Type*} [CommRing R]
    (rs : List R) (r : R) (hmem : r ∈ rs) (hr : r = 0) : rs.prod = 0 :=
  List.prod_eq_zero (by simpa [hr] using hmem)

/-- **The repair, generically.** Folding the same list with conjunction — one
independent gate per residual, which is what a descriptor emits — leaves every
residual load-bearing: none can be erased by another. -/
theorem conjunctive_encoding_has_no_erasable_factor {R : Type*} [CommRing R]
    (rs : List R) (r : R) (hmem : r ∈ rs) (h : ∀ s ∈ rs, s = 0) : r = 0 :=
  h r hmem

/-! ## The published swap relation and its repair, over the same residuals -/

/-- The three swap conditions as SEPARATE residuals: balance change, quoted
output, constant product. -/
def swapResiduals {R : Type*} [CommRing R] (A B A' B' k quotedOutput : R) :
    List R :=
  [A' - A + k, B' - B - quotedOutput, A * B - A' * B']

/-- The repaired relation: every residual must vanish independently.  This is
the conjunctive fold a descriptor gate list realizes. -/
def RepairedSwapAccepts {R : Type*} [CommRing R]
    (A B A' B' k quotedOutput : R) : Prop :=
  ∀ r ∈ swapResiduals A B A' B' k quotedOutput, r = 0

/-- The published relation is precisely the PRODUCT of the same three residuals.
Nothing else differs between the broken relation and the repair. -/
theorem published_swap_is_product_of_the_same_residuals {R : Type*} [CommRing R]
    (A B A' B' k quotedOutput : R) :
    bitLogicSwapPolynomial A B A' B' k quotedOutput =
      (swapResiduals A B A' B' k quotedOutput).prod := by
  simp [bitLogicSwapPolynomial, swapResiduals, mul_assoc]

theorem repaired_accepts_iff_all_constraints {R : Type*} [CommRing R]
    (A B A' B' k quotedOutput : R) :
    RepairedSwapAccepts A B A' B' k quotedOutput ↔
      (A' - A + k = 0 ∧ B' - B - quotedOutput = 0 ∧ A * B - A' * B' = 0) := by
  simp [RepairedSwapAccepts, swapResiduals]

/-- The repair is strictly stronger, never weaker: everything the conjunction
accepts, the published product accepts too.  So the repair adds no false
rejections; it only removes the forgeries. -/
theorem repaired_accept_implies_published_accept {R : Type*} [CommRing R]
    (A B A' B' k quotedOutput : R)
    (h : RepairedSwapAccepts A B A' B' k quotedOutput) :
    bitLogicSwapPolynomial A B A' B' k quotedOutput = 0 := by
  obtain ⟨h1, -, -⟩ := (repaired_accepts_iff_all_constraints A B A' B' k
    quotedOutput).mp h
  simp [bitLogicSwapPolynomial, h1]

/-! ## The armed canary: the exact forged witness -/

/-- **The falsifier, now proving rejection.**  On the single witness
`A = B = 10, k = q = 1, A' = 9, B' = 999` of
`published_swap_accepts_invalid_witness`, the published product accepts and the
repaired conjunction REJECTS.  If anyone ever folds these residuals back into a
product, this theorem stops compiling. -/
theorem repaired_rejects_the_published_forgery :
    bitLogicSwapPolynomial (10 : ℤ) 10 9 999 1 1 = 0 ∧
      ¬ RepairedSwapAccepts (10 : ℤ) 10 9 999 1 1 := by
  refine ⟨by norm_num [bitLogicSwapPolynomial], ?_⟩
  rw [repaired_accepts_iff_all_constraints]
  rintro ⟨-, h2, -⟩
  norm_num at h2

/-- The repair breaks the published relation's POLYNOMIAL IDENTITY.
⚠ READ THE STATEMENT, NOT THIS SENTENCE: what is proven is the NEGATION OF A
UNIVERSAL -- `¬ ∀ A B B' k q, RepairedSwapAccepts A B (A - k) B' k q` -- i.e. the
`A' = A - k` substitution is NOT an identity for the repaired relation (some
instance rejects). That is exactly the negation of
`published_swap_bypass_is_polynomial_identity`, and it is strictly WEAKER than
"no bypass exists": it does not rule out other bypass families. Claiming the
repair kills the general attack would overstate this theorem. -/
theorem repaired_has_no_polynomial_identity_bypass :
    ¬ ∀ (A B B' k quotedOutput : ℤ),
        RepairedSwapAccepts A B (A - k) B' k quotedOutput := by
  intro h
  have hbad := h 10 10 999 1 1
  rw [repaired_accepts_iff_all_constraints] at hbad
  obtain ⟨-, h2, -⟩ := hbad
  norm_num at h2

/-- An honest swap is still accepted: the repair is not vacuous rejection.
`A = B = 10, A' = 5, k = 5, B' = 20, q = 10` satisfies all three residuals. -/
theorem repaired_accepts_an_honest_swap :
    RepairedSwapAccepts (10 : ℤ) 10 5 20 5 10 := by
  rw [repaired_accepts_iff_all_constraints]
  norm_num

/-! ## Executable teeth (cheap `Bool`, no kernel `decide` on instances) -/

/-- Decision procedure for the published product form. -/
def publishedAcceptsB (A B A' B' k quotedOutput : ℤ) : Bool :=
  bitLogicSwapPolynomial A B A' B' k quotedOutput == 0

/-- Decision procedure for the repaired conjunctive form. -/
def repairedAcceptsB (A B A' B' k quotedOutput : ℤ) : Bool :=
  (swapResiduals A B A' B' k quotedOutput).all (· == 0)

-- The forgery: accepted by the published relation, rejected by the repair.
#guard publishedAcceptsB 10 10 9 999 1 1 == true
#guard repairedAcceptsB 10 10 9 999 1 1 == false

-- The identity bypass, sampled: `A' = A - k` accepts the published relation for
-- arbitrary unrelated `B'` and `q`, and is rejected by the repair each time.
#guard publishedAcceptsB 10 10 9 999 1 1 == true
#guard publishedAcceptsB 7 3 4 (-11) 3 88 == true
#guard publishedAcceptsB 0 5 (-2) 31 2 6 == true
#guard repairedAcceptsB 7 3 4 (-11) 3 88 == false
#guard repairedAcceptsB 0 5 (-2) 31 2 6 == false

-- Not vacuous: the honest swap passes both.
#guard repairedAcceptsB 10 10 5 20 5 10 == true
#guard publishedAcceptsB 10 10 5 20 5 10 == true

/-! ## The shipped dregg analogue

A Lean model of `Market.DarkAmmPrivateDescriptor.semanticBodies`
(`Market/DarkAmmPrivateDescriptor.lean:94-101`), each entry of which becomes its
own `.gate` at line 146.  It is a conjunction, so
`conjunctive_encoding_has_no_erasable_factor` applies to it and the published
bypass does not.  This is a transcription for the canary, NOT a proof about the
JSON; the emit path owns that obligation. -/

/-- Residuals of the shipped private-AMM swap, in descriptor order. -/
def shippedAmmResiduals {R : Type*} [CommRing R]
    (x y dx dy x' y' k dxInv dyInv : R) : List R :=
  [x' - (x + dx),          -- gate 3: x' = x + dx
   y - (y' + dy),          -- gate 4: y  = y' + dy
   x * y - k,              -- gate 5: pre-state constant product
   x' * y' - k,            -- gate 6: post-state constant product
   dx * dxInv - 1,         -- gate 7: dx invertible
   dy * dyInv - 1]         -- gate 8: dy invertible

def ShippedAmmAccepts {R : Type*} [CommRing R]
    (x y dx dy x' y' k dxInv dyInv : R) : Prop :=
  ∀ r ∈ shippedAmmResiduals x y dx dy x' y' k dxInv dyInv, r = 0

/-- Every shipped gate stays load-bearing: acceptance entails the post-state
constant product, which is exactly the factor the published relation erases. -/
theorem shipped_accept_implies_post_constant_product {R : Type*} [CommRing R]
    (x y dx dy x' y' k dxInv dyInv : R)
    (h : ShippedAmmAccepts x y dx dy x' y' k dxInv dyInv) :
    x' * y' = k := by
  have hres := conjunctive_encoding_has_no_erasable_factor
    (shippedAmmResiduals x y dx dy x' y' k dxInv dyInv) (x' * y' - k)
    (by simp [shippedAmmResiduals]) h
  exact sub_eq_zero.mp hres

/-- The forged reserves of the published witness are refused by the shipped
gate shape: `10 * 10 = 100 = k` but `9 * 999 = 8991 ≠ k`. -/
theorem shipped_refuses_the_published_forgery
    (dx dy dxInv dyInv : ℤ) :
    ¬ ShippedAmmAccepts 10 10 dx dy 9 999 100 dxInv dyInv := by
  intro h
  have hk := shipped_accept_implies_post_constant_product
    10 10 dx dy 9 999 100 dxInv dyInv h
  norm_num at hk

#assert_all_clean [product_encoding_erases_every_other_residual,
  conjunctive_encoding_has_no_erasable_factor,
  published_swap_is_product_of_the_same_residuals,
  repaired_accepts_iff_all_constraints,
  repaired_accept_implies_published_accept,
  repaired_rejects_the_published_forgery,
  repaired_has_no_polynomial_identity_bypass,
  repaired_accepts_an_honest_swap,
  shipped_accept_implies_post_constant_product,
  shipped_refuses_the_published_forgery]

end Dregg2.Metatheory.SwapRelationRepairCanary
