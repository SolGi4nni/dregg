/-
# Dregg2.Crypto.BN254.Curves — the two pairing groups `G1 ⊂ E(Fq)` and `G2 ⊂ E'(Fp2)`.

Groth16/BN254 pairs a `G1` point with a `G2` point.  Both are order-`r` subgroups (`r = rBN254`,
the scalar field) of elliptic curves:

* **G1** lives on `E : y² = x³ + 3` over the base field `Fq` (cofactor 1: `#E(Fq) = r`, so
  `G1 = E(Fq)`).  Generator `(1, 2)` — `1³ + 3 = 4 = 2²`.
* **G2** lives on the sextic twist `E' : y² = x³ + b'` over `Fp2`, `b' = 3/ξ = 3/(9+u)`.  The two
  `Fq`-coordinates of `b'` are the deployed Solidity constants `FRACTION_27_82_FP` (real) and
  `−FRACTION_3_82_FP` (imaginary).  `G2` is the order-`r` subgroup with the standard generator below.

This file gives the COMPUTABLE on-curve predicates (so the generators are real `#guard` KATs), ties
each to Mathlib's `WeierstrassCurve.Affine.Equation`, and records the group law via Mathlib's
`WeierstrassCurve.Affine.Point` — whose `AddCommGroup` instance holds once the base is a `Field`
(i.e. under `[Fact (Nat.Prime pBN254)]`).  The b'-correctness KAT `b' · ξ = 3` verifies the twist
constant with NO inverse (ring-only), independent of the field seam.
-/
import Dregg2.Crypto.BN254.Fp2
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace Dregg2.Crypto.BN254

set_option autoImplicit false

/-! ## §1 G1 : `E : y² = x³ + 3` over `Fq`. -/

/-- The BN254 G1 curve as a Mathlib Weierstrass curve `⟨a₁,a₂,a₃,a₄,a₆⟩ = ⟨0,0,0,0,3⟩`. -/
def W1 : WeierstrassCurve Fq := ⟨0, 0, 0, 0, 3⟩

/-- Computable on-curve predicate for G1: `y² = x³ + 3`. -/
def OnCurveG1 (x y : Fq) : Prop := y * y = x * x * x + 3

instance (x y : Fq) : Decidable (OnCurveG1 x y) := inferInstanceAs (Decidable (_ = _))

/-- **Bridge to Mathlib.**  The self-contained predicate is exactly Mathlib's Weierstrass
`Equation` for `W1`. -/
theorem onCurveG1_iff (x y : Fq) : OnCurveG1 x y ↔ W1.toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [W1, OnCurveG1]
  constructor <;> intro h <;> ring_nf <;> ring_nf at h <;> linear_combination h

/-- The G1 point group, reusing Mathlib.  `AddCommGroup W1.toAffine.Point` is available once
`Fq` is a field (`[Fact (Nat.Prime pBN254)]`); the generator is `(1,2)`. -/
abbrev G1Point := W1.toAffine.Point

example [Fact (Nat.Prime pBN254)] : AddCommGroup G1Point := inferInstance

/-- The G1 generator `(1, 2)`. -/
def g1GenX : Fq := 1
def g1GenY : Fq := 2

-- KAT: the generator is on the curve (`1 + 3 = 4 = 2²`).
#guard OnCurveG1 g1GenX g1GenY
-- KAT: a wrong `y` is rejected — the predicate has teeth.
#guard ¬ OnCurveG1 g1GenX 3

/-! ## §2 G2 : the sextic twist `E' : y² = x³ + b'` over `Fp2`, `b' = 3/ξ`. -/

/-- The twist constant `b' = 3/(9+u) ∈ Fp2`.  Coordinates are the deployed Solidity fractions:
real `= 27/82 = FRACTION_27_82_FP`, imaginary `= −3/82 = −FRACTION_3_82_FP`. -/
def bTwist : Fp2 :=
  ⟨19485874751759354771024239261021720505790618469301721065564631296452457478373,
   266929791119991161246907387137283842545076965332900288569378510910307636690⟩

-- b'-correctness, inverse-free: `b' · ξ = 3` in `Fp2` with `ξ = 9 + u` (equivalently `b' = 3/ξ`).
-- A pure ring KAT verifying the deployed twist constant with NO field inverse.
#guard (bTwist * (⟨9, 1⟩ : Fp2) = Fp2.ofFq 3)

/-- The BN254 G2 curve as a Mathlib Weierstrass curve over `Fp2`. -/
def W2 : WeierstrassCurve Fp2 := ⟨0, 0, 0, 0, bTwist⟩

/-- Computable on-curve predicate for G2: `y² = x³ + b'` over `Fp2`. -/
def OnCurveG2 (x y : Fp2) : Prop := y * y = x * x * x + bTwist

instance (x y : Fp2) : Decidable (OnCurveG2 x y) := inferInstanceAs (Decidable (_ = _))

theorem onCurveG2_iff (x y : Fp2) : OnCurveG2 x y ↔ W2.toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [W2, OnCurveG2]
  constructor <;> intro h <;> ring_nf <;> ring_nf at h <;> linear_combination h

/-- The G2 point group, reusing Mathlib (`AddCommGroup` under the `Fp2`-field seam). -/
abbrev G2Point := W2.toAffine.Point

/-- The standard BN254 G2 generator (EIP-197 / gnark), `c0 + c1·u` per coordinate. -/
def g2GenX : Fp2 :=
  ⟨10857046999023057135944570762232829481370756359578518086990519993285655852781,
   11559732032986387107991004021392285783925812861821192530917403151452391805634⟩
def g2GenY : Fp2 :=
  ⟨8495653923123431417604973247489272438418190587263600148770280649306958101930,
   4082367875863433681332203403145435568316851327593401208105741076214120093531⟩

-- KAT: the standard G2 generator is on the twist.
#guard OnCurveG2 g2GenX g2GenY
-- KAT: a perturbed generator is rejected.
#guard ¬ OnCurveG2 g2GenX (g2GenY + 1)

/-! ## §3 The common subgroup order `r` (= the scalar field), named for the pairing. -/

/-- The order of both pairing groups `G1`, `G2` and of the pairing's image `μ_r ⊆ Fp12ˣ`: the BN254
scalar prime `r = rBN254`.  (For BN254, `#E(Fq) = r` exactly — G1 cofactor 1.) -/
def subgroupOrder : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- **The group-structure obligations (named; the `AddCommGroup` is Mathlib's under the field
seam).**  What remains for a full `G1`/`G2` model is: (a) the `[Fact (Nat.Prime pBN254)]` field
discharge, giving the `Point` `AddCommGroup` for free; (b) that the generators generate an order-`r`
subgroup; (c) for G2, the twist isomorphism to `E(Fq¹²)`.  None is needed for the pairing DEFINITION;
they enter for bilinearity/non-degeneracy. -/
def GroupStructureGoal : Prop :=
  OnCurveG1 g1GenX g1GenY ∧ OnCurveG2 g2GenX g2GenY

theorem groupStructureGoal_holds : GroupStructureGoal := by
  refine ⟨?_, ?_⟩ <;> decide

#assert_axioms onCurveG1_iff
#assert_axioms onCurveG2_iff
#assert_axioms groupStructureGoal_holds

end Dregg2.Crypto.BN254
