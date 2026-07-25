/-
# Dregg2.Crypto.BN254.Fp12 — the top tower level `F_{p¹²} = Fp6[w]/(w² − v)`.

The pairing's target group lives here: `e : G1 × G2 → F_{p¹²}` (more precisely the order-`r`
subgroup `μ_r ⊆ F_{p¹²}ˣ`).  `Fp12` is the quadratic extension of `Fp6` by a root `w` of `X² − v`,
where `v` is the cubic generator of `Fp6` (Solidity/gnark tower: `Fp12 = Fp6[w]/(w² − v)`).  An
element `a₀ + a₁·w` is the coordinate pair `⟨c0, c1⟩` over `Fp6`.

The multiplication uses the KEY SIMPLIFICATION that "reduce `w² ↦ v`" is just multiplication by the
`Fp6`-element `v = ⟨0,1,0⟩` in the `Fp6` ring (which already satisfies `v³ = ξ`):
* `c0' = a₀b₀ + v·(a₁b₁)`
* `c1' = a₀b₁ + a₁b₀`
so the whole `CommRing` is expressed in `Fp6` arithmetic and `ring` closes every axiom with `v` an
opaque constant.  No primality anywhere in the tower; `Field Fp12` (needing `X² − v` irreducible) is
the named downstream goal.  This completes the field tower the Miller loop and final exponentiation
of the BN254 optimal-ate pairing are defined over.
-/
import Dregg2.Crypto.BN254.Fp6

namespace Dregg2.Crypto.BN254

set_option autoImplicit false

/-! ## §1 The coordinate ring `Fp12 = Fp6[w]/(w² − v)`. -/

/-- An element of `F_{p¹²}`: `c0 + c1·w` with `w² = v` (`v` the cubic generator of `Fp6`). -/
@[ext] structure Fp12 where
  c0 : Fp6
  c1 : Fp6
  deriving DecidableEq

namespace Fp12

instance : Zero Fp12 := ⟨⟨0, 0⟩⟩
instance : One Fp12 := ⟨⟨1, 0⟩⟩
instance : Add Fp12 := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1⟩⟩
instance : Neg Fp12 := ⟨fun a => ⟨-a.c0, -a.c1⟩⟩
/-- Quadratic multiplication reducing `w² = v` (as the `Fp6`-element `Fp6.v`). -/
instance : Mul Fp12 := ⟨fun a b =>
  ⟨a.c0 * b.c0 + Fp6.v * (a.c1 * b.c1),
   a.c0 * b.c1 + a.c1 * b.c0⟩⟩

@[simp] theorem zero_c0 : (0 : Fp12).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp12).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp12).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp12).c1 = 0 := rfl
@[simp] theorem add_c0 (a b : Fp12) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp12) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem neg_c0 (a : Fp12) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp12) : (-a).c1 = -a.c1 := rfl
@[simp] theorem mul_c0 (a b : Fp12) : (a * b).c0 = a.c0 * b.c0 + Fp6.v * (a.c1 * b.c1) := rfl
@[simp] theorem mul_c1 (a b : Fp12) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl

/-- Keep every ring-axiom proof AT THE `Fp12` LEVEL: `simp only` with the `Fp12` coordinate
lemmas rewrites into `Fp6` arithmetic (with `Fp6.v` an opaque constant), and `ring` over the
`Fp6` `CommRing` closes it.  Full `simp` here would unfold `Fp6`/`Fp2`/`Fq` and blow the
heartbeat budget on `mul_assoc`. -/
local macro "fp12_ring" : tactic =>
  `(tactic| (intros <;> ext <;>
    simp only [add_c0, add_c1, mul_c0, mul_c1, neg_c0, neg_c1, zero_c0, zero_c1, one_c0, one_c1] <;>
    ring))

instance instAddCommGroup : AddCommGroup Fp12 := by
  refine
  { add := (· + ·), zero := 0, neg := Neg.neg, sub := fun a b => a + -b,
    nsmul := @nsmulRec Fp12 ⟨0⟩ ⟨(· + ·)⟩,
    zsmul := @zsmulRec Fp12 ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec Fp12 ⟨0⟩ ⟨(· + ·)⟩),
    add_assoc := ?_, zero_add := ?_, add_zero := ?_,
    neg_add_cancel := ?_, add_comm := ?_ } <;>
  fp12_ring

instance instCommRing : CommRing Fp12 := by
  refine
  { Fp12.instAddCommGroup with
    mul := (· * ·), one := 1,
    npow := @npowRec Fp12 ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_,
    left_distrib := ?_, right_distrib := ?_,
    zero_mul := ?_, mul_zero := ?_, mul_assoc := ?_,
    one_mul := ?_, mul_one := ?_, mul_comm := ?_ } <;>
  fp12_ring

/-! ## §2 The generator `w`, its relation, and the tower embeddings. -/

/-- The adjoined quadratic root `w`, `w² = v`. -/
def w : Fp12 := ⟨0, 1⟩

/-- The base-`Fp6` embedding. -/
def ofFp6 (a : Fp6) : Fp12 := ⟨a, 0⟩

/-- The full base-field embedding `Fq ↪ Fp12` (the target of `1` in the pairing check). -/
def ofFq (a : Fq) : Fp12 := ofFp6 (Fp6.ofFp2 (Fp2.ofFq a))

@[simp] theorem ofFp6_c0 (a : Fp6) : (ofFp6 a).c0 = a := rfl
@[simp] theorem ofFp6_c1 (a : Fp6) : (ofFp6 a).c1 = 0 := rfl

/-- **The defining relation `w² = v`** (embedded into `Fp12`). -/
theorem w_sq : w * w = ofFp6 Fp6.v := by ext <;> simp [w]

/-! ## §3 The `Field Fp12` obligation (named; not discharged here). -/

/-- **The `Fp12` field obligation.**  `Fp12` is a field iff `X² − v` is irreducible over `Fp6`, i.e.
`v` is a non-square in `Fp6` (true for BN254 by tower construction).  Needs the `Fp6` field
structure; named here.  The pairing DEFINITION (Miller loop + final exponentiation as a power) is
pure `CommRing` arithmetic and does not consume it; only NON-DEGENERACY / the multiplicative-group
argument later does. -/
def Fp12FieldGoal : Prop := ∀ x : Fp6, x ^ 2 ≠ Fp6.v

/-! ## §4 KATs — the tower relation computes; embeddings are ring homs on constants. -/

-- `w² = v`.
#guard (w * w = ofFp6 Fp6.v)

-- `w⁴ = v² ≠ 1`, and `w⁶ = v³ = ξ` embedded — the tower composes to `F_{p¹²}` correctly.
#guard (w ^ 6 = ofFp6 (Fp6.ofFp2 xiFp2))

-- `1 : Fp12` embeds `1 : Fq`.
#guard (ofFq 1 = (1 : Fp12))

#assert_axioms w_sq

end Fp12
end Dregg2.Crypto.BN254
