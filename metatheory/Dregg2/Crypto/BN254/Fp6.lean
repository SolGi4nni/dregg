/-
# Dregg2.Crypto.BN254.Fp6 — the cubic tower level `F_{p⁶} = Fp2[v]/(v³ − ξ)`, `ξ = 9 + u`.

The sextic-twist tower's middle level: a cubic extension of `Fp2` by a root `v` of `X³ − ξ`, where
`ξ = 9 + u` is the standard BN254 non-residue (the same `9 + i` that fixes the twist and the whole
gnark/arkworks/Solidity BN254 arithmetic).  An element `a₀ + a₁·v + a₂·v²` is the coordinate triple
`⟨c0, c1, c2⟩` over `Fp2`.

Multiplication reduces `v³ ↦ ξ`, `v⁴ ↦ ξ·v`:
* `c0' = a₀b₀ + ξ·(a₁b₂ + a₂b₁)`
* `c1' = a₀b₁ + a₁b₀ + ξ·(a₂b₂)`
* `c2' = a₀b₂ + a₁b₁ + a₂b₀`

`CommRing` over the `CommRing Fp2` (no primality); `ring` closes every axiom with `ξ` an opaque
constant.  Field structure (needing `X³ − ξ` irreducible, i.e. `ξ` a non-cube in `Fp2`) is the named
downstream goal — irrelevant to the pairing DEFINITION, which is all ring arithmetic.
-/
import Dregg2.Crypto.BN254.Fp2

namespace Dregg2.Crypto.BN254

set_option autoImplicit false

/-! ## §1 The non-residue `ξ = 9 + u` and the coordinate ring. -/

/-- The BN254 cubic/sextic non-residue `ξ = 9 + u ∈ Fp2`. -/
def xiFp2 : Fp2 := ⟨9, 1⟩

/-- An element of `F_{p⁶}`: `c0 + c1·v + c2·v²` with `v³ = ξ`. -/
@[ext] structure Fp6 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2
  deriving DecidableEq

namespace Fp6

instance : Zero Fp6 := ⟨⟨0, 0, 0⟩⟩
instance : One Fp6 := ⟨⟨1, 0, 0⟩⟩
instance : Add Fp6 := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩⟩
instance : Neg Fp6 := ⟨fun a => ⟨-a.c0, -a.c1, -a.c2⟩⟩
/-- Cubic multiplication reducing `v³ = ξ`. -/
instance : Mul Fp6 := ⟨fun a b =>
  ⟨a.c0 * b.c0 + xiFp2 * (a.c1 * b.c2 + a.c2 * b.c1),
   a.c0 * b.c1 + a.c1 * b.c0 + xiFp2 * (a.c2 * b.c2),
   a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0⟩⟩

@[simp] theorem zero_c0 : (0 : Fp6).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp6).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : Fp6).c2 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp6).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp6).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : Fp6).c2 = 0 := rfl
@[simp] theorem add_c0 (a b : Fp6) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp6) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : Fp6) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem neg_c0 (a : Fp6) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp6) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 (a : Fp6) : (-a).c2 = -a.c2 := rfl
@[simp] theorem mul_c0 (a b : Fp6) :
    (a * b).c0 = a.c0 * b.c0 + xiFp2 * (a.c1 * b.c2 + a.c2 * b.c1) := rfl
@[simp] theorem mul_c1 (a b : Fp6) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 + xiFp2 * (a.c2 * b.c2) := rfl
@[simp] theorem mul_c2 (a b : Fp6) :
    (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 := rfl

instance instAddCommGroup : AddCommGroup Fp6 := by
  refine
  { add := (· + ·), zero := 0, neg := Neg.neg, sub := fun a b => a + -b,
    nsmul := @nsmulRec Fp6 ⟨0⟩ ⟨(· + ·)⟩,
    zsmul := @zsmulRec Fp6 ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec Fp6 ⟨0⟩ ⟨(· + ·)⟩),
    add_assoc := ?_, zero_add := ?_, add_zero := ?_,
    neg_add_cancel := ?_, add_comm := ?_ } <;>
  intros <;> ext <;> simp <;> ring

instance instCommRing : CommRing Fp6 := by
  refine
  { Fp6.instAddCommGroup with
    mul := (· * ·), one := 1,
    npow := @npowRec Fp6 ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_,
    left_distrib := ?_, right_distrib := ?_,
    zero_mul := ?_, mul_zero := ?_, mul_assoc := ?_,
    one_mul := ?_, mul_one := ?_, mul_comm := ?_ } <;>
  intros <;> ext <;> simp <;> ring

/-! ## §2 The generator `v`, its cubic relation, and the `Fp2`-embedding. -/

/-- The adjoined cubic root `v`, `v³ = ξ`. -/
def v : Fp6 := ⟨0, 1, 0⟩

/-- The base-`Fp2` embedding `a ↦ a + 0·v + 0·v²`. -/
def ofFp2 (a : Fp2) : Fp6 := ⟨a, 0, 0⟩

@[simp] theorem ofFp2_c0 (a : Fp2) : (ofFp2 a).c0 = a := rfl
@[simp] theorem ofFp2_c1 (a : Fp2) : (ofFp2 a).c1 = 0 := rfl
@[simp] theorem ofFp2_c2 (a : Fp2) : (ofFp2 a).c2 = 0 := rfl

/-- **The defining relation `v³ = ξ`** (embedded into `Fp6`). -/
theorem v_cubed : v * v * v = ofFp2 xiFp2 := by ext <;> simp [v, xiFp2] <;> ring

/-! ## §3 The `Field Fp6` obligation (named; not discharged here). -/

/-- **The `Fp6` field obligation.**  `Fp6` is a field iff `X³ − ξ` is irreducible over `Fp2`; for a
cubic that is exactly `ξ = 9 + u` having no cube root in `Fp2` (true for BN254).  Discharging it
(and then the `Fp6` inverse) needs the `Fp2` field structure first; named here, not on the
pairing-DEFINITION path (which is pure ring arithmetic). -/
def Fp6FieldGoal : Prop := ∀ x : Fp2, x ^ 3 ≠ xiFp2

/-! ## §4 KATs — the cubic relation and a nontrivial product compute. -/

-- `v · v · v = ξ` embedded.
#guard (v * v * v = ofFp2 xiFp2)

-- `v² · v = ξ` via the mul definition (associativity sanity on the generator).
#guard (v * v * v = (ofFp2 xiFp2 : Fp6))

-- A concrete product exercising the `ξ`-reduction: `(v²)·(v²) = ξ·v` since `v⁴ = ξ·v`.
#guard ((⟨0, 0, 1⟩ : Fp6) * ⟨0, 0, 1⟩ = ⟨0, xiFp2, 0⟩)

#assert_axioms v_cubed

end Fp6
end Dregg2.Crypto.BN254
