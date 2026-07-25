/-
# Dregg2.Crypto.BN254.Fp2 — the quadratic tower level `F_{p²} = Fq[u]/(u² + 1)`.

The first tower level above the base field.  `Fp2` is the complex extension of `Fq` with `u² = -1`
(Solidity: *"Extension field Fp2 = Fp[i] / (i² + 1)"*).  An element `a₀ + a₁·u` is the coordinate
pair `⟨c0, c1⟩`.

This is authored as an EXPLICIT COORDINATE ring, not `AdjoinRoot (X²+1)`, for two reasons:
(1) it is a `CommRing` over the base `CommRing Fq` with NO primality hypothesis — only the FIELD
(inverse) structure needs `-1` to be a non-residue, which is a named downstream goal; and
(2) it COMPUTES, so the KATs below (`u² = -1`, the norm identity) are real `#guard`s, and the same
representation feeds the pairing's line-function `#eval`s later.  The `CommRing` is built with the
`Zsqrtd`-style ladder (`AddCommGroup → AddGroupWithOne → CommRing`), each field discharged by
`intros <;> ext <;> simp <;> ring`.

Conjugation `⟨c0, c1⟩ ↦ ⟨c0, -c1⟩` is the nontrivial `Fq`-automorphism (the `p`-power Frobenius of
`Fp2`); `norm a = a · conj a = c0² + c1²` lands in `Fq`.
-/
import Dregg2.Crypto.BN254.Fq

namespace Dregg2.Crypto.BN254

set_option autoImplicit false

/-! ## §1 The coordinate ring `Fp2 = Fq[u]/(u²+1)`. -/

/-- An element of `F_{p²}`: `c0 + c1·u` with `u² = -1`. -/
@[ext] structure Fp2 where
  c0 : Fq
  c1 : Fq
  deriving DecidableEq

namespace Fp2

instance : Zero Fp2 := ⟨⟨0, 0⟩⟩
instance : One Fp2 := ⟨⟨1, 0⟩⟩
instance : Add Fp2 := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1⟩⟩
instance : Neg Fp2 := ⟨fun a => ⟨-a.c0, -a.c1⟩⟩
/-- Complex multiplication with `u² = -1`:
`(a₀+a₁u)(b₀+b₁u) = (a₀b₀ − a₁b₁) + (a₀b₁ + a₁b₀)u`. -/
instance : Mul Fp2 := ⟨fun a b => ⟨a.c0 * b.c0 - a.c1 * b.c1, a.c0 * b.c1 + a.c1 * b.c0⟩⟩

@[simp] theorem zero_c0 : (0 : Fp2).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp2).c1 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp2).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp2).c1 = 0 := rfl
@[simp] theorem add_c0 (a b : Fp2) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp2) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem neg_c0 (a : Fp2) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp2) : (-a).c1 = -a.c1 := rfl
@[simp] theorem mul_c0 (a b : Fp2) : (a * b).c0 = a.c0 * b.c0 - a.c1 * b.c1 := rfl
@[simp] theorem mul_c1 (a b : Fp2) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl

instance instAddCommGroup : AddCommGroup Fp2 := by
  refine
  { add := (· + ·), zero := 0, neg := Neg.neg, sub := fun a b => a + -b,
    nsmul := @nsmulRec Fp2 ⟨0⟩ ⟨(· + ·)⟩,
    zsmul := @zsmulRec Fp2 ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec Fp2 ⟨0⟩ ⟨(· + ·)⟩),
    add_assoc := ?_, zero_add := ?_, add_zero := ?_,
    neg_add_cancel := ?_, add_comm := ?_ } <;>
  intros <;> ext <;> simp <;> ring

instance instCommRing : CommRing Fp2 := by
  refine
  { Fp2.instAddCommGroup with
    mul := (· * ·), one := 1,
    npow := @npowRec Fp2 ⟨1⟩ ⟨(· * ·)⟩,
    add_comm := ?_,
    left_distrib := ?_, right_distrib := ?_,
    zero_mul := ?_, mul_zero := ?_, mul_assoc := ?_,
    one_mul := ?_, mul_one := ?_, mul_comm := ?_ } <;>
  intros <;> ext <;> simp <;> ring

/-! ## §2 The generator `u`, its defining relation, embeddings, conjugation, norm. -/

/-- The adjoined root `u` (`i` in the Solidity comments). -/
def u : Fp2 := ⟨0, 1⟩

/-- The base-field embedding `Fq ↪ Fp2`, `a ↦ a + 0·u`. -/
def ofFq (a : Fq) : Fp2 := ⟨a, 0⟩

@[simp] theorem ofFq_c0 (a : Fq) : (ofFq a).c0 = a := rfl
@[simp] theorem ofFq_c1 (a : Fq) : (ofFq a).c1 = 0 := rfl

/-- **The defining relation `u² = -1`.** -/
theorem u_sq : u * u = -1 := by ext <;> simp [u]

/-- Conjugation `a₀ + a₁u ↦ a₀ − a₁u` — the nontrivial `Fq`-automorphism of `Fp2`
(the `p`-power Frobenius). -/
def conj (a : Fp2) : Fp2 := ⟨a.c0, -a.c1⟩

@[simp] theorem conj_c0 (a : Fp2) : (conj a).c0 = a.c0 := rfl
@[simp] theorem conj_c1 (a : Fp2) : (conj a).c1 = -a.c1 := rfl

theorem conj_conj (a : Fp2) : conj (conj a) = a := by ext <;> simp

/-- The field norm `N(a) = a · conj a = c0² + c1² ∈ Fq` (embedded), a multiplicative map to the
base field.  Nonvanishing of the norm on `a ≠ 0` is exactly the `Field Fp2` obstruction
(`-1` a non-residue mod `p`) — the named downstream goal. -/
def normFp2 (a : Fp2) : Fq := a.c0 * a.c0 + a.c1 * a.c1

theorem mul_conj (a : Fp2) : a * conj a = ofFq (normFp2 a) := by
  ext <;> simp [conj, normFp2, ofFq] <;> ring

/-! ## §3 The `Field Fp2` obligation (named; not discharged here). -/

/-- **The `Fp2` field obligation.**  `Fp2` is a field iff `X² + 1` is irreducible over `Fq`, i.e.
`-1` is not a quadratic residue mod `p` (true: `p ≡ 3 mod 4`).  Discharging it (and then defining
`a⁻¹ = conj a / normFp2 a`) needs `[Fact (Nat.Prime pBN254)]` plus the residue fact; named here,
done later.  The whole `CommRing` tower — hence the pairing DEFINITION — does not depend on it. -/
def Fp2FieldGoal : Prop := ∀ a : Fp2, a ≠ 0 → normFp2 a ≠ 0

/-! ## §4 KATs — the defining relation and the norm identity compute. -/

-- `u² = -1` as a closed `#guard` (the whole point of the coordinate representation).
#guard (u * u = (-1 : Fp2))

-- `(1 + u)(1 − u) = 1 − u² = 2` — the norm of `1 + u` is `2`.
#guard ((⟨1, 1⟩ : Fp2) * ⟨1, -1⟩ = ⟨2, 0⟩)
#guard (normFp2 ⟨1, 1⟩ = 2)

-- Conjugation is an involution on a concrete element.
#guard (conj (conj ⟨3, 7⟩) = (⟨3, 7⟩ : Fp2))

#assert_axioms u_sq
#assert_axioms conj_conj
#assert_axioms mul_conj

end Fp2
end Dregg2.Crypto.BN254
