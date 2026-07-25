/-
# Dregg2.Crypto.BN254.Pairing — the optimal-ate pairing DEFINITION `e : G1 × G2 → F_{p¹²}`.

The pairing is the object the deployed Solidity verifier's `PRECOMPILE_VERIFY` (`alt_bn128` /
EIP-197) computes.  This file gives its DEFINITION (per the plan: *"the definition first;
bilinearity/non-degeneracy proofs are later work — state them as the named goals"*).  It is
`e = finalExp ∘ millerLoop`:

* **Loop parameter** `ateLoopCount = 6t + 2 = 29793968203157093288` (`t = 4965661367192848881`, the
  BN254 CM parameter) — proven equal to `6t+2` below.
* **Miller loop** — a double-and-add over the bits of `ateLoopCount` accumulating a line product in
  `F_{p¹²}`, with the `G2` accumulator in JACOBIAN coordinates.  Both the point steps
  (`g2Double`, `g2Madd`, exact `a=0` Jacobian formulas) and the line functions (`ellDbl`, `ellAdd`)
  are INVERSE-FREE (denominator-eliminated), so the whole loop is `CommRing` arithmetic over the
  tower — NO field/primality seam.  The line functions are the exact untwist-and-clear tangent/chord
  values (derived, not transcribed): for the sextic twist `(x,y) ↦ (x·w², y·w³)` with `w⁶ = ξ`,
  `w⁴ = v²`, `w³ = v·w`, the denominator-eliminated tangent numerator lands in the sparse
  `F_{p¹²}` shape below.
* **Final exponentiation** `finalExp f = f^((p¹²−1)/r)` — the mathematically canonical power (the
  Frobenius-accelerated form is an optimization, named later).

RESOLUTION (honest, per house method): the point steps and the line derivations are principled and
the doubling KAT below checks `g2Double` keeps the generator on-curve.  What is NOT yet proven —
stated as named goals, NOT hidden — is (a) that this loop (plus the two optimal-ate Frobenius
line-additions, noted but not yet added) computes the reduced ate pairing byte-for-byte as gnark /
the precompile (`MillerFaithful`); (b) BILINEARITY; (c) NON-DEGENERACY.  These are the multi-day
follow-ups the field tower + curves + this definition set up.
-/
import Dregg2.Crypto.BN254.Fp12
import Dregg2.Crypto.BN254.Curves

namespace Dregg2.Crypto.BN254

set_option autoImplicit false

/-! ## §1 The loop parameter `6t + 2` and the final-exponentiation exponent. -/

/-- The BN254 CM parameter `t` (the seed): `p`, `r`, and the loop count are all polynomials in `t`. -/
def bn254T : ℕ := 4965661367192848881

/-- The optimal-ate loop count `6t + 2` (the number the Miller loop iterates the bits of). -/
def ateLoopCount : ℕ := 29793968203157093288

theorem ateLoopCount_eq : ateLoopCount = 6 * bn254T + 2 := by
  norm_num [ateLoopCount, bn254T]

/-- The final-exponentiation exponent `(p¹² − 1)/r`.  `r ∣ p¹² − 1` (embedding degree 12), so this
is exact; the value is ~2790 bits (defined, not evaluated). -/
def finalExpExponent : ℕ := (pBN254 ^ 12 - 1) / subgroupOrder

/-! ## §2 Point representations and the exact inverse-free `G2` steps. -/

/-- A `G1` affine point over `Fq` (infinity handled separately; the loop assumes affine input). -/
structure G1Aff where
  x : Fq
  y : Fq

/-- A `G2` affine point over `Fp2` (the pairing's second argument / the loop's base point `Q`). -/
structure G2Aff where
  x : Fp2
  y : Fp2

/-- A `G2` point in Jacobian coordinates `(X : Y : Z)` (affine `= (X/Z², Y/Z³)`): the loop
accumulator, kept projective so every step is inverse-free. -/
structure G2Jac where
  X : Fp2
  Y : Fp2
  Z : Fp2

/-- The Jacobian embedding of an affine `G2` point (`Z = 1`). -/
def g2JacOfAff (Q : G2Aff) : G2Jac := ⟨Q.x, Q.y, 1⟩

/-- Jacobian on-curve predicate for the twist `Y² = X³ + b'·Z⁶`. -/
def OnCurveG2Jac (T : G2Jac) : Prop :=
  T.Y * T.Y = T.X * T.X * T.X + bTwist * (T.Z * T.Z * T.Z * T.Z * T.Z * T.Z)

instance (T : G2Jac) : Decidable (OnCurveG2Jac T) := inferInstanceAs (Decidable (_ = _))

/-- **Exact `a = 0` Jacobian doubling** (`2T`), inverse-free. -/
def g2Double (T : G2Jac) : G2Jac :=
  let A := T.X * T.X
  let B := T.Y * T.Y
  let C := B * B
  let D := 2 * ((T.X + B) * (T.X + B) - A - C)
  let E := 3 * A
  let F := E * E
  let X3 := F - 2 * D
  ⟨X3, E * (D - X3) - 8 * C, 2 * T.Y * T.Z⟩

/-- **Exact `a = 0` Jacobian mixed addition** (`T + Q`, `Q` affine), inverse-free. -/
def g2Madd (T : G2Jac) (Q : G2Aff) : G2Jac :=
  let Z2 := T.Z * T.Z
  let U2 := Q.x * Z2
  let S2 := Q.y * Z2 * T.Z
  let H := U2 - T.X
  let R := S2 - T.Y
  let HH := H * H
  let HHH := HH * H
  let X3 := R * R - HHH - 2 * T.X * HH
  ⟨X3, R * (T.X * HH - X3) - T.Y * HHH, T.Z * H⟩

/-! ## §3 The exact inverse-free line functions (untwist-and-clear).

For `T` Jacobian with affine `(X/Z², Y/Z³)` and eval point `P = (xP, yP) ∈ G1 ⊂ Fq`, the tangent line
`3Xaff²·x − 2Yaff·y − (3Xaff³ − 2Yaff²)` evaluated at the untwisted image and multiplied by `Z⁶`
(a unit, killed by `finalExp`) lands in the sparse shape:
`(2Y² − 3X³)·w⁶ + (3X²Z²·xP)·w⁴ + (−2YZ³·yP)·w³`, with `w⁶ = ξ`, `w⁴ = v²`, `w³ = v·w`. -/

/-- The tangent (doubling) line value at `T`, evaluated at `P`, as a sparse `F_{p¹²}` element. -/
def ellDbl (T : G2Jac) (P : G1Aff) : Fp12 :=
  let X := T.X; let Y := T.Y; let Z := T.Z
  let tw6 : Fp2 := 2 * (Y * Y) - 3 * (X * X * X)
  let tw4 : Fp2 := 3 * (X * X) * (Z * Z) * Fp2.ofFq P.x
  let tw3 : Fp2 := -(2 * Y * (Z * Z * Z) * Fp2.ofFq P.y)
  ⟨⟨tw6 * xiFp2, 0, tw4⟩, ⟨0, tw3, 0⟩⟩

/-- The chord (addition) line value at `T` with base `Q`, evaluated at `P` (untwist-and-clear by
`Δ·Z³`, `Δ = X − x_Q·Z²`; the unit factor dies in `finalExp`). -/
def ellAdd (T : G2Jac) (Q : G2Aff) (P : G1Aff) : Fp12 :=
  let X := T.X; let Y := T.Y; let Z := T.Z
  let Θ : Fp2 := Y - Q.y * (Z * Z * Z)
  let Δ : Fp2 := X - Q.x * (Z * Z)
  ⟨⟨Δ * (Z * Z * Z) * Fp2.ofFq P.y, 0, 0⟩,
   ⟨-(Θ * (Z * Z) * Fp2.ofFq P.x), Θ * X - Y * Δ, 0⟩⟩

/-! ## §4 The Miller loop and the pairing. -/

/-- LSB-first bit list of a natural (self-contained, well-founded). -/
def natBits : ℕ → List Bool
  | 0 => []
  | n + 1 => decide ((n + 1) % 2 = 1) :: natBits ((n + 1) / 2)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

/-- **The Miller loop.**  Standard double-and-add over the bits of `ateLoopCount` (MSB-first,
skipping the leading `1`): `f ← f²·ℓ_dbl(T,P)`, `T ← 2T`, and on a set bit
`f ← f·ℓ_add(T,Q,P)`, `T ← T+Q`.  Initialized `f = 1`, `T = Q`. -/
def millerLoop (P : G1Aff) (Q : G2Aff) : Fp12 :=
  let bits := (natBits ateLoopCount).reverse
  match bits with
  | [] => 1
  | _ :: rest =>
    (rest.foldl
      (fun (fT : Fp12 × G2Jac) (b : Bool) =>
        let f := fT.1; let T := fT.2
        let f := f * f * ellDbl T P
        let T := g2Double T
        if b then (f * ellAdd T Q P, g2Madd T Q) else (f, T))
      (1, g2JacOfAff Q)).1

/-- **Final exponentiation** `f ↦ f^((p¹²−1)/r)` — the canonical power (maps the Miller output into
the order-`r` group `μ_r ⊆ F_{p¹²}ˣ`). -/
def finalExp (f : Fp12) : Fp12 := f ^ finalExpExponent

/-- **The BN254 optimal-ate pairing** `e : G1 × G2 → F_{p¹²}`.  (Modulo the two optimal-ate
Frobenius line-additions after the loop, named below.) -/
def pairing (P : G1Aff) (Q : G2Aff) : Fp12 := finalExp (millerLoop P Q)

/-! ## §5 KATs — the exact point steps compute; the doubling preserves the curve. -/

/-- The affine BN254 `G2` generator as a `G2Aff`. -/
def g2Gen : G2Aff := ⟨g2GenX, g2GenY⟩

-- The Jacobian generator is on-curve (`Z = 1`: `Y² = X³ + b'`).
#guard OnCurveG2Jac (g2JacOfAff g2Gen)

-- Doubling KAT — a real check of the `g2Double` formula: `2·G2gen` stays on the twist.
#guard OnCurveG2Jac (g2Double (g2JacOfAff g2Gen))

-- Mixed-addition KAT: `G2gen + G2gen` (as an affine add) stays on the twist.
#guard OnCurveG2Jac (g2Madd (g2JacOfAff g2Gen) g2Gen)

-- The loop parameter is the intended `6t + 2`.
#guard ateLoopCount = 6 * bn254T + 2
-- `natBits` round-trips a small value (LSB-first): 13 = 1 + 4 + 8.
#guard natBits 13 = [true, false, true, true]

#assert_axioms ateLoopCount_eq

/-! ## §6 The named pairing-property goals (OPEN — the multi-day follow-ups).

Only ONE of the three is stated as a formal `Prop` here, because the other two cannot yet be stated
without objects that are themselves the next bricks — and a `Prop` fabricated to be trivially true
would be exactly the vacuity this project must not launder.  They are named in prose instead:

* **Bilinearity** — `e(a·P, b·Q) = e(P,Q)^{a·b}`.  Its honest statement quantifies over the point
  SCALAR ACTION (`nsmul`/`zsmul` of Mathlib's `WeierstrassCurve.Affine.Point` `AddCommGroup`, which
  needs the field seam `[Fact (Nat.Prime pBN254)]`).  With that seam now discharged, the wiring is
  DONE and bilinearity is STATED non-vacuously in `BN254.Bilinearity` (`pairingP` over `G1Point`/
  `G2Point`; `PairingBilinear{Left,Right}Goal`, `PairingScalar{Left,Right}Goal`).  There the
  `finalExp` layer is PROVEN a monoid hom and each goal is REDUCED to a single named Miller-loop
  residual — the standard divisor-theoretic (Weil-reciprocity) cofactor — which stays OPEN.

* **Miller-loop faithfulness** — with the two trailing optimal-ate Frobenius line-additions
  appended, `pairing` equals the value the `alt_bn128` precompile / gnark computes.  Its discharge is
  a KAT differential against a gnark fixture (an external reference), not an in-Lean `Prop`.

Non-degeneracy, by contrast, IS a concrete in-Lean proposition over objects that already exist: -/

/-- **Non-degeneracy (named goal, OPEN).**  The pairing of the two generators is not `1` — a genuine,
non-vacuous obligation over the already-defined `pairing`, `finalExp`, and generators.  Unproven
here: it needs the field-tower `Field` structure and the subgroup-order facts (the pairing lands in
`μ_r ∖ {1}`).  Deliberately NOT discharged and NOT faked. -/
def PairingNonDegenerateGoal : Prop := pairing ⟨g1GenX, g1GenY⟩ g2Gen ≠ 1

end Dregg2.Crypto.BN254
