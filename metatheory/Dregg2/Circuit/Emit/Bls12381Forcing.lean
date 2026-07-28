/-
# Dregg2.Circuit.Emit.Bls12381Forcing — the COMPOSED forcing lemmas for the BLS12-381 tower+curve.

## What this file IS (KAT'd → FORCED, mirroring the SHA fold's rigor)

`Bls12381Tower` proved the atomic Fp/Fp2 gate forcings (`fp{Mul,Add,Sub}Core_forces`, `fp2Mul_forces`)
and `Bls12381TowerExt` KAT'd the Fp6/Fp12/G1/G2 gadgets. This file closes the last rigor gap: it
COMPOSES the atomic forcings UP THE TOWER into whole-structure forcing theorems — the way the SHA
gadget composes `xor3_forces`/`addMod32_forces` into a round, and the way `fp2Mul_forces` already
composed the Fp gate forcings for Fp2. These are PROOFS (no `#guard`, no `native_decide`, no `sorry`):
a chain of ℤ-divisibility (congruence-mod-p) reasoning, NOT a kernel reduction.

The vehicle is a small congruence algebra over ℤ:
  * `CZ u v := p ∣ (u − v)` — "u ≡ v (mod the real BLS12-381 prime p)" — a genuine equivalence + ring
    congruence (`CZ.add/sub/mul`, the last = `Bls12381Tower.dvd_mul_lift`).
  * `Cong2` on `ℤ×ℤ` (Fp2), `Cong6` on `(ℤ×ℤ)³` (Fp6), `Cong12` on `(Fp6)²` — each a congruence for
    the tower operations (`mul2/add2/xi2`, `mul6/add6/sub6/gamma6`, `mul12`), proved from `CZ`.

## ⚑ What was WRONG here until 2026-07-27

This file's 29 theorems contained the string `acceptB` ZERO times. Every one of them took either RAW
GATE EQUATIONS over FREE column bases (`evalH (fpMulHead a0 b0 v0 qv0) a = 0`, with `v0`, `qv0`, …
universally quantified) or the CONCLUSIONS of other lemmas (`Cong2 …`). No generator — not
`fp2MulGadget`, not `g1AddGadget`, not `g1DoubleGadget` — appeared in any statement. The commit
claimed `g1Double`/`g1Add` were "**fully gadget-tied, like `fp2Mul_forces`**"; they were not, and
neither was `fp2Mul_forces`. Nothing here related *the emitted circuit* to *the curve operation*, and
no theorem in the file or in the tree ever applied any of the nine leaves.

§9 is the repair. It supplies the acceptance rungs, and everything that could not be tied in this
pass was RENAMED to what it is, so the names stop claiming more than the statements deliver:

  * TIED to `acceptB <generator>` (§9): `fp2Mul_cong` (`fp2MulGadget`, outputs at the gadget's own
    `fp2MulR0/R1`), `fp2Add_cong`, `fp2Sub_cong`, `mulByXi_cong` (**new — the `xi2` bridge the tower
    theorems assumed and no lemma produced**), `g1Double_forces` (`g1DoubleGadget`, outputs at
    `S+156/234/260`), `g1Add_forces` (`g1AddGadget`, outputs at the triple it RETURNS).
  * RENAMED, raw-gate helper forms — real lemmas, wrong names: `fp2Mul_core_cong`,
    `fp2Add_core_cong`, `fp2Sub_core_cong`, `g1Double_core_forces`, `g1Add_core_forces`. The tied
    rungs above instantiate exactly these at the gadgets' own layouts.
  * RENAMED, NOT TIED — hypotheses are other lemmas' `Cong2`/`Cong6` conclusions, not gates:
    `fp6Mul_of_subop_congs`, `fp12Mul_of_subop_congs`, `g2Double_of_subop_congs`,
    `g2Add_of_subop_congs`. These are the tower/curve ALGEBRA (`mul6`/`mul12`/`g2dblTrace`'s `let`
    chains re-derived through `Cong2.trans`), which is correct and useful, but it is not forcing.
    Tying them is mechanical and is the named next step: split `fp6MulGadget` (17 `++` segments),
    `fp12MulGadget` (9), `g2DoubleGadget` (21), `g2AddGadget` (29) with `acceptB_append` and
    discharge each segment with the §9 atoms. It is NOT done here.

## The residual every rung in this file carries

The congruence is mod `p` on the ℤ readings. Every gadget here emits VALUE gates only — no
`fpLimbRange`, no `binGate` — so the limb encoding is not pinned to a canonical representative and
the carry/borrow columns are unconstrained integers. A tied theorem says "the output columns are
congruent mod `p` to the point operation", not "the output columns are the canonical encoding of it".

## What remains (the pairing arc)

The Miller-loop and final-exponentiation GENERATORS are not built yet. This file claims exactly the
tower+curve layer, not a pairing.

## Axiom hygiene

§10 carries `#assert_axioms` for all 34 named results — the check RUNS. The previous header asserted
`#assert_axioms`-cleanliness while the file contained ZERO `#assert_axioms` commands (the measurement
was real but ephemeral: one `#print axioms` on a throwaway `/tmp` file, written into the docstring as
if it were a file property). It also said "standalone (NOT imported by the truncated `Dregg2.lean`)"
— false: `Dregg2.lean:1535` imports it. Both corrected.
-/
import Dregg2.Circuit.Emit.Bls12381TowerExt

namespace Dregg2.Circuit.Emit.Bls12381Forcing

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.Bls12381Tower
open Dregg2.Circuit.Emit.Bls12381TowerExt (mulByXiGadget fp2AddGadget fp2SubGadget g1DoubleGadget g1AddGadget)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2)

set_option autoImplicit false

/-! ## §0 — The Fp congruence `CZ` (mod the real BLS12-381 prime) and its ring laws. -/

/-- `u ≡ v (mod p)` over ℤ. -/
def CZ (u v : ℤ) : Prop := (p : ℤ) ∣ (u - v)

namespace CZ

theorem refl (u : ℤ) : CZ u u := by unfold CZ; simp
theorem symm {u v : ℤ} (h : CZ u v) : CZ v u := by
  unfold CZ at *; rw [show v - u = -(u - v) by ring]; exact dvd_neg.mpr h
theorem trans {u v w : ℤ} (h1 : CZ u v) (h2 : CZ v w) : CZ u w := by
  unfold CZ at *; rw [show u - w = (u - v) + (v - w) by ring]; exact dvd_add h1 h2
theorem add {a a' b b' : ℤ} (h1 : CZ a a') (h2 : CZ b b') : CZ (a + b) (a' + b') := by
  unfold CZ at *; rw [show a + b - (a' + b') = (a - a') + (b - b') by ring]; exact dvd_add h1 h2
theorem sub {a a' b b' : ℤ} (h1 : CZ a a') (h2 : CZ b b') : CZ (a - b) (a' - b') := by
  unfold CZ at *; rw [show a - b - (a' - b') = (a - a') - (b - b') by ring]; exact dvd_sub h1 h2
theorem mul {a a' b b' : ℤ} (h1 : CZ a a') (h2 : CZ b b') : CZ (a * b) (a' * b') :=
  dvd_mul_lift h1 h2   -- from Bls12381Tower

end CZ

/-! ## §1 — `Cong2` (Fp2 = ℤ×ℤ) with `add2/sub2/mul2/xi2` and their congruence laws. -/

abbrev C2 := Nat × Nat
/-- The ℤ value of an Fp2 element at column-bases `c`. -/
def V2 (a : Assignment) (c : C2) : ℤ × ℤ := (fpVal a c.1, fpVal a c.2)

def add2 (u v : ℤ × ℤ) : ℤ × ℤ := (u.1 + v.1, u.2 + v.2)
def sub2 (u v : ℤ × ℤ) : ℤ × ℤ := (u.1 - v.1, u.2 - v.2)
def mul2 (u v : ℤ × ℤ) : ℤ × ℤ := (u.1 * v.1 - u.2 * v.2, u.1 * v.2 + u.2 * v.1)
/-- Multiply by `ξ = u+1`. -/
def xi2 (u : ℤ × ℤ) : ℤ × ℤ := (u.1 - u.2, u.1 + u.2)

/-- Fp2 congruence mod `p` (coordinate-wise). -/
def Cong2 (u v : ℤ × ℤ) : Prop := CZ u.1 v.1 ∧ CZ u.2 v.2

namespace Cong2
theorem refl (u : ℤ × ℤ) : Cong2 u u := ⟨CZ.refl _, CZ.refl _⟩
theorem trans {u v w} (h1 : Cong2 u v) (h2 : Cong2 v w) : Cong2 u w :=
  ⟨CZ.trans h1.1 h2.1, CZ.trans h1.2 h2.2⟩
theorem add {u u' v v'} (h1 : Cong2 u u') (h2 : Cong2 v v') : Cong2 (add2 u v) (add2 u' v') :=
  ⟨CZ.add h1.1 h2.1, CZ.add h1.2 h2.2⟩
theorem sub {u u' v v'} (h1 : Cong2 u u') (h2 : Cong2 v v') : Cong2 (sub2 u v) (sub2 u' v') :=
  ⟨CZ.sub h1.1 h2.1, CZ.sub h1.2 h2.2⟩
theorem xi {u u'} (h : Cong2 u u') : Cong2 (xi2 u) (xi2 u') :=
  ⟨CZ.sub h.1 h.2, CZ.add h.1 h.2⟩
theorem mul {u u' v v'} (h1 : Cong2 u u') (h2 : Cong2 v v') : Cong2 (mul2 u v) (mul2 u' v') :=
  ⟨CZ.sub (CZ.mul h1.1 h2.1) (CZ.mul h1.2 h2.2), CZ.add (CZ.mul h1.1 h2.2) (CZ.mul h1.2 h2.1)⟩
end Cong2

/-! ## §2 — The atomic bridge: `fp2MulGadget`'s gates FORCE the Fp2-product congruence. -/

/-- **`fp2Mul_core_cong`** — the 8 raw gate satisfactions of one `fp2MulGadget` (the same hypotheses
`fp2Mul_forces` takes) force `Cong2 (output) (mul2 inputs)` — the composable form the tower theorems
consume. -/
theorem fp2Mul_core_cong (a : Assignment) (a0 a1 b0 b1 v0 v1 sa sb v2 w r0 r1
    qv0 qv1 qv2 csa csb cw br0 br1 : Nat)
    (h0 : evalH (fpMulHead a0 b0 v0 qv0) a = 0)
    (h1 : evalH (fpMulHead a1 b1 v1 qv1) a = 0)
    (h2 : evalH (fpAddHead a0 a1 sa csa) a = 0)
    (h3 : evalH (fpAddHead b0 b1 sb csb) a = 0)
    (h4 : evalH (fpMulHead sa sb v2 qv2) a = 0)
    (h5 : evalH (fpAddHead v0 v1 w cw) a = 0)
    (h6 : evalH (fpSubHead v0 v1 r0 br0) a = 0)
    (h7 : evalH (fpSubHead v2 w r1 br1) a = 0) :
    Cong2 (V2 a (r0, r1)) (mul2 (V2 a (a0, a1)) (V2 a (b0, b1))) := by
  obtain ⟨e1, e2⟩ := fp2Mul_forces a a0 a1 b0 b1 v0 v1 sa sb v2 w r0 r1
    qv0 qv1 qv2 csa csb cw br0 br1 h0 h1 h2 h3 h4 h5 h6 h7
  exact ⟨CZ.symm e1, CZ.symm e2⟩

/-! ## §3 — `fp6Mul_of_subop_congs`: the Fp6 product gadget forces all 3 Fp2 coordinates.

`F6z = (Fp2)³`. `mul6` is the schoolbook Fp6 product with the `v³ = ξ` fold. The hypotheses are the
per-sub-operation congruences the gadget's 9 `fp2Mul_core_cong` + 6 `fp2Add` + 2 `mulByXi` deliver. -/

abbrev F6z := (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ)

def add6 (A B : F6z) : F6z := (add2 A.1 B.1, add2 A.2.1 B.2.1, add2 A.2.2 B.2.2)
def sub6 (A B : F6z) : F6z := (sub2 A.1 B.1, sub2 A.2.1 B.2.1, sub2 A.2.2 B.2.2)
/-- Multiply an Fp6 by `γ = v`: `(ξ·c2, c0, c1)`. -/
def gamma6 (C : F6z) : F6z := (xi2 C.2.2, C.1, C.2.1)
/-- Fp6 schoolbook product with the `v³ = ξ` fold. -/
def mul6 (A B : F6z) : F6z :=
  ( add2 (mul2 A.1 B.1) (xi2 (add2 (mul2 A.2.1 B.2.2) (mul2 A.2.2 B.2.1)))
  , add2 (add2 (mul2 A.1 B.2.1) (mul2 A.2.1 B.1)) (xi2 (mul2 A.2.2 B.2.2))
  , add2 (add2 (mul2 A.1 B.2.2) (mul2 A.2.1 B.2.1)) (mul2 A.2.2 B.1) )

/-- Fp6 congruence mod `p`. -/
def Cong6 (A B : F6z) : Prop := Cong2 A.1 B.1 ∧ Cong2 A.2.1 B.2.1 ∧ Cong2 A.2.2 B.2.2

namespace Cong6
theorem trans {A B C : F6z} (h1 : Cong6 A B) (h2 : Cong6 B C) : Cong6 A C :=
  ⟨Cong2.trans h1.1 h2.1, Cong2.trans h1.2.1 h2.2.1, Cong2.trans h1.2.2 h2.2.2⟩
theorem add {A A' B B'} (h1 : Cong6 A A') (h2 : Cong6 B B') : Cong6 (add6 A B) (add6 A' B') :=
  ⟨Cong2.add h1.1 h2.1, Cong2.add h1.2.1 h2.2.1, Cong2.add h1.2.2 h2.2.2⟩
theorem sub {A A' B B'} (h1 : Cong6 A A') (h2 : Cong6 B B') : Cong6 (sub6 A B) (sub6 A' B') :=
  ⟨Cong2.sub h1.1 h2.1, Cong2.sub h1.2.1 h2.2.1, Cong2.sub h1.2.2 h2.2.2⟩
theorem gamma {A A'} (h : Cong6 A A') : Cong6 (gamma6 A) (gamma6 A') :=
  ⟨Cong2.xi h.2.2, h.1, h.2.1⟩
theorem mul {A A' B B'} (h1 : Cong6 A A') (h2 : Cong6 B B') : Cong6 (mul6 A B) (mul6 A' B') :=
  ⟨ Cong2.add (Cong2.mul h1.1 h2.1)
      (Cong2.xi (Cong2.add (Cong2.mul h1.2.1 h2.2.2) (Cong2.mul h1.2.2 h2.2.1)))
  , Cong2.add (Cong2.add (Cong2.mul h1.1 h2.2.1) (Cong2.mul h1.2.1 h2.1))
      (Cong2.xi (Cong2.mul h1.2.2 h2.2.2))
  , Cong2.add (Cong2.add (Cong2.mul h1.1 h2.2.2) (Cong2.mul h1.2.1 h2.2.1))
      (Cong2.mul h1.2.2 h2.1) ⟩
end Cong6

/-- The ℤ value of an Fp6 element at its 3 Fp2 column-bases. -/
def V6 (a : Assignment) (x y z : C2) : F6z := (V2 a x, V2 a y, V2 a z)

/-- **`fp6Mul_of_subop_congs`** — the 88-gate `fp6MulGadget` forces the Fp6 product in all 3 Fp2 coordinates.
Hypotheses = the sub-operation congruences (9 `fp2Mul_core_cong` products, 5 Fp2 adds, 2 `mulByXi`, 3 output
adds); conclusion = the reconstructed output `(c0,c1,c2)` ≡ `mul6` of the reconstructed inputs. -/
theorem fp6Mul_of_subop_congs (a : Assignment) (a0 a1 a2 b0 b1 b2 : C2)
    (p00 p11 p22 p12 p21 p01 p10 p02 p20 : C2) (s1 x1 s2 x2 s3 c0 c1 c2 : C2)
    (hp00 : Cong2 (V2 a p00) (mul2 (V2 a a0) (V2 a b0)))
    (hp11 : Cong2 (V2 a p11) (mul2 (V2 a a1) (V2 a b1)))
    (hp22 : Cong2 (V2 a p22) (mul2 (V2 a a2) (V2 a b2)))
    (hp12 : Cong2 (V2 a p12) (mul2 (V2 a a1) (V2 a b2)))
    (hp21 : Cong2 (V2 a p21) (mul2 (V2 a a2) (V2 a b1)))
    (hp01 : Cong2 (V2 a p01) (mul2 (V2 a a0) (V2 a b1)))
    (hp10 : Cong2 (V2 a p10) (mul2 (V2 a a1) (V2 a b0)))
    (hp02 : Cong2 (V2 a p02) (mul2 (V2 a a0) (V2 a b2)))
    (hp20 : Cong2 (V2 a p20) (mul2 (V2 a a2) (V2 a b0)))
    (hs1 : Cong2 (V2 a s1) (add2 (V2 a p12) (V2 a p21)))
    (hx1 : Cong2 (V2 a x1) (xi2 (V2 a s1)))
    (hc0 : Cong2 (V2 a c0) (add2 (V2 a p00) (V2 a x1)))
    (hs2 : Cong2 (V2 a s2) (add2 (V2 a p01) (V2 a p10)))
    (hx2 : Cong2 (V2 a x2) (xi2 (V2 a p22)))
    (hc1 : Cong2 (V2 a c1) (add2 (V2 a s2) (V2 a x2)))
    (hs3 : Cong2 (V2 a s3) (add2 (V2 a p02) (V2 a p11)))
    (hc2 : Cong2 (V2 a c2) (add2 (V2 a s3) (V2 a p20))) :
    Cong6 (V6 a c0 c1 c2) (mul6 (V6 a a0 a1 a2) (V6 a b0 b1 b2)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Cong2.trans hc0 (Cong2.add hp00
      (Cong2.trans hx1 (Cong2.xi (Cong2.trans hs1 (Cong2.add hp12 hp21)))))
  · exact Cong2.trans hc1 (Cong2.add
      (Cong2.trans hs2 (Cong2.add hp01 hp10)) (Cong2.trans hx2 (Cong2.xi hp22)))
  · exact Cong2.trans hc2 (Cong2.add (Cong2.trans hs3 (Cong2.add hp02 hp11)) hp20)

/-! ## §4 — `fp12Mul_of_subop_congs`: the Fp12 product gadget forces both Fp6 coordinates. -/

abbrev F12z := F6z × F6z
def mul12 (A B : F12z) : F12z :=
  ( add6 (mul6 A.1 B.1) (gamma6 (mul6 A.2 B.2))
  , sub6 (mul6 (add6 A.1 A.2) (add6 B.1 B.2)) (add6 (mul6 A.1 B.1) (mul6 A.2 B.2)) )
def Cong12 (A B : F12z) : Prop := Cong6 A.1 B.1 ∧ Cong6 A.2 B.2

/-- The ℤ value of an Fp12 element at its 2 Fp6 bases. -/
def V12 (a : Assignment) (A B : C2 × C2 × C2) : F12z :=
  ((V2 a A.1, V2 a A.2.1, V2 a A.2.2), (V2 a B.1, V2 a B.2.1, V2 a B.2.2))

/-- **`fp12Mul_of_subop_congs`** — the 296-gate `fp12MulGadget` forces the Fp12 product in both Fp6 coords.
Hypotheses = the sub-operation Fp6 congruences (3 `fp6Mul_of_subop_congs` products, 2 adds, the γ fold, the two
output add/sub); conclusion = `(d0,d1)` ≡ `mul12` of the reconstructed inputs. Uses `Cong6.mul` to lift
`sa·sb ≡ (a0+a1)(b0+b1)`. -/
theorem fp12Mul_of_subop_congs (a : Assignment) (a0 a1 b0 b1 : C2 × C2 × C2)
    (v0 v1 v2 sa sb gv1 d0 w d1 : C2 × C2 × C2)
    (hv0 : Cong6 (V12 a v0 v0).1 (mul6 (V12 a a0 a0).1 (V12 a b0 b0).1))
    (hv1 : Cong6 (V12 a v1 v1).1 (mul6 (V12 a a1 a1).1 (V12 a b1 b1).1))
    (hsa : Cong6 (V12 a sa sa).1 (add6 (V12 a a0 a0).1 (V12 a a1 a1).1))
    (hsb : Cong6 (V12 a sb sb).1 (add6 (V12 a b0 b0).1 (V12 a b1 b1).1))
    (hv2 : Cong6 (V12 a v2 v2).1 (mul6 (V12 a sa sa).1 (V12 a sb sb).1))
    (hgv1 : Cong6 (V12 a gv1 gv1).1 (gamma6 (V12 a v1 v1).1))
    (hd0 : Cong6 (V12 a d0 d0).1 (add6 (V12 a v0 v0).1 (V12 a gv1 gv1).1))
    (hw : Cong6 (V12 a w w).1 (add6 (V12 a v0 v0).1 (V12 a v1 v1).1))
    (hd1 : Cong6 (V12 a d1 d1).1 (sub6 (V12 a v2 v2).1 (V12 a w w).1)) :
    Cong12 (V12 a d0 d1) (mul12 (V12 a a0 a1) (V12 a b0 b1)) := by
  refine ⟨?_, ?_⟩
  · exact Cong6.trans hd0 (Cong6.add hv0 (Cong6.trans hgv1 (Cong6.gamma hv1)))
  · exact Cong6.trans hd1 (Cong6.sub
      (Cong6.trans hv2 (Cong6.mul hsa hsb)) (Cong6.trans hw (Cong6.add hv0 hv1)))

/-! ## §5 — Curve forcing over Fp: the Jacobian G1 gadgets force the ℤ point-op.

At the Fp level the sub-operations ARE the gates, so these take the raw gate satisfactions (like
`fp2Mul_forces`) and conclude the reconstructed output ≡ the ℤ formula, via `CZ` chaining. `g1dblZ`
mirrors `g1DoubleGadget` term-for-term. -/

/-- ℤ Jacobian doubling (a=0), mirroring `g1DoubleGadget`. -/
def g1dblZ (X Y Z : ℤ) : ℤ × ℤ × ℤ :=
  let A := X * X; let B := Y * Y; let C := B * B
  let XB := X + B; let XB2 := XB * XB
  let T1 := XB2 - A; let T2 := T1 - C
  let D := T2 + T2; let A2 := A + A; let E := A2 + A
  let F := E * E; let D2 := D + D; let X3 := F - D2
  let DX3 := D - X3; let EE := E * DX3
  let C2 := C + C; let C4 := C2 + C2; let C8 := C4 + C4
  let Y3 := EE - C8; let YZ := Y * Z; let Z3 := YZ + YZ
  (X3, Y3, Z3)

/-- Turn a `fpMulCore`/`fpAddCore`/`fpSubCore` satisfaction into the reconstructed-output `CZ` fact
(output ≡ the op of the inputs). -/
private theorem mulCZ {a : Assignment} {x y z q : Nat} (h : evalH (fpMulHead x y z q) a = 0) :
    CZ (fpVal a z) (fpVal a x * fpVal a y) := CZ.symm (fpMulCore_forces a x y z q h)
private theorem addCZ {a : Assignment} {x y z c : Nat} (h : evalH (fpAddHead x y z c) a = 0) :
    CZ (fpVal a z) (fpVal a x + fpVal a y) := CZ.symm (fpAddCore_forces a x y z c h)
private theorem subCZ {a : Assignment} {x y z c : Nat} (h : evalH (fpSubHead x y z c) a = 0) :
    CZ (fpVal a z) (fpVal a x - fpVal a y) := CZ.symm (fpSubCore_forces a x y z c h)

/-- **`g1Double_core_forces`** — the 21-gate `g1DoubleGadget` forces `(X3,Y3,Z3) ≡ g1dblZ (X,Y,Z)` over Fp,
from the raw gate satisfactions. -/
theorem g1Double_core_forces (a : Assignment)
    (Xc Yc Zc Ac Bc Cc XBc XB2c T1c T2c Dc A2c Ec Fc D2c X3c DX3c EEc C2c C4c C8c Y3c YZc Z3c
     qAc qBc qCc qXB2c qFc qEEc qYZc cXBc bT1c bT2c cDc cA2c cEc cD2c bX3c bDX3c cC2c cC4c cC8c
     bY3c cZ3c : Nat)
    (hA : evalH (fpMulHead Xc Xc Ac qAc) a = 0)
    (hB : evalH (fpMulHead Yc Yc Bc qBc) a = 0)
    (hC : evalH (fpMulHead Bc Bc Cc qCc) a = 0)
    (hXB : evalH (fpAddHead Xc Bc XBc cXBc) a = 0)
    (hXB2 : evalH (fpMulHead XBc XBc XB2c qXB2c) a = 0)
    (hT1 : evalH (fpSubHead XB2c Ac T1c bT1c) a = 0)
    (hT2 : evalH (fpSubHead T1c Cc T2c bT2c) a = 0)
    (hD : evalH (fpAddHead T2c T2c Dc cDc) a = 0)
    (hA2 : evalH (fpAddHead Ac Ac A2c cA2c) a = 0)
    (hE : evalH (fpAddHead A2c Ac Ec cEc) a = 0)
    (hF : evalH (fpMulHead Ec Ec Fc qFc) a = 0)
    (hD2 : evalH (fpAddHead Dc Dc D2c cD2c) a = 0)
    (hX3 : evalH (fpSubHead Fc D2c X3c bX3c) a = 0)
    (hDX3 : evalH (fpSubHead Dc X3c DX3c bDX3c) a = 0)
    (hEE : evalH (fpMulHead Ec DX3c EEc qEEc) a = 0)
    (hC2 : evalH (fpAddHead Cc Cc C2c cC2c) a = 0)
    (hC4 : evalH (fpAddHead C2c C2c C4c cC4c) a = 0)
    (hC8 : evalH (fpAddHead C4c C4c C8c cC8c) a = 0)
    (hY3 : evalH (fpSubHead EEc C8c Y3c bY3c) a = 0)
    (hYZ : evalH (fpMulHead Yc Zc YZc qYZc) a = 0)
    (hZ3 : evalH (fpAddHead YZc YZc Z3c cZ3c) a = 0) :
    CZ (fpVal a X3c) (g1dblZ (fpVal a Xc) (fpVal a Yc) (fpVal a Zc)).1
    ∧ CZ (fpVal a Y3c) (g1dblZ (fpVal a Xc) (fpVal a Yc) (fpVal a Zc)).2.1
    ∧ CZ (fpVal a Z3c) (g1dblZ (fpVal a Xc) (fpVal a Yc) (fpVal a Zc)).2.2 := by
  -- reconstructed intermediates ≡ their ℤ formulas, bottom-up
  have eA : CZ (fpVal a Ac) (fpVal a Xc * fpVal a Xc) := mulCZ hA
  have eB : CZ (fpVal a Bc) (fpVal a Yc * fpVal a Yc) := mulCZ hB
  have eC : CZ (fpVal a Cc) (fpVal a Bc * fpVal a Bc) := mulCZ hC
  have eXB : CZ (fpVal a XBc) (fpVal a Xc + fpVal a Bc) := addCZ hXB
  have eXB2 : CZ (fpVal a XB2c) (fpVal a XBc * fpVal a XBc) := mulCZ hXB2
  have eT1 : CZ (fpVal a T1c) (fpVal a XB2c - fpVal a Ac) := subCZ hT1
  have eT2 : CZ (fpVal a T2c) (fpVal a T1c - fpVal a Cc) := subCZ hT2
  have eD : CZ (fpVal a Dc) (fpVal a T2c + fpVal a T2c) := addCZ hD
  have eA2 : CZ (fpVal a A2c) (fpVal a Ac + fpVal a Ac) := addCZ hA2
  have eE : CZ (fpVal a Ec) (fpVal a A2c + fpVal a Ac) := addCZ hE
  have eF : CZ (fpVal a Fc) (fpVal a Ec * fpVal a Ec) := mulCZ hF
  have eD2 : CZ (fpVal a D2c) (fpVal a Dc + fpVal a Dc) := addCZ hD2
  have eX3 : CZ (fpVal a X3c) (fpVal a Fc - fpVal a D2c) := subCZ hX3
  have eDX3 : CZ (fpVal a DX3c) (fpVal a Dc - fpVal a X3c) := subCZ hDX3
  have eEE : CZ (fpVal a EEc) (fpVal a Ec * fpVal a DX3c) := mulCZ hEE
  have eC2 : CZ (fpVal a C2c) (fpVal a Cc + fpVal a Cc) := addCZ hC2
  have eC4 : CZ (fpVal a C4c) (fpVal a C2c + fpVal a C2c) := addCZ hC4
  have eC8 : CZ (fpVal a C8c) (fpVal a C4c + fpVal a C4c) := addCZ hC8
  have eY3 : CZ (fpVal a Y3c) (fpVal a EEc - fpVal a C8c) := subCZ hY3
  have eYZ : CZ (fpVal a YZc) (fpVal a Yc * fpVal a Zc) := mulCZ hYZ
  have eZ3 : CZ (fpVal a Z3c) (fpVal a YZc + fpVal a YZc) := addCZ hZ3
  -- abbreviations for the ℤ formula, matching g1dblZ's lets
  set X := fpVal a Xc; set Y := fpVal a Yc; set Z := fpVal a Zc
  have fA : CZ (fpVal a Ac) (X * X) := eA
  have fB : CZ (fpVal a Bc) (Y * Y) := eB
  have fC : CZ (fpVal a Cc) ((Y * Y) * (Y * Y)) := CZ.trans eC (CZ.mul fB fB)
  have fXB : CZ (fpVal a XBc) (X + Y * Y) := CZ.trans eXB (CZ.add (CZ.refl X) fB)
  have fXB2 : CZ (fpVal a XB2c) ((X + Y * Y) * (X + Y * Y)) := CZ.trans eXB2 (CZ.mul fXB fXB)
  have fT1 : CZ (fpVal a T1c) ((X + Y * Y) * (X + Y * Y) - X * X) :=
    CZ.trans eT1 (CZ.sub fXB2 fA)
  have fT2 : CZ (fpVal a T2c) ((X + Y * Y) * (X + Y * Y) - X * X - (Y * Y) * (Y * Y)) :=
    CZ.trans eT2 (CZ.sub fT1 fC)
  have fD : CZ (fpVal a Dc)
      (((X + Y * Y) * (X + Y * Y) - X * X - (Y * Y) * (Y * Y))
        + ((X + Y * Y) * (X + Y * Y) - X * X - (Y * Y) * (Y * Y))) :=
    CZ.trans eD (CZ.add fT2 fT2)
  have fA2 : CZ (fpVal a A2c) (X * X + X * X) := CZ.trans eA2 (CZ.add fA fA)
  have fE : CZ (fpVal a Ec) (X * X + X * X + X * X) := CZ.trans eE (CZ.add fA2 fA)
  have fF : CZ (fpVal a Fc) ((X * X + X * X + X * X) * (X * X + X * X + X * X)) :=
    CZ.trans eF (CZ.mul fE fE)
  have fD2 : CZ (fpVal a D2c)
      ((((X + Y * Y) * (X + Y * Y) - X * X - (Y * Y) * (Y * Y))
        + ((X + Y * Y) * (X + Y * Y) - X * X - (Y * Y) * (Y * Y)))
       + (((X + Y * Y) * (X + Y * Y) - X * X - (Y * Y) * (Y * Y))
        + ((X + Y * Y) * (X + Y * Y) - X * X - (Y * Y) * (Y * Y)))) :=
    CZ.trans eD2 (CZ.add fD fD)
  have fX3 : CZ (fpVal a X3c) (g1dblZ X Y Z).1 := CZ.trans eX3 (CZ.sub fF fD2)
  have fDX3 : CZ (fpVal a DX3c)
      ((((X + Y * Y) * (X + Y * Y) - X * X - (Y * Y) * (Y * Y))
        + ((X + Y * Y) * (X + Y * Y) - X * X - (Y * Y) * (Y * Y))) - (g1dblZ X Y Z).1) :=
    CZ.trans eDX3 (CZ.sub fD fX3)
  have fEE : CZ (fpVal a EEc)
      ((X * X + X * X + X * X)
        * ((((X + Y * Y) * (X + Y * Y) - X * X - (Y * Y) * (Y * Y))
          + ((X + Y * Y) * (X + Y * Y) - X * X - (Y * Y) * (Y * Y))) - (g1dblZ X Y Z).1)) :=
    CZ.trans eEE (CZ.mul fE fDX3)
  have fC2 : CZ (fpVal a C2c) ((Y * Y) * (Y * Y) + (Y * Y) * (Y * Y)) := CZ.trans eC2 (CZ.add fC fC)
  have fC4 : CZ (fpVal a C4c)
      (((Y * Y) * (Y * Y) + (Y * Y) * (Y * Y)) + ((Y * Y) * (Y * Y) + (Y * Y) * (Y * Y))) :=
    CZ.trans eC4 (CZ.add fC2 fC2)
  have fC8 : CZ (fpVal a C8c)
      ((((Y * Y) * (Y * Y) + (Y * Y) * (Y * Y)) + ((Y * Y) * (Y * Y) + (Y * Y) * (Y * Y)))
       + (((Y * Y) * (Y * Y) + (Y * Y) * (Y * Y)) + ((Y * Y) * (Y * Y) + (Y * Y) * (Y * Y)))) :=
    CZ.trans eC8 (CZ.add fC4 fC4)
  have fY3 : CZ (fpVal a Y3c) (g1dblZ X Y Z).2.1 := CZ.trans eY3 (CZ.sub fEE fC8)
  have fYZ : CZ (fpVal a YZc) (Y * Z) := CZ.trans eYZ (CZ.refl _)
  have fZ3 : CZ (fpVal a Z3c) (g1dblZ X Y Z).2.2 := CZ.trans eZ3 (CZ.add fYZ fYZ)
  exact ⟨fX3, fY3, fZ3⟩

/-! ## §6 — Fp2-operation congruence bridges (what the G2 gadgets' sub-`fp2` gates deliver). -/

/-- The two `fpAddCore` of one `fp2AddGadget` force `Cong2 (output) (add2 inputs)`. -/
theorem fp2Add_core_cong (a : Assignment) (a0 a1 b0 b1 r0 r1 c0 c1 : Nat)
    (h0 : evalH (fpAddHead a0 b0 r0 c0) a = 0) (h1 : evalH (fpAddHead a1 b1 r1 c1) a = 0) :
    Cong2 (V2 a (r0, r1)) (add2 (V2 a (a0, a1)) (V2 a (b0, b1))) := ⟨addCZ h0, addCZ h1⟩

/-- The two `fpSubCore` of one `fp2SubGadget` force `Cong2 (output) (sub2 inputs)`. -/
theorem fp2Sub_core_cong (a : Assignment) (a0 a1 b0 b1 r0 r1 c0 c1 : Nat)
    (h0 : evalH (fpSubHead a0 b0 r0 c0) a = 0) (h1 : evalH (fpSubHead a1 b1 r1 c1) a = 0) :
    Cong2 (V2 a (r0, r1)) (sub2 (V2 a (a0, a1)) (V2 a (b0, b1))) := ⟨subCZ h0, subCZ h1⟩

/-! ## §7 — Curve forcing over Fp2: the Jacobian G2 gadgets force the ℤ point-op.

The G2 sub-operations are `fp2` gadgets (2–8 gates each), so these take the per-`fp2`-operation
congruences (exactly `fp2Mul_core_cong` / `fp2Add_core_cong` / `fp2Sub_core_cong` deliver) and conclude the output ≡
the ℤ Fp2 point-op. `g2dblTrace` is a named intermediate trace mirroring `g2DoubleGadget` term-for-
term, so each field is defeq-reducible and the chain avoids hand-expanding the deep formula. -/

/-- A Jacobian-doubling intermediate trace over a field `R` (mirrors the doubling gadget's columns). -/
structure DblT (R : Type) where
  A : R
  B : R
  C : R
  XB : R
  XB2 : R
  T1 : R
  T2 : R
  D : R
  A2 : R
  E : R
  F : R
  D2 : R
  X3 : R
  DX3 : R
  EE : R
  C2 : R
  C4 : R
  C8 : R
  Y3 : R
  YZ : R
  Z3 : R

/-- ℤ Fp2 Jacobian doubling trace, mirroring `g2DoubleGadget`. -/
def g2dblTrace (X Y Z : ℤ × ℤ) : DblT (ℤ × ℤ) :=
  let A := mul2 X X; let B := mul2 Y Y; let C := mul2 B B
  let XB := add2 X B; let XB2 := mul2 XB XB
  let T1 := sub2 XB2 A; let T2 := sub2 T1 C
  let D := add2 T2 T2; let A2 := add2 A A; let E := add2 A2 A
  let F := mul2 E E; let D2 := add2 D D; let X3 := sub2 F D2
  let DX3 := sub2 D X3; let EE := mul2 E DX3
  let C2 := add2 C C; let C4 := add2 C2 C2; let C8 := add2 C4 C4
  let Y3 := sub2 EE C8; let YZ := mul2 Y Z; let Z3 := add2 YZ YZ
  { A, B, C, XB, XB2, T1, T2, D, A2, E, F, D2, X3, DX3, EE, C2, C4, C8, Y3, YZ, Z3 }

/-- **`g2Double_of_subop_congs`** — the `g2DoubleGadget` forces `(X3,Y3,Z3) ≡ g2dblTrace (X,Y,Z)` over Fp2,
from the per-`fp2`-operation congruences. -/
theorem g2Double_of_subop_congs (a : Assignment)
    (Xc Yc Zc Ac Bc Cc XBc XB2c T1c T2c Dc A2c Ec Fc D2c X3c DX3c EEc C2c C4c C8c Y3c YZc Z3c : C2)
    (hA : Cong2 (V2 a Ac) (mul2 (V2 a Xc) (V2 a Xc)))
    (hB : Cong2 (V2 a Bc) (mul2 (V2 a Yc) (V2 a Yc)))
    (hC : Cong2 (V2 a Cc) (mul2 (V2 a Bc) (V2 a Bc)))
    (hXB : Cong2 (V2 a XBc) (add2 (V2 a Xc) (V2 a Bc)))
    (hXB2 : Cong2 (V2 a XB2c) (mul2 (V2 a XBc) (V2 a XBc)))
    (hT1 : Cong2 (V2 a T1c) (sub2 (V2 a XB2c) (V2 a Ac)))
    (hT2 : Cong2 (V2 a T2c) (sub2 (V2 a T1c) (V2 a Cc)))
    (hD : Cong2 (V2 a Dc) (add2 (V2 a T2c) (V2 a T2c)))
    (hA2 : Cong2 (V2 a A2c) (add2 (V2 a Ac) (V2 a Ac)))
    (hE : Cong2 (V2 a Ec) (add2 (V2 a A2c) (V2 a Ac)))
    (hF : Cong2 (V2 a Fc) (mul2 (V2 a Ec) (V2 a Ec)))
    (hD2 : Cong2 (V2 a D2c) (add2 (V2 a Dc) (V2 a Dc)))
    (hX3 : Cong2 (V2 a X3c) (sub2 (V2 a Fc) (V2 a D2c)))
    (hDX3 : Cong2 (V2 a DX3c) (sub2 (V2 a Dc) (V2 a X3c)))
    (hEE : Cong2 (V2 a EEc) (mul2 (V2 a Ec) (V2 a DX3c)))
    (hC2 : Cong2 (V2 a C2c) (add2 (V2 a Cc) (V2 a Cc)))
    (hC4 : Cong2 (V2 a C4c) (add2 (V2 a C2c) (V2 a C2c)))
    (hC8 : Cong2 (V2 a C8c) (add2 (V2 a C4c) (V2 a C4c)))
    (hY3 : Cong2 (V2 a Y3c) (sub2 (V2 a EEc) (V2 a C8c)))
    (hYZ : Cong2 (V2 a YZc) (mul2 (V2 a Yc) (V2 a Zc)))
    (hZ3 : Cong2 (V2 a Z3c) (add2 (V2 a YZc) (V2 a YZc))) :
    Cong2 (V2 a X3c) (g2dblTrace (V2 a Xc) (V2 a Yc) (V2 a Zc)).X3
    ∧ Cong2 (V2 a Y3c) (g2dblTrace (V2 a Xc) (V2 a Yc) (V2 a Zc)).Y3
    ∧ Cong2 (V2 a Z3c) (g2dblTrace (V2 a Xc) (V2 a Yc) (V2 a Zc)).Z3 := by
  let T := g2dblTrace (V2 a Xc) (V2 a Yc) (V2 a Zc)
  have fA : Cong2 (V2 a Ac) T.A := hA
  have fB : Cong2 (V2 a Bc) T.B := hB
  have fC : Cong2 (V2 a Cc) T.C := Cong2.trans hC (Cong2.mul fB fB)
  have fXB : Cong2 (V2 a XBc) T.XB := Cong2.trans hXB (Cong2.add (Cong2.refl _) fB)
  have fXB2 : Cong2 (V2 a XB2c) T.XB2 := Cong2.trans hXB2 (Cong2.mul fXB fXB)
  have fT1 : Cong2 (V2 a T1c) T.T1 := Cong2.trans hT1 (Cong2.sub fXB2 fA)
  have fT2 : Cong2 (V2 a T2c) T.T2 := Cong2.trans hT2 (Cong2.sub fT1 fC)
  have fD : Cong2 (V2 a Dc) T.D := Cong2.trans hD (Cong2.add fT2 fT2)
  have fA2 : Cong2 (V2 a A2c) T.A2 := Cong2.trans hA2 (Cong2.add fA fA)
  have fE : Cong2 (V2 a Ec) T.E := Cong2.trans hE (Cong2.add fA2 fA)
  have fF : Cong2 (V2 a Fc) T.F := Cong2.trans hF (Cong2.mul fE fE)
  have fD2 : Cong2 (V2 a D2c) T.D2 := Cong2.trans hD2 (Cong2.add fD fD)
  have fX3 : Cong2 (V2 a X3c) T.X3 := Cong2.trans hX3 (Cong2.sub fF fD2)
  have fDX3 : Cong2 (V2 a DX3c) T.DX3 := Cong2.trans hDX3 (Cong2.sub fD fX3)
  have fEE : Cong2 (V2 a EEc) T.EE := Cong2.trans hEE (Cong2.mul fE fDX3)
  have fC2 : Cong2 (V2 a C2c) T.C2 := Cong2.trans hC2 (Cong2.add fC fC)
  have fC4 : Cong2 (V2 a C4c) T.C4 := Cong2.trans hC4 (Cong2.add fC2 fC2)
  have fC8 : Cong2 (V2 a C8c) T.C8 := Cong2.trans hC8 (Cong2.add fC4 fC4)
  have fY3 : Cong2 (V2 a Y3c) T.Y3 := Cong2.trans hY3 (Cong2.sub fEE fC8)
  have fYZ : Cong2 (V2 a YZc) T.YZ := hYZ
  have fZ3 : Cong2 (V2 a Z3c) T.Z3 := Cong2.trans hZ3 (Cong2.add fYZ fYZ)
  exact ⟨fX3, fY3, fZ3⟩

/-! ## §8 — Jacobian point ADDITION traces + forcing (G1 over Fp, G2 over Fp2).

`AddT R` is the addition-gadget intermediate trace over `R` (add-2007-bl). `g1Add_core_forces` takes the 29
raw Fp gate satisfactions (fully gadget-tied); `g2Add_of_subop_congs` takes the 29 per-`fp2`-operation
congruences (the sub-`fp2`-gadget forcings). Each field of the trace is defeq-reducible, so the chain
is one line per column with no hand-expansion of the (very deep) addition formula. -/

/-- A Jacobian-addition intermediate trace over a field `R` (mirrors the addition gadget's columns). -/
structure AddT (R : Type) where
  Z1Z1 : R
  Z2Z2 : R
  U1 : R
  U2 : R
  Y1Z2 : R
  S1 : R
  Y2Z1 : R
  S2 : R
  H : R
  twoH : R
  I : R
  J : R
  S2S1 : R
  r : R
  V : R
  rr : R
  rrJ : R
  twoV : R
  X3 : R
  VX3 : R
  rVX3 : R
  S1J : R
  twoS1J : R
  Y3 : R
  Z1Z2 : R
  Z1Z2s : R
  t1 : R
  t2 : R
  Z3 : R

/-- ℤ Jacobian addition trace, mirroring `g1AddGadget`. -/
def g1addTrace (X1 Y1 Z1 X2 Y2 Z2 : ℤ) : AddT ℤ :=
  let Z1Z1 := Z1 * Z1; let Z2Z2 := Z2 * Z2
  let U1 := X1 * Z2Z2; let U2 := X2 * Z1Z1
  let Y1Z2 := Y1 * Z2; let S1 := Y1Z2 * Z2Z2
  let Y2Z1 := Y2 * Z1; let S2 := Y2Z1 * Z1Z1
  let H := U2 - U1; let twoH := H + H; let I := twoH * twoH; let J := H * I
  let S2S1 := S2 - S1; let r := S2S1 + S2S1; let V := U1 * I
  let rr := r * r; let rrJ := rr - J; let twoV := V + V; let X3 := rrJ - twoV
  let VX3 := V - X3; let rVX3 := r * VX3; let S1J := S1 * J; let twoS1J := S1J + S1J
  let Y3 := rVX3 - twoS1J
  let Z1Z2 := Z1 + Z2; let Z1Z2s := Z1Z2 * Z1Z2; let t1 := Z1Z2s - Z1Z1; let t2 := t1 - Z2Z2
  let Z3 := t2 * H
  { Z1Z1, Z2Z2, U1, U2, Y1Z2, S1, Y2Z1, S2, H, twoH, I, J, S2S1, r, V, rr, rrJ, twoV, X3, VX3,
    rVX3, S1J, twoS1J, Y3, Z1Z2, Z1Z2s, t1, t2, Z3 }

/-- ℤ Fp2 Jacobian addition trace, mirroring `g2AddGadget`. -/
def g2addTrace (X1 Y1 Z1 X2 Y2 Z2 : ℤ × ℤ) : AddT (ℤ × ℤ) :=
  let Z1Z1 := mul2 Z1 Z1; let Z2Z2 := mul2 Z2 Z2
  let U1 := mul2 X1 Z2Z2; let U2 := mul2 X2 Z1Z1
  let Y1Z2 := mul2 Y1 Z2; let S1 := mul2 Y1Z2 Z2Z2
  let Y2Z1 := mul2 Y2 Z1; let S2 := mul2 Y2Z1 Z1Z1
  let H := sub2 U2 U1; let twoH := add2 H H; let I := mul2 twoH twoH; let J := mul2 H I
  let S2S1 := sub2 S2 S1; let r := add2 S2S1 S2S1; let V := mul2 U1 I
  let rr := mul2 r r; let rrJ := sub2 rr J; let twoV := add2 V V; let X3 := sub2 rrJ twoV
  let VX3 := sub2 V X3; let rVX3 := mul2 r VX3; let S1J := mul2 S1 J; let twoS1J := add2 S1J S1J
  let Y3 := sub2 rVX3 twoS1J
  let Z1Z2 := add2 Z1 Z2; let Z1Z2s := mul2 Z1Z2 Z1Z2; let t1 := sub2 Z1Z2s Z1Z1; let t2 := sub2 t1 Z2Z2
  let Z3 := mul2 t2 H
  { Z1Z1, Z2Z2, U1, U2, Y1Z2, S1, Y2Z1, S2, H, twoH, I, J, S2S1, r, V, rr, rrJ, twoV, X3, VX3,
    rVX3, S1J, twoS1J, Y3, Z1Z2, Z1Z2s, t1, t2, Z3 }

/-- **`g1Add_core_forces`** — the 29-gate `g1AddGadget` forces `(X3,Y3,Z3) ≡ g1addTrace (P,Q)` over Fp,
from the raw gate satisfactions. -/
theorem g1Add_core_forces (a : Assignment)
    (X1c Y1c Z1c X2c Y2c Z2c Z1Z1c Z2Z2c U1c U2c Y1Z2c S1c Y2Z1c S2c Hc twoHc Ic Jc S2S1c rc Vc rrc
     rrJc twoVc X3c VX3c rVX3c S1Jc twoS1Jc Y3c Z1Z2c Z1Z2sc t1c t2c Z3c
     qZ1Z1 qZ2Z2 qU1 qU2 qY1Z2 qS1 qY2Z1 qS2 qI qJ qV qrr qrVX3 qS1J qZ1Z2s qZ3
     bH ctwoH bS2S1 cr brrJ ctwoV bX3 bVX3 ctwoS1J bY3 cZ1Z2 bt1 bt2 : Nat)
    (hZ1Z1 : evalH (fpMulHead Z1c Z1c Z1Z1c qZ1Z1) a = 0)
    (hZ2Z2 : evalH (fpMulHead Z2c Z2c Z2Z2c qZ2Z2) a = 0)
    (hU1 : evalH (fpMulHead X1c Z2Z2c U1c qU1) a = 0)
    (hU2 : evalH (fpMulHead X2c Z1Z1c U2c qU2) a = 0)
    (hY1Z2 : evalH (fpMulHead Y1c Z2c Y1Z2c qY1Z2) a = 0)
    (hS1 : evalH (fpMulHead Y1Z2c Z2Z2c S1c qS1) a = 0)
    (hY2Z1 : evalH (fpMulHead Y2c Z1c Y2Z1c qY2Z1) a = 0)
    (hS2 : evalH (fpMulHead Y2Z1c Z1Z1c S2c qS2) a = 0)
    (hH : evalH (fpSubHead U2c U1c Hc bH) a = 0)
    (htwoH : evalH (fpAddHead Hc Hc twoHc ctwoH) a = 0)
    (hI : evalH (fpMulHead twoHc twoHc Ic qI) a = 0)
    (hJ : evalH (fpMulHead Hc Ic Jc qJ) a = 0)
    (hS2S1 : evalH (fpSubHead S2c S1c S2S1c bS2S1) a = 0)
    (hr : evalH (fpAddHead S2S1c S2S1c rc cr) a = 0)
    (hV : evalH (fpMulHead U1c Ic Vc qV) a = 0)
    (hrr : evalH (fpMulHead rc rc rrc qrr) a = 0)
    (hrrJ : evalH (fpSubHead rrc Jc rrJc brrJ) a = 0)
    (htwoV : evalH (fpAddHead Vc Vc twoVc ctwoV) a = 0)
    (hX3 : evalH (fpSubHead rrJc twoVc X3c bX3) a = 0)
    (hVX3 : evalH (fpSubHead Vc X3c VX3c bVX3) a = 0)
    (hrVX3 : evalH (fpMulHead rc VX3c rVX3c qrVX3) a = 0)
    (hS1J : evalH (fpMulHead S1c Jc S1Jc qS1J) a = 0)
    (htwoS1J : evalH (fpAddHead S1Jc S1Jc twoS1Jc ctwoS1J) a = 0)
    (hY3 : evalH (fpSubHead rVX3c twoS1Jc Y3c bY3) a = 0)
    (hZ1Z2 : evalH (fpAddHead Z1c Z2c Z1Z2c cZ1Z2) a = 0)
    (hZ1Z2s : evalH (fpMulHead Z1Z2c Z1Z2c Z1Z2sc qZ1Z2s) a = 0)
    (ht1 : evalH (fpSubHead Z1Z2sc Z1Z1c t1c bt1) a = 0)
    (ht2 : evalH (fpSubHead t1c Z2Z2c t2c bt2) a = 0)
    (hZ3 : evalH (fpMulHead t2c Hc Z3c qZ3) a = 0) :
    CZ (fpVal a X3c) (g1addTrace (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                        (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).X3
    ∧ CZ (fpVal a Y3c) (g1addTrace (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                        (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).Y3
    ∧ CZ (fpVal a Z3c) (g1addTrace (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                        (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).Z3 := by
  let T := g1addTrace (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
             (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)
  have fZ1Z1 : CZ (fpVal a Z1Z1c) T.Z1Z1 := mulCZ hZ1Z1
  have fZ2Z2 : CZ (fpVal a Z2Z2c) T.Z2Z2 := mulCZ hZ2Z2
  have fU1 : CZ (fpVal a U1c) T.U1 := CZ.trans (mulCZ hU1) (CZ.mul (CZ.refl _) fZ2Z2)
  have fU2 : CZ (fpVal a U2c) T.U2 := CZ.trans (mulCZ hU2) (CZ.mul (CZ.refl _) fZ1Z1)
  have fY1Z2 : CZ (fpVal a Y1Z2c) T.Y1Z2 := mulCZ hY1Z2
  have fS1 : CZ (fpVal a S1c) T.S1 := CZ.trans (mulCZ hS1) (CZ.mul fY1Z2 fZ2Z2)
  have fY2Z1 : CZ (fpVal a Y2Z1c) T.Y2Z1 := mulCZ hY2Z1
  have fS2 : CZ (fpVal a S2c) T.S2 := CZ.trans (mulCZ hS2) (CZ.mul fY2Z1 fZ1Z1)
  have fH : CZ (fpVal a Hc) T.H := CZ.trans (subCZ hH) (CZ.sub fU2 fU1)
  have ftwoH : CZ (fpVal a twoHc) T.twoH := CZ.trans (addCZ htwoH) (CZ.add fH fH)
  have fI : CZ (fpVal a Ic) T.I := CZ.trans (mulCZ hI) (CZ.mul ftwoH ftwoH)
  have fJ : CZ (fpVal a Jc) T.J := CZ.trans (mulCZ hJ) (CZ.mul fH fI)
  have fS2S1 : CZ (fpVal a S2S1c) T.S2S1 := CZ.trans (subCZ hS2S1) (CZ.sub fS2 fS1)
  have fr : CZ (fpVal a rc) T.r := CZ.trans (addCZ hr) (CZ.add fS2S1 fS2S1)
  have fV : CZ (fpVal a Vc) T.V := CZ.trans (mulCZ hV) (CZ.mul fU1 fI)
  have frr : CZ (fpVal a rrc) T.rr := CZ.trans (mulCZ hrr) (CZ.mul fr fr)
  have frrJ : CZ (fpVal a rrJc) T.rrJ := CZ.trans (subCZ hrrJ) (CZ.sub frr fJ)
  have ftwoV : CZ (fpVal a twoVc) T.twoV := CZ.trans (addCZ htwoV) (CZ.add fV fV)
  have fX3 : CZ (fpVal a X3c) T.X3 := CZ.trans (subCZ hX3) (CZ.sub frrJ ftwoV)
  have fVX3 : CZ (fpVal a VX3c) T.VX3 := CZ.trans (subCZ hVX3) (CZ.sub fV fX3)
  have frVX3 : CZ (fpVal a rVX3c) T.rVX3 := CZ.trans (mulCZ hrVX3) (CZ.mul fr fVX3)
  have fS1J : CZ (fpVal a S1Jc) T.S1J := CZ.trans (mulCZ hS1J) (CZ.mul fS1 fJ)
  have ftwoS1J : CZ (fpVal a twoS1Jc) T.twoS1J := CZ.trans (addCZ htwoS1J) (CZ.add fS1J fS1J)
  have fY3 : CZ (fpVal a Y3c) T.Y3 := CZ.trans (subCZ hY3) (CZ.sub frVX3 ftwoS1J)
  have fZ1Z2 : CZ (fpVal a Z1Z2c) T.Z1Z2 := addCZ hZ1Z2
  have fZ1Z2s : CZ (fpVal a Z1Z2sc) T.Z1Z2s := CZ.trans (mulCZ hZ1Z2s) (CZ.mul fZ1Z2 fZ1Z2)
  have ft1 : CZ (fpVal a t1c) T.t1 := CZ.trans (subCZ ht1) (CZ.sub fZ1Z2s fZ1Z1)
  have ft2 : CZ (fpVal a t2c) T.t2 := CZ.trans (subCZ ht2) (CZ.sub ft1 fZ2Z2)
  have fZ3 : CZ (fpVal a Z3c) T.Z3 := CZ.trans (mulCZ hZ3) (CZ.mul ft2 fH)
  exact ⟨fX3, fY3, fZ3⟩

/-- **`g2Add_of_subop_congs`** — the `g2AddGadget` forces `(X3,Y3,Z3) ≡ g2addTrace (P,Q)` over Fp2, from the
per-`fp2`-operation congruences. -/
theorem g2Add_of_subop_congs (a : Assignment)
    (X1c Y1c Z1c X2c Y2c Z2c Z1Z1c Z2Z2c U1c U2c Y1Z2c S1c Y2Z1c S2c Hc twoHc Ic Jc S2S1c rc Vc rrc
     rrJc twoVc X3c VX3c rVX3c S1Jc twoS1Jc Y3c Z1Z2c Z1Z2sc t1c t2c Z3c : C2)
    (hZ1Z1 : Cong2 (V2 a Z1Z1c) (mul2 (V2 a Z1c) (V2 a Z1c)))
    (hZ2Z2 : Cong2 (V2 a Z2Z2c) (mul2 (V2 a Z2c) (V2 a Z2c)))
    (hU1 : Cong2 (V2 a U1c) (mul2 (V2 a X1c) (V2 a Z2Z2c)))
    (hU2 : Cong2 (V2 a U2c) (mul2 (V2 a X2c) (V2 a Z1Z1c)))
    (hY1Z2 : Cong2 (V2 a Y1Z2c) (mul2 (V2 a Y1c) (V2 a Z2c)))
    (hS1 : Cong2 (V2 a S1c) (mul2 (V2 a Y1Z2c) (V2 a Z2Z2c)))
    (hY2Z1 : Cong2 (V2 a Y2Z1c) (mul2 (V2 a Y2c) (V2 a Z1c)))
    (hS2 : Cong2 (V2 a S2c) (mul2 (V2 a Y2Z1c) (V2 a Z1Z1c)))
    (hH : Cong2 (V2 a Hc) (sub2 (V2 a U2c) (V2 a U1c)))
    (htwoH : Cong2 (V2 a twoHc) (add2 (V2 a Hc) (V2 a Hc)))
    (hI : Cong2 (V2 a Ic) (mul2 (V2 a twoHc) (V2 a twoHc)))
    (hJ : Cong2 (V2 a Jc) (mul2 (V2 a Hc) (V2 a Ic)))
    (hS2S1 : Cong2 (V2 a S2S1c) (sub2 (V2 a S2c) (V2 a S1c)))
    (hr : Cong2 (V2 a rc) (add2 (V2 a S2S1c) (V2 a S2S1c)))
    (hV : Cong2 (V2 a Vc) (mul2 (V2 a U1c) (V2 a Ic)))
    (hrr : Cong2 (V2 a rrc) (mul2 (V2 a rc) (V2 a rc)))
    (hrrJ : Cong2 (V2 a rrJc) (sub2 (V2 a rrc) (V2 a Jc)))
    (htwoV : Cong2 (V2 a twoVc) (add2 (V2 a Vc) (V2 a Vc)))
    (hX3 : Cong2 (V2 a X3c) (sub2 (V2 a rrJc) (V2 a twoVc)))
    (hVX3 : Cong2 (V2 a VX3c) (sub2 (V2 a Vc) (V2 a X3c)))
    (hrVX3 : Cong2 (V2 a rVX3c) (mul2 (V2 a rc) (V2 a VX3c)))
    (hS1J : Cong2 (V2 a S1Jc) (mul2 (V2 a S1c) (V2 a Jc)))
    (htwoS1J : Cong2 (V2 a twoS1Jc) (add2 (V2 a S1Jc) (V2 a S1Jc)))
    (hY3 : Cong2 (V2 a Y3c) (sub2 (V2 a rVX3c) (V2 a twoS1Jc)))
    (hZ1Z2 : Cong2 (V2 a Z1Z2c) (add2 (V2 a Z1c) (V2 a Z2c)))
    (hZ1Z2s : Cong2 (V2 a Z1Z2sc) (mul2 (V2 a Z1Z2c) (V2 a Z1Z2c)))
    (ht1 : Cong2 (V2 a t1c) (sub2 (V2 a Z1Z2sc) (V2 a Z1Z1c)))
    (ht2 : Cong2 (V2 a t2c) (sub2 (V2 a t1c) (V2 a Z2Z2c)))
    (hZ3 : Cong2 (V2 a Z3c) (mul2 (V2 a t2c) (V2 a Hc))) :
    Cong2 (V2 a X3c) (g2addTrace (V2 a X1c) (V2 a Y1c) (V2 a Z1c)
                        (V2 a X2c) (V2 a Y2c) (V2 a Z2c)).X3
    ∧ Cong2 (V2 a Y3c) (g2addTrace (V2 a X1c) (V2 a Y1c) (V2 a Z1c)
                        (V2 a X2c) (V2 a Y2c) (V2 a Z2c)).Y3
    ∧ Cong2 (V2 a Z3c) (g2addTrace (V2 a X1c) (V2 a Y1c) (V2 a Z1c)
                        (V2 a X2c) (V2 a Y2c) (V2 a Z2c)).Z3 := by
  let T := g2addTrace (V2 a X1c) (V2 a Y1c) (V2 a Z1c) (V2 a X2c) (V2 a Y2c) (V2 a Z2c)
  have fZ1Z1 : Cong2 (V2 a Z1Z1c) T.Z1Z1 := hZ1Z1
  have fZ2Z2 : Cong2 (V2 a Z2Z2c) T.Z2Z2 := hZ2Z2
  have fU1 : Cong2 (V2 a U1c) T.U1 := Cong2.trans hU1 (Cong2.mul (Cong2.refl _) fZ2Z2)
  have fU2 : Cong2 (V2 a U2c) T.U2 := Cong2.trans hU2 (Cong2.mul (Cong2.refl _) fZ1Z1)
  have fY1Z2 : Cong2 (V2 a Y1Z2c) T.Y1Z2 := hY1Z2
  have fS1 : Cong2 (V2 a S1c) T.S1 := Cong2.trans hS1 (Cong2.mul fY1Z2 fZ2Z2)
  have fY2Z1 : Cong2 (V2 a Y2Z1c) T.Y2Z1 := hY2Z1
  have fS2 : Cong2 (V2 a S2c) T.S2 := Cong2.trans hS2 (Cong2.mul fY2Z1 fZ1Z1)
  have fH : Cong2 (V2 a Hc) T.H := Cong2.trans hH (Cong2.sub fU2 fU1)
  have ftwoH : Cong2 (V2 a twoHc) T.twoH := Cong2.trans htwoH (Cong2.add fH fH)
  have fI : Cong2 (V2 a Ic) T.I := Cong2.trans hI (Cong2.mul ftwoH ftwoH)
  have fJ : Cong2 (V2 a Jc) T.J := Cong2.trans hJ (Cong2.mul fH fI)
  have fS2S1 : Cong2 (V2 a S2S1c) T.S2S1 := Cong2.trans hS2S1 (Cong2.sub fS2 fS1)
  have fr : Cong2 (V2 a rc) T.r := Cong2.trans hr (Cong2.add fS2S1 fS2S1)
  have fV : Cong2 (V2 a Vc) T.V := Cong2.trans hV (Cong2.mul fU1 fI)
  have frr : Cong2 (V2 a rrc) T.rr := Cong2.trans hrr (Cong2.mul fr fr)
  have frrJ : Cong2 (V2 a rrJc) T.rrJ := Cong2.trans hrrJ (Cong2.sub frr fJ)
  have ftwoV : Cong2 (V2 a twoVc) T.twoV := Cong2.trans htwoV (Cong2.add fV fV)
  have fX3 : Cong2 (V2 a X3c) T.X3 := Cong2.trans hX3 (Cong2.sub frrJ ftwoV)
  have fVX3 : Cong2 (V2 a VX3c) T.VX3 := Cong2.trans hVX3 (Cong2.sub fV fX3)
  have frVX3 : Cong2 (V2 a rVX3c) T.rVX3 := Cong2.trans hrVX3 (Cong2.mul fr fVX3)
  have fS1J : Cong2 (V2 a S1Jc) T.S1J := Cong2.trans hS1J (Cong2.mul fS1 fJ)
  have ftwoS1J : Cong2 (V2 a twoS1Jc) T.twoS1J := Cong2.trans htwoS1J (Cong2.add fS1J fS1J)
  have fY3 : Cong2 (V2 a Y3c) T.Y3 := Cong2.trans hY3 (Cong2.sub frVX3 ftwoS1J)
  have fZ1Z2 : Cong2 (V2 a Z1Z2c) T.Z1Z2 := hZ1Z2
  have fZ1Z2s : Cong2 (V2 a Z1Z2sc) T.Z1Z2s := Cong2.trans hZ1Z2s (Cong2.mul fZ1Z2 fZ1Z2)
  have ft1 : Cong2 (V2 a t1c) T.t1 := Cong2.trans ht1 (Cong2.sub fZ1Z2s fZ1Z1)
  have ft2 : Cong2 (V2 a t2c) T.t2 := Cong2.trans ht2 (Cong2.sub ft1 fZ2Z2)
  have fZ3 : Cong2 (V2 a Z3c) T.Z3 := Cong2.trans hZ3 (Cong2.mul ft2 fH)
  exact ⟨fX3, fY3, fZ3⟩

/-! ## §9 — GATE ACCEPTANCE: the rungs that actually name their gadget.

Everything above §9 takes RAW GATE EQUATIONS over FREE column bases (`*_core_*`) or the CONCLUSIONS
of other lemmas (`*_of_subop_congs`). None of them mentions a generator, so none of them says
anything about the circuit that is emitted — audit finding F5/F6. This section supplies the missing
half: `acceptB <generator applied to its real arguments>` as a hypothesis, destructured along the
generator's own list literal, with the column bases INSTANTIATED at the gadget's own layout.

`acceptB` is `Bls12381Tower`'s ℤ reading of the emitted gate bodies — the same predicate the Tower /
TowerExt `#guard` KATs use. -/

/-- The ℤ reading of one emitted `Head` gate. -/
theorem gateBodyEvalZero_cgH (a : Assignment) (h : Head) :
    gateBodyEvalZero a (cgH h) = decide (evalH h a = 0) := by
  simp only [cgH, cg, gateBodyEvalZero, headToExpr_eval]

theorem acceptB_append (l1 l2 : List VmConstraint2) (a : Assignment) :
    acceptB (l1 ++ l2) a = (acceptB l1 a && acceptB l2 a) := by simp [acceptB, List.all_append]

/-- Peel a whole gadget's acceptance into its per-gate `evalH … = 0` facts. Each `fp{Mul,Add,Sub}Core`
IS `cgH` of the corresponding head, so this is `simp` through the generator's list literal. -/
private theorem head_of_gate {a : Assignment} {h : Head}
    (hb : gateBodyEvalZero a (cgH h) = true) : evalH h a = 0 := by
  rw [gateBodyEvalZero_cgH] at hb; exact of_decide_eq_true hb

/-- The simp set that turns `acceptB <list literal of `*Core` gates>` into a conjunction of
`evalH <head> a = 0`. -/
private def accSplitTag : Unit := ()

/-- **`fp2Mul_cong` — the TIED atom.** GIVEN `fp2MulGadget`'s 8 emitted gates are ACCEPTED, the
gadget's OWN output columns (`fp2MulR0 base = base+78`, `fp2MulR1 base = base+91`) carry the Fp2
product of the inputs. Every scratch column is `fp2MulGadget`'s own; none is a free parameter. -/
theorem fp2Mul_cong (a : Assignment) (a0 a1 b0 b1 base : Nat)
    (hacc : acceptB (fp2MulGadget a0 a1 b0 b1 base) a = true) :
    Cong2 (V2 a (fp2MulR0 base, fp2MulR1 base)) (mul2 (V2 a (a0, a1)) (V2 a (b0, b1))) := by
  simp only [fp2MulGadget, acceptB, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, fpMulCore, fpAddCore, fpSubCore] at hacc
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hacc
  exact fp2Mul_core_cong a a0 a1 b0 b1 _ _ _ _ _ _ (fp2MulR0 base) (fp2MulR1 base) _ _ _ _ _ _ _ _
    (head_of_gate h0) (head_of_gate h1) (head_of_gate h2) (head_of_gate h3)
    (head_of_gate h4) (head_of_gate h5) (head_of_gate h6) (head_of_gate h7)

/-- **`fp2Add_cong` — the TIED atom.** `fp2AddGadget`'s 2 emitted gates accepted ⟹ its outputs carry
the Fp2 sum. -/
theorem fp2Add_cong (a : Assignment) (a0 a1 b0 b1 r0 r1 c0 c1 : Nat)
    (hacc : acceptB (fp2AddGadget a0 a1 b0 b1 r0 r1 c0 c1) a = true) :
    Cong2 (V2 a (r0, r1)) (add2 (V2 a (a0, a1)) (V2 a (b0, b1))) := by
  simp only [fp2AddGadget, acceptB, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, fpAddCore] at hacc
  exact fp2Add_core_cong a a0 a1 b0 b1 r0 r1 c0 c1 (head_of_gate hacc.1) (head_of_gate hacc.2)

/-- **`fp2Sub_cong` — the TIED atom.** -/
theorem fp2Sub_cong (a : Assignment) (a0 a1 b0 b1 r0 r1 c0 c1 : Nat)
    (hacc : acceptB (fp2SubGadget a0 a1 b0 b1 r0 r1 c0 c1) a = true) :
    Cong2 (V2 a (r0, r1)) (sub2 (V2 a (a0, a1)) (V2 a (b0, b1))) := by
  simp only [fp2SubGadget, acceptB, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, fpSubCore] at hacc
  exact fp2Sub_core_cong a a0 a1 b0 b1 r0 r1 c0 c1 (head_of_gate hacc.1) (head_of_gate hacc.2)

/-- **`mulByXi_cong` — the TIED atom that did not exist.** `fp6Mul_of_subop_congs` and
`fp12Mul_of_subop_congs` both ASSUME `Cong2 (V2 a x) (xi2 (V2 a s))`, and no lemma in the tree
produced it: `Bls12381TowerExt.mulByXi_forces` gives the raw divisibility pair, not `Cong2`, and is
itself untied. This is that lemma, tied to `mulByXiGadget`. -/
theorem mulByXi_cong (a : Assignment) (x0 x1 r0 r1 br cr : Nat)
    (hacc : acceptB (mulByXiGadget x0 x1 r0 r1 br cr) a = true) :
    Cong2 (V2 a (r0, r1)) (xi2 (V2 a (x0, x1))) := by
  simp only [mulByXiGadget, acceptB, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, fpAddCore, fpSubCore] at hacc
  exact ⟨subCZ (head_of_gate hacc.1), addCZ (head_of_gate hacc.2)⟩

/-- **`g1Double_forces` — the TIED rung.** GIVEN the 21 emitted gates of `g1DoubleGadget X Y Z S` are
ACCEPTED, the gadget's OWN output columns `X3 = S+156`, `Y3 = S+234`, `Z3 = S+260` carry the Jacobian
double of the input columns, mod `p`. The commit that landed `g1Double_core_forces` called it "fully
gadget-tied"; it was not — all 45 of its column bases were free parameters and `g1DoubleGadget` did
not appear. This is the statement that claim described.

The congruence is mod `p` on the ℤ readings. `g1DoubleGadget` emits VALUE gates only — no
`fpLimbRange`, no `binGate` — so the limb encoding is not pinned to a canonical representative and
the carry/borrow columns are unconstrained integers. That is the same named encoding-canonicity gap
`fpMulCore_forces` carries (audit F6, secondary); it is NOT closed here. -/
theorem g1Double_forces (a : Assignment) (X Y Z S : Nat)
    (hacc : acceptB (g1DoubleGadget X Y Z S) a = true) :
    CZ (fpVal a (S + 156)) (g1dblZ (fpVal a X) (fpVal a Y) (fpVal a Z)).1
    ∧ CZ (fpVal a (S + 234)) (g1dblZ (fpVal a X) (fpVal a Y) (fpVal a Z)).2.1
    ∧ CZ (fpVal a (S + 260)) (g1dblZ (fpVal a X) (fpVal a Y) (fpVal a Z)).2.2 := by
  simp only [g1DoubleGadget, acceptB, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, fpMulCore, fpAddCore, fpSubCore] at hacc
  obtain ⟨hA, hB, hC, hXB, hXB2, hT1, hT2, hD, hA2, hE, hF, hD2, hX3, hDX3, hEE,
          hC2, hC4, hC8, hY3, hYZ, hZ3⟩ := hacc
  exact g1Double_core_forces a X Y Z (S) (S + 13) (S + 26) (S + 39) (S + 52) (S + 65) (S + 78)
    (S + 91) (S + 104) (S + 117) (S + 130) (S + 143) (S + 156) (S + 169) (S + 182) (S + 195)
    (S + 208) (S + 221) (S + 234) (S + 247) (S + 260)
    (S + 273) (S + 286) (S + 299) (S + 312) (S + 325) (S + 338) (S + 351)
    (S + 364) (S + 365) (S + 366) (S + 367) (S + 368) (S + 369) (S + 370) (S + 371) (S + 372)
    (S + 373) (S + 374) (S + 375) (S + 376) (S + 377)
    (head_of_gate hA) (head_of_gate hB) (head_of_gate hC) (head_of_gate hXB) (head_of_gate hXB2)
    (head_of_gate hT1) (head_of_gate hT2) (head_of_gate hD) (head_of_gate hA2) (head_of_gate hE)
    (head_of_gate hF) (head_of_gate hD2) (head_of_gate hX3) (head_of_gate hDX3) (head_of_gate hEE)
    (head_of_gate hC2) (head_of_gate hC4) (head_of_gate hC8) (head_of_gate hY3) (head_of_gate hYZ)
    (head_of_gate hZ3)

/-- **`g1Add_forces` — the TIED rung.** GIVEN the 29 emitted gates of
`g1AddGadget X1 Y1 Z1 X2 Y2 Z2 fresh` are ACCEPTED, the columns the gadget RETURNS as `(X3, Y3, Z3)`
carry the Jacobian sum, mod `p`. Same encoding-canonicity caveat as `g1Double_forces`. -/
theorem g1Add_forces (a : Assignment) (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat)
    (hacc : acceptB (g1AddGadget X1 Y1 Z1 X2 Y2 Z2 fresh).1 a = true) :
    CZ (fpVal a (g1AddGadget X1 Y1 Z1 X2 Y2 Z2 fresh).2.1.1)
       (g1addTrace (fpVal a X1) (fpVal a Y1) (fpVal a Z1)
                   (fpVal a X2) (fpVal a Y2) (fpVal a Z2)).X3
    ∧ CZ (fpVal a (g1AddGadget X1 Y1 Z1 X2 Y2 Z2 fresh).2.1.2.1)
       (g1addTrace (fpVal a X1) (fpVal a Y1) (fpVal a Z1)
                   (fpVal a X2) (fpVal a Y2) (fpVal a Z2)).Y3
    ∧ CZ (fpVal a (g1AddGadget X1 Y1 Z1 X2 Y2 Z2 fresh).2.1.2.2)
       (g1addTrace (fpVal a X1) (fpVal a Y1) (fpVal a Z1)
                   (fpVal a X2) (fpVal a Y2) (fpVal a Z2)).Z3 := by
  simp only [g1AddGadget, acceptB, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, fpMulCore, fpAddCore, fpSubCore] at hacc
  obtain ⟨hZ1Z1, hZ2Z2, hU1, hU2, hY1Z2, hS1, hY2Z1, hS2, hH, htwoH, hI, hJ, hS2S1, hr, hV, hrr,
          hrrJ, htwoV, hX3, hVX3, hrVX3, hS1J, htwoS1J, hY3, hZ1Z2, hZ1Z2s, ht1, ht2, hZ3⟩ := hacc
  exact g1Add_core_forces a X1 Y1 Z1 X2 Y2 Z2
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _
    (head_of_gate hZ1Z1) (head_of_gate hZ2Z2) (head_of_gate hU1) (head_of_gate hU2)
    (head_of_gate hY1Z2) (head_of_gate hS1) (head_of_gate hY2Z1) (head_of_gate hS2)
    (head_of_gate hH) (head_of_gate htwoH) (head_of_gate hI) (head_of_gate hJ)
    (head_of_gate hS2S1) (head_of_gate hr) (head_of_gate hV) (head_of_gate hrr)
    (head_of_gate hrrJ) (head_of_gate htwoV) (head_of_gate hX3) (head_of_gate hVX3)
    (head_of_gate hrVX3) (head_of_gate hS1J) (head_of_gate htwoS1J) (head_of_gate hY3)
    (head_of_gate hZ1Z2) (head_of_gate hZ1Z2s) (head_of_gate ht1) (head_of_gate ht2)
    (head_of_gate hZ3)

/-! ## §10 — Axiom hygiene (the CHECK, not the claim).

Until 2026-07-27 this file's §"Axiom hygiene" ASSERTED `#assert_axioms`-cleanliness while containing
ZERO `#assert_axioms` commands. The transcripts show the measurement was real but EPHEMERAL — one
`#print axioms` run on a throwaway `/tmp` file — and was then written into the docstring as though it
were a property of this file. These are the pins; they run in the root build. -/

#assert_axioms CZ.refl
#assert_axioms CZ.symm
#assert_axioms CZ.trans
#assert_axioms CZ.add
#assert_axioms CZ.sub
#assert_axioms CZ.mul
#assert_axioms Cong2.refl
#assert_axioms Cong2.trans
#assert_axioms Cong2.add
#assert_axioms Cong2.sub
#assert_axioms Cong2.xi
#assert_axioms Cong2.mul
#assert_axioms Cong6.trans
#assert_axioms Cong6.add
#assert_axioms Cong6.sub
#assert_axioms Cong6.gamma
#assert_axioms Cong6.mul
#assert_axioms gateBodyEvalZero_cgH
#assert_axioms acceptB_append
#assert_axioms fp2Mul_core_cong
#assert_axioms fp2Add_core_cong
#assert_axioms fp2Sub_core_cong
#assert_axioms fp6Mul_of_subop_congs
#assert_axioms fp12Mul_of_subop_congs
#assert_axioms g1Double_core_forces
#assert_axioms g1Add_core_forces
#assert_axioms g2Double_of_subop_congs
#assert_axioms g2Add_of_subop_congs
#assert_axioms fp2Mul_cong
#assert_axioms fp2Add_cong
#assert_axioms fp2Sub_cong
#assert_axioms mulByXi_cong
#assert_axioms g1Double_forces
#assert_axioms g1Add_forces

end Dregg2.Circuit.Emit.Bls12381Forcing
