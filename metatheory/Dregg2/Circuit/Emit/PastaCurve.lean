/-
# Dregg2.Circuit.Emit.PastaCurve — Pallas/Vesta CURVE point ops + the Pasta endomorphism,
on K1's forced Pasta field floor (task K2 of `docs/MINA-KIMCHI-VERIFIER-PLAN.md`).

## What this file IS

K1 (`PastaField`, commit `1ba1d6613`) built the forced Fp/Fq arithmetic floor (`fpMul/fpAdd/fpSub`,
`fqMul/fqAdd/fqSub`, quotient-witness reduction gates, six forcing lemmas). This file is the CURVE
layer on top — a direct crib of `Bls12381TowerExt` (gadget generators) and `Bls12381Forcing`
(congruence-algebra forcing), because Pallas/Vesta are the SAME short-Weierstrass shape as BLS12-381
G1 (`a = 0`, Jacobian dbl-2009-l / add-2007-bl), just with `b = 5` and 255-bit primes:

  * **Pallas** `y² = x³ + 5` over **Fp** (`pN`) — `pallasDoubleGadget` (21 core gates),
    `pallasAddGadget` (29 core gates), composing K1's `fpMulCore/fpAddCore/fpSubCore`.
  * **Vesta** `y² = x³ + 5` over **Fq** (`qN`) — `vestaDoubleGadget`/`vestaAddGadget`, the SAME
    generic builders instantiated with K1's `fq*Core` gates.
  * **The endomorphism** — `φ(x,y) = (ζ·x, y)` with `ζ` a primitive cube root of unity in the base
    field. One `fpMulCore` (or `fqMulCore`) plus a one-gate constant pin. This is the GLV enabler
    (§5): the reason a Pasta scalar mul is ~2× cheaper than naive double-and-add.

Everything GENERATED (House Law #1): one generic short-Weierstrass double/add builder
(`swDoubleGadget`/`swAddGadget`) parameterized by the three field-core constructors, instantiated
twice (Fp and Fq). No gate is hand-authored per curve.

## The curve parameters (VERIFIED against the pinned source)

SOURCE: the `mina-curves` crate of o1-labs `proof-systems` at rev `36a8b510` (the rev this repo's
`circuit-prove/sketches/mina-pasta-hash-probe/Cargo.toml` pins), files:
  * `curves/src/pasta/curves/pallas.rs` — `COEFF_A = 0`, `COEFF_B = 5`, generator
    `G = (1, 12418654782883325593414442427049395787963493412651469444558597405572177144507)`, base
    field Fp, scalar field Fq, cofactor 1.
  * `curves/src/pasta/curves/vesta.rs` — `COEFF_A = 0`, `COEFF_B = 5`, generator
    `G = (1, 11426906929455361843568202299992114520848200991084027513389447476559454104162)`, base
    field Fq, scalar field Fp, cofactor 1.
Both generators are independently checked ON-CURVE here (`#guard`, and Python: `y² ≡ 1 + 5`).

## The endomorphism scalars (VERIFIED against the pinned source, recipe reproduced exactly)

The pinned crate derives (not hardcodes) the endo constants; we reproduce its recipe bit-for-bit:
  * `poseidon/src/sponge.rs:110` — `endo_coefficient<F>() = F::GENERATOR^((|F|−1)/3)`, and both
    fields pin `#[generator = "5"]` (`curves/src/pasta/fields/fp.rs:10`, `fq.rs:10`). So
    `ζ_p = 5^((p−1)/3) mod p` (in Fp), `ζ_q = 5^((q−1)/3) mod q` (in Fq).
  * `poly-commitment/src/ipa.rs` (`endos()`): the base-field `ζ` is the curve endo (`endo_q`);
    the scalar-field `λ` (`endo_r`, the GLV lambda) is the candidate `ζ_scalar` IF
    `G·λ_candidate = φ(G)`, else its SQUARE. For BOTH Pasta curves the square is the one that
    matches (verified by scalar multiplication in Python, and re-verified in-kernel below by the
    `φ(G) = λ·G` Jacobian-equality `#guard`).

The four constants:
  * `zetaP = 20444556541222657078399132219657928148671392403212669005631716460534733845831` ∈ Fp —
    the PALLAS curve endo coefficient (φ on Pallas) AND the VESTA GLV-candidate.
  * `zetaQ = 2942865608506852014473558576493638302197734138389222805617480874486368177743` ∈ Fq —
    the VESTA curve endo coefficient AND the PALLAS GLV-candidate.
  * `lambdaPallas = 26005156700822196841419187675678338661165322343552424574062261873906994770353`
    ∈ Fq = `zetaQ² mod q` — the PALLAS GLV lambda: `φ(P) = [λ]·P` on Pallas.
  * `lambdaVesta = 8503465768106391777493614032514048814691664078728891710322960303815233784505`
    ∈ Fp = `zetaP² mod p` — the VESTA GLV lambda.
All four are `by decide`-proven primitive cube roots of unity in their fields (`x³ ≡ 1`, `x ≠ 1`),
and the two λ↔ζ square relations are `by decide`-proven. The curve-level correspondence
`φ(G) = λ·G` is a kernel `#guard` (real 255-bit scalar mul of the generator, Jacobian cross-checked).

## What is AUTHORED + built vs NAMED continuation

AUTHORED + built: the generic short-Weierstrass builders + the four curve gadgets; the endo-apply
gadgets with the one-gate ζ pin; the `Nat` Jacobian reference (generic in the modulus) + KAT
anchors (Python-computed, cross-checked against independent affine scalar muls); the on-curve
invariant KATs (non-vacuous — a wrong formula lands off-curve); the `φ(G) = λ·G` correspondence
KATs; the forcing lemmas `pallasDouble_forces`/`pallasAdd_forces`/`vestaDouble_forces`/
`vestaAdd_forces` (direct `CZm`-chain proofs over a modulus-parameterized congruence algebra —
a generic-in-bridge-variables formulation was tried and abandoned: its instantiation
whnf-exploded, so each curve's lemma is a direct proof in the `Bls12381Forcing` pattern) and
`pallasEndo_forces`/`vestaEndo_forces`; both-polarity gadget KATs
(honest witness ACCEPTED, bumped output limb REJECTED). NAMED continuation + residuals: §6.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard` KATs and `by decide` primality-of-cube-root facts reduce in the kernel.
NEW file; imports read-only (`PastaField`); standalone (NOT imported by the truncated `Dregg2`
root; built directly as `Dregg2.Circuit.Emit.PastaCurve`).
-/
import Dregg2.Circuit.Emit.PastaField

namespace Dregg2.Circuit.Emit.PastaCurve

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.PastaField
open Dregg2.Circuit.Emit.PastaField.Ref (limbOf)

set_option autoImplicit false

/-! ## §0 — Curve parameters, generators, and the four endomorphism scalars. -/

/-- The short-Weierstrass `b` coefficient, shared by Pallas and Vesta (`y² = x³ + 5`). -/
def curveB : Nat := 5

/-- **Pallas generator** (affine), from `curves/src/pasta/curves/pallas.rs`. -/
def Gp : Nat × Nat :=
  (1, 12418654782883325593414442427049395787963493412651469444558597405572177144507)
/-- **Vesta generator** (affine), from `curves/src/pasta/curves/vesta.rs`. -/
def Gv : Nat × Nat :=
  (1, 11426906929455361843568202299992114520848200991084027513389447476559454104162)

/-- The Pallas/Vesta generators as Jacobian points (`Z = 1`). -/
def GpJ : Nat × Nat × Nat := (Gp.1, Gp.2, 1)
def GvJ : Nat × Nat × Nat := (Gv.1, Gv.2, 1)

/-- **`ζ_p`** — the primitive cube root of unity in **Fp**: the PALLAS curve endomorphism
coefficient (`φ(x,y) = (ζ_p·x, y)` on Pallas). `= 5^((p−1)/3) mod p`, the pinned crate's
`endo_coefficient::<Fp>()` recipe (`GENERATOR = 5`). -/
def zetaP : Nat :=
  20444556541222657078399132219657928148671392403212669005631716460534733845831

/-- **`ζ_q`** — the primitive cube root of unity in **Fq**: the VESTA curve endomorphism
coefficient. `= 5^((q−1)/3) mod q`. -/
def zetaQ : Nat :=
  2942865608506852014473558576493638302197734138389222805617480874486368177743

/-- **`λ_Pallas`** — the GLV lambda for Pallas (in its scalar field **Fq**): `φ(P) = [λ]·P`.
`= ζ_q² mod q` (the pinned `ipa.rs::endos()` picks the square — the bare candidate fails the
`G·λ = φ(G)` check). -/
def lambdaPallas : Nat :=
  26005156700822196841419187675678338661165322343552424574062261873906994770353

/-- **`λ_Vesta`** — the GLV lambda for Vesta (in its scalar field **Fp**). `= ζ_p² mod p`. -/
def lambdaVesta : Nat :=
  8503465768106391777493614032514048814691664078728891710322960303815233784505

-- The four endo scalars are primitive cube roots of unity in their fields, and the λs are the
-- squares of the base-field ζs (the `ipa.rs::endos()` recipe). All kernel-checked by `decide`.
theorem zetaP_cube : (zetaP ^ 3) % pN = 1 := by decide
theorem zetaP_ne_one : zetaP ≠ 1 := by decide
theorem zetaQ_cube : (zetaQ ^ 3) % qN = 1 := by decide
theorem zetaQ_ne_one : zetaQ ≠ 1 := by decide
theorem lambdaPallas_cube : (lambdaPallas ^ 3) % qN = 1 := by decide
theorem lambdaPallas_ne_one : lambdaPallas ≠ 1 := by decide
theorem lambdaVesta_cube : (lambdaVesta ^ 3) % pN = 1 := by decide
theorem lambdaVesta_ne_one : lambdaVesta ≠ 1 := by decide
theorem lambdaPallas_eq_zetaQ_sq : lambdaPallas = (zetaQ ^ 2) % qN := by decide
theorem lambdaVesta_eq_zetaP_sq : lambdaVesta = (zetaP ^ 2) % pN := by decide

/-! ## §1 — The `Nat` Jacobian reference (generic in the modulus), with KAT anchors.

The trace structures mirror the gadget column allocations field-for-field, so the KAT witnesses
(§4) and the forcing chains (§3) read the same shape. `dblTraceM`/`addTraceM` reduce mod `m` after
every op (the honest trace of the generated gates); `dblTraceZ`/`addTraceZ` are the plain-ℤ
formulas the forcing lemmas conclude against. The Python anchor computation used the IDENTICAL
formulas and cross-checked every Jacobian triple against an independent affine scalar mul. -/

/-- A Jacobian-doubling intermediate trace over `R` (dbl-2009-l; field order = allocation order). -/
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

/-- A Jacobian-addition intermediate trace over `R` (add-2007-bl; field order = allocation order). -/
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

/-- The output point of a trace. -/
def DblT.toPt {R : Type} (t : DblT R) : R × R × R := (t.X3, t.Y3, t.Z3)
/-- The output point of a trace. -/
def AddT.toPt {R : Type} (t : AddT R) : R × R × R := (t.X3, t.Y3, t.Z3)

/-- `Nat` Jacobian doubling trace, per-op reduced mod `m` (mirrors the doubling gadget). -/
def dblTraceM (m : Nat) (X Y Z : Nat) : DblT Nat :=
  let M : Nat → Nat → Nat := fun x y => (x * y) % m
  let Ad : Nat → Nat → Nat := fun x y => (x + y) % m
  let Sb : Nat → Nat → Nat := fun x y => (x + m - y) % m
  let A := M X X; let B := M Y Y; let C := M B B
  let XB := Ad X B; let XB2 := M XB XB
  let T1 := Sb XB2 A; let T2 := Sb T1 C
  let D := Ad T2 T2; let A2 := Ad A A; let E := Ad A2 A
  let F := M E E; let D2 := Ad D D; let X3 := Sb F D2
  let DX3 := Sb D X3; let EE := M E DX3
  let C2 := Ad C C; let C4 := Ad C2 C2; let C8 := Ad C4 C4
  let Y3 := Sb EE C8; let YZ := M Y Z; let Z3 := Ad YZ YZ
  { A, B, C, XB, XB2, T1, T2, D, A2, E, F, D2, X3, DX3, EE, C2, C4, C8, Y3, YZ, Z3 }

/-- `Nat` Jacobian addition trace, per-op reduced mod `m` (mirrors the addition gadget). -/
def addTraceM (m : Nat) (X1 Y1 Z1 X2 Y2 Z2 : Nat) : AddT Nat :=
  let M : Nat → Nat → Nat := fun x y => (x * y) % m
  let Ad : Nat → Nat → Nat := fun x y => (x + y) % m
  let Sb : Nat → Nat → Nat := fun x y => (x + m - y) % m
  let Z1Z1 := M Z1 Z1; let Z2Z2 := M Z2 Z2
  let U1 := M X1 Z2Z2; let U2 := M X2 Z1Z1
  let Y1Z2 := M Y1 Z2; let S1 := M Y1Z2 Z2Z2
  let Y2Z1 := M Y2 Z1; let S2 := M Y2Z1 Z1Z1
  let H := Sb U2 U1; let twoH := Ad H H; let I := M twoH twoH; let J := M H I
  let S2S1 := Sb S2 S1; let r := Ad S2S1 S2S1; let V := M U1 I
  let rr := M r r; let rrJ := Sb rr J; let twoV := Ad V V; let X3 := Sb rrJ twoV
  let VX3 := Sb V X3; let rVX3 := M r VX3; let S1J := M S1 J; let twoS1J := Ad S1J S1J
  let Y3 := Sb rVX3 twoS1J
  let Z1Z2 := Ad Z1 Z2; let Z1Z2s := M Z1Z2 Z1Z2; let t1 := Sb Z1Z2s Z1Z1; let t2 := Sb t1 Z2Z2
  let Z3 := M t2 H
  { Z1Z1, Z2Z2, U1, U2, Y1Z2, S1, Y2Z1, S2, H, twoH, I, J, S2S1, r, V, rr, rrJ, twoV, X3, VX3,
    rVX3, S1J, twoS1J, Y3, Z1Z2, Z1Z2s, t1, t2, Z3 }

/-- ℤ Jacobian doubling trace (the formula the forcing lemmas conclude against). -/
def dblTraceZ (X Y Z : ℤ) : DblT ℤ :=
  let A := X * X; let B := Y * Y; let C := B * B
  let XB := X + B; let XB2 := XB * XB
  let T1 := XB2 - A; let T2 := T1 - C
  let D := T2 + T2; let A2 := A + A; let E := A2 + A
  let F := E * E; let D2 := D + D; let X3 := F - D2
  let DX3 := D - X3; let EE := E * DX3
  let C2 := C + C; let C4 := C2 + C2; let C8 := C4 + C4
  let Y3 := EE - C8; let YZ := Y * Z; let Z3 := YZ + YZ
  { A, B, C, XB, XB2, T1, T2, D, A2, E, F, D2, X3, DX3, EE, C2, C4, C8, Y3, YZ, Z3 }

/-- ℤ Jacobian addition trace. -/
def addTraceZ (X1 Y1 Z1 X2 Y2 Z2 : ℤ) : AddT ℤ :=
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

/-- On-curve (Jacobian) `Y² = X³ + 5·Z⁶` over `ZMod m` (a wrong formula lands off-curve — the
non-vacuity check). -/
def oncurveM (m : Nat) (P : Nat × Nat × Nat) : Bool :=
  let M : Nat → Nat → Nat := fun x y => (x * y) % m
  let Z3v := M (M P.2.2 P.2.2) P.2.2
  M P.2.1 P.2.1 == (M (M P.1 P.1) P.1 + curveB * M Z3v Z3v) % m

/-- The endomorphism on a Jacobian point: `φ(X,Y,Z) = (ζ·X, Y, Z)` (affine `(ζ·x, y)`). -/
def endoJM (m xi : Nat) (P : Nat × Nat × Nat) : Nat × Nat × Nat :=
  ((xi * P.1) % m, P.2.1, P.2.2)

/-- Jacobian point equality over `ZMod m`, cross-multiplied (no inversion):
`X1·Z2² = X2·Z1²` and `Y1·Z2³ = Y2·Z1³`. -/
def jacEqM (m : Nat) (P Q : Nat × Nat × Nat) : Bool :=
  let M : Nat → Nat → Nat := fun x y => (x * y) % m
  let Z1sq := M P.2.2 P.2.2; let Z2sq := M Q.2.2 Q.2.2
  M P.1 Z2sq == M Q.1 Z1sq && M P.2.1 (M Z2sq Q.2.2) == M Q.2.1 (M Z1sq P.2.2)

/-- Reference scalar mul (double-and-add over the low 255 bits, `Option` for the identity start).
KAT AID ONLY — the gadget scalar mul is K4. -/
def scMulM (m k : Nat) (P : Nat × Nat × Nat) : Option (Nat × Nat × Nat) :=
  ((List.range 255).foldl (fun acc i =>
    let R := acc.1; let D := acc.2
    let R' := if k.testBit i then
        (match R with
         | none => some D
         | some Rv => some (addTraceM m Rv.1 Rv.2.1 Rv.2.2 D.1 D.2.1 D.2.2).toPt)
      else R
    (R', (dblTraceM m D.1 D.2.1 D.2.2).toPt)) ((none : Option (Nat × Nat × Nat)), P)).1

/-! ### KAT anchors — Python-computed (identical formulas), affine-cross-checked. -/

/-- `[2]·G` on Pallas (Jacobian trace output). -/
def Gp2 : Nat × Nat × Nat := (dblTraceM pN Gp.1 Gp.2 1).toPt
/-- `[3]·G` on Pallas (`2G + G`). -/
def Gp3 : Nat × Nat × Nat := (addTraceM pN Gp2.1 Gp2.2.1 Gp2.2.2 Gp.1 Gp.2 1).toPt
/-- `[2]·G` on Vesta. -/
def Gv2 : Nat × Nat × Nat := (dblTraceM qN Gv.1 Gv.2 1).toPt
/-- `[3]·G` on Vesta. -/
def Gv3 : Nat × Nat × Nat := (addTraceM qN Gv2.1 Gv2.2.1 Gv2.2.2 Gv.1 Gv.2 1).toPt

-- External anchors (independent Python computation, cross-checked against affine scalar muls).
#guard Gp2 ==
  ( 28948022309329048855892746252171976963363056481941560715954676764349967630298
  , 28948022309329048855892746252171976963363056481941560715954676764349967630238
  , 24837309565766651186828884854098791575926986825302938889117194811144354289014 )
#guard Gp3 ==
  ( 837216
  , 28948022309329048855892746252171976963363056481941560715954676764349038429441
  , 3114595879060773104022896381874226523590239938481742705661455654392136339368 )
#guard Gv2 ==
  ( 28948022309329048855892746252171976963363056481941647379679742748393362948058
  , 28948022309329048855892746252171976963363056481941647379679742748393362947998
  , 22853813858910723687136404599984229041696401982168055026778894953118908208324 )
#guard Gv3 ==
  ( 837216
  , 28948022309329048855892746252171976963363056481941647379679742748392433747201
  , 13726337599175347845805100632987139880804058040951842785846232002039502387221 )

-- On-curve invariants: the generators, doubled, and 2G+G stay on `y² = x³ + 5Z⁶`.
#guard oncurveM pN GpJ == true
#guard oncurveM pN Gp2 == true
#guard oncurveM pN Gp3 == true
#guard oncurveM qN GvJ == true
#guard oncurveM qN Gv2 == true
#guard oncurveM qN Gv3 == true
-- The endomorphism PRESERVES the curve (because `ζ³ = 1`: `(ζx)³ + 5 = x³ + 5`).
#guard oncurveM pN (endoJM pN zetaP GpJ) == true
#guard oncurveM qN (endoJM qN zetaQ GvJ) == true

-- THE GLV correspondence, kernel-verified: `φ(G) = [λ]·G` on BOTH curves (real 255-bit
-- scalar muls of the generators, Jacobian cross-multiplied — no affine inversion).
#guard jacEqM pN (endoJM pN zetaP GpJ) ((scMulM pN lambdaPallas GpJ).get!) == true
#guard jacEqM qN (endoJM qN zetaQ GvJ) ((scMulM qN lambdaVesta GvJ).get!) == true

/-! ## §2 — The GENERATED curve gadgets.

One generic short-Weierstrass builder per operation, parameterized by the three field-core
constructors (`mulC addC subC : Nat → Nat → Nat → Nat → VmConstraint2`); instantiated with K1's
`fp*Core` (Pallas, modulus `p`) and `fq*Core` (Vesta, modulus `q`). Layout: 9-limb field groups
(K1's `numLimbs = 9`), then quotient groups (one per mul), then carry/borrow bits (one per
add/sub). -/

/-- **Generic Jacobian doubling gadget** (dbl-2009-l): 7 muls + 14 adds/subs = **21 core gates**.
Inputs `X,Y,Z` (9-limb groups); 21 intermediates at `fresh..fresh+188`, 7 quotient groups at
`fresh+189..fresh+251`, 14 carry/borrow bits at `fresh+252..fresh+265`; next fresh `fresh + 266`. -/
def swDoubleGadget (mulC addC subC : Nat → Nat → Nat → Nat → VmConstraint2)
    (X Y Z fresh : Nat) : List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  let A := fresh; let B := fresh + 9; let C := fresh + 18; let XB := fresh + 27
  let XB2 := fresh + 36; let T1 := fresh + 45; let T2 := fresh + 54; let D := fresh + 63
  let A2 := fresh + 72; let E := fresh + 81; let F := fresh + 90; let D2 := fresh + 99
  let X3 := fresh + 108; let DX3 := fresh + 117; let EE := fresh + 126; let C2 := fresh + 135
  let C4 := fresh + 144; let C8 := fresh + 153; let Y3 := fresh + 162; let YZ := fresh + 171
  let Z3 := fresh + 180
  let q0 := fresh + 189
  let b0 := fresh + 252
  ( [ mulC X X A q0              -- A = X²
    , mulC Y Y B (q0 + 9)        -- B = Y²
    , mulC B B C (q0 + 18)       -- C = B²
    , addC X B XB b0             -- XB = X + B
    , mulC XB XB XB2 (q0 + 27)   -- XB2 = XB²
    , subC XB2 A T1 (b0 + 1)     -- T1 = XB2 − A
    , subC T1 C T2 (b0 + 2)      -- T2 = T1 − C
    , addC T2 T2 D (b0 + 3)      -- D = 2·inner
    , addC A A A2 (b0 + 4)       -- A2 = 2A
    , addC A2 A E (b0 + 5)       -- E = 3A
    , mulC E E F (q0 + 36)       -- F = E²
    , addC D D D2 (b0 + 6)       -- D2 = 2D
    , subC F D2 X3 (b0 + 7)      -- X3 = F − 2D
    , subC D X3 DX3 (b0 + 8)     -- DX3 = D − X3
    , mulC E DX3 EE (q0 + 45)    -- EE = E·(D−X3)
    , addC C C C2 (b0 + 9)       -- C2 = 2C
    , addC C2 C2 C4 (b0 + 10)    -- C4 = 4C
    , addC C4 C4 C8 (b0 + 11)    -- C8 = 8C
    , subC EE C8 Y3 (b0 + 12)    -- Y3 = EE − 8C
    , mulC Y Z YZ (q0 + 54)      -- YZ = Y·Z
    , addC YZ YZ Z3 (b0 + 13)    -- Z3 = 2YZ
    ], (X3, Y3, Z3), fresh + 266 )

/-- **Generic Jacobian addition gadget** (add-2007-bl): 16 muls + 13 adds/subs = **29 core gates**.
Inputs `X1..Z2`; 29 intermediates at `fresh..fresh+260`, 16 quotient groups at
`fresh+261..fresh+404`, 13 carry/borrow bits at `fresh+405..fresh+417`; next fresh `fresh + 418`. -/
def swAddGadget (mulC addC subC : Nat → Nat → Nat → Nat → VmConstraint2)
    (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat) : List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  let Z1Z1 := fresh; let Z2Z2 := fresh + 9; let U1 := fresh + 18; let U2 := fresh + 27
  let Y1Z2 := fresh + 36; let S1 := fresh + 45; let Y2Z1 := fresh + 54; let S2 := fresh + 63
  let H := fresh + 72; let twoH := fresh + 81; let I := fresh + 90; let J := fresh + 99
  let S2S1 := fresh + 108; let r := fresh + 117; let V := fresh + 126; let rr := fresh + 135
  let rrJ := fresh + 144; let twoV := fresh + 153; let X3 := fresh + 162; let VX3 := fresh + 171
  let rVX3 := fresh + 180; let S1J := fresh + 189; let twoS1J := fresh + 198; let Y3 := fresh + 207
  let Z1Z2 := fresh + 216; let Z1Z2s := fresh + 225; let t1 := fresh + 234; let t2 := fresh + 243
  let Z3 := fresh + 252
  let q0 := fresh + 261
  let b0 := fresh + 405
  ( [ mulC Z1 Z1 Z1Z1 q0           -- Z1Z1 = Z1²
    , mulC Z2 Z2 Z2Z2 (q0 + 9)     -- Z2Z2 = Z2²
    , mulC X1 Z2Z2 U1 (q0 + 18)    -- U1 = X1·Z2Z2
    , mulC X2 Z1Z1 U2 (q0 + 27)    -- U2 = X2·Z1Z1
    , mulC Y1 Z2 Y1Z2 (q0 + 36)    -- Y1Z2 = Y1·Z2
    , mulC Y1Z2 Z2Z2 S1 (q0 + 45)  -- S1 = Y1·Z2·Z2Z2
    , mulC Y2 Z1 Y2Z1 (q0 + 54)    -- Y2Z1 = Y2·Z1
    , mulC Y2Z1 Z1Z1 S2 (q0 + 63)  -- S2 = Y2·Z1·Z1Z1
    , subC U2 U1 H b0              -- H = U2 − U1
    , addC H H twoH (b0 + 1)       -- twoH = 2H
    , mulC twoH twoH I (q0 + 72)   -- I = (2H)²
    , mulC H I J (q0 + 81)         -- J = H·I
    , subC S2 S1 S2S1 (b0 + 2)     -- S2S1 = S2 − S1
    , addC S2S1 S2S1 r (b0 + 3)    -- r = 2(S2 − S1)
    , mulC U1 I V (q0 + 90)        -- V = U1·I
    , mulC r r rr (q0 + 99)        -- rr = r²
    , subC rr J rrJ (b0 + 4)       -- rrJ = r² − J
    , addC V V twoV (b0 + 5)       -- twoV = 2V
    , subC rrJ twoV X3 (b0 + 6)    -- X3 = r² − J − 2V
    , subC V X3 VX3 (b0 + 7)       -- VX3 = V − X3
    , mulC r VX3 rVX3 (q0 + 108)   -- rVX3 = r·(V − X3)
    , mulC S1 J S1J (q0 + 117)     -- S1J = S1·J
    , addC S1J S1J twoS1J (b0 + 8) -- twoS1J = 2·S1·J
    , subC rVX3 twoS1J Y3 (b0 + 9) -- Y3 = r(V−X3) − 2S1J
    , addC Z1 Z2 Z1Z2 (b0 + 10)    -- Z1Z2 = Z1 + Z2
    , mulC Z1Z2 Z1Z2 Z1Z2s (q0 + 126) -- Z1Z2s = (Z1+Z2)²
    , subC Z1Z2s Z1Z1 t1 (b0 + 11) -- t1 = (Z1+Z2)² − Z1Z1
    , subC t1 Z2Z2 t2 (b0 + 12)    -- t2 = t1 − Z2Z2
    , mulC t2 H Z3 (q0 + 135)      -- Z3 = t2·H
    ], (X3, Y3, Z3), fresh + 418 )

/-- **`pallasDoubleGadget`** — Pallas `[2]P` over Fp (21 core gates, K1's `fp*Core`). -/
def pallasDoubleGadget := swDoubleGadget fpMulCore fpAddCore fpSubCore
/-- **`pallasAddGadget`** — Pallas `P + Q` over Fp (29 core gates). -/
def pallasAddGadget := swAddGadget fpMulCore fpAddCore fpSubCore
/-- **`vestaDoubleGadget`** — Vesta `[2]P` over Fq (21 core gates, K1's `fq*Core`). -/
def vestaDoubleGadget := swDoubleGadget fqMulCore fqAddCore fqSubCore
/-- **`vestaAddGadget`** — Vesta `P + Q` over Fq (29 core gates). -/
def vestaAddGadget := swAddGadget fqMulCore fqAddCore fqSubCore

/-- The ζ-pin head for Pallas: `fpValue zetaB − ζ_p`; zero forces the ζ columns to reconstruct
EXACTLY to `ζ_p` (a one-gate constant pin — the head's constant carries `−ζ`). -/
def zetaPinHeadP (zetaB : Nat) : Head := (fpValue zetaB).addConst (-(zetaP : ℤ))
/-- The ζ-pin head for Vesta. -/
def zetaPinHeadQ (zetaB : Nat) : Head := (fpValue zetaB).addConst (-(zetaQ : ℤ))

/-- **`pallasEndoGadget`** — the Pallas endomorphism `φ(X,Y,Z) = (ζ_p·X, Y, Z)`: the ζ pin plus
ONE `fpMulCore` (`X3 = ζ·X`); `Y`/`Z` pass through (wire relabel, no gate). **2 core gates.** -/
def pallasEndoGadget (xB zetaB x3B qB : Nat) : List VmConstraint2 :=
  [cgH (zetaPinHeadP zetaB), fpMulCore xB zetaB x3B qB]
/-- **`vestaEndoGadget`** — the Vesta endomorphism, modulus `q`. **2 core gates.** -/
def vestaEndoGadget (xB zetaB x3B qB : Nat) : List VmConstraint2 :=
  [cgH (zetaPinHeadQ zetaB), fqMulCore xB zetaB x3B qB]

/-! ## §3 — Forcing: the curve gadgets force the real ℤ point-ops (congruence algebra `CZm`).

`CZm m u v := m ∣ (u − v)` — "u ≡ v (mod m)" — the modulus-parameterized crib of
`Bls12381Forcing.CZ` (that one is hardcoded to the BLS prime; we need two moduli). Each curve's
forcing lemma is a direct `CZm`-chain proof over its K1 core forcings (the BLS pattern). -/

/-- Congruence mod `m` over ℤ. -/
def CZm (m : ℤ) (u v : ℤ) : Prop := m ∣ (u - v)

namespace CZm

variable {m : ℤ}

theorem refl (u : ℤ) : CZm m u u := by unfold CZm; simp
theorem symm {u v : ℤ} (h : CZm m u v) : CZm m v u := by
  unfold CZm at *; rw [show v - u = -(u - v) by ring]; exact dvd_neg.mpr h
theorem trans {u v w : ℤ} (h1 : CZm m u v) (h2 : CZm m v w) : CZm m u w := by
  unfold CZm at *; rw [show u - w = (u - v) + (v - w) by ring]; exact dvd_add h1 h2
theorem add {a a' b b' : ℤ} (h1 : CZm m a a') (h2 : CZm m b b') : CZm m (a + b) (a' + b') := by
  unfold CZm at *; rw [show a + b - (a' + b') = (a - a') + (b - b') by ring]; exact dvd_add h1 h2
theorem sub {a a' b b' : ℤ} (h1 : CZm m a a') (h2 : CZm m b b') : CZm m (a - b) (a' - b') := by
  unfold CZm at *; rw [show a - b - (a' - b') = (a - a') - (b - b') by ring]; exact dvd_sub h1 h2
theorem mul {a a' b b' : ℤ} (h1 : CZm m a a') (h2 : CZm m b b') : CZm m (a * b) (a' * b') := by
  unfold CZm at *
  have hrw : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [hrw]; exact dvd_add (dvd_mul_of_dvd_left h1 b) (dvd_mul_of_dvd_right h2 a')

end CZm

/-- Congruence mod the Pallas-base/Vesta-scalar prime `p`. -/
abbrev CZp := CZm p
/-- Congruence mod the Vesta-base/Pallas-scalar prime `q`. -/
abbrev CZq := CZm q

/-- The `addConst` evaluation rule (a one-line `evalH` fact the ζ-pin forcing rewrites with). -/
theorem evalH_addConst (a : Assignment) (h : Head) (k : ℤ) :
    evalH (h.addConst k) a = evalH h a + k := by
  simp only [evalH, Head.addConst]; ring

/-- The ζ-pin gate FORCES the ζ columns to reconstruct to `ζ_p`. -/
theorem zetaPinP_forces (a : Assignment) (zetaB : Nat)
    (hg : evalH (zetaPinHeadP zetaB) a = 0) : fpVal a zetaB = (zetaP : ℤ) := by
  rw [zetaPinHeadP, evalH_addConst, fpVal_eq] at hg; linarith
/-- The ζ-pin gate FORCES the ζ columns to reconstruct to `ζ_q`. -/
theorem zetaPinQ_forces (a : Assignment) (zetaB : Nat)
    (hg : evalH (zetaPinHeadQ zetaB) a = 0) : fpVal a zetaB = (zetaQ : ℤ) := by
  rw [zetaPinHeadQ, evalH_addConst, fpVal_eq] at hg; linarith

/-- Fp bridge: a satisfied `fpMulCore` forces `z ≡ x·y (mod p)`. -/
private theorem mulCZp {a : Assignment} {x y z qb : Nat}
    (h : evalH (fpMulHead x y z qb) a = 0) : CZp (fpVal a z) (fpVal a x * fpVal a y) :=
  CZm.symm (fpMulCore_forces a x y z qb h)
/-- Fp bridge: a satisfied `fpAddCore` forces `z ≡ x+y (mod p)`. -/
private theorem addCZp {a : Assignment} {x y z c : Nat}
    (h : evalH (fpAddHead x y z c) a = 0) : CZp (fpVal a z) (fpVal a x + fpVal a y) :=
  CZm.symm (fpAddCore_forces a x y z c h)
/-- Fp bridge: a satisfied `fpSubCore` forces `z ≡ x−y (mod p)`. -/
private theorem subCZp {a : Assignment} {x y z c : Nat}
    (h : evalH (fpSubHead x y z c) a = 0) : CZp (fpVal a z) (fpVal a x - fpVal a y) :=
  CZm.symm (fpSubCore_forces a x y z c h)
/-- Fq bridge: a satisfied `fqMulCore` forces `z ≡ x·y (mod q)`. -/
private theorem mulCZq {a : Assignment} {x y z qb : Nat}
    (h : evalH (fqMulHead x y z qb) a = 0) : CZq (fpVal a z) (fpVal a x * fpVal a y) :=
  CZm.symm (fqMulCore_forces a x y z qb h)
/-- Fq bridge: a satisfied `fqAddCore` forces `z ≡ x+y (mod q)`. -/
private theorem addCZq {a : Assignment} {x y z c : Nat}
    (h : evalH (fqAddHead x y z c) a = 0) : CZq (fpVal a z) (fpVal a x + fpVal a y) :=
  CZm.symm (fqAddCore_forces a x y z c h)
/-- Fq bridge: a satisfied `fqSubCore` forces `z ≡ x−y (mod q)`. -/
private theorem subCZq {a : Assignment} {x y z c : Nat}
    (h : evalH (fqSubHead x y z c) a = 0) : CZq (fpVal a z) (fpVal a x - fpVal a y) :=
  CZm.symm (fqSubCore_forces a x y z c h)

/-- **`pallasDouble_forces`** — the 21 raw gate satisfactions of `pallasDoubleGadget` force
`(X3,Y3,Z3) ≡ dblTraceZ (X,Y,Z)` mod the real Pallas-base prime `p`, via the `CZm` chain (the
direct-proof pattern of `Bls12381Forcing.g1Double_forces`; a generic-in-bridge-variables
formulation was tried and abandoned — its instantiation cost whnf-exploded). -/
theorem pallasDouble_forces (a : Assignment)
    {Xc Yc Zc Ac Bc Cc XBc XB2c T1c T2c Dc A2c Ec Fc D2c X3c DX3c EEc C2c C4c C8c Y3c YZc Z3c
     qAc qBc qCc qXB2c qFc qEEc qYZc cXBc bT1c bT2c cDc cA2c cEc cD2c bX3c bDX3c cC2c cC4c cC8c
     bY3c cZ3c : Nat}
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
    CZp (fpVal a X3c) (dblTraceZ (fpVal a Xc) (fpVal a Yc) (fpVal a Zc)).X3
    ∧ CZp (fpVal a Y3c) (dblTraceZ (fpVal a Xc) (fpVal a Yc) (fpVal a Zc)).Y3
    ∧ CZp (fpVal a Z3c) (dblTraceZ (fpVal a Xc) (fpVal a Yc) (fpVal a Zc)).Z3 := by
  let T := dblTraceZ (fpVal a Xc) (fpVal a Yc) (fpVal a Zc)
  have fA : CZp (fpVal a Ac) T.A := mulCZp hA
  have fB : CZp (fpVal a Bc) T.B := mulCZp hB
  have fC : CZp (fpVal a Cc) T.C := CZm.trans (mulCZp hC) (CZm.mul fB fB)
  have fXB : CZp (fpVal a XBc) T.XB := CZm.trans (addCZp hXB) (CZm.add (CZm.refl _) fB)
  have fXB2 : CZp (fpVal a XB2c) T.XB2 := CZm.trans (mulCZp hXB2) (CZm.mul fXB fXB)
  have fT1 : CZp (fpVal a T1c) T.T1 := CZm.trans (subCZp hT1) (CZm.sub fXB2 fA)
  have fT2 : CZp (fpVal a T2c) T.T2 := CZm.trans (subCZp hT2) (CZm.sub fT1 fC)
  have fD : CZp (fpVal a Dc) T.D := CZm.trans (addCZp hD) (CZm.add fT2 fT2)
  have fA2 : CZp (fpVal a A2c) T.A2 := CZm.trans (addCZp hA2) (CZm.add fA fA)
  have fE : CZp (fpVal a Ec) T.E := CZm.trans (addCZp hE) (CZm.add fA2 fA)
  have fF : CZp (fpVal a Fc) T.F := CZm.trans (mulCZp hF) (CZm.mul fE fE)
  have fD2 : CZp (fpVal a D2c) T.D2 := CZm.trans (addCZp hD2) (CZm.add fD fD)
  have fX3 : CZp (fpVal a X3c) T.X3 := CZm.trans (subCZp hX3) (CZm.sub fF fD2)
  have fDX3 : CZp (fpVal a DX3c) T.DX3 := CZm.trans (subCZp hDX3) (CZm.sub fD fX3)
  have fEE : CZp (fpVal a EEc) T.EE := CZm.trans (mulCZp hEE) (CZm.mul fE fDX3)
  have fC2 : CZp (fpVal a C2c) T.C2 := CZm.trans (addCZp hC2) (CZm.add fC fC)
  have fC4 : CZp (fpVal a C4c) T.C4 := CZm.trans (addCZp hC4) (CZm.add fC2 fC2)
  have fC8 : CZp (fpVal a C8c) T.C8 := CZm.trans (addCZp hC8) (CZm.add fC4 fC4)
  have fY3 : CZp (fpVal a Y3c) T.Y3 := CZm.trans (subCZp hY3) (CZm.sub fEE fC8)
  have fYZ : CZp (fpVal a YZc) T.YZ := mulCZp hYZ
  have fZ3 : CZp (fpVal a Z3c) T.Z3 := CZm.trans (addCZp hZ3) (CZm.add fYZ fYZ)
  exact ⟨fX3, fY3, fZ3⟩

/-- **`vestaDouble_forces`** — the Vesta doubling gadget forces the real Fq doubling. -/
theorem vestaDouble_forces (a : Assignment)
    {Xc Yc Zc Ac Bc Cc XBc XB2c T1c T2c Dc A2c Ec Fc D2c X3c DX3c EEc C2c C4c C8c Y3c YZc Z3c
     qAc qBc qCc qXB2c qFc qEEc qYZc cXBc bT1c bT2c cDc cA2c cEc cD2c bX3c bDX3c cC2c cC4c cC8c
     bY3c cZ3c : Nat}
    (hA : evalH (fqMulHead Xc Xc Ac qAc) a = 0)
    (hB : evalH (fqMulHead Yc Yc Bc qBc) a = 0)
    (hC : evalH (fqMulHead Bc Bc Cc qCc) a = 0)
    (hXB : evalH (fqAddHead Xc Bc XBc cXBc) a = 0)
    (hXB2 : evalH (fqMulHead XBc XBc XB2c qXB2c) a = 0)
    (hT1 : evalH (fqSubHead XB2c Ac T1c bT1c) a = 0)
    (hT2 : evalH (fqSubHead T1c Cc T2c bT2c) a = 0)
    (hD : evalH (fqAddHead T2c T2c Dc cDc) a = 0)
    (hA2 : evalH (fqAddHead Ac Ac A2c cA2c) a = 0)
    (hE : evalH (fqAddHead A2c Ac Ec cEc) a = 0)
    (hF : evalH (fqMulHead Ec Ec Fc qFc) a = 0)
    (hD2 : evalH (fqAddHead Dc Dc D2c cD2c) a = 0)
    (hX3 : evalH (fqSubHead Fc D2c X3c bX3c) a = 0)
    (hDX3 : evalH (fqSubHead Dc X3c DX3c bDX3c) a = 0)
    (hEE : evalH (fqMulHead Ec DX3c EEc qEEc) a = 0)
    (hC2 : evalH (fqAddHead Cc Cc C2c cC2c) a = 0)
    (hC4 : evalH (fqAddHead C2c C2c C4c cC4c) a = 0)
    (hC8 : evalH (fqAddHead C4c C4c C8c cC8c) a = 0)
    (hY3 : evalH (fqSubHead EEc C8c Y3c bY3c) a = 0)
    (hYZ : evalH (fqMulHead Yc Zc YZc qYZc) a = 0)
    (hZ3 : evalH (fqAddHead YZc YZc Z3c cZ3c) a = 0) :
    CZq (fpVal a X3c) (dblTraceZ (fpVal a Xc) (fpVal a Yc) (fpVal a Zc)).X3
    ∧ CZq (fpVal a Y3c) (dblTraceZ (fpVal a Xc) (fpVal a Yc) (fpVal a Zc)).Y3
    ∧ CZq (fpVal a Z3c) (dblTraceZ (fpVal a Xc) (fpVal a Yc) (fpVal a Zc)).Z3 := by
  let T := dblTraceZ (fpVal a Xc) (fpVal a Yc) (fpVal a Zc)
  have fA : CZq (fpVal a Ac) T.A := mulCZq hA
  have fB : CZq (fpVal a Bc) T.B := mulCZq hB
  have fC : CZq (fpVal a Cc) T.C := CZm.trans (mulCZq hC) (CZm.mul fB fB)
  have fXB : CZq (fpVal a XBc) T.XB := CZm.trans (addCZq hXB) (CZm.add (CZm.refl _) fB)
  have fXB2 : CZq (fpVal a XB2c) T.XB2 := CZm.trans (mulCZq hXB2) (CZm.mul fXB fXB)
  have fT1 : CZq (fpVal a T1c) T.T1 := CZm.trans (subCZq hT1) (CZm.sub fXB2 fA)
  have fT2 : CZq (fpVal a T2c) T.T2 := CZm.trans (subCZq hT2) (CZm.sub fT1 fC)
  have fD : CZq (fpVal a Dc) T.D := CZm.trans (addCZq hD) (CZm.add fT2 fT2)
  have fA2 : CZq (fpVal a A2c) T.A2 := CZm.trans (addCZq hA2) (CZm.add fA fA)
  have fE : CZq (fpVal a Ec) T.E := CZm.trans (addCZq hE) (CZm.add fA2 fA)
  have fF : CZq (fpVal a Fc) T.F := CZm.trans (mulCZq hF) (CZm.mul fE fE)
  have fD2 : CZq (fpVal a D2c) T.D2 := CZm.trans (addCZq hD2) (CZm.add fD fD)
  have fX3 : CZq (fpVal a X3c) T.X3 := CZm.trans (subCZq hX3) (CZm.sub fF fD2)
  have fDX3 : CZq (fpVal a DX3c) T.DX3 := CZm.trans (subCZq hDX3) (CZm.sub fD fX3)
  have fEE : CZq (fpVal a EEc) T.EE := CZm.trans (mulCZq hEE) (CZm.mul fE fDX3)
  have fC2 : CZq (fpVal a C2c) T.C2 := CZm.trans (addCZq hC2) (CZm.add fC fC)
  have fC4 : CZq (fpVal a C4c) T.C4 := CZm.trans (addCZq hC4) (CZm.add fC2 fC2)
  have fC8 : CZq (fpVal a C8c) T.C8 := CZm.trans (addCZq hC8) (CZm.add fC4 fC4)
  have fY3 : CZq (fpVal a Y3c) T.Y3 := CZm.trans (subCZq hY3) (CZm.sub fEE fC8)
  have fYZ : CZq (fpVal a YZc) T.YZ := mulCZq hYZ
  have fZ3 : CZq (fpVal a Z3c) T.Z3 := CZm.trans (addCZq hZ3) (CZm.add fYZ fYZ)
  exact ⟨fX3, fY3, fZ3⟩

/-- **`pallasAdd_forces`** — the 29 raw gate satisfactions of `pallasAddGadget` force
`(X3,Y3,Z3) ≡ addTraceZ (P,Q)` mod `p`. -/
theorem pallasAdd_forces (a : Assignment)
    {X1c Y1c Z1c X2c Y2c Z2c Z1Z1c Z2Z2c U1c U2c Y1Z2c S1c Y2Z1c S2c Hc twoHc Ic Jc S2S1c rc Vc
     rrc rrJc twoVc X3c VX3c rVX3c S1Jc twoS1Jc Y3c Z1Z2c Z1Z2sc t1c t2c Z3c
     qZ1Z1 qZ2Z2 qU1 qU2 qY1Z2 qS1 qY2Z1 qS2 qI qJ qV qrr qrVX3 qS1J qZ1Z2s qZ3
     bH ctwoH bS2S1 cr brrJ ctwoV bX3 bVX3 ctwoS1J bY3 cZ1Z2 bt1 bt2 : Nat}
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
    CZp (fpVal a X3c) (addTraceZ (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                        (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).X3
    ∧ CZp (fpVal a Y3c) (addTraceZ (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                        (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).Y3
    ∧ CZp (fpVal a Z3c) (addTraceZ (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                        (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).Z3 := by
  let T := addTraceZ (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
             (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)
  have fZ1Z1 : CZp (fpVal a Z1Z1c) T.Z1Z1 := mulCZp hZ1Z1
  have fZ2Z2 : CZp (fpVal a Z2Z2c) T.Z2Z2 := mulCZp hZ2Z2
  have fU1 : CZp (fpVal a U1c) T.U1 := CZm.trans (mulCZp hU1) (CZm.mul (CZm.refl _) fZ2Z2)
  have fU2 : CZp (fpVal a U2c) T.U2 := CZm.trans (mulCZp hU2) (CZm.mul (CZm.refl _) fZ1Z1)
  have fY1Z2 : CZp (fpVal a Y1Z2c) T.Y1Z2 := mulCZp hY1Z2
  have fS1 : CZp (fpVal a S1c) T.S1 := CZm.trans (mulCZp hS1) (CZm.mul fY1Z2 fZ2Z2)
  have fY2Z1 : CZp (fpVal a Y2Z1c) T.Y2Z1 := mulCZp hY2Z1
  have fS2 : CZp (fpVal a S2c) T.S2 := CZm.trans (mulCZp hS2) (CZm.mul fY2Z1 fZ1Z1)
  have fH : CZp (fpVal a Hc) T.H := CZm.trans (subCZp hH) (CZm.sub fU2 fU1)
  have ftwoH : CZp (fpVal a twoHc) T.twoH := CZm.trans (addCZp htwoH) (CZm.add fH fH)
  have fI : CZp (fpVal a Ic) T.I := CZm.trans (mulCZp hI) (CZm.mul ftwoH ftwoH)
  have fJ : CZp (fpVal a Jc) T.J := CZm.trans (mulCZp hJ) (CZm.mul fH fI)
  have fS2S1 : CZp (fpVal a S2S1c) T.S2S1 := CZm.trans (subCZp hS2S1) (CZm.sub fS2 fS1)
  have fr : CZp (fpVal a rc) T.r := CZm.trans (addCZp hr) (CZm.add fS2S1 fS2S1)
  have fV : CZp (fpVal a Vc) T.V := CZm.trans (mulCZp hV) (CZm.mul fU1 fI)
  have frr : CZp (fpVal a rrc) T.rr := CZm.trans (mulCZp hrr) (CZm.mul fr fr)
  have frrJ : CZp (fpVal a rrJc) T.rrJ := CZm.trans (subCZp hrrJ) (CZm.sub frr fJ)
  have ftwoV : CZp (fpVal a twoVc) T.twoV := CZm.trans (addCZp htwoV) (CZm.add fV fV)
  have fX3 : CZp (fpVal a X3c) T.X3 := CZm.trans (subCZp hX3) (CZm.sub frrJ ftwoV)
  have fVX3 : CZp (fpVal a VX3c) T.VX3 := CZm.trans (subCZp hVX3) (CZm.sub fV fX3)
  have frVX3 : CZp (fpVal a rVX3c) T.rVX3 := CZm.trans (mulCZp hrVX3) (CZm.mul fr fVX3)
  have fS1J : CZp (fpVal a S1Jc) T.S1J := CZm.trans (mulCZp hS1J) (CZm.mul fS1 fJ)
  have ftwoS1J : CZp (fpVal a twoS1Jc) T.twoS1J :=
    CZm.trans (addCZp htwoS1J) (CZm.add fS1J fS1J)
  have fY3 : CZp (fpVal a Y3c) T.Y3 := CZm.trans (subCZp hY3) (CZm.sub frVX3 ftwoS1J)
  have fZ1Z2 : CZp (fpVal a Z1Z2c) T.Z1Z2 := addCZp hZ1Z2
  have fZ1Z2s : CZp (fpVal a Z1Z2sc) T.Z1Z2s :=
    CZm.trans (mulCZp hZ1Z2s) (CZm.mul fZ1Z2 fZ1Z2)
  have ft1 : CZp (fpVal a t1c) T.t1 := CZm.trans (subCZp ht1) (CZm.sub fZ1Z2s fZ1Z1)
  have ft2 : CZp (fpVal a t2c) T.t2 := CZm.trans (subCZp ht2) (CZm.sub ft1 fZ2Z2)
  have fZ3 : CZp (fpVal a Z3c) T.Z3 := CZm.trans (mulCZp hZ3) (CZm.mul ft2 fH)
  exact ⟨fX3, fY3, fZ3⟩

/-- **`vestaAdd_forces`** — the Vesta addition gadget forces the real Fq addition. -/
theorem vestaAdd_forces (a : Assignment)
    {X1c Y1c Z1c X2c Y2c Z2c Z1Z1c Z2Z2c U1c U2c Y1Z2c S1c Y2Z1c S2c Hc twoHc Ic Jc S2S1c rc Vc
     rrc rrJc twoVc X3c VX3c rVX3c S1Jc twoS1Jc Y3c Z1Z2c Z1Z2sc t1c t2c Z3c
     qZ1Z1 qZ2Z2 qU1 qU2 qY1Z2 qS1 qY2Z1 qS2 qI qJ qV qrr qrVX3 qS1J qZ1Z2s qZ3
     bH ctwoH bS2S1 cr brrJ ctwoV bX3 bVX3 ctwoS1J bY3 cZ1Z2 bt1 bt2 : Nat}
    (hZ1Z1 : evalH (fqMulHead Z1c Z1c Z1Z1c qZ1Z1) a = 0)
    (hZ2Z2 : evalH (fqMulHead Z2c Z2c Z2Z2c qZ2Z2) a = 0)
    (hU1 : evalH (fqMulHead X1c Z2Z2c U1c qU1) a = 0)
    (hU2 : evalH (fqMulHead X2c Z1Z1c U2c qU2) a = 0)
    (hY1Z2 : evalH (fqMulHead Y1c Z2c Y1Z2c qY1Z2) a = 0)
    (hS1 : evalH (fqMulHead Y1Z2c Z2Z2c S1c qS1) a = 0)
    (hY2Z1 : evalH (fqMulHead Y2c Z1c Y2Z1c qY2Z1) a = 0)
    (hS2 : evalH (fqMulHead Y2Z1c Z1Z1c S2c qS2) a = 0)
    (hH : evalH (fqSubHead U2c U1c Hc bH) a = 0)
    (htwoH : evalH (fqAddHead Hc Hc twoHc ctwoH) a = 0)
    (hI : evalH (fqMulHead twoHc twoHc Ic qI) a = 0)
    (hJ : evalH (fqMulHead Hc Ic Jc qJ) a = 0)
    (hS2S1 : evalH (fqSubHead S2c S1c S2S1c bS2S1) a = 0)
    (hr : evalH (fqAddHead S2S1c S2S1c rc cr) a = 0)
    (hV : evalH (fqMulHead U1c Ic Vc qV) a = 0)
    (hrr : evalH (fqMulHead rc rc rrc qrr) a = 0)
    (hrrJ : evalH (fqSubHead rrc Jc rrJc brrJ) a = 0)
    (htwoV : evalH (fqAddHead Vc Vc twoVc ctwoV) a = 0)
    (hX3 : evalH (fqSubHead rrJc twoVc X3c bX3) a = 0)
    (hVX3 : evalH (fqSubHead Vc X3c VX3c bVX3) a = 0)
    (hrVX3 : evalH (fqMulHead rc VX3c rVX3c qrVX3) a = 0)
    (hS1J : evalH (fqMulHead S1c Jc S1Jc qS1J) a = 0)
    (htwoS1J : evalH (fqAddHead S1Jc S1Jc twoS1Jc ctwoS1J) a = 0)
    (hY3 : evalH (fqSubHead rVX3c twoS1Jc Y3c bY3) a = 0)
    (hZ1Z2 : evalH (fqAddHead Z1c Z2c Z1Z2c cZ1Z2) a = 0)
    (hZ1Z2s : evalH (fqMulHead Z1Z2c Z1Z2c Z1Z2sc qZ1Z2s) a = 0)
    (ht1 : evalH (fqSubHead Z1Z2sc Z1Z1c t1c bt1) a = 0)
    (ht2 : evalH (fqSubHead t1c Z2Z2c t2c bt2) a = 0)
    (hZ3 : evalH (fqMulHead t2c Hc Z3c qZ3) a = 0) :
    CZq (fpVal a X3c) (addTraceZ (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                        (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).X3
    ∧ CZq (fpVal a Y3c) (addTraceZ (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                        (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).Y3
    ∧ CZq (fpVal a Z3c) (addTraceZ (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                        (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).Z3 := by
  let T := addTraceZ (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
             (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)
  have fZ1Z1 : CZq (fpVal a Z1Z1c) T.Z1Z1 := mulCZq hZ1Z1
  have fZ2Z2 : CZq (fpVal a Z2Z2c) T.Z2Z2 := mulCZq hZ2Z2
  have fU1 : CZq (fpVal a U1c) T.U1 := CZm.trans (mulCZq hU1) (CZm.mul (CZm.refl _) fZ2Z2)
  have fU2 : CZq (fpVal a U2c) T.U2 := CZm.trans (mulCZq hU2) (CZm.mul (CZm.refl _) fZ1Z1)
  have fY1Z2 : CZq (fpVal a Y1Z2c) T.Y1Z2 := mulCZq hY1Z2
  have fS1 : CZq (fpVal a S1c) T.S1 := CZm.trans (mulCZq hS1) (CZm.mul fY1Z2 fZ2Z2)
  have fY2Z1 : CZq (fpVal a Y2Z1c) T.Y2Z1 := mulCZq hY2Z1
  have fS2 : CZq (fpVal a S2c) T.S2 := CZm.trans (mulCZq hS2) (CZm.mul fY2Z1 fZ1Z1)
  have fH : CZq (fpVal a Hc) T.H := CZm.trans (subCZq hH) (CZm.sub fU2 fU1)
  have ftwoH : CZq (fpVal a twoHc) T.twoH := CZm.trans (addCZq htwoH) (CZm.add fH fH)
  have fI : CZq (fpVal a Ic) T.I := CZm.trans (mulCZq hI) (CZm.mul ftwoH ftwoH)
  have fJ : CZq (fpVal a Jc) T.J := CZm.trans (mulCZq hJ) (CZm.mul fH fI)
  have fS2S1 : CZq (fpVal a S2S1c) T.S2S1 := CZm.trans (subCZq hS2S1) (CZm.sub fS2 fS1)
  have fr : CZq (fpVal a rc) T.r := CZm.trans (addCZq hr) (CZm.add fS2S1 fS2S1)
  have fV : CZq (fpVal a Vc) T.V := CZm.trans (mulCZq hV) (CZm.mul fU1 fI)
  have frr : CZq (fpVal a rrc) T.rr := CZm.trans (mulCZq hrr) (CZm.mul fr fr)
  have frrJ : CZq (fpVal a rrJc) T.rrJ := CZm.trans (subCZq hrrJ) (CZm.sub frr fJ)
  have ftwoV : CZq (fpVal a twoVc) T.twoV := CZm.trans (addCZq htwoV) (CZm.add fV fV)
  have fX3 : CZq (fpVal a X3c) T.X3 := CZm.trans (subCZq hX3) (CZm.sub frrJ ftwoV)
  have fVX3 : CZq (fpVal a VX3c) T.VX3 := CZm.trans (subCZq hVX3) (CZm.sub fV fX3)
  have frVX3 : CZq (fpVal a rVX3c) T.rVX3 := CZm.trans (mulCZq hrVX3) (CZm.mul fr fVX3)
  have fS1J : CZq (fpVal a S1Jc) T.S1J := CZm.trans (mulCZq hS1J) (CZm.mul fS1 fJ)
  have ftwoS1J : CZq (fpVal a twoS1Jc) T.twoS1J :=
    CZm.trans (addCZq htwoS1J) (CZm.add fS1J fS1J)
  have fY3 : CZq (fpVal a Y3c) T.Y3 := CZm.trans (subCZq hY3) (CZm.sub frVX3 ftwoS1J)
  have fZ1Z2 : CZq (fpVal a Z1Z2c) T.Z1Z2 := addCZq hZ1Z2
  have fZ1Z2s : CZq (fpVal a Z1Z2sc) T.Z1Z2s :=
    CZm.trans (mulCZq hZ1Z2s) (CZm.mul fZ1Z2 fZ1Z2)
  have ft1 : CZq (fpVal a t1c) T.t1 := CZm.trans (subCZq ht1) (CZm.sub fZ1Z2s fZ1Z1)
  have ft2 : CZq (fpVal a t2c) T.t2 := CZm.trans (subCZq ht2) (CZm.sub ft1 fZ2Z2)
  have fZ3 : CZq (fpVal a Z3c) T.Z3 := CZm.trans (mulCZq hZ3) (CZm.mul ft2 fH)
  exact ⟨fX3, fY3, fZ3⟩

/-- **`pallasEndo_forces`** — the endo gadget forces `X3 ≡ ζ_p·X (mod p)`: the pin forces the ζ
columns to BE `ζ_p` (`zetaPinP_forces`), the mul core forces the product. -/
theorem pallasEndo_forces (a : Assignment) (xB zetaB x3B qB : Nat)
    (hpin : evalH (zetaPinHeadP zetaB) a = 0)
    (hmul : evalH (fpMulHead xB zetaB x3B qB) a = 0) :
    CZp (fpVal a x3B) ((zetaP : ℤ) * fpVal a xB) := by
  have hz := zetaPinP_forces a zetaB hpin
  have hm : CZp (fpVal a x3B) (fpVal a xB * fpVal a zetaB) :=
    CZm.symm (fpMulCore_forces a xB zetaB x3B qB hmul)
  rw [hz, Int.mul_comm] at hm
  exact hm

/-- **`vestaEndo_forces`** — the Vesta endo forces `X3 ≡ ζ_q·X (mod q)`. -/
theorem vestaEndo_forces (a : Assignment) (xB zetaB x3B qB : Nat)
    (hpin : evalH (zetaPinHeadQ zetaB) a = 0)
    (hmul : evalH (fqMulHead xB zetaB x3B qB) a = 0) :
    CZq (fpVal a x3B) ((zetaQ : ℤ) * fpVal a xB) := by
  have hz := zetaPinQ_forces a zetaB hpin
  have hm : CZq (fpVal a x3B) (fpVal a xB * fpVal a zetaB) :=
    CZm.symm (fqMulCore_forces a xB zetaB x3B qB hmul)
  rw [hz, Int.mul_comm] at hm
  exact hm

#assert_axioms zetaP_cube
#assert_axioms lambdaPallas_cube
#assert_axioms lambdaVesta_cube
#assert_axioms zetaPinP_forces
#assert_axioms zetaPinQ_forces
#assert_axioms pallasDouble_forces
#assert_axioms vestaDouble_forces
#assert_axioms pallasAdd_forces
#assert_axioms vestaAdd_forces
#assert_axioms pallasEndo_forces
#assert_axioms vestaEndo_forces

/-! ## §4 — KAT: the GENERATED gates ACCEPT the reference's honest witness and REJECT a bump.

Reuses `PastaField.acceptB`/`bumpAt` (the ℤ reading of the emitted gate bodies). Witnesses are
reference-derived (§1 traces; quotient/carry/borrow values from the same per-op-reduced values). -/

/-- The doubling witness (generic in the modulus). Layout: inputs X=0,Y=9,Z=18; intermediates
27..215; quotients 216..278; carry/borrow bits 279..292 (matches `swDoubleGadget 0 9 18 27`). -/
def dblAsg (m : Nat) (Xv Yv Zv : Nat) : Assignment := fun col =>
  let t := dblTraceM m Xv Yv Zv
  let vals : List Nat :=
    [t.A, t.B, t.C, t.XB, t.XB2, t.T1, t.T2, t.D, t.A2, t.E, t.F, t.D2, t.X3, t.DX3, t.EE,
     t.C2, t.C4, t.C8, t.Y3, t.YZ, t.Z3]
  let qs : List Nat :=
    [ (Xv * Xv - t.A) / m, (Yv * Yv - t.B) / m, (t.B * t.B - t.C) / m,
      (t.XB * t.XB - t.XB2) / m, (t.E * t.E - t.F) / m, (t.E * t.DX3 - t.EE) / m,
      (Yv * Zv - t.YZ) / m ]
  let bs : List Nat :=
    [ (Xv + t.B - t.XB) / m, (t.T1 + t.A - t.XB2) / m, (t.T2 + t.C - t.T1) / m,
      (t.T2 + t.T2 - t.D) / m, (t.A + t.A - t.A2) / m, (t.A2 + t.A - t.E) / m,
      (t.D + t.D - t.D2) / m, (t.X3 + t.D2 - t.F) / m, (t.DX3 + t.X3 - t.D) / m,
      (t.C + t.C - t.C2) / m, (t.C2 + t.C2 - t.C4) / m, (t.C4 + t.C4 - t.C8) / m,
      (t.Y3 + t.C8 - t.EE) / m, (t.YZ + t.YZ - t.Z3) / m ]
  if col < 9 then limbOf Xv col
  else if col < 18 then limbOf Yv (col - 9)
  else if col < 27 then limbOf Zv (col - 18)
  else if col < 216 then limbOf (vals.getD ((col - 27) / 9) 0) ((col - 27) % 9)
  else if col < 279 then limbOf (qs.getD ((col - 216) / 9) 0) ((col - 216) % 9)
  else if col < 293 then ((bs.getD (col - 279) 0 : Nat) : ℤ)
  else 0

/-- The addition witness (generic in the modulus). Layout: inputs 0..53; intermediates 54..314;
quotients 315..458; bits 459..471 (matches `swAddGadget 0 9 18 27 36 45 54`). -/
def addAsg (m : Nat) (X1v Y1v Z1v X2v Y2v Z2v : Nat) : Assignment := fun col =>
  let t := addTraceM m X1v Y1v Z1v X2v Y2v Z2v
  let vals : List Nat :=
    [t.Z1Z1, t.Z2Z2, t.U1, t.U2, t.Y1Z2, t.S1, t.Y2Z1, t.S2, t.H, t.twoH, t.I, t.J, t.S2S1,
     t.r, t.V, t.rr, t.rrJ, t.twoV, t.X3, t.VX3, t.rVX3, t.S1J, t.twoS1J, t.Y3, t.Z1Z2,
     t.Z1Z2s, t.t1, t.t2, t.Z3]
  let qs : List Nat :=
    [ (Z1v * Z1v - t.Z1Z1) / m, (Z2v * Z2v - t.Z2Z2) / m, (X1v * t.Z2Z2 - t.U1) / m,
      (X2v * t.Z1Z1 - t.U2) / m, (Y1v * Z2v - t.Y1Z2) / m, (t.Y1Z2 * t.Z2Z2 - t.S1) / m,
      (Y2v * Z1v - t.Y2Z1) / m, (t.Y2Z1 * t.Z1Z1 - t.S2) / m, (t.twoH * t.twoH - t.I) / m,
      (t.H * t.I - t.J) / m, (t.U1 * t.I - t.V) / m, (t.r * t.r - t.rr) / m,
      (t.r * t.VX3 - t.rVX3) / m, (t.S1 * t.J - t.S1J) / m,
      (t.Z1Z2 * t.Z1Z2 - t.Z1Z2s) / m, (t.t2 * t.H - t.Z3) / m ]
  let bs : List Nat :=
    [ (t.H + t.U1 - t.U2) / m, (t.H + t.H - t.twoH) / m, (t.S2S1 + t.S1 - t.S2) / m,
      (t.S2S1 + t.S2S1 - t.r) / m, (t.rrJ + t.J - t.rr) / m, (t.V + t.V - t.twoV) / m,
      (t.X3 + t.twoV - t.rrJ) / m, (t.VX3 + t.X3 - t.V) / m,
      (t.S1J + t.S1J - t.twoS1J) / m, (t.Y3 + t.twoS1J - t.rVX3) / m,
      (Z1v + Z2v - t.Z1Z2) / m, (t.t1 + t.Z1Z1 - t.Z1Z2s) / m, (t.t2 + t.Z2Z2 - t.t1) / m ]
  if col < 9 then limbOf X1v col
  else if col < 18 then limbOf Y1v (col - 9)
  else if col < 27 then limbOf Z1v (col - 18)
  else if col < 36 then limbOf X2v (col - 27)
  else if col < 45 then limbOf Y2v (col - 36)
  else if col < 54 then limbOf Z2v (col - 45)
  else if col < 315 then limbOf (vals.getD ((col - 54) / 9) 0) ((col - 54) % 9)
  else if col < 459 then limbOf (qs.getD ((col - 315) / 9) 0) ((col - 315) % 9)
  else if col < 472 then ((bs.getD (col - 459) 0 : Nat) : ℤ)
  else 0

/-- The endo witness (generic in the modulus). Layout: x=0, ζ=9, x3=18, q=27. -/
def endoAsg (m xv zetav : Nat) : Assignment := fun col =>
  let rv := (xv * zetav) % m
  let qq := (xv * zetav - rv) / m
  if col < 9 then limbOf xv col
  else if col < 18 then limbOf zetav (col - 9)
  else if col < 27 then limbOf rv (col - 18)
  else if col < 36 then limbOf qq (col - 27)
  else 0

/-! ### Pallas doubling — honest generator-doubling trace ACCEPTED; bumped output limbs REJECTED. -/

/-- The doubling gadget at the KAT layout. -/
def pallasDoubleGad : List VmConstraint2 := (pallasDoubleGadget 0 9 18 27).1

#guard acceptB pallasDoubleGad (dblAsg pN Gp.1 Gp.2 1) == true
#guard acceptB pallasDoubleGad (bumpAt (dblAsg pN Gp.1 Gp.2 1) 135) == false  -- bump X3 limb 0
#guard acceptB pallasDoubleGad (bumpAt (dblAsg pN Gp.1 Gp.2 1) 189) == false  -- bump Y3 limb 0
#guard acceptB pallasDoubleGad (bumpAt (dblAsg pN Gp.1 Gp.2 1) 207) == false  -- bump Z3 limb 0
-- A second, generic point (still a valid trace of the arithmetic).
#guard acceptB pallasDoubleGad (dblAsg pN 123456789 987654321 555) == true
#guard acceptB pallasDoubleGad (bumpAt (dblAsg pN 123456789 987654321 555) 135) == false

/-! ### Pallas addition — honest `2G + G` trace ACCEPTED; bumped output limbs REJECTED. -/

/-- The addition gadget at the KAT layout. -/
def pallasAddGad : List VmConstraint2 := (pallasAddGadget 0 9 18 27 36 45 54).1

#guard acceptB pallasAddGad (addAsg pN Gp2.1 Gp2.2.1 Gp2.2.2 Gp.1 Gp.2 1) == true
#guard acceptB pallasAddGad (bumpAt (addAsg pN Gp2.1 Gp2.2.1 Gp2.2.2 Gp.1 Gp.2 1) 216) == false
#guard acceptB pallasAddGad (bumpAt (addAsg pN Gp2.1 Gp2.2.1 Gp2.2.2 Gp.1 Gp.2 1) 261) == false
#guard acceptB pallasAddGad (bumpAt (addAsg pN Gp2.1 Gp2.2.1 Gp2.2.2 Gp.1 Gp.2 1) 306) == false

/-! ### Vesta doubling + addition — same shapes, modulus `q`, the Vesta generator. -/

/-- The Vesta doubling gadget at the KAT layout. -/
def vestaDoubleGad : List VmConstraint2 := (vestaDoubleGadget 0 9 18 27).1

#guard acceptB vestaDoubleGad (dblAsg qN Gv.1 Gv.2 1) == true
#guard acceptB vestaDoubleGad (bumpAt (dblAsg qN Gv.1 Gv.2 1) 135) == false
#guard acceptB vestaDoubleGad (bumpAt (dblAsg qN Gv.1 Gv.2 1) 189) == false
#guard acceptB vestaDoubleGad (bumpAt (dblAsg qN Gv.1 Gv.2 1) 207) == false

/-- The Vesta addition gadget at the KAT layout. -/
def vestaAddGad : List VmConstraint2 := (vestaAddGadget 0 9 18 27 36 45 54).1

#guard acceptB vestaAddGad (addAsg qN Gv2.1 Gv2.2.1 Gv2.2.2 Gv.1 Gv.2 1) == true
#guard acceptB vestaAddGad (bumpAt (addAsg qN Gv2.1 Gv2.2.1 Gv2.2.2 Gv.1 Gv.2 1) 216) == false
#guard acceptB vestaAddGad (bumpAt (addAsg qN Gv2.1 Gv2.2.1 Gv2.2.2 Gv.1 Gv.2 1) 306) == false

/-! ### The endo gadgets — honest `φ` witness ACCEPTED (both gates exercised); bumped output limb
AND bumped ζ limb both REJECTED (the pin and the mul each bite). -/

#guard acceptB (pallasEndoGadget 0 9 18 27) (endoAsg pN Gp.1 zetaP) == true
#guard acceptB (pallasEndoGadget 0 9 18 27) (bumpAt (endoAsg pN Gp.1 zetaP) 18) == false
#guard acceptB (pallasEndoGadget 0 9 18 27) (bumpAt (endoAsg pN Gp.1 zetaP) 9) == false
#guard acceptB (pallasEndoGadget 0 9 18 27) (endoAsg pN 12345 zetaP) == true
#guard acceptB (pallasEndoGadget 0 9 18 27) (bumpAt (endoAsg pN 12345 zetaP) 18) == false

#guard acceptB (vestaEndoGadget 0 9 18 27) (endoAsg qN Gv.1 zetaQ) == true
#guard acceptB (vestaEndoGadget 0 9 18 27) (bumpAt (endoAsg qN Gv.1 zetaQ) 18) == false
#guard acceptB (vestaEndoGadget 0 9 18 27) (bumpAt (endoAsg qN Gv.1 zetaQ) 9) == false

/-! ## §5 — Structural `#guard`s (the budgeted shapes) + AIR packaging. -/

#guard (pallasDoubleGadget 0 9 18 27).1.length == 21
#guard (pallasDoubleGadget 0 9 18 27).2.2 == 293
#guard (pallasAddGadget 0 9 18 27 36 45 54).1.length == 29
#guard (pallasAddGadget 0 9 18 27 36 45 54).2.2 == 472
#guard (vestaDoubleGadget 0 9 18 27).1.length == 21
#guard (vestaAddGadget 0 9 18 27 36 45 54).1.length == 29
#guard (pallasEndoGadget 0 9 18 27).length == 2
#guard (vestaEndoGadget 0 9 18 27).length == 2

/-- A Pallas doubling packaged as an `EffectVmDescriptor2` (drops into the deployed vocabulary). -/
def pallasDoubleDesc : EffectVmDescriptor2 :=
  { name        := "dregg-pasta-pallas-double::demo"
  , traceWidth  := 293
  , piCount     := 0
  , tables      := []
  , constraints := (pallasDoubleGadget 0 9 18 27).1
  , hashSites   := []
  , ranges      := [] }

#guard pallasDoubleDesc.constraints.length == 21
#guard pallasDoubleDesc.traceWidth == 293

/-! ## §6 — GLV: how the endo cuts the scalar-mul cost, and the PRECISE named residuals.

### The GLV story (stated, not built — the scalar mul is K4)

Because `φ(P) = [λ]·P` with `λ` a cube root of unity in the scalar field (kernel-verified above
for both curves), a 255-bit scalar `k` decomposes as `k ≡ k1 + k2·λ (mod r)` with
`|k1|, |k2| ≈ √r ≈ 2^127.5` — two ~128-bit halves (the lattice exists and is tiny; finding the
half-scalars is PROVER-side preprocessing, no gates). Then

  `[k]·P = [k1]·P + [k2]·(λ·P) = [k1]·P + [k2]·φ(P)`

and `φ(P)` costs ONE field mul (`pallasEndoGadget` = 2 core gates; with K1's full generators,
`1 pin + 1 fpMul = 1 + 559 = 560` gates). A joint (Shamir) double-and-add over the two half-scalars
then runs **128 doublings + ~96 joint additions** instead of the naive **255 doublings + ~128
additions**. With the §2 gadgets at K1's full-generator gate counts (double = `7·559 + 14·281 =
7847`; add = `16·559 + 13·281 = 12597`):

  * naive 255-bit scalar mul:  `255·7847 + 128·12597 ≈ 3.61M` gates;
  * GLV + Shamir:              `128·7847 +  96·12597 + 560 ≈ 2.21M` gates,

≈ **1.6× fewer gates and HALF the serial doubling depth** — and in the IPA setting (K4) the two
half-scalar MSMs also parallelize. This is exactly how Kimchi uses it: the pinned
`poseidon/src/sponge.rs` constructs scalar challenges "from exactly 128 bits (2 limbs)" and
`poly-commitment/src/ipa.rs` drives the MSM with the `(endo_q, endo_r)` pair derived by the
recipe §0 reproduces. The endomorphism is why "as fast as possible" Pasta verification is an
MSM/endo game, and it is now a forced, KAT'd, 2-gate gadget.

### RESIDUALS (named; nothing laundered)

  1. **The `z < p` / `z < q` canonical compare is NOT generated** (inherited from K1, same shape
     as `Bls12381TowerExt`): the gadgets compose the CORE gates; per-output limb ranges
     (`pastaLimbRange`) and the final compare are the named reduction residual. The gates force
     the CONGRUENCE (proved), not the canonical representative.
  2. **The `ℤ ↔ p_felt` field-width gap** (inherited from K1): gates are read over ℤ (the
     schoolbook cross-sums overflow BabyBear); native-field soundness is the shared residual.
  3. **add-2007-bl is not a complete formula.** The addition gadget forces the formula as
     generated, which is correct for `P ≠ ±Q` with neither point at infinity (the KATs exercise
     generic points: `2G + G`). Exceptional-case handling (identity, `P = ±Q`) in a scalar-mul
     ladder is K4's job; the doubling gadget has no exceptional cases for `Y ≠ 0`.
  4. **The GLV decomposition is stated, not built.** What landed is the endo-apply gadget + its
     forcing + the `φ(G) = λ·G` correspondence KAT. The lattice split, the Shamir ladder, and the
     IPA MSM are K4. No scalar-mul gadget, no IPA, no Poseidon, no verifier is claimed here.
  5. **Primality of the moduli is inherited** from `mina-curves` (as K1 named); the curve order /
     group-structure facts (cofactor 1, `r = the other prime`) are likewise inherited from the
     pinned crate, used only in the Python/KAT cross-checks.

CONTINUATION: K3 (Poseidon-over-Pasta sponge) and K4 (GLV scalar mul + IPA MSM) compose these
forced pieces; the affine finalization needs ONE witnessed `fpInv` (`x·x⁻¹ ≡ 1`, K1 §6's shape).
-/

end Dregg2.Circuit.Emit.PastaCurve
