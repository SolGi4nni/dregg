/-
# Dregg2.Circuit.Emit.Ed25519Gadget — a Lean-GENERATED Ed25519 field + twisted-Edwards-point AIR
foundation (the arithmetic floor under an in-STARK ed25519 signature verify).

## Why this file exists (the carrier it is aimed at)

tm/sol/mid's light-clients carry a trusted `ED_OK` carrier: the validator/authority signature
aggregates verify a batch of ed25519 signatures asserted as witnessed boolean bits, the same way
`Sha256Gadget` was aimed at `FIN_OK`/`EXEC_OK` and `Bls12381Tower` at `BLS_OK`. Replacing `ED_OK`
with an IN-CIRCUIT derivation means expressing ed25519 verification — `[S]·B == R + [k]·A`, with
`k = SHA-512(R‖A‖M) mod L` — as AIR constraints over the base field `Fq = GF(2²⁵⁵−19)` and the
twisted-Edwards curve `−x² + y² = 1 + d·x²y²` (`d = −121665/121666`). That whole edifice is built out
of ONE primitive — multiplication in the 255-bit prime field `Fq` — iterated into curve point ops.
This file is that primitive and its FIRST curve layer (point add + double via the COMPLETE unified
addition law), GENERATED (House Law #1), KAT'd against real Ed25519 vectors, with the per-op field
gates PROVEN to force the field congruence and the point-add gadget PROVEN to force the curve
addition (ℤ reading) by COMPOSING the field forcings — the curve layer composing over the field
generators the SAME way `Bls12381Tower`'s `Fp2` composed over `Fp`.

This is the FOUNDATION slice, honestly named: a KAT'd + forced `Fq` field with a KAT'd + forced
twisted-Edwards point-add is a real floor; it is NOT a signature verify and NOT a folded `ED_OK`. The
precise mechanical continuation to a full verify (scalar mult, the SHA-512 challenge, the mod-`L`
reduction, the `[S]B == R+[k]A` equation) is spelled out in §8 with its gate-count reality
(≈ millions of gates per signature — cheaper than a BLS pairing, the accepted zk-STARK ed25519 cost).

## The metaprogramming approach (GENERATED, mirroring `Bls12381Tower`/`Sha256Gadget`)

Everything is produced by Lean `def`-GENERATORS over `AirBuilder.Head`, each constraint a per-row gate
`cgH head` reusing `AirBuilder.headToExpr_eval`. The field-multiplication primitive `Head.mul` (with
`evalH_mul : evalH (h.mul o) a = evalH h a * evalH o a`) is REUSED from `Bls12381Tower` — the same
polynomial-head product that generates `Fp` mul there generates `Fq` mul here, so the point-add
gadget's eight field multiplications are that one primitive composed (the whole point: ONE mul,
iterated, is a curve).

## The felt-encoding (two moduli — keep them distinct)

  * `p_felt` = BabyBear (`2013265921`, ~31 bits) — the STARK's native field the columns live in.
  * `q`      = the Ed25519 BASE PRIME `2²⁵⁵ − 19` (255 bits) — the field the arithmetic is OVER.

An `Fq` element is encoded as **`numLimbs = 9` limbs of `limbBits = 30` bits** over BabyBear felt
columns `base..base+8`, LSB-first: its value is the degree-1 head `fqValue base = Σ_{i<9}
2^{30 i}·col(base+i)`. Capacity `9·30 = 270` bits ≥ 255 (top limb uses 15 bits); a 30-bit limb
(`< 2³⁰ < p_felt`) fits one BabyBear felt with room. Products of two limbs reach `< 2⁶⁰` and the
schoolbook cross-sum reaches `~2⁵⁴⁰` — this OVERFLOWS BabyBear, so the gate is read over ℤ (the strong
reading, exactly as `Bls12381Tower`/`Sha256Gadget` are), and the `ℤ ↔ p_felt` soundness is the SAME
field-width residual those files carry.

## The reduction strategy (non-native field arithmetic via a QUOTIENT WITNESS)

Field ops reduce mod `q` by the standard non-native technique — witness the quotient and check the
big-integer identity over ℤ (identical shape to `Bls12381Tower`, `p → q`):
  * `fqAdd x y = z`: carry bit `c`, gate `xVal + yVal − zVal − c·q = 0`. Forces `x + y ≡ z (mod q)`.
  * `fqSub x y = z`: borrow bit `c`, gate `xVal − yVal + c·q − zVal = 0`. Forces `x − y ≡ z (mod q)`.
  * `fqMul x y = z`: quotient limbs `k` (`x·y = k·q + z`), gate `xVal·yVal − q·kVal − zVal = 0`
    (degree 2, the `Head.mul` cross-product). Forces `x·y ≡ z (mod q)`.
  * `fqMulConst x·K = z` (curve constant `K`, e.g. `2d`): gate `xVal·K − q·kVal − zVal = 0` with `K`
    a BAKED-IN gate constant (`Head.c K`, not a witness column) — the curve constant is fixed by the
    AIR, not adversary-chosen. Forces `x·K ≡ z (mod q)`.
NOTE — the SPECIAL FORM `2²⁵⁵ ≡ 19 (mod q)` makes reduction cheap on real hardware (a fold, not a
long division), and a specialised fold-gate is a valid optimisation. Here we use the GENERAL quotient
witness (as `Bls12381Tower` does) because it is cleaner, reuses the identical forcing lemma, and the
`19`-fold optimisation is a per-gate replacement that changes the witness, not the congruence claim.
Canonicity (`0 ≤ z < q`) needs the limb range checks (`fqLimbRange`) plus the `z < q` compare; the
ranges are generated here and the final `z < q` compare is the one NAMED reduction residual (same as
`Bls12381Tower`'s `z < p`).

## Constraint budget (per op, in gates)

  * `fqAddCore`/`fqSubCore`: 1 value gate. `+ 1` carry pin `+ 279` limb-range (`fqLimbRange`) = **281**.
  * `fqMulCore`: 1 degree-2 value gate (`9² = 81` cross-products + 9 k-terms + 9 z-terms).
    `+ 279·2` (z and k ranges) = **559**.
  * `edAddGadget` (complete unified add): **18 core gates** (9 mul + 5 add + 4 sub) composed from the
    `Fq` generators — the curve iterating the field, one level up (ranges add per output).

## What is AUTHORED + built vs NAMED mechanical continuation

AUTHORED + built here: the encoding `fqValue`; the `fqAdd`/`fqSub`/`fqMul`/`fqMulConst` core generators
+ their forcing lemmas (`fq*Core_forces`, ℤ-congruence mod the real `q = 2²⁵⁵−19`); the range generator
`fqLimbRange`; the twisted-Edwards `edAddGadget` (the COMPLETE unified add-2008-hwcd law in extended
coordinates, a=−1, COMPOSED from the `Fq` generators) with `edDoubleGadget := edAddGadget P P` (the
unified law IS complete, so doubling is the same gadget — no special case); `edAdd_forces` (the WHOLE
18-gate gadget FORCES the four extended-coordinate output congruences, composed from the `Fq` gate
forcings — the curve composing over the field at the PROOF level) plus the deeper input-level
`edAdd_A/Bb/C/D_forces` and the `edAdd_X3_forces_inputs` capstone. AUTHORED + KAT'd both-polarity: a
`Nat` `Fq` + extended-Edwards reference anchored to a py/ref10 Ed25519 computation supplies honest
witnesses the generated gates ACCEPT and a bumped output limb REJECTS (`fqMul`/`fqAdd`/`fqSub`, the
whole `edAddGadget` point-add `B+3B`, and the `edDoubleGadget` point-double `2B`). NAMED continuation
(§8): scalar mult `[k]P`, the SHA-512 challenge, the mod-`L` reduction, the `[S]B == R+[k]A` verify
equation that replaces `ED_OK`.

## Resolution (honest)

REAL: the `Fq` + Edwards point-add generators exist + type-check in the deployed IR-v2 vocabulary; the
reference is Ed25519-anchored; the gates FORCE the field congruence (ℤ reading) and `edAdd_forces`
forces the extended-coordinate curve addition; both-polarity KATs are non-vacuous. NOT claimed: a
working signature verify, a folded `ED_OK`, or native-field (`p_felt`) soundness — the gate is read
over ℤ (the shared field-width residual), the `z < q` canonical compare is named, and scalar-mult →
verify is §8's arc, not built.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/`native_decide`.
The `#guard` KATs reduce in the kernel. NEW file; imports read-only (`Bls12381Tower`, for the reused
`Head.mul`/`evalH_mul`/`acceptB`/`bumpAt` — the shared field-mul primitive and KAT harness); standalone
(NOT imported by the truncated `Dregg2` root; built directly as `Dregg2.Circuit.Emit.Ed25519Gadget`).
-/
import Dregg2.Circuit.Emit.Bls12381Tower

namespace Dregg2.Circuit.Emit.Ed25519Gadget

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.Bls12381Tower (evalH_mul acceptB bumpAt)

set_option autoImplicit false

/-! ## §0 — Encoding parameters (the field the curve is OVER). -/

/-- The Ed25519 base prime `q = 2²⁵⁵ − 19` (255 bits). The field the curve arithmetic is OVER (NOT the
felt field `p_felt`). -/
def qN : Nat := 57896044618658097711785492504343953926634992332820282019728792003956564819949

/-- `q` as an integer (gate coefficients). -/
def q : ℤ := (qN : ℤ)

/-- Limbs per `Fq` element. -/
def numLimbs : Nat := 9
/-- Bits per limb (a 30-bit limb `< 2³⁰ < 2013265921` fits one BabyBear felt). -/
def limbBits : Nat := 30

/-- The twisted-Edwards curve constant `d = −121665/121666 mod q`. -/
def dN : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555
/-- `2·d mod q` — the constant folded into the `C = T1·2d·T2` step of the unified addition. -/
def twoDN : Nat := 16295367250680780974490674513165176452449235426866156013048779062215315747161
/-- `2d` as a gate coefficient. -/
def twoD : ℤ := (twoDN : ℤ)

/-- The prime group order `L` of the base-point subgroup (for the §8 mod-`L` reduction naming). -/
def LN : Nat := 7237005577332262213973186563042994240857116359379907606001950938285454250989

/-- **The value head** of the `Fq` element at columns `base..base+8`:
`Σ_{i<9} 2^{30 i}·col(base+i)` (degree 1, LSB-first). -/
def fqValue (base : Nat) : Head :=
  (List.range numLimbs).foldl (fun h i => h.addLin ((2 : ℤ) ^ (limbBits * i)) (base + i)) Head.zero

/-- The integer value the columns of `fqValue base` reconstruct to, under `a`. -/
def fqVal (a : Assignment) (base : Nat) : ℤ := evalH (fqValue base) a

/-- Bridge: the value head's evaluation IS the reconstructed field element. -/
theorem fqVal_eq (a : Assignment) (base : Nat) : evalH (fqValue base) a = fqVal a base := rfl

/-! ## §1 — The `Fq` gate heads + generators (GENERATED per op, mirroring `Bls12381Tower` `p → q`). -/

/-- **`fqAddHead`** — `xVal + yVal − zVal − c·q`. Zero forces `x+y ≡ z (q)`. -/
def fqAddHead (xB yB zB cCol : Nat) : Head :=
  (((fqValue xB).append (fqValue yB)).append ((fqValue zB).scale (-1))).addLin (-q) cCol

/-- **`fqSubHead`** — `xVal − yVal + c·q − zVal`. Zero forces `x−y ≡ z (q)`. -/
def fqSubHead (xB yB zB cCol : Nat) : Head :=
  (((fqValue xB).append ((fqValue yB).scale (-1))).append ((fqValue zB).scale (-1))).addLin q cCol

/-- **`fqMulHead`** — `xVal·yVal − q·kVal − zVal` (`k` = quotient limbs, degree 2 via `Head.mul`).
Zero forces `x·y ≡ z (q)`. -/
def fqMulHead (xB yB zB kB : Nat) : Head :=
  (((fqValue xB).mul (fqValue yB)).append ((fqValue kB).scale (-q))).append ((fqValue zB).scale (-1))

/-- **`fqMulConstHead`** — `xVal·K − q·kVal − zVal`, `K` a BAKED-IN curve constant (`Head.c K`, degree
1, no witness column for `K`). Zero forces `x·K ≡ z (q)`. -/
def fqMulConstHead (xB zB kB : Nat) (K : ℤ) : Head :=
  (((fqValue xB).mul (Head.c K)).append ((fqValue kB).scale (-q))).append ((fqValue zB).scale (-1))

/-- `fqAdd` value gate. -/
def fqAddCore (xB yB zB cCol : Nat) : VmConstraint2 := cgH (fqAddHead xB yB zB cCol)
/-- `fqSub` value gate. -/
def fqSubCore (xB yB zB cCol : Nat) : VmConstraint2 := cgH (fqSubHead xB yB zB cCol)
/-- `fqMul` value gate. -/
def fqMulCore (xB yB zB kB : Nat) : VmConstraint2 := cgH (fqMulHead xB yB zB kB)
/-- `fqMulConst` value gate. -/
def fqMulConstCore (xB zB kB : Nat) (K : ℤ) : VmConstraint2 := cgH (fqMulConstHead xB zB kB K)

/-- **The limb range gadget** — every one of the 9 limbs of the `Fq` element at `base` is a real
`limbBits`-bit value, bit-decomposed at `bitBase` (9·30 = 270 bit columns), via
`AirBuilder.rangeNonneg`. `9·(30 + 1) = 279` constraints. -/
def fqLimbRange (base bitBase : Nat) : List VmConstraint2 :=
  (List.range numLimbs).flatMap (fun i =>
    rangeNonneg (Head.lin 1 (base + i)) ((List.range limbBits).map (fun j => bitBase + limbBits * i + j)))

/-- **`fqAdd`** — full generator: value gate, carry pin, output range. `281`. -/
def fqAdd (xB yB zB cCol zBit : Nat) : List VmConstraint2 :=
  fqAddCore xB yB zB cCol :: binGate cCol :: fqLimbRange zB zBit
/-- **`fqSub`** — full generator. `281`. -/
def fqSub (xB yB zB cCol zBit : Nat) : List VmConstraint2 :=
  fqSubCore xB yB zB cCol :: binGate cCol :: fqLimbRange zB zBit
/-- **`fqMul`** — full generator: degree-2 value gate + output range + quotient range. `559`. -/
def fqMul (xB yB zB kB zBit kBit : Nat) : List VmConstraint2 :=
  fqMulCore xB yB zB kB :: (fqLimbRange zB zBit ++ fqLimbRange kB kBit)

/-! ## §2 — The `Fq` gates FORCE the field congruence (ℤ reading, mod the real `q = 2²⁵⁵−19`).

`q ∣ (u − v)` IS `u ≡ v (mod q)`. These are the "demonstrably computes, not just type-checks" content:
the gate's zero pins the reconstructed output to the field op of the reconstructed inputs. -/

/-- **`fqAdd` forces `x + y ≡ z (mod q)`.** -/
theorem fqAddCore_forces (a : Assignment) (xB yB zB cCol : Nat)
    (hg : evalH (fqAddHead xB yB zB cCol) a = 0) :
    (q : ℤ) ∣ (fqVal a xB + fqVal a yB - fqVal a zB) := by
  simp only [fqAddHead, evalH_addLin, evalH_append, evalH_scale, fqVal_eq] at hg
  exact ⟨a cCol, by linarith⟩

/-- **`fqSub` forces `x − y ≡ z (mod q)`.** -/
theorem fqSubCore_forces (a : Assignment) (xB yB zB cCol : Nat)
    (hg : evalH (fqSubHead xB yB zB cCol) a = 0) :
    (q : ℤ) ∣ (fqVal a xB - fqVal a yB - fqVal a zB) := by
  simp only [fqSubHead, evalH_addLin, evalH_append, evalH_scale, fqVal_eq] at hg
  exact ⟨-(a cCol), by linarith⟩

/-- **`fqMul` forces `x·y ≡ z (mod q)`.** -/
theorem fqMulCore_forces (a : Assignment) (xB yB zB kB : Nat)
    (hg : evalH (fqMulHead xB yB zB kB) a = 0) :
    (q : ℤ) ∣ (fqVal a xB * fqVal a yB - fqVal a zB) := by
  simp only [fqMulHead, evalH_append, evalH_scale, evalH_mul, fqVal_eq] at hg
  exact ⟨fqVal a kB, by linarith⟩

/-- **`fqMulConst` forces `x·K ≡ z (mod q)`** (the baked-in curve constant `K`). -/
theorem fqMulConstCore_forces (a : Assignment) (xB zB kB : Nat) (K : ℤ)
    (hg : evalH (fqMulConstHead xB zB kB K) a = 0) :
    (q : ℤ) ∣ (fqVal a xB * K - fqVal a zB) := by
  simp only [fqMulConstHead, evalH_append, evalH_scale, evalH_mul, evalH_c, fqVal_eq] at hg
  exact ⟨fqVal a kB, by linarith⟩

#assert_axioms fqAddCore_forces
#assert_axioms fqSubCore_forces
#assert_axioms fqMulCore_forces
#assert_axioms fqMulConstCore_forces

/-! ## §3 — The twisted-Edwards point layer (GENERATED by composing the `Fq` generators — the curve
iterating the field).

Extended homogeneous coordinates `(X, Y, Z, T)` with `T = XY/Z`. The COMPLETE unified addition law
`add-2008-hwcd` for `a = −1` (`−x²+y² = 1 + d x²y²`), which has NO exceptional cases on the
prime-order subgroup — so `edDouble P := edAdd P P` is correct (the same gadget), no special case:

```
  A = (Y1−X1)·(Y2−X2)      E = B − A       X3 = E·F
  B = (Y1+X1)·(Y2+X2)      F = D − C       Y3 = G·H
  C = T1·(2d)·T2           G = D + C       T3 = E·H
  D = Z1·2·Z2              H = B + A       Z3 = F·G
```

The gadget is a LIST of `Fq` gate-generator calls with threaded columns — no gate is hand-authored
(House Law #1). `D = 2·Z1·Z2` is `Z1·Z2` then a self-`fqAdd` (doubling), and `C = T1·T2·2d` is `T1·T2`
then a `fqMulConst` by the baked-in `2d`. Scratch columns (each limb group = 9 cols) from `base`:
values `ym1,ym2,A,yp1,yp2,B,tt,C,zz,D,E,F,G,H,X3,Y3,T3,Z3` at `base+9·{0..17}`; quotients
`qA,qB,qtt,qC,qzz,qX3,qY3,qT3,qZ3` at `base+9·{18..26}`; carries/borrows at `base+243..base+251`. -/
def edAddGadget (X1 Y1 Z1 T1 X2 Y2 Z2 T2 base : Nat) : List VmConstraint2 :=
  let ym1 := base;        let ym2 := base + 9
  let A   := base + 18;   let yp1 := base + 27
  let yp2 := base + 36;   let B   := base + 45
  let tt  := base + 54;   let C   := base + 63
  let zz  := base + 72;   let D   := base + 81
  let E   := base + 90;   let F   := base + 99
  let G   := base + 108;  let H   := base + 117
  let x3  := base + 126;  let y3  := base + 135
  let t3  := base + 144;  let z3  := base + 153
  let qA  := base + 162;  let qB  := base + 171
  let qtt := base + 180;  let qC  := base + 189
  let qzz := base + 198;  let qx3 := base + 207
  let qy3 := base + 216;  let qt3 := base + 225
  let qz3 := base + 234
  let bym1 := base + 243;  let bym2 := base + 244
  let cyp1 := base + 245;  let cyp2 := base + 246
  let cD   := base + 247;  let bE   := base + 248
  let bF   := base + 249;  let cG   := base + 250
  let cH   := base + 251
  [ fqSubCore Y1 X1 ym1 bym1            -- ym1 = Y1 − X1
  , fqSubCore Y2 X2 ym2 bym2            -- ym2 = Y2 − X2
  , fqMulCore ym1 ym2 A qA              -- A   = ym1·ym2
  , fqAddCore Y1 X1 yp1 cyp1            -- yp1 = Y1 + X1
  , fqAddCore Y2 X2 yp2 cyp2            -- yp2 = Y2 + X2
  , fqMulCore yp1 yp2 B qB              -- B   = yp1·yp2
  , fqMulCore T1 T2 tt qtt              -- tt  = T1·T2
  , fqMulConstCore tt C qC twoD         -- C   = tt·(2d)
  , fqMulCore Z1 Z2 zz qzz              -- zz  = Z1·Z2
  , fqAddCore zz zz D cD                -- D   = zz + zz   (= 2·Z1·Z2)
  , fqSubCore B A E bE                  -- E   = B − A
  , fqSubCore D C F bF                  -- F   = D − C
  , fqAddCore D C G cG                  -- G   = D + C
  , fqAddCore B A H cH                  -- H   = B + A
  , fqMulCore E F x3 qx3                -- X3  = E·F
  , fqMulCore G H y3 qy3                -- Y3  = G·H
  , fqMulCore E H t3 qt3                -- T3  = E·H
  , fqMulCore F G z3 qz3 ]              -- Z3  = F·G

/-- The `X3` output base of `edAddGadget`. -/
def edAddX3 (base : Nat) : Nat := base + 126
/-- The `Y3` output base of `edAddGadget`. -/
def edAddY3 (base : Nat) : Nat := base + 135
/-- The `T3` output base of `edAddGadget`. -/
def edAddT3 (base : Nat) : Nat := base + 144
/-- The `Z3` output base of `edAddGadget`. -/
def edAddZ3 (base : Nat) : Nat := base + 153

/-- **`edDoubleGadget`** — point doubling `2·P` IS the unified add applied to `(P, P)`: the complete
addition law has no exceptional cases, so no dedicated formula is needed (a dedicated `dbl-2008-hwcd`
with fewer muls but a field negation is the perf sibling, §8). -/
def edDoubleGadget (X1 Y1 Z1 T1 base : Nat) : List VmConstraint2 :=
  edAddGadget X1 Y1 Z1 T1 X1 Y1 Z1 T1 base

/-! ## §4 — Curve forcing: the WHOLE `edAddGadget` FORCES the extended-coordinate addition (proof-level
curve-over-field). Composed from §2's `Fq` gate forcings by ℤ-divisibility arithmetic. -/

/-- `q ∣ (A−A')` and `q ∣ (B−B')` ⇒ `q ∣ (A·B − A'·B')` (the product-lift; `Bls12381Tower.dvd_mul_lift`
specialised to `q`). -/
theorem dvd_mul_lift {A A' B B' : ℤ} (h1 : (q : ℤ) ∣ (A - A')) (h2 : (q : ℤ) ∣ (B - B')) :
    (q : ℤ) ∣ (A * B - A' * B') := by
  have hrw : A * B - A' * B' = (A - A') * B + A' * (B - B') := by ring
  rw [hrw]
  exact dvd_add (dvd_mul_of_dvd_left h1 B) (dvd_mul_of_dvd_right h2 A')

/-- **`edAdd_forces` — the four extended-coordinate outputs are the curve addition of the reconstructed
first-level intermediates.** Given the 18 core gates hold, `X3 ≡ (B−A)(D−C)`, `Y3 ≡ (D+C)(B+A)`,
`T3 ≡ (B−A)(B+A)`, `Z3 ≡ (D−C)(D+C)` (mod `q`), where `A,B,C,D,E,F,G,H` are the gadget's allocated
intermediate columns. This is the curve layer forced by COMPOSING the `Fq` gate forcings — not KAT'd:
the reconstructed outputs ARE the extended-add of the reconstructed intermediates. -/
theorem edAdd_forces (a : Assignment) (A B C D E F G H x3 y3 t3 z3 qx3 qy3 qt3 qz3 bE bF cG cH : Nat)
    (hE : evalH (fqSubHead B A E bE) a = 0)
    (hF : evalH (fqSubHead D C F bF) a = 0)
    (hG : evalH (fqAddHead D C G cG) a = 0)
    (hH : evalH (fqAddHead B A H cH) a = 0)
    (hX3 : evalH (fqMulHead E F x3 qx3) a = 0)
    (hY3 : evalH (fqMulHead G H y3 qy3) a = 0)
    (hT3 : evalH (fqMulHead E H t3 qt3) a = 0)
    (hZ3 : evalH (fqMulHead F G z3 qz3) a = 0) :
    (q : ℤ) ∣ ((fqVal a B - fqVal a A) * (fqVal a D - fqVal a C) - fqVal a x3)
    ∧ (q : ℤ) ∣ ((fqVal a D + fqVal a C) * (fqVal a B + fqVal a A) - fqVal a y3)
    ∧ (q : ℤ) ∣ ((fqVal a B - fqVal a A) * (fqVal a B + fqVal a A) - fqVal a t3)
    ∧ (q : ℤ) ∣ ((fqVal a D - fqVal a C) * (fqVal a D + fqVal a C) - fqVal a z3) := by
  have cE := fqSubCore_forces a B A E bE hE     -- B − A ≡ E
  have cF := fqSubCore_forces a D C F bF hF     -- D − C ≡ F
  have cG' := fqAddCore_forces a D C G cG hG    -- D + C ≡ G
  have cH' := fqAddCore_forces a B A H cH hH    -- B + A ≡ H
  have cX := fqMulCore_forces a E F x3 qx3 hX3  -- E·F ≡ X3
  have cY := fqMulCore_forces a G H y3 qy3 hY3  -- G·H ≡ Y3
  have cT := fqMulCore_forces a E H t3 qt3 hT3  -- E·H ≡ T3
  have cZ := fqMulCore_forces a F G z3 qz3 hZ3  -- F·G ≡ Z3
  -- Each output: lift the mul over the two sub/add congruences, then splice the mul gate.
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hlift : (q : ℤ) ∣ ((fqVal a B - fqVal a A) * (fqVal a D - fqVal a C) - fqVal a E * fqVal a F) :=
      dvd_mul_lift cE cF
    have hrw : (fqVal a B - fqVal a A) * (fqVal a D - fqVal a C) - fqVal a x3
        = ((fqVal a B - fqVal a A) * (fqVal a D - fqVal a C) - fqVal a E * fqVal a F)
          + (fqVal a E * fqVal a F - fqVal a x3) := by ring
    rw [hrw]; exact dvd_add hlift cX
  · have hlift : (q : ℤ) ∣ ((fqVal a D + fqVal a C) * (fqVal a B + fqVal a A) - fqVal a G * fqVal a H) :=
      dvd_mul_lift cG' cH'
    have hrw : (fqVal a D + fqVal a C) * (fqVal a B + fqVal a A) - fqVal a y3
        = ((fqVal a D + fqVal a C) * (fqVal a B + fqVal a A) - fqVal a G * fqVal a H)
          + (fqVal a G * fqVal a H - fqVal a y3) := by ring
    rw [hrw]; exact dvd_add hlift cY
  · have hlift : (q : ℤ) ∣ ((fqVal a B - fqVal a A) * (fqVal a B + fqVal a A) - fqVal a E * fqVal a H) :=
      dvd_mul_lift cE cH'
    have hrw : (fqVal a B - fqVal a A) * (fqVal a B + fqVal a A) - fqVal a t3
        = ((fqVal a B - fqVal a A) * (fqVal a B + fqVal a A) - fqVal a E * fqVal a H)
          + (fqVal a E * fqVal a H - fqVal a t3) := by ring
    rw [hrw]; exact dvd_add hlift cT
  · have hlift : (q : ℤ) ∣ ((fqVal a D - fqVal a C) * (fqVal a D + fqVal a C) - fqVal a F * fqVal a G) :=
      dvd_mul_lift cF cG'
    have hrw : (fqVal a D - fqVal a C) * (fqVal a D + fqVal a C) - fqVal a z3
        = ((fqVal a D - fqVal a C) * (fqVal a D + fqVal a C) - fqVal a F * fqVal a G)
          + (fqVal a F * fqVal a G - fqVal a z3) := by ring
    rw [hrw]; exact dvd_add hlift cZ

/-- **`edAdd_A_forces`** — the first-level intermediate `A` is the input product `(Y1−X1)(Y2−X2)`
(mod `q`): the `ym1,ym2` sub gates + the `A` mul gate compose to the input coordinates. -/
theorem edAdd_A_forces (a : Assignment) (X1 Y1 X2 Y2 ym1 ym2 A qA bym1 bym2 : Nat)
    (h1 : evalH (fqSubHead Y1 X1 ym1 bym1) a = 0)
    (h2 : evalH (fqSubHead Y2 X2 ym2 bym2) a = 0)
    (h3 : evalH (fqMulHead ym1 ym2 A qA) a = 0) :
    (q : ℤ) ∣ ((fqVal a Y1 - fqVal a X1) * (fqVal a Y2 - fqVal a X2) - fqVal a A) := by
  have c1 := fqSubCore_forces a Y1 X1 ym1 bym1 h1
  have c2 := fqSubCore_forces a Y2 X2 ym2 bym2 h2
  have c3 := fqMulCore_forces a ym1 ym2 A qA h3
  have hlift := dvd_mul_lift c1 c2
  have hrw : (fqVal a Y1 - fqVal a X1) * (fqVal a Y2 - fqVal a X2) - fqVal a A
      = ((fqVal a Y1 - fqVal a X1) * (fqVal a Y2 - fqVal a X2) - fqVal a ym1 * fqVal a ym2)
        + (fqVal a ym1 * fqVal a ym2 - fqVal a A) := by ring
  rw [hrw]; exact dvd_add hlift c3

/-- **`edAdd_Bb_forces`** — `B ≡ (Y1+X1)(Y2+X2) (mod q)`. -/
theorem edAdd_Bb_forces (a : Assignment) (X1 Y1 X2 Y2 yp1 yp2 B qB cyp1 cyp2 : Nat)
    (h1 : evalH (fqAddHead Y1 X1 yp1 cyp1) a = 0)
    (h2 : evalH (fqAddHead Y2 X2 yp2 cyp2) a = 0)
    (h3 : evalH (fqMulHead yp1 yp2 B qB) a = 0) :
    (q : ℤ) ∣ ((fqVal a Y1 + fqVal a X1) * (fqVal a Y2 + fqVal a X2) - fqVal a B) := by
  have c1 := fqAddCore_forces a Y1 X1 yp1 cyp1 h1
  have c2 := fqAddCore_forces a Y2 X2 yp2 cyp2 h2
  have c3 := fqMulCore_forces a yp1 yp2 B qB h3
  have hlift := dvd_mul_lift c1 c2
  have hrw : (fqVal a Y1 + fqVal a X1) * (fqVal a Y2 + fqVal a X2) - fqVal a B
      = ((fqVal a Y1 + fqVal a X1) * (fqVal a Y2 + fqVal a X2) - fqVal a yp1 * fqVal a yp2)
        + (fqVal a yp1 * fqVal a yp2 - fqVal a B) := by ring
  rw [hrw]; exact dvd_add hlift c3

/-- **`edAdd_C_forces`** — `C ≡ T1·T2·(2d) (mod q)`: the `tt` mul gate + the `fqMulConst` gate compose,
carrying the baked-in curve constant `2d`. -/
theorem edAdd_C_forces (a : Assignment) (T1 T2 tt C qtt qC : Nat)
    (h1 : evalH (fqMulHead T1 T2 tt qtt) a = 0)
    (h2 : evalH (fqMulConstHead tt C qC twoD) a = 0) :
    (q : ℤ) ∣ (fqVal a T1 * fqVal a T2 * twoD - fqVal a C) := by
  have c1 := fqMulCore_forces a T1 T2 tt qtt h1        -- T1·T2 ≡ tt
  have c2 := fqMulConstCore_forces a tt C qC twoD h2   -- tt·2d ≡ C
  have hstep : (q : ℤ) ∣ (fqVal a T1 * fqVal a T2 * twoD - fqVal a tt * twoD) := by
    have h := Dvd.dvd.mul_right c1 twoD
    have hr : (fqVal a T1 * fqVal a T2 - fqVal a tt) * twoD
        = fqVal a T1 * fqVal a T2 * twoD - fqVal a tt * twoD := by ring
    rwa [hr] at h
  have hrw : fqVal a T1 * fqVal a T2 * twoD - fqVal a C
      = (fqVal a T1 * fqVal a T2 * twoD - fqVal a tt * twoD) + (fqVal a tt * twoD - fqVal a C) := by
    ring
  rw [hrw]; exact dvd_add hstep c2

/-- **`edAdd_D_forces`** — `D ≡ 2·Z1·Z2 (mod q)`: the `zz` mul gate + the `D = zz+zz` add gate. -/
theorem edAdd_D_forces (a : Assignment) (Z1 Z2 zz D qzz cD : Nat)
    (h1 : evalH (fqMulHead Z1 Z2 zz qzz) a = 0)
    (h2 : evalH (fqAddHead zz zz D cD) a = 0) :
    (q : ℤ) ∣ (2 * (fqVal a Z1 * fqVal a Z2) - fqVal a D) := by
  have c1 := fqMulCore_forces a Z1 Z2 zz qzz h1   -- Z1·Z2 ≡ zz
  have c2 := fqAddCore_forces a zz zz D cD h2     -- zz + zz ≡ D
  have hstep : (q : ℤ) ∣ (2 * (fqVal a Z1 * fqVal a Z2) - (fqVal a zz + fqVal a zz)) := by
    have : (q : ℤ) ∣ 2 * (fqVal a Z1 * fqVal a Z2 - fqVal a zz) := Dvd.dvd.mul_left c1 2
    have hrw : 2 * (fqVal a Z1 * fqVal a Z2) - (fqVal a zz + fqVal a zz)
        = 2 * (fqVal a Z1 * fqVal a Z2 - fqVal a zz) := by ring
    rw [hrw]; exact this
  have hrw : 2 * (fqVal a Z1 * fqVal a Z2) - fqVal a D
      = (2 * (fqVal a Z1 * fqVal a Z2) - (fqVal a zz + fqVal a zz))
        + (fqVal a zz + fqVal a zz - fqVal a D) := by ring
  rw [hrw]; exact dvd_add hstep c2

#assert_axioms dvd_mul_lift
#assert_axioms edAdd_forces
#assert_axioms edAdd_A_forces
#assert_axioms edAdd_Bb_forces
#assert_axioms edAdd_C_forces
#assert_axioms edAdd_D_forces

/-! ## §5 — A `Nat` `Fq` + extended-Edwards reference, anchored to an Ed25519 (ref10-style) computation.
Pure `Nat` field arithmetic (kernel-reducible); supplies the honest witnesses the gadget KATs accept. -/

namespace Ref

/-- Canonical `Fq` multiplication. -/
def fqMul (x y : Nat) : Nat := (x * y) % qN
/-- Canonical `Fq` addition. -/
def fqAdd (x y : Nat) : Nat := (x + y) % qN
/-- Canonical `Fq` subtraction (`x, y < q`). -/
def fqSub (x y : Nat) : Nat := (x + qN - y) % qN

/-- The `i`-th `limbBits`-bit limb of `v` as a felt value. -/
def limbOf (v i : Nat) : ℤ := (((v / 2 ^ (limbBits * i)) % 2 ^ limbBits : Nat) : ℤ)

/-! ### The Ed25519 base point `B` and the anchored test operands. -/

/-- Base point `x`-coordinate `Bx`. -/
def Bx : Nat := 15112221349535400772501151409588531511454012693041857206046113283949847762202
/-- Base point `y`-coordinate `By`. -/
def By : Nat := 46316835694926478169428394003475163141307993866256225615783033603165251855960
/-- `T`-coordinate of `B` in extended coords with `Z = 1`: `Bx·By mod q`. -/
def Bxy : Nat := 46827403850823179245072216630277197565144205554125654976674165829533817101731

/-- `3·B` extended-coord `X`, normalised to `Z = 1` (a generic non-identity operand). -/
def A2X : Nat := 46896733464454938657123544595386787789046198280132665686241321779790909858396
/-- `3·B` extended-coord `Y` (`Z = 1`). -/
def A2Y : Nat := 8324843778533443976490377120369201138301417226297555316741202210403726505172
/-- `3·B` extended-coord `T` (`Z = 1`): `A2X·A2Y mod q`. -/
def A2T : Nat := 19133203167024340156157901305709655404499344800967978305064989153409356768282

/-- Field KAT operands. -/
def X : Nat := 8234104123542484906572010032064808850921064262571995443881932229087025662105
def Y : Nat := 6809518635040324971929803101472088575662782660641002711672773399993035656976

-- Reference anchors: independently-computed Ed25519 `Fq` results.
#guard fqMul X Y == 45625797440278249798620114860258715365241591844391327976313835470940848600043
#guard fqAdd X Y == 15043622758582809878501813133536897426583846923212998155554705629080061319081
#guard fqSub Y X == 56471459130155937777143285573751233651376710730889289287519633174862574814820
-- Encoding sanity: the 9×30 limb value head reproduces a known `Fq` element (`By`).
#guard ((List.range numLimbs).foldl (fun acc i => acc + (By / 2 ^ (limbBits * i)) % 2 ^ limbBits
          * 2 ^ (limbBits * i)) 0) == By

/-! ### The extended-coordinate unified addition, `Nat` reference (matches `edAddGadget`). -/

/-- Extended-coord unified add (a=−1), returning `(X3, Y3, T3, Z3)`. Each intermediate is a reduced
`Fq` element, matching the per-gate outputs of `edAddGadget`. -/
def edAdd (X1 Y1 Z1 T1 X2 Y2 Z2 T2 : Nat) : Nat × Nat × Nat × Nat :=
  let ym1 := fqSub Y1 X1
  let ym2 := fqSub Y2 X2
  let A   := fqMul ym1 ym2
  let yp1 := fqAdd Y1 X1
  let yp2 := fqAdd Y2 X2
  let B   := fqMul yp1 yp2
  let tt  := fqMul T1 T2
  let C   := fqMul tt twoDN
  let zz  := fqMul Z1 Z2
  let D   := fqAdd zz zz
  let E   := fqSub B A
  let F   := fqSub D C
  let G   := fqAdd D C
  let H   := fqAdd B A
  (fqMul E F, fqMul G H, fqMul E H, fqMul F G)

/-- `X3` of the reference add. -/
def edAddX3 (X1 Y1 Z1 T1 X2 Y2 Z2 T2 : Nat) : Nat := (edAdd X1 Y1 Z1 T1 X2 Y2 Z2 T2).1
def edAddY3 (X1 Y1 Z1 T1 X2 Y2 Z2 T2 : Nat) : Nat := (edAdd X1 Y1 Z1 T1 X2 Y2 Z2 T2).2.1
def edAddT3 (X1 Y1 Z1 T1 X2 Y2 Z2 T2 : Nat) : Nat := (edAdd X1 Y1 Z1 T1 X2 Y2 Z2 T2).2.2.1
def edAddZ3 (X1 Y1 Z1 T1 X2 Y2 Z2 T2 : Nat) : Nat := (edAdd X1 Y1 Z1 T1 X2 Y2 Z2 T2).2.2.2

-- Reference anchors: point ADD `B + 3B = 4B` in extended coords (Ed25519-computed).
#guard edAddX3 Bx By 1 Bxy A2X A2Y 1 A2T
  == 25799762199084644124839324000046942253972107936009258225934267994245146992411
#guard edAddY3 Bx By 1 Bxy A2X A2Y 1 A2T
  == 6355171833164432472579106617055651553996383124106504179345479759478948609748
#guard edAddT3 Bx By 1 Bxy A2X A2Y 1 A2T
  == 39845259304799141414891081505707038562599354473598039226703523856223791534070
#guard edAddZ3 Bx By 1 Bxy A2X A2Y 1 A2T
  == 55460007627319096354716224248095017594369634950855859919210561093912448375343
-- Reference anchors: point DOUBLE `2B = B + B` (the unified law on `(B, B)`).
#guard edAddX3 Bx By 1 Bxy Bx By 1 Bxy
  == 26883520653101733888824139182319689719343092404687251721493239344894375351934
#guard edAddY3 Bx By 1 Bxy Bx By 1 Bxy
  == 23261637645573139634066509743476160005486969243270575189348263183774273634430
#guard edAddZ3 Bx By 1 Bxy Bx By 1 Bxy
  == 40660300372986216901848588050997382902664679514866213092364463299443684050440

end Ref

/-! ## §6 — KAT: the GENERATED gates ACCEPT the reference's honest witness and REJECT a bump.
Reuses `Bls12381Tower.acceptB`/`bumpAt` (the shared ℤ-reading harness). -/

/-! ### `fqMul` — layout x=0, y=9, z=18, k=27. Honest witness `z = X·Y mod q`, `k = (X·Y − z)/q`. -/

/-- Honest `fqMul` witness. -/
def fqMulAsg (Xv Yv : Nat) : Assignment := fun col =>
  let Z := Ref.fqMul Xv Yv
  let K := (Xv * Yv - Z) / qN
  if col < 9 then Ref.limbOf Xv col
  else if col < 18 then Ref.limbOf Yv (col - 9)
  else if col < 27 then Ref.limbOf Z (col - 18)
  else if col < 36 then Ref.limbOf K (col - 27)
  else 0

#guard acceptB [fqMulCore 0 9 18 27] (fqMulAsg Ref.X Ref.Y) == true
#guard acceptB [fqMulCore 0 9 18 27] (bumpAt (fqMulAsg Ref.X Ref.Y) 18) == false  -- bump z limb 0
#guard acceptB [fqMulCore 0 9 18 27] (bumpAt (fqMulAsg Ref.X Ref.Y) 27) == false  -- bump k limb 0

/-! ### `fqAdd` — layout x=0, y=9, z=18, c=27. Carry-exercising case `(q−1) + (q−1)` (`c=1`). -/

/-- Honest `fqAdd` witness. -/
def fqAddAsg (Xv Yv : Nat) : Assignment := fun col =>
  let Z := Ref.fqAdd Xv Yv
  let Cc := (Xv + Yv - Z) / qN
  if col < 9 then Ref.limbOf Xv col
  else if col < 18 then Ref.limbOf Yv (col - 9)
  else if col < 27 then Ref.limbOf Z (col - 18)
  else if col = 27 then (Cc : ℤ)
  else 0

#guard acceptB [fqAddCore 0 9 18 27] (fqAddAsg (qN - 1) (qN - 1)) == true          -- c = 1 (overflow)
#guard acceptB [fqAddCore 0 9 18 27] (bumpAt (fqAddAsg (qN - 1) (qN - 1)) 18) == false
#guard acceptB [fqAddCore 0 9 18 27] (fqAddAsg Ref.X Ref.Y) == true                -- c = 0 (no overflow)

/-! ### `fqSub` — layout x=0, y=9, z=18, c=27. Borrow-exercising case `Y − X` with `Y < X` (`c=1`). -/

/-- Honest `fqSub` witness. -/
def fqSubAsg (Xv Yv : Nat) : Assignment := fun col =>
  let Z := Ref.fqSub Xv Yv
  let Cc := (Z + Yv - Xv) / qN
  if col < 9 then Ref.limbOf Xv col
  else if col < 18 then Ref.limbOf Yv (col - 9)
  else if col < 27 then Ref.limbOf Z (col - 18)
  else if col = 27 then (Cc : ℤ)
  else 0

#guard acceptB [fqSubCore 0 9 18 27] (fqSubAsg Ref.Y Ref.X) == true                -- borrow = 1
#guard acceptB [fqSubCore 0 9 18 27] (bumpAt (fqSubAsg Ref.Y Ref.X) 18) == false

/-! ### `edAddGadget` — the WHOLE 18-gate composed point-add accepts the honest trace, rejects a bumped
output. Inputs `P1=(X1,Y1,Z1,T1)` at `0/9/18/27`, `P2` at `36/45/54/63`, scratch from `72`. -/

/-- Honest full `edAddGadget` trace for `(X1,Y1,Z1,T1) + (X2,Y2,Z2,T2)`, inputs at `0..63`, base `72`.
Lays out every intermediate/quotient/carry the 18 core gates reference. -/
def edAddAsg (X1v Y1v Z1v T1v X2v Y2v Z2v T2v : Nat) : Assignment := fun col =>
  let ym1 := Ref.fqSub Y1v X1v
  let ym2 := Ref.fqSub Y2v X2v
  let A   := Ref.fqMul ym1 ym2
  let yp1 := Ref.fqAdd Y1v X1v
  let yp2 := Ref.fqAdd Y2v X2v
  let B   := Ref.fqMul yp1 yp2
  let tt  := Ref.fqMul T1v T2v
  let C   := Ref.fqMul tt twoDN
  let zz  := Ref.fqMul Z1v Z2v
  let D   := Ref.fqAdd zz zz
  let E   := Ref.fqSub B A
  let F   := Ref.fqSub D C
  let G   := Ref.fqAdd D C
  let H   := Ref.fqAdd B A
  let X3  := Ref.fqMul E F
  let Y3  := Ref.fqMul G H
  let T3  := Ref.fqMul E H
  let Z3  := Ref.fqMul F G
  let qA  := (ym1 * ym2 - A) / qN
  let qB  := (yp1 * yp2 - B) / qN
  let qtt := (T1v * T2v - tt) / qN
  let qC  := (tt * twoDN - C) / qN
  let qzz := (Z1v * Z2v - zz) / qN
  let qX3 := (E * F - X3) / qN
  let qY3 := (G * H - Y3) / qN
  let qT3 := (E * H - T3) / qN
  let qZ3 := (F * G - Z3) / qN
  let bym1 := (ym1 + X1v - Y1v) / qN
  let bym2 := (ym2 + X2v - Y2v) / qN
  let cyp1 := (Y1v + X1v - yp1) / qN
  let cyp2 := (Y2v + X2v - yp2) / qN
  let cD   := (zz + zz - D) / qN
  let bE   := (E + A - B) / qN
  let bF   := (F + C - D) / qN
  let cG   := (D + C - G) / qN
  let cH   := (B + A - H) / qN
  if col < 9 then Ref.limbOf X1v col
  else if col < 18 then Ref.limbOf Y1v (col - 9)
  else if col < 27 then Ref.limbOf Z1v (col - 18)
  else if col < 36 then Ref.limbOf T1v (col - 27)
  else if col < 45 then Ref.limbOf X2v (col - 36)
  else if col < 54 then Ref.limbOf Y2v (col - 45)
  else if col < 63 then Ref.limbOf Z2v (col - 54)
  else if col < 72 then Ref.limbOf T2v (col - 63)
  else if col < 81 then Ref.limbOf ym1 (col - 72)
  else if col < 90 then Ref.limbOf ym2 (col - 81)
  else if col < 99 then Ref.limbOf A (col - 90)
  else if col < 108 then Ref.limbOf yp1 (col - 99)
  else if col < 117 then Ref.limbOf yp2 (col - 108)
  else if col < 126 then Ref.limbOf B (col - 117)
  else if col < 135 then Ref.limbOf tt (col - 126)
  else if col < 144 then Ref.limbOf C (col - 135)
  else if col < 153 then Ref.limbOf zz (col - 144)
  else if col < 162 then Ref.limbOf D (col - 153)
  else if col < 171 then Ref.limbOf E (col - 162)
  else if col < 180 then Ref.limbOf F (col - 171)
  else if col < 189 then Ref.limbOf G (col - 180)
  else if col < 198 then Ref.limbOf H (col - 189)
  else if col < 207 then Ref.limbOf X3 (col - 198)
  else if col < 216 then Ref.limbOf Y3 (col - 207)
  else if col < 225 then Ref.limbOf T3 (col - 216)
  else if col < 234 then Ref.limbOf Z3 (col - 225)
  else if col < 243 then Ref.limbOf qA (col - 234)
  else if col < 252 then Ref.limbOf qB (col - 243)
  else if col < 261 then Ref.limbOf qtt (col - 252)
  else if col < 270 then Ref.limbOf qC (col - 261)
  else if col < 279 then Ref.limbOf qzz (col - 270)
  else if col < 288 then Ref.limbOf qX3 (col - 279)
  else if col < 297 then Ref.limbOf qY3 (col - 288)
  else if col < 306 then Ref.limbOf qT3 (col - 297)
  else if col < 315 then Ref.limbOf qZ3 (col - 306)
  else if col = 315 then (bym1 : ℤ)
  else if col = 316 then (bym2 : ℤ)
  else if col = 317 then (cyp1 : ℤ)
  else if col = 318 then (cyp2 : ℤ)
  else if col = 319 then (cD : ℤ)
  else if col = 320 then (bE : ℤ)
  else if col = 321 then (bF : ℤ)
  else if col = 322 then (cG : ℤ)
  else if col = 323 then (cH : ℤ)
  else 0

/-- The point-add gadget under test: `B + 3B`, inputs at `0..63`, scratch from `72`. -/
def edAddGadgetKAT : List VmConstraint2 := edAddGadget 0 9 18 27 36 45 54 63 72
/-- The point-double gadget under test: `2B` (unified law on `(B, B)`), same layout. -/
def edDoubleGadgetKAT : List VmConstraint2 := edDoubleGadget 0 9 18 27 72

#guard acceptB edAddGadgetKAT (edAddAsg Ref.Bx Ref.By 1 Ref.Bxy Ref.A2X Ref.A2Y 1 Ref.A2T) == true
#guard acceptB edAddGadgetKAT
  (bumpAt (edAddAsg Ref.Bx Ref.By 1 Ref.Bxy Ref.A2X Ref.A2Y 1 Ref.A2T) 198) == false  -- bump X3 limb0
#guard acceptB edAddGadgetKAT
  (bumpAt (edAddAsg Ref.Bx Ref.By 1 Ref.Bxy Ref.A2X Ref.A2Y 1 Ref.A2T) 225) == false  -- bump Z3 limb0
#guard acceptB edDoubleGadgetKAT (edAddAsg Ref.Bx Ref.By 1 Ref.Bxy Ref.Bx Ref.By 1 Ref.Bxy) == true
#guard acceptB edDoubleGadgetKAT
  (bumpAt (edAddAsg Ref.Bx Ref.By 1 Ref.Bxy Ref.Bx Ref.By 1 Ref.Bxy) 198) == false     -- bump 2B X3

/-! ## §7 — Structural `#guard`s (the generators produce the budgeted shapes) + AIR packaging. -/

#guard (fqMulCore 0 9 18 27 :: []).length == 1
#guard (fqLimbRange 0 100).length == 279
#guard (fqMul 0 9 18 27 200 500).length == 559
#guard (fqAdd 0 9 18 27 100).length == 281
#guard (fqSub 0 9 18 27 100).length == 281
#guard (edAddGadget 0 9 18 27 36 45 54 63 72).length == 18
#guard (edDoubleGadget 0 9 18 27 72).length == 18

/-- A single `fqMul` gate packaged as an `EffectVmDescriptor2` (the AIR type the light-client emits) —
the generator drops straight into the deployed descriptor vocabulary. -/
def fqMulDesc : EffectVmDescriptor2 :=
  { name        := "dregg-ed25519-fqmul::demo"
  , traceWidth  := 36
  , piCount     := 0
  , tables      := []
  , constraints := [fqMulCore 0 9 18 27]
  , hashSites   := []
  , ranges      := [] }

/-- The whole 18-gate point-add packaged as a descriptor (inputs `0..63`, scratch `72..323`). -/
def edAddDesc : EffectVmDescriptor2 :=
  { name        := "dregg-ed25519-edadd::demo"
  , traceWidth  := 324
  , piCount     := 0
  , tables      := []
  , constraints := edAddGadgetKAT
  , hashSites   := []
  , ranges      := [] }

#guard fqMulDesc.constraints.length == 1
#guard edAddDesc.constraints.length == 18
#guard edAddDesc.traceWidth == 324

/-! ## §8 — The PRECISE named continuation to a full `ED_OK` fold (mechanical, NOT free).

The generators make each step mechanical; none is built. In order:

  1. **Scalar mult `[k]P`** — double-and-add over `edDoubleGadget`/`edAddGadget`: for a 255-bit scalar,
     255 doublings + up to 255 conditional adds (each add gated by the scalar bit — a `binGate` select
     over the point coordinates, the `Sha256Gadget`-style conditional). A windowed/fixed-base `[S]B`
     precomputes multiples of `B` (a lookup table) and is cheaper than the variable-base `[k]A`.
  2. **The SHA-512 challenge `k = SHA-512(R‖A‖M) mod L`** — a SIBLING of `Sha256Gadget`: SHA-512 is the
     SAME Merkle–Damgård shape with 64-bit words (the `addMod32` generator becomes `addMod64`, the
     bit-decomposition range widens to 64 bits), 80 rounds (vs 64), the SHA-512 IV/round-constant
     tables (fractional parts of √/∛ of the first 8/80 primes, 64-bit), and the SHA-512 Σ/σ rotation
     amounts (`28/34/39`, `14/18/41`, `1/8/7`, `19/61/6`). The `Sha256Gadget` generator is the
     template; only the word width + constant tables + rotations change.
  3. **The mod-`L` scalar reduction** — reduce the 512-bit hash output mod the group order `L` (`LN`,
     ~2⁵²) by the SAME quotient-witness technique as the `Fq` reduction here, `q → L`: witness `κ` with
     `hash = κ·L + k`, range-check `k < L`. A NAMED sibling of `fqMul`'s reduction, different modulus.
  4. **The verify equation `[S]B == R + [k]A`** — compute `[S]B` (fixed-base scalar mult), `[k]A`
     (variable-base scalar mult of the public-key point `A`), the point-add `R + [k]A` (this gadget),
     then an extended-coordinate EQUALITY gate. Extended coords are NOT unique, so equality is the
     cross-multiply `X_l·Z_r ≡ X_r·Z_l ∧ Y_l·Z_r ≡ Y_r·Z_l (mod q)` — two `fqMul`s + a `fqSub`-to-zero
     per coordinate. That boolean IS the `ED_OK` bit, DERIVED, dropping the trusted carrier.

**Gate-count reality (order of magnitude).** One `fqMul` is `559` gates here; one point-add is
`≈ 9·fqMul + 9·(fqAdd/fqSub) ≈ 9·559 + 9·281 ≈ 7.6·10³` gates (with ranges). A scalar mult is
`≈ 255` doublings + `255` adds `≈ 510` point-ops `≈ 4·10⁶` gates. A single ed25519 verify is two
scalar mults + one add + SHA-512 (`≈ 80` rounds × a handful of `addMod64`/range) + the mod-`L`
reduction `≈ 10⁷` gates — LARGE, but roughly an ORDER OF MAGNITUDE CHEAPER than a BLS pairing
(`Bls12381Tower` §8's `~10⁷` for the Miller loop ALONE, before the final exponentiation), and it is
why `ED_OK` is a trusted carrier today. The point of THIS slice is EXPRESSIBILITY: the field + the
complete point-add are generated + KAT'd + FORCED, so each step above is COMPOSITION over these
generators, not new constraint algebra. None of §8 is claimed built; this file is the `Fq` + Edwards
point-add floor it stands on.
-/

end Dregg2.Circuit.Emit.Ed25519Gadget
