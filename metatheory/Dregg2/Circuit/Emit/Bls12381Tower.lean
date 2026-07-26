/-
# Dregg2.Circuit.Emit.Bls12381Tower — a Lean-GENERATED BLS12-381 field-TOWER AIR foundation
(the arithmetic floor under an in-STARK pairing).

## Why this file exists (the carrier it is aimed at)

The ETH light-client's LAST trusted carrier is `BLS_OK`: the sync-committee aggregate signature
verify `e(sig, g2) == e(H(m), agg_pk)`, a BLS12-381 pairing asserted as a witnessed boolean bit the
same way `Sha256Gadget` was aimed at `FIN_OK`/`EXEC_OK`. Replacing `BLS_OK` with an IN-CIRCUIT
derivation means expressing the Tate/ate pairing `e : G1 × G2 → Fp12` as AIR constraints: a Miller
loop + a final exponentiation, over the FIELD TOWER `Fp ⊂ Fp2 ⊂ Fp6 ⊂ Fp12`. That whole edifice is
built out of ONE primitive — multiplication in the 381-bit prime field `Fp` — iterated. This file is
that primitive and its FIRST tower layer (`Fp2`), GENERATED (House Law #1), KAT'd against real
BLS12-381 vectors, with the per-op gates PROVEN to force the field congruence.

This is the FOUNDATION slice, honestly named: a KAT'd + forced `Fp`/`Fp2` tower is a real floor; it
is NOT a pairing. The precise mechanical continuation to a full `e(·,·)` (Fp6/Fp12, G1/G2, Miller,
final-exp, the `BLS_OK` rewrite) is spelled out in §7 with its gate-count reality (~millions of
gates — the accepted zk-STARK pairing cost).

## The metaprogramming approach (GENERATED, mirroring `Sha256Gadget`)

Everything is produced by Lean `def`-GENERATORS over `AirBuilder.Head` (`Σ coeff·∏cols + const`), each
constraint a per-row gate `cgH head = .base (.gate (headToExpr head))` that reuses
`AirBuilder.headToExpr_eval` — the emitted gate polynomial evaluates to exactly the head value, the
SAME `body ≡ 0 [ZMOD p_felt]` tooth every deployed gate carries. New library primitive added here:
`Head.mul` (product of two polynomial heads) with `evalH_mul : evalH (h.mul o) a = evalH h a * evalH o
a` — the field multiplication gate is `(value-head x).mul (value-head y)` minus the reduction, so
`Fp2`/`Fp6`/`Fp12` multiplication are the SAME generator composed (the whole point).

## The felt-encoding (two moduli — keep them distinct)

There are TWO moduli in play and they are unrelated:
  * `p_felt` = BabyBear (`2013265921`, ~31 bits) — the STARK's native field the columns live in.
  * `p`      = the BLS12-381 BASE PRIME (381 bits) — the field the arithmetic is OVER.

A BLS12-381 `Fp` element is encoded as **`numLimbs = 13` limbs of `limbBits = 30` bits** over BabyBear
felt columns `base .. base+12`, LSB-first: its value is the degree-1 head
`fpValue base = Σ_{i<13} 2^{30 i}·col(base+i)`. Capacity 390 bits ≥ 381 (top limb uses 21 bits); a
30-bit limb (`< 2^30 = 1073741824 < p_felt`) fits one BabyBear felt with room. Products of two limbs
reach `< 2^60` and the schoolbook cross-sum reaches `~2^780` — this OVERFLOWS BabyBear, so the gate is
read over ℤ (the strong reading, exactly as `Sha256Gadget.addMod32` is), and the `ℤ ↔ p_felt`
soundness is the SAME field-width residual `LightClientEthAir` §6 and the SHA gadget already carry.

## The reduction strategy (non-native field arithmetic via a QUOTIENT WITNESS)

Field ops reduce mod `p` by the standard non-native technique — witness the quotient and check the
big-integer identity over ℤ:
  * `fpAdd x y = z`: witness carry bit `c ∈ {0,1}`, gate `xVal + yVal − zVal − c·p = 0`
    (`x,y<p ⇒ x+y<2p`, so one carry). Forces `x + y ≡ z  (mod p)`.
  * `fpSub x y = z`: witness borrow bit `c ∈ {0,1}`, gate `xVal − yVal + c·p − zVal = 0`.
    Forces `x − y ≡ z  (mod p)`.
  * `fpMul x y = z`: witness quotient limbs `q` (`x·y = q·p + z`, `q < 2^382`), gate
    `xVal·yVal − p·qVal − zVal = 0` (degree 2, the `Head.mul` cross-product). Forces `x·y ≡ z (mod p)`.
Canonicity (`0 ≤ z < p`, the UNIQUE representative) needs the limb range checks `z_i ∈ [0,2^30)`
(`fpLimbRange`, generated via `AirBuilder.rangeNonneg`) plus the `z < p` comparison; the ranges are
generated here and the final `z < p` compare is the one NAMED reduction residual (`AirBuilder`'s
`forcedGe0` is the shape). The congruence — the arithmetic content — is a proved forcing lemma.

## Constraint budget (per op, in gates)

  * `fpAddCore`/`fpSubCore`: 1 value gate. `+ 1` carry pin `+ 403` limb-range (`fpLimbRange`) = **405**.
  * `fpMulCore`: 1 degree-2 value gate (`13² = 169` cross-products + 13 q-terms + 13 z-terms).
    `+ 403·2` (z and q ranges) = **807**.
  * `fp2Mul` (Karatsuba, `3 mul + 3 add + 2 sub` core gates) = **8 core gates** composed (ranges add
    per output). The tower iterates: `Fp6 = 3·Fp2`, `Fp12 = 2·Fp6` — same generator, deeper fold.

## What is AUTHORED + built vs NAMED mechanical continuation

AUTHORED + built here: the encoding `fpValue`; `Head.mul`/`evalH_mul`; the `fpAdd`/`fpSub`/`fpMul`
core generators + their forcing lemmas (`fp{Add,Sub,Mul}Core_forces`, ℤ-congruence mod the real
BLS12-381 `p`); the range generator `fpLimbRange`; the `Fp2` layer `fp2Add`/`fp2MulGadget` (COMPOSED
from the `Fp` generators) + `fp2Mul_forces` (the whole `Fp2` product congruence, PROVEN by composing
the `Fp` gate forcings — the tower composing at the proof level). AUTHORED + KAT'd both-polarity: a
`Nat` `Fp`/`Fp2` reference anchored to py_ecc-computed BLS12-381 vectors supplies honest witnesses the
generated gates ACCEPT and a bumped limb REJECTS (`fpMul`/`fpAdd`(carry)/`fpSub`(borrow)/`fp2Mul`, plus
a range-bite KAT). NAMED continuation (§7): `Fp6`/`Fp12`, `G1`/`G2` point ops, the Miller loop, the
final exponentiation, the aggregate-verify wiring that replaces `BLS_OK`.

## Resolution (honest)

REAL: the `Fp`/`Fp2` generators exist + type-check in the deployed IR-v2 vocabulary; the reference is
py_ecc-anchored; the gates FORCE the field congruence (ℤ reading) and `fp2Mul` forces the `Fp2`
product; both-polarity KATs are non-vacuous. NOT claimed: a working pairing, a folded `BLS_OK`, or
native-field (`p_felt`) soundness — the gate is read over ℤ (the shared field-width residual), the
`z < p` canonical compare is named, and Fp6→pairing is §7's arc, not built.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/`native_decide`.
The `#guard` KATs reduce in the kernel. NEW file; imports read-only (`AirBuilder`); standalone (NOT
imported by the `Dregg2` root, built directly as `Dregg2.Circuit.Emit.Bls12381Tower`).
-/
import Dregg2.Circuit.Emit.AirBuilder

namespace Dregg2.Circuit.Emit.Bls12381Tower

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.AirBuilder

set_option autoImplicit false

/-! ## §0 — Encoding parameters + `Head.mul` (the new metaprogramming primitive). -/

/-- The BLS12-381 base prime `p` (381 bits). The field the tower is OVER (NOT the felt field). -/
def pN : Nat :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

/-- `p` as an integer (gate coefficients). -/
def p : ℤ := (pN : ℤ)

/-- Limbs per `Fp` element. -/
def numLimbs : Nat := 13
/-- Bits per limb (a 30-bit limb `< 2^30 < 2013265921` fits one BabyBear felt). -/
def limbBits : Nat := 30

/-- **The value head** of the `Fp` element at columns `base..base+12`:
`Σ_{i<13} 2^{30 i}·col(base+i)` (degree 1, LSB-first, no packed-felt column). -/
def fpValue (base : Nat) : Head :=
  (List.range numLimbs).foldl (fun h i => h.addLin ((2 : ℤ) ^ (limbBits * i)) (base + i)) Head.zero

/-- The integer value the columns of `fpValue base` reconstruct to, under `a`. The forcing lemmas
speak in this — the reconstructed field element. (Definitionally `evalH (fpValue base) a`.) -/
def fpVal (a : Assignment) (base : Nat) : ℤ := evalH (fpValue base) a

/-- Bridge: the value head's evaluation IS the reconstructed field element (rewrites the gate
evaluation into `fpVal` for the forcing lemmas). -/
theorem fpVal_eq (a : Assignment) (base : Nat) : evalH (fpValue base) a = fpVal a base := rfl

/-! ### `Head.mul` — the PRODUCT of two polynomial heads. `(Σ tᵢ + c)(Σ sⱼ + d)` distributed:
cross products `tᵢ·sⱼ` (coeffs multiply, columns concatenate), the two constant·linear cross terms,
and the constant·constant. This is what makes `fpMul` — and every tower multiplication — GENERATED
from the value heads rather than hand-written. Declared into the `AirBuilder.Head` namespace (so
`(fpValue x).mul (fpValue y)` resolves) via an absolute path — this file adds to the vocabulary
without touching `AirBuilder.lean`. -/

/-- Product of two heads. -/
def _root_.Dregg2.Circuit.Emit.AirBuilder.Head.mul (h o : Head) : Head :=
  ⟨ h.terms.flatMap (fun t => o.terms.map (fun s => (t.1 * s.1, t.2 ++ s.2)))
      ++ o.terms.map (fun s => (h.const * s.1, s.2))
      ++ h.terms.map (fun t => (o.const * t.1, t.2))
  , h.const * o.const ⟩

/-- One cross term's value factors: `evalTerm (tc·sc, tcols ++ scols) = evalTerm t · evalTerm s`. -/
theorem evalTerm_mul_pair (a : Assignment) (t s : ℤ × List Nat) :
    evalTerm a (t.1 * s.1, t.2 ++ s.2) = evalTerm a t * evalTerm a s := by
  simp only [evalTerm, List.map_append, List.prod_append]
  ring

/-- One scaled term's value: `evalTerm (c·sc, scols) = c · evalTerm s`. -/
theorem evalTerm_scale_pair (a : Assignment) (c : ℤ) (s : ℤ × List Nat) :
    evalTerm a (c * s.1, s.2) = c * evalTerm a s := by
  simp only [evalTerm]; ring

/-- Scaling every term of a list by a constant `c` scales the term-sum by `c`. -/
theorem sum_evalTerm_scaleTerms (a : Assignment) (c : ℤ) (ss : List (ℤ × List Nat)) :
    ((ss.map (fun s => (c * s.1, s.2))).map (evalTerm a)).sum = c * (ss.map (evalTerm a)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons, ih, evalTerm_scale_pair]
    ring

/-- One `flatMap` step's term-sum: `t` distributed over `ss`. (Standalone — avoids a nested
induction colliding with the outer IH.) -/
theorem sum_evalTerm_cross_step (a : Assignment) (t : ℤ × List Nat) (ss : List (ℤ × List Nat)) :
    ((ss.map (fun s => (t.1 * s.1, t.2 ++ s.2))).map (evalTerm a)).sum
      = evalTerm a t * (ss.map (evalTerm a)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih, evalTerm_mul_pair]; ring

/-- The cross-product term-sum factors into the two term-sums (the distribution law). -/
theorem sum_evalTerm_cross (a : Assignment) (ts ss : List (ℤ × List Nat)) :
    ((ts.flatMap (fun t => ss.map (fun s => (t.1 * s.1, t.2 ++ s.2)))).map (evalTerm a)).sum
      = (ts.map (evalTerm a)).sum * (ss.map (evalTerm a)).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
      List.sum_cons, sum_evalTerm_cross_step]
    ring

/-- **THE PRODUCT BRIDGE.** The product head evaluates to the product of the head values. So a
`fpMul` gate over two value heads carries exactly `xVal·yVal`, and every tower multiplication is this
one lemma composed. -/
theorem evalH_mul (a : Assignment) (h o : Head) : evalH (h.mul o) a = evalH h a * evalH o a := by
  simp only [evalH, Head.mul, List.map_append, List.sum_append]
  rw [sum_evalTerm_cross a h.terms o.terms, sum_evalTerm_scaleTerms a h.const o.terms,
    sum_evalTerm_scaleTerms a o.const h.terms]
  ring

/-! ## §1 — The `Fp` gate heads + generators (GENERATED per op). -/

/-- **`fpAddHead`** — `xVal + yVal − zVal − c·p` (`c` = carry bit column). Zero forces `x+y ≡ z (p)`. -/
def fpAddHead (xB yB zB cCol : Nat) : Head :=
  (((fpValue xB).append (fpValue yB)).append ((fpValue zB).scale (-1))).addLin (-p) cCol

/-- **`fpSubHead`** — `xVal − yVal + c·p − zVal` (`c` = borrow bit). Zero forces `x−y ≡ z (p)`. -/
def fpSubHead (xB yB zB cCol : Nat) : Head :=
  (((fpValue xB).append ((fpValue yB).scale (-1))).append ((fpValue zB).scale (-1))).addLin p cCol

/-- **`fpMulHead`** — `xVal·yVal − p·qVal − zVal` (`q` = quotient limbs, degree 2 via `Head.mul`).
Zero forces `x·y ≡ z (p)`. -/
def fpMulHead (xB yB zB qB : Nat) : Head :=
  (((fpValue xB).mul (fpValue yB)).append ((fpValue qB).scale (-p))).append ((fpValue zB).scale (-1))

/-- `fpAdd` value gate. -/
def fpAddCore (xB yB zB cCol : Nat) : VmConstraint2 := cgH (fpAddHead xB yB zB cCol)
/-- `fpSub` value gate. -/
def fpSubCore (xB yB zB cCol : Nat) : VmConstraint2 := cgH (fpSubHead xB yB zB cCol)
/-- `fpMul` value gate. -/
def fpMulCore (xB yB zB qB : Nat) : VmConstraint2 := cgH (fpMulHead xB yB zB qB)

/-- **The limb range gadget** — every one of the 13 limbs of the `Fp` element at `base` is a real
`limbBits`-bit value, bit-decomposed at `bitBase` (13·30 = 390 bit columns), via
`AirBuilder.rangeNonneg`. `13·(30 + 1) = 403` constraints. -/
def fpLimbRange (base bitBase : Nat) : List VmConstraint2 :=
  (List.range numLimbs).flatMap (fun i =>
    rangeNonneg (Head.lin 1 (base + i)) ((List.range limbBits).map (fun j => bitBase + limbBits * i + j)))

/-- **`fpAdd`** — full generator: the value gate, the carry pin, and the output range. `405`. -/
def fpAdd (xB yB zB cCol zBit : Nat) : List VmConstraint2 :=
  fpAddCore xB yB zB cCol :: binGate cCol :: fpLimbRange zB zBit
/-- **`fpSub`** — full generator. `405`. -/
def fpSub (xB yB zB cCol zBit : Nat) : List VmConstraint2 :=
  fpSubCore xB yB zB cCol :: binGate cCol :: fpLimbRange zB zBit
/-- **`fpMul`** — full generator: the degree-2 value gate + the output range + the quotient range.
`807`. -/
def fpMul (xB yB zB qB zBit qBit : Nat) : List VmConstraint2 :=
  fpMulCore xB yB zB qB :: (fpLimbRange zB zBit ++ fpLimbRange qB qBit)

/-! ## §2 — The `Fp` gates FORCE the field congruence (ℤ reading, mod the real BLS12-381 `p`).

`p ∣ (u − v)` IS `u ≡ v (mod p)`. These are the "demonstrably computes, not just type-checks" content:
the gate's zero pins the reconstructed output to the field op of the reconstructed inputs. No
`native_decide`; the quotient/carry witness makes the reduction an ℤ identity. -/

/-- **`fpAdd` forces `x + y ≡ z (mod p)`.** -/
theorem fpAddCore_forces (a : Assignment) (xB yB zB cCol : Nat)
    (hg : evalH (fpAddHead xB yB zB cCol) a = 0) :
    (p : ℤ) ∣ (fpVal a xB + fpVal a yB - fpVal a zB) := by
  simp only [fpAddHead, evalH_addLin, evalH_append, evalH_scale, fpVal_eq] at hg
  exact ⟨a cCol, by linarith⟩

/-- **`fpSub` forces `x − y ≡ z (mod p)`.** -/
theorem fpSubCore_forces (a : Assignment) (xB yB zB cCol : Nat)
    (hg : evalH (fpSubHead xB yB zB cCol) a = 0) :
    (p : ℤ) ∣ (fpVal a xB - fpVal a yB - fpVal a zB) := by
  simp only [fpSubHead, evalH_addLin, evalH_append, evalH_scale, fpVal_eq] at hg
  exact ⟨-(a cCol), by linarith⟩

/-- **`fpMul` forces `x·y ≡ z (mod p)`.** -/
theorem fpMulCore_forces (a : Assignment) (xB yB zB qB : Nat)
    (hg : evalH (fpMulHead xB yB zB qB) a = 0) :
    (p : ℤ) ∣ (fpVal a xB * fpVal a yB - fpVal a zB) := by
  simp only [fpMulHead, evalH_append, evalH_scale, evalH_mul, fpVal_eq] at hg
  exact ⟨fpVal a qB, by linarith⟩

#assert_axioms evalH_mul
#assert_axioms fpAddCore_forces
#assert_axioms fpSubCore_forces
#assert_axioms fpMulCore_forces

/-! ## §3 — The `Fp2` layer (GENERATED by composing the `Fp` generators — the tower composing).

`Fp2 = Fp[u]/(u²+1)`, element `a0 + a1·u`. Multiplication via Karatsuba (3 `Fp` muls):
`(a0+a1 u)(b0+b1 u) = (a0 b0 − a1 b1) + ((a0+a1)(b0+b1) − a0 b0 − a1 b1)·u`. The gadget is a LIST of
`Fp` gate-generator calls with threaded columns — no gate is hand-authored (House Law #1). -/

/-- **`fp2Add`** — `(a0,a1) + (b0,b1) = (a0+b0, a1+b1)`: two `fpAdd`s. Inputs `a0,a1,b0,b1`, outputs
`r0,r1`, carry bits `c0,c1`, output ranges at `r0Bit,r1Bit`. -/
def fp2Add (a0 a1 b0 b1 r0 r1 c0 c1 r0Bit r1Bit : Nat) : List VmConstraint2 :=
  fpAdd a0 b0 r0 c0 r0Bit ++ fpAdd a1 b1 r1 c1 r1Bit

/-- **`fp2MulGadget`** — the `Fp2` product `(a0,a1)·(b0,b1)`, 8 CORE gates composed from the `Fp`
generators, intermediates allocated from `base` (values-only; the output ranges are the named
per-output addition). Layout (each limb group = 13 cols): `v0=a0·b0` at `base`, `v1=a1·b1` at
`base+13`, `sa=a0+a1` at `+26`, `sb=b0+b1` at `+39`, `v2=sa·sb` at `+52`, `w=v0+v1` at `+65`,
`r0=v0−v1` at `+78`, `r1=v2−w` at `+91`; quotients `qv0/qv1/qv2` at `+104/+117/+130`; carries/borrows
`csa/csb/cw/br0/br1` at `+143/+144/+145/+146/+147`. Outputs land at `base+78` (r0) and `base+91` (r1). -/
def fp2MulGadget (a0 a1 b0 b1 base : Nat) : List VmConstraint2 :=
  let v0 := base;      let v1 := base + 13
  let sa := base + 26; let sb := base + 39
  let v2 := base + 52; let w := base + 65
  let r0 := base + 78; let r1 := base + 91
  let qv0 := base + 104; let qv1 := base + 117; let qv2 := base + 130
  let csa := base + 143; let csb := base + 144; let cw := base + 145
  let br0 := base + 146; let br1 := base + 147
  [ fpMulCore a0 b0 v0 qv0      -- v0 = a0·b0
  , fpMulCore a1 b1 v1 qv1      -- v1 = a1·b1
  , fpAddCore a0 a1 sa csa      -- sa = a0+a1
  , fpAddCore b0 b1 sb csb      -- sb = b0+b1
  , fpMulCore sa sb v2 qv2      -- v2 = sa·sb
  , fpAddCore v0 v1 w cw        -- w  = v0+v1
  , fpSubCore v0 v1 r0 br0      -- r0 = v0−v1        (real part)
  , fpSubCore v2 w r1 br1 ]     -- r1 = v2−w         (imaginary part)

/-- The r0 output base of `fp2MulGadget`. -/
def fp2MulR0 (base : Nat) : Nat := base + 78
/-- The r1 output base of `fp2MulGadget`. -/
def fp2MulR1 (base : Nat) : Nat := base + 91

/-! ## §4 — `Fp2` forcing: the whole gadget FORCES the `Fp2` product congruence (proof-level tower).

Composed from §2's `Fp` gate forcings by ℤ-divisibility arithmetic — `Fp2` multiplication is CORRECT
mod `p` in each coordinate whenever the 8 gates hold, not merely KAT'd. -/

/-- `p ∣ (A−A')` and `p ∣ (B−B')` ⇒ `p ∣ (A·B − A'·B')` (the product-lift). -/
theorem dvd_mul_lift {A A' B B' : ℤ} (h1 : (p : ℤ) ∣ (A - A')) (h2 : (p : ℤ) ∣ (B - B')) :
    (p : ℤ) ∣ (A * B - A' * B') := by
  have hrw : A * B - A' * B' = (A - A') * B + A' * (B - B') := by ring
  rw [hrw]
  exact dvd_add (dvd_mul_of_dvd_left h1 B) (dvd_mul_of_dvd_right h2 A')

/-- **`fp2Mul` forces the `Fp2` product**, both coordinates, given the 8 core gates of `fp2MulGadget`
hold. `r0 ≡ a0 b0 − a1 b1` and `r1 ≡ a0 b1 + a1 b0` (mod `p`), i.e. the reconstructed outputs are the
`Fp2` product of the reconstructed inputs. The intermediates (`v0,v1,sa,sb,v2,w`) are the gadget's
allocated columns. -/
theorem fp2Mul_forces (a : Assignment) (a0 a1 b0 b1 v0 v1 sa sb v2 w r0 r1
    qv0 qv1 qv2 csa csb cw br0 br1 : Nat)
    (h0 : evalH (fpMulHead a0 b0 v0 qv0) a = 0)
    (h1 : evalH (fpMulHead a1 b1 v1 qv1) a = 0)
    (h2 : evalH (fpAddHead a0 a1 sa csa) a = 0)
    (h3 : evalH (fpAddHead b0 b1 sb csb) a = 0)
    (h4 : evalH (fpMulHead sa sb v2 qv2) a = 0)
    (h5 : evalH (fpAddHead v0 v1 w cw) a = 0)
    (h6 : evalH (fpSubHead v0 v1 r0 br0) a = 0)
    (h7 : evalH (fpSubHead v2 w r1 br1) a = 0) :
    (p : ℤ) ∣ (fpVal a a0 * fpVal a b0 - fpVal a a1 * fpVal a b1 - fpVal a r0)
    ∧ (p : ℤ) ∣ (fpVal a a0 * fpVal a b1 + fpVal a a1 * fpVal a b0 - fpVal a r1) := by
  -- The per-gate congruences.
  have c0 := fpMulCore_forces a a0 b0 v0 qv0 h0   -- a0·b0 ≡ v0
  have c1 := fpMulCore_forces a a1 b1 v1 qv1 h1   -- a1·b1 ≡ v1
  have ca := fpAddCore_forces a a0 a1 sa csa h2   -- a0+a1 ≡ sa
  have cb := fpAddCore_forces a b0 b1 sb csb h3   -- b0+b1 ≡ sb
  have c2 := fpMulCore_forces a sa sb v2 qv2 h4   -- sa·sb ≡ v2
  have cw' := fpAddCore_forces a v0 v1 w cw h5    -- v0+v1 ≡ w
  have cr0 := fpSubCore_forces a v0 v1 r0 br0 h6  -- v0−v1 ≡ r0
  have cr1 := fpSubCore_forces a v2 w r1 br1 h7   -- v2−w ≡ r1
  refine ⟨?_, ?_⟩
  · -- a0 b0 − a1 b1 − r0 = (a0 b0 − v0) − (a1 b1 − v1) + (v0 − v1 − r0)
    have hrw : fpVal a a0 * fpVal a b0 - fpVal a a1 * fpVal a b1 - fpVal a r0
        = (fpVal a a0 * fpVal a b0 - fpVal a v0) - (fpVal a a1 * fpVal a b1 - fpVal a v1)
          + (fpVal a v0 - fpVal a v1 - fpVal a r0) := by ring
    rw [hrw]; exact dvd_add (dvd_sub c0 c1) cr0
  · -- lift sa·sb ≡ (a0+a1)(b0+b1); then v2 ≡ that; combine with v0+v1≡w and v2−w≡r1.
    have hsa : (p : ℤ) ∣ ((fpVal a a0 + fpVal a a1) - fpVal a sa) := ca
    have hsb : (p : ℤ) ∣ ((fpVal a b0 + fpVal a b1) - fpVal a sb) := cb
    have hprod : (p : ℤ) ∣ ((fpVal a a0 + fpVal a a1) * (fpVal a b0 + fpVal a b1)
        - fpVal a sa * fpVal a sb) := dvd_mul_lift hsa hsb
    -- v2 ≡ sa·sb ≡ (a0+a1)(b0+b1); w ≡ v0+v1 ≡ a0 b0 + a1 b1.
    have hv2 : (p : ℤ) ∣ ((fpVal a a0 + fpVal a a1) * (fpVal a b0 + fpVal a b1) - fpVal a v2) := by
      have := dvd_add hprod c2
      have hrw : (fpVal a a0 + fpVal a a1) * (fpVal a b0 + fpVal a b1) - fpVal a v2
          = ((fpVal a a0 + fpVal a a1) * (fpVal a b0 + fpVal a b1) - fpVal a sa * fpVal a sb)
            + (fpVal a sa * fpVal a sb - fpVal a v2) := by ring
      rw [hrw]; exact this
    have hw : (p : ℤ) ∣ (fpVal a a0 * fpVal a b0 + fpVal a a1 * fpVal a b1 - fpVal a w) := by
      -- w ≡ v0+v1, v0 ≡ a0 b0, v1 ≡ a1 b1.
      have hstep : (p : ℤ) ∣ ((fpVal a v0 + fpVal a v1) - fpVal a w) := cw'
      have hrw : fpVal a a0 * fpVal a b0 + fpVal a a1 * fpVal a b1 - fpVal a w
          = (fpVal a a0 * fpVal a b0 - fpVal a v0) + (fpVal a a1 * fpVal a b1 - fpVal a v1)
            + ((fpVal a v0 + fpVal a v1) - fpVal a w) := by ring
      rw [hrw]; exact dvd_add (dvd_add c0 c1) hstep
    -- r1 ≡ v2 − w ≡ (a0+a1)(b0+b1) − (a0 b0 + a1 b1) = a0 b1 + a1 b0.
    have hrw : fpVal a a0 * fpVal a b1 + fpVal a a1 * fpVal a b0 - fpVal a r1
        = ((fpVal a a0 + fpVal a a1) * (fpVal a b0 + fpVal a b1) - fpVal a v2)
          - (fpVal a a0 * fpVal a b0 + fpVal a a1 * fpVal a b1 - fpVal a w)
          + (fpVal a v2 - fpVal a w - fpVal a r1) := by ring
    rw [hrw]; exact dvd_add (dvd_sub hv2 hw) cr1

#assert_axioms dvd_mul_lift
#assert_axioms fp2Mul_forces

/-! ## §5 — A `Nat` `Fp`/`Fp2` reference, anchored to py_ecc-computed BLS12-381 vectors.

Pure `Nat` field arithmetic (kernel-reducible). Anchors itself against independently-computed
(py_ecc-style) BLS12-381 products, and supplies the honest witness values the gadget KATs accept. -/

namespace Ref

/-- Canonical `Fp` multiplication. -/
def fpMul (x y : Nat) : Nat := (x * y) % pN
/-- Canonical `Fp` addition. -/
def fpAdd (x y : Nat) : Nat := (x + y) % pN
/-- Canonical `Fp` subtraction (`x, y < p`). -/
def fpSub (x y : Nat) : Nat := (x + pN - y) % pN

/-- `Fp2` product real part `a0 b0 − a1 b1`. -/
def fp2MulR0 (a0 a1 b0 b1 : Nat) : Nat := fpSub (fpMul a0 b0) (fpMul a1 b1)
/-- `Fp2` product imaginary part `(a0+a1)(b0+b1) − a0 b0 − a1 b1`. -/
def fp2MulR1 (a0 a1 b0 b1 : Nat) : Nat :=
  fpSub (fpMul (fpAdd a0 a1) (fpAdd b0 b1)) (fpAdd (fpMul a0 b0) (fpMul a1 b1))

/-- The `i`-th `limbBits`-bit limb of `v` as a felt value. -/
def limbOf (v i : Nat) : ℤ := (((v / 2 ^ (limbBits * i)) % 2 ^ limbBits : Nat) : ℤ)

/-- KAT operands (`< p`): two 252-bit field elements. -/
def X : Nat := 8234104123542484906572010032064808850921064262571995443881932229087025662105
def Y : Nat := 6809518635040324971929803101472088575662782660641002711672773399993035656976
/-- A third operand for the `Fp2` KAT (`b1 = 3·X + 7 < p`). -/
def B1 : Nat := 24702312370627454719716030096194426552763192787715986331645796687261076986322

-- Reference anchor: `fpMul X Y` = the py_ecc-computed BLS12-381 product `X·Y mod p`.
#guard fpMul X Y ==
  1224085606879803198787824264204261046198249508230733658036154861720999100425751149556484681853390918736473535192704
-- Reference anchors: the `Fp2` product `(X + Y·u)·(Y + B1·u)`, py_ecc-computed, both coordinates.
#guard fp2MulR0 X Y Y B1 ==
  1554238341462060995842141297327382064112717173032258294456239790971728829609696086705231246440524412764995952575547
#guard fp2MulR1 X Y Y B1 ==
  163644966253132151284173628538107985141451690402425043927029038526519404830533240576699297308899983406158068060272

end Ref

/-! ## §6 — KAT: the GENERATED gates ACCEPT the reference's honest witness and REJECT a bump.

`acceptB` is the ℤ reading of the emitted gate bodies (like `Sha256Gadget.acceptB` /
`LightClientEthAir.airAccepts`): every `.base (.gate e)` has `e.eval a = 0`. -/

/-- The ℤ reading of one emitted constraint (non-gates are addressing, vacuously true). -/
def gateBodyEvalZero (a : Assignment) : VmConstraint2 → Bool
  | .base (.gate e) => decide (e.eval a = 0)
  | _ => true

/-- The ℤ acceptance predicate over a generated constraint list. -/
def acceptB (gs : List VmConstraint2) (a : Assignment) : Bool := gs.all (gateBodyEvalZero a)

/-- Bump the felt at column `c` by 1 (to forge a witness; any change breaks the value gate). -/
def bumpAt (a : Assignment) (c : Nat) : Assignment := fun col => if col = c then a col + 1 else a col

/-! ### `fpMul` — layout x=0, y=13, z=26, q=39. Honest witness `z = X·Y mod p`, `q = (X·Y − z)/p`. -/

/-- Honest `fpMul` witness. -/
def fpMulAsg (Xv Yv : Nat) : Assignment := fun col =>
  let Z := Ref.fpMul Xv Yv
  let Q := (Xv * Yv - Z) / pN
  if col < 13 then Ref.limbOf Xv col
  else if col < 26 then Ref.limbOf Yv (col - 13)
  else if col < 39 then Ref.limbOf Z (col - 26)
  else if col < 52 then Ref.limbOf Q (col - 39)
  else 0

#guard acceptB [fpMulCore 0 13 26 39] (fpMulAsg Ref.X Ref.Y) == true
#guard acceptB [fpMulCore 0 13 26 39] (bumpAt (fpMulAsg Ref.X Ref.Y) 26) == false  -- bump z limb 0
#guard acceptB [fpMulCore 0 13 26 39] (bumpAt (fpMulAsg Ref.X Ref.Y) 39) == false  -- bump q limb 0

/-! ### `fpAdd` — layout x=0, y=13, z=26, c=39. Carry-exercising case `(p−1) + (p−1)` (`c=1`). -/

/-- Honest `fpAdd` witness. -/
def fpAddAsg (Xv Yv : Nat) : Assignment := fun col =>
  let Z := Ref.fpAdd Xv Yv
  let C := (Xv + Yv - Z) / pN
  if col < 13 then Ref.limbOf Xv col
  else if col < 26 then Ref.limbOf Yv (col - 13)
  else if col < 39 then Ref.limbOf Z (col - 26)
  else if col = 39 then (C : ℤ)
  else 0

#guard acceptB [fpAddCore 0 13 26 39] (fpAddAsg (pN - 1) (pN - 1)) == true          -- c = 1 (overflow)
#guard acceptB [fpAddCore 0 13 26 39] (bumpAt (fpAddAsg (pN - 1) (pN - 1)) 26) == false
#guard acceptB [fpAddCore 0 13 26 39] (fpAddAsg Ref.X Ref.Y) == true                -- c = 0 (no overflow)

/-! ### `fpSub` — layout x=0, y=13, z=26, c=39. Borrow-exercising case `Y − X` with `Y < X` (`c=1`). -/

/-- Honest `fpSub` witness. -/
def fpSubAsg (Xv Yv : Nat) : Assignment := fun col =>
  let Z := Ref.fpSub Xv Yv
  let C := (Z + Yv - Xv) / pN
  if col < 13 then Ref.limbOf Xv col
  else if col < 26 then Ref.limbOf Yv (col - 13)
  else if col < 39 then Ref.limbOf Z (col - 26)
  else if col = 39 then (C : ℤ)
  else 0

#guard acceptB [fpSubCore 0 13 26 39] (fpSubAsg Ref.Y Ref.X) == true                -- borrow = 1
#guard acceptB [fpSubCore 0 13 26 39] (bumpAt (fpSubAsg Ref.Y Ref.X) 26) == false

/-! ### `fp2Mul` — the WHOLE composed gadget accepts the honest trace, rejects a bumped output. -/

/-- Honest full `fp2Mul` trace witness for inputs `(a0v,a1v)·(b0v,b1v)`, base = 52 (inputs at
`0/13/26/39`). Lays out every intermediate the 8 core gates reference. -/
def fp2MulAsg (a0v a1v b0v b1v : Nat) : Assignment := fun col =>
  let v0 := Ref.fpMul a0v b0v
  let v1 := Ref.fpMul a1v b1v
  let sa := Ref.fpAdd a0v a1v
  let sb := Ref.fpAdd b0v b1v
  let v2 := Ref.fpMul sa sb
  let w := Ref.fpAdd v0 v1
  let r0 := Ref.fpSub v0 v1
  let r1 := Ref.fpSub v2 w
  let qv0 := (a0v * b0v - v0) / pN
  let qv1 := (a1v * b1v - v1) / pN
  let qv2 := (sa * sb - v2) / pN
  let csa := (a0v + a1v - sa) / pN
  let csb := (b0v + b1v - sb) / pN
  let cw := (v0 + v1 - w) / pN
  let br0 := (r0 + v1 - v0) / pN
  let br1 := (r1 + w - v2) / pN
  if col < 13 then Ref.limbOf a0v col
  else if col < 26 then Ref.limbOf a1v (col - 13)
  else if col < 39 then Ref.limbOf b0v (col - 26)
  else if col < 52 then Ref.limbOf b1v (col - 39)
  else if col < 65 then Ref.limbOf v0 (col - 52)
  else if col < 78 then Ref.limbOf v1 (col - 65)
  else if col < 91 then Ref.limbOf sa (col - 78)
  else if col < 104 then Ref.limbOf sb (col - 91)
  else if col < 117 then Ref.limbOf v2 (col - 104)
  else if col < 130 then Ref.limbOf w (col - 117)
  else if col < 143 then Ref.limbOf r0 (col - 130)
  else if col < 156 then Ref.limbOf r1 (col - 143)
  else if col < 169 then Ref.limbOf qv0 (col - 156)
  else if col < 182 then Ref.limbOf qv1 (col - 169)
  else if col < 195 then Ref.limbOf qv2 (col - 182)
  else if col = 195 then (csa : ℤ)
  else if col = 196 then (csb : ℤ)
  else if col = 197 then (cw : ℤ)
  else if col = 198 then (br0 : ℤ)
  else if col = 199 then (br1 : ℤ)
  else 0

/-- The gadget under test: `(X + Y·u)·(Y + B1·u)`, inputs at 0/13/26/39, scratch from 52. -/
def fp2Gadget : List VmConstraint2 := fp2MulGadget 0 13 26 39 52

#guard acceptB fp2Gadget (fp2MulAsg Ref.X Ref.Y Ref.Y Ref.B1) == true
#guard acceptB fp2Gadget (bumpAt (fp2MulAsg Ref.X Ref.Y Ref.Y Ref.B1) 130) == false  -- bump r0 limb 0
#guard acceptB fp2Gadget (bumpAt (fp2MulAsg Ref.X Ref.Y Ref.Y Ref.B1) 143) == false  -- bump r1 limb 0

/-! ### Range bite — `rangeNonneg` (the reduction's canonicity component) accepts in-range, rejects
out-of-range. A compact 4-bit instance (the 30-bit `fpLimbRange` is the same generator, wider). -/

/-- A 4-bit range on col 0, bits at cols 1..4; honest decomposition of `v`. -/
def rangeAsg4 (v : Nat) : Assignment := fun col =>
  if col = 0 then (v : ℤ)
  else if col ≤ 4 then (((v >>> (col - 1)) &&& 1 : Nat) : ℤ)
  else 0

def range4Gadget : List VmConstraint2 := rangeNonneg (Head.lin 1 0) [1, 2, 3, 4]

#guard acceptB range4Gadget (rangeAsg4 10) == true                       -- 10 < 16, in range
#guard acceptB range4Gadget (rangeAsg4 20) == false                      -- 20 ≥ 16: recomposition fails

/-! ## §7 — Structural `#guard`s (the generators produce the budgeted shapes) + AIR packaging. -/

#guard (fpMulCore 0 13 26 39 :: []).length == 1
#guard (fpLimbRange 0 100).length == 403
#guard (fpMul 0 13 26 39 200 590).length == 807
#guard (fpAdd 0 13 26 39 100).length == 405
#guard (fpSub 0 13 26 39 100).length == 405
#guard (fp2Add 0 13 26 39 52 65 78 79 80 470).length == 810
#guard (fp2MulGadget 0 13 26 39 52).length == 8

/-- A single `fpMul` gate packaged as an `EffectVmDescriptor2` (the AIR type the light-client emits),
showing the generator drops straight into the deployed descriptor vocabulary. -/
def fpMulDesc : EffectVmDescriptor2 :=
  { name        := "dregg-bls12381-fpmul::demo"
  , traceWidth  := 52
  , piCount     := 0
  , tables      := []
  , constraints := [fpMulCore 0 13 26 39]
  , hashSites   := []
  , ranges      := [] }

#guard fpMulDesc.constraints.length == 1
#guard fpMulDesc.traceWidth == 52

/-! ## §8 — The PRECISE named continuation to a full pairing (mechanical, NOT free).

The generator makes each step mechanical; none is authored yet. In order:

  1. **Fp6 = Fp2[v]/(v³ − (u+1))** — element `c0 + c1·v + c2·v²` (3 Fp2). Multiplication is Toom/
     Karatsuba over Fp2 (6 Fp2 muls + the `v³ = u+1` fold, which is a `mul-by-(u+1)` = one Fp2 mul by
     a constant). SAME pattern as `fp2MulGadget`, one level up: compose `fp2MulGadget`/`fp2Add`.
  2. **Fp12 = Fp6[w]/(w² − v)** — element `d0 + d1·w` (2 Fp6). Multiplication = 3 Fp6 muls (Karatsuba)
     + the `w² = v` fold. An Fp12 mul is thus `3·6 = 18` Fp2 muls `≈ 54` Fp muls; an Fp12 SQUARING
     (the cyclotomic squaring used in the Miller loop) is cheaper (~12 Fp2 muls).
  3. **G1 ⊂ E(Fp) / G2 ⊂ E'(Fp2)** — point add/double in Jacobian/projective coordinates (NO
     per-op inversion; the field ops are `fpMul`/`fpAdd`/`fpSub` and their Fp2 lifts). A G2 double is
     ~a dozen Fp2 muls; a G2 add ~a dozen more. Affine (final) needs ONE `fpInv` — a witnessed
     inverse gate `x·x⁻¹ ≡ 1 (mod p)` (`fpMulCore` with output pinned to the encoded `1`), the SAME
     quotient-witness shape (a NAMED addition, not built here).
  4. **The Miller loop** — ~64 iterations (the bit length of the BLS12-381 loop parameter
     `x = -0xd201000000010000`) of: a G2 doubling + a line evaluation (a sparse Fp12 element) +
     an Fp12 squaring + a sparse Fp12 multiply-in; plus additions at the set bits. Each iteration is
     a handful of Fp12 muls/squares ≈ hundreds of Fp muls. Total ≈ `64 · O(10²)` Fp muls.
  5. **Final exponentiation** — raise to `(p¹² − 1)/r`: the easy part `(p⁶−1)(p²+1)` (Frobenius +
     one Fp12 inversion) then the hard part (a fixed addition chain in `x` of cyclotomic squarings +
     multiplies) ≈ another `O(10³)` Fp12 muls.
  6. **Aggregate-verify wiring (the `BLS_OK` rewrite)** — two pairings `e(sig, g2)` and
     `e(H(m), agg_pk)` and an Fp12 equality gate (`bindRootWords`-style, coordinate-for-coordinate),
     with `agg_pk = Σ pk_i` (G1 adds over the participating sync-committee bits) and `H(m)` the
     hash-to-G2. This is the constraint set `BLS_OK` would be DERIVED from, dropping the trusted bit.

**Gate-count reality (order of magnitude).** One `fpMul` is `807` gates here; an Fp12 mul `≈ 54`
`fpMul`s `≈ 4·10⁴` gates; the Miller loop `≈ 64` iterations `× O(10)` Fp12 ops `≈ 10⁷` gates; the final
exponentiation a similar `~10⁶`–`10⁷`. A single sync-committee aggregate pairing check is therefore on
the order of **millions of AIR gates** — the accepted, published zk-STARK/SNARK cost of a BLS pairing
(the reason `BLS_OK` is a trusted carrier today, and the reason the point of THIS slice is
EXPRESSIBILITY: the tower is generated + KAT'd + forced, so each step above is composition, not new
constraint algebra). None of §7 is claimed built; this file is the `Fp`/`Fp2` floor it stands on.
-/

end Dregg2.Circuit.Emit.Bls12381Tower
