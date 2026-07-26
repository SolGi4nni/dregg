/-
# Dregg2.Circuit.Emit.PastaCurveComplete — the UNIFIED RCB complete-add gadget for Pallas/Vesta
(the exception-free curve-op the GLV scalar mul stands on; task K4 of
`docs/MINA-KIMCHI-VERIFIER-PLAN.md`).

## What this file IS (and why it exists on top of K2)

K2 (`PastaCurve`, commit `6a3ff11ab`) built the Jacobian `add-2007-bl` / `dbl-2009-l` gadgets and
FORCED them mod the real Pasta primes. But `add-2007-bl` is INCOMPLETE (K2 residual #3): it is
correct only for `P ≠ ±Q` with neither point at infinity, so a scalar-mul ladder built on it needs
exceptional-case handling at every step. This file replaces the point-op with the **RCB
(Renes–Costello–Batina 2015) complete addition** — Algorithm 7, the `j`-invariant-0
(`a = 0`, `y² = x³ + b`) case — which is **strongly unified** (correct even when `P = Q`, so it
doubles too) and **complete** on prime-order curves. Pasta has cofactor 1 (prime order), so RCB
completeness applies and `[k]P` via GLV/Shamir becomes ONE curve-op gadget with NO case splits
(kimi's K4 decision, `docs/MINA-KIMCHI-VERIFIER-PLAN.md` "K4 design").

Projective coordinates `(X : Y : Z)` (NOT Jacobian): the finite point `(x, y)` is `(x : y : 1)`,
the identity `O` is `(0 : 1 : 0)`, the curve is the homogenization `Y²·Z = X³ + b·Z³`.

## The RCB Algorithm 7 gate shape (a = 0, b3 = 3b = 15 for Pasta)

SSA-linearized Algorithm 7 (the exact 33 field ops of RCB'15 Alg. 7, register-renamed to
single-assignment so each write is a fresh 9-limb column group over K1's `fpValue`):
**12 field muls + 2 constant-muls (by `b3`) + 14 adds + 5 subs = 33 core gates.** The generic
builder `swCompleteAddGadget` is parameterized by the four field-core constructors and instantiated
twice — `pallasCompleteAdd` (K1's `fp*Core`, modulus `p`) and `vestaCompleteAdd` (`fq*Core`,
modulus `q`). No gate is hand-authored per curve (House Law #1).

## What is AUTHORED + built vs INHERITED (honest completeness scope)

AUTHORED + built: the generic Alg. 7 builder + the const-mul-by-`b3` core (`fpSMulCore`/`fqSMulCore`
with forcing) + the two curve gadgets; a `Nat`/ℤ RCB reference (`rcbTraceM`/`rcbTraceZ`); the
projective helpers (`projOnCurveM`/`projEqM`/`isInfM`/`jacToProjM`/`projJacEqM`); the FORCING lemmas
`pallasCompleteAdd_forces`/`vestaCompleteAdd_forces` (the 33 gate satisfactions force
`(X3,Y3,Z3) ≡ rcbTraceZ(P,Q)` mod the real prime, direct `CZm`-chain proofs in the K2/BLS pattern);
both-polarity gate KATs (honest RCB trace ACCEPTED, bumped limb REJECTED); and — the completeness
evidence — in-kernel KATs that the RCB REFERENCE reproduces the EXCEPTIONAL cases `P=Q` (doubling),
`P+O`, `O+P`, `P+(−P)=O`, `O+O` and, cross-tied to K2's already-verified Jacobian points, `[2]G`
and `[3]G` (`projJacEqM` against K2's `Gp2`/`Gp3`/`Gv2`/`Gv3`), with a negative control.

INHERITED (named, NOT re-proven in-kernel): the RCB **completeness theorem** itself — that Alg. 7
computes the group law for ALL inputs on a prime-order `a=0` curve — is Renes–Costello–Batina 2015
(Theorem 1 / §3), cited, not machine-checked here. What IS machine-checked is (a) the gadget forces
the RCB formula, and (b) the formula agrees with the real group law on the representative
exceptional inputs `add-2007-bl` canNOT handle. The shared K1 residuals (`z < p` canonical compare;
`ℤ ↔ p_felt` field width) and inherited modulus primality stand unchanged (§6).

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard` KATs reduce in the kernel. NEW file; imports read-only (`PastaCurve`,
transitively `PastaField`); standalone (NOT imported by the truncated `Dregg2` root; built directly
as `Dregg2.Circuit.Emit.PastaCurveComplete`).
-/
import Dregg2.Circuit.Emit.PastaCurve

namespace Dregg2.Circuit.Emit.PastaCurveComplete

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.PastaField
open Dregg2.Circuit.Emit.PastaField.Ref (limbOf)
open Dregg2.Circuit.Emit.PastaCurve (curveB Gp Gv Gp2 Gp3 Gv2 Gv3 CZm CZp CZq)

set_option autoImplicit false

/-! ## §0 — The `b3 = 3b` constant (shared by Pallas and Vesta: `b = 5 ⇒ b3 = 15`). -/

/-- The RCB `b3 = 3·b` constant; `< p, q` so it needs no reduction as a coefficient. -/
def curveB3 : Nat := 3 * curveB

#guard curveB3 == 15

/-! ## §1 — The constant-multiply core (`m·x ≡ z`), per field, with forcing.

RCB Alg. 7 multiplies by the constant `b3` twice. A constant-mul is DEGREE 1 (`m·xVal − mod·qVal −
zVal`, no cross terms), cheaper than a full `fpMul`; the quotient witness is K1's discipline. Cribs
`PastaPoseidon.fpSMulHead` exactly (single source of the shape, re-expressed here for both moduli). -/

/-- **`fpSMulHead`** — `m·xVal − p·qVal − zVal`. Zero forces `m·x ≡ z (mod p)`. -/
def fpSMulHead (m : ℤ) (xB zB qB : Nat) : Head :=
  ((fpValue xB).scale m).append (((fpValue qB).scale (-p)).append ((fpValue zB).scale (-1)))
/-- **`fqSMulHead`** — the const-mul gate, modulus `q`. -/
def fqSMulHead (m : ℤ) (xB zB qB : Nat) : Head :=
  ((fpValue xB).scale m).append (((fpValue qB).scale (-q)).append ((fpValue zB).scale (-1)))

/-- `fpSMul` value gate. -/
def fpSMulCore (m : ℤ) (xB zB qB : Nat) : VmConstraint2 := cgH (fpSMulHead m xB zB qB)
/-- `fqSMul` value gate. -/
def fqSMulCore (m : ℤ) (xB zB qB : Nat) : VmConstraint2 := cgH (fqSMulHead m xB zB qB)

/-- **`fpSMulCore` forces `m·x ≡ z (mod p)`**. -/
theorem fpSMulCore_forces (a : Assignment) (m : ℤ) (xB zB qB : Nat)
    (hg : evalH (fpSMulHead m xB zB qB) a = 0) :
    (p : ℤ) ∣ m * fpVal a xB - fpVal a zB := by
  simp only [fpSMulHead, evalH_append, evalH_scale, fpVal_eq] at hg
  exact ⟨fpVal a qB, by linarith⟩

/-- **`fqSMulCore` forces `m·x ≡ z (mod q)`**. -/
theorem fqSMulCore_forces (a : Assignment) (m : ℤ) (xB zB qB : Nat)
    (hg : evalH (fqSMulHead m xB zB qB) a = 0) :
    (q : ℤ) ∣ m * fpVal a xB - fpVal a zB := by
  simp only [fqSMulHead, evalH_append, evalH_scale, fpVal_eq] at hg
  exact ⟨fpVal a qB, by linarith⟩

/-! ## §2 — The RCB reference (Algorithm 7), `Nat` (per-op reduced) and ℤ (the forcing target).

The 33 SSA intermediates are named exactly as the gadget's column groups so the forcing chain and
the KAT witness read the same shape. -/

/-- The RCB Alg. 7 intermediate trace over `R` (SSA order = gadget allocation order). -/
structure RcbT (R : Type) where
  t0a : R
  t1a : R
  t2a : R
  t3a : R
  t4a : R
  t3b : R
  t4b : R
  t3c : R
  t4c : R
  X3a : R
  t4d : R
  X3b : R
  t4e : R
  X3c : R
  Y3a : R
  X3d : R
  Y3b : R
  Y3c : R
  X3e : R
  t0b : R
  t2b : R
  Z3a : R
  t1b : R
  Y3d : R
  X3f : R
  t2c : R
  X3g : R
  Y3e : R
  t1c : R
  Y3f : R
  t0c : R
  Z3b : R
  Z3c : R

/-- The output projective point `(X3, Y3, Z3)` of a trace (`X3g, Y3f, Z3c`). -/
def RcbT.out {R : Type} (t : RcbT R) : R × R × R := (t.X3g, t.Y3f, t.Z3c)

/-- **`Nat` RCB add**, per-op reduced mod `m`, constant `b3` (mirrors the generated gates). -/
def rcbTraceM (m b3 : Nat) (X1 Y1 Z1 X2 Y2 Z2 : Nat) : RcbT Nat :=
  let M : Nat → Nat → Nat := fun x y => (x * y) % m
  let Ad : Nat → Nat → Nat := fun x y => (x + y) % m
  let Sb : Nat → Nat → Nat := fun x y => (x + m - y) % m
  let Sm : Nat → Nat := fun x => (b3 * x) % m
  let t0a := M X1 X2; let t1a := M Y1 Y2; let t2a := M Z1 Z2
  let t3a := Ad X1 Y1; let t4a := Ad X2 Y2; let t3b := M t3a t4a
  let t4b := Ad t0a t1a; let t3c := Sb t3b t4b; let t4c := Ad Y1 Z1
  let X3a := Ad Y2 Z2; let t4d := M t4c X3a; let X3b := Ad t1a t2a
  let t4e := Sb t4d X3b; let X3c := Ad X1 Z1; let Y3a := Ad X2 Z2
  let X3d := M X3c Y3a; let Y3b := Ad t0a t2a; let Y3c := Sb X3d Y3b
  let X3e := Ad t0a t0a; let t0b := Ad X3e t0a; let t2b := Sm t2a
  let Z3a := Ad t1a t2b; let t1b := Sb t1a t2b; let Y3d := Sm Y3c
  let X3f := M t4e Y3d; let t2c := M t3c t1b; let X3g := Sb t2c X3f
  let Y3e := M Y3d t0b; let t1c := M t1b Z3a; let Y3f := Ad t1c Y3e
  let t0c := M t0b t3c; let Z3b := M Z3a t4e; let Z3c := Ad Z3b t0c
  { t0a, t1a, t2a, t3a, t4a, t3b, t4b, t3c, t4c, X3a, t4d, X3b, t4e, X3c, Y3a, X3d, Y3b, Y3c,
    X3e, t0b, t2b, Z3a, t1b, Y3d, X3f, t2c, X3g, Y3e, t1c, Y3f, t0c, Z3b, Z3c }

/-- **ℤ RCB add** (the formula the forcing lemmas conclude against), constant `b3 : ℤ`. -/
def rcbTraceZ (b3 : ℤ) (X1 Y1 Z1 X2 Y2 Z2 : ℤ) : RcbT ℤ :=
  let t0a := X1 * X2; let t1a := Y1 * Y2; let t2a := Z1 * Z2
  let t3a := X1 + Y1; let t4a := X2 + Y2; let t3b := t3a * t4a
  let t4b := t0a + t1a; let t3c := t3b - t4b; let t4c := Y1 + Z1
  let X3a := Y2 + Z2; let t4d := t4c * X3a; let X3b := t1a + t2a
  let t4e := t4d - X3b; let X3c := X1 + Z1; let Y3a := X2 + Z2
  let X3d := X3c * Y3a; let Y3b := t0a + t2a; let Y3c := X3d - Y3b
  let X3e := t0a + t0a; let t0b := X3e + t0a; let t2b := b3 * t2a
  let Z3a := t1a + t2b; let t1b := t1a - t2b; let Y3d := b3 * Y3c
  let X3f := t4e * Y3d; let t2c := t3c * t1b; let X3g := t2c - X3f
  let Y3e := Y3d * t0b; let t1c := t1b * Z3a; let Y3f := t1c + Y3e
  let t0c := t0b * t3c; let Z3b := Z3a * t4e; let Z3c := Z3b + t0c
  { t0a, t1a, t2a, t3a, t4a, t3b, t4b, t3c, t4c, X3a, t4d, X3b, t4e, X3c, Y3a, X3d, Y3b, Y3c,
    X3e, t0b, t2b, Z3a, t1b, Y3d, X3f, t2c, X3g, Y3e, t1c, Y3f, t0c, Z3b, Z3c }

/-- Reference projective RCB add (`.out` of the `Nat` trace), `b3` the constant. -/
def rcbAddM (m b3 : Nat) (P Q : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (rcbTraceM m b3 P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2).out

/-! ### Projective geometry helpers (all cross-multiplied — NO modular inversion in-kernel). -/

/-- The identity `O = (0 : 1 : 0)`. -/
def Oproj : Nat × Nat × Nat := (0, 1, 0)

/-- Projective on-curve `Y²·Z ≡ X³ + b·Z³ (mod m)` (a wrong formula lands off-curve). -/
def projOnCurveM (m b : Nat) (P : Nat × Nat × Nat) : Bool :=
  let X := P.1; let Y := P.2.1; let Z := P.2.2
  (Y * Y % m * Z) % m == (X * X % m * X + b * (Z * Z % m * Z % m)) % m

/-- Projective equality `X_P·Z_Q ≡ X_Q·Z_P ∧ Y_P·Z_Q ≡ Y_Q·Z_P (mod m)`. -/
def projEqM (m : Nat) (P Q : Nat × Nat × Nat) : Bool :=
  (P.1 * Q.2.2) % m == (Q.1 * P.2.2) % m && (P.2.1 * Q.2.2) % m == (Q.2.1 * P.2.2) % m

/-- On an on-curve point, `Z ≡ 0` iff the point is `O` (the only `Z = 0` point). -/
def isInfM (m : Nat) (P : Nat × Nat × Nat) : Bool := P.2.2 % m == 0 && P.1 % m == 0

/-- Jacobian `(Xj : Yj : Zj)` → projective `(Xj·Zj : Yj : Zj³)` (affine-preserving; no inverse:
`x = Xj/Zj² = (Xj·Zj)/Zj³`, `y = Yj/Zj³`). Lets the KAT feed K2's Jacobian points to RCB. -/
def jacToProjM (m : Nat) (J : Nat × Nat × Nat) : Nat × Nat × Nat :=
  ((J.1 * J.2.2) % m, J.2.1 % m, (J.2.2 * J.2.2 % m * J.2.2) % m)

/-- Mixed projective-vs-Jacobian equality (cross-multiplied): projective `(Xp:Yp:Zp)` equals
Jacobian `(Xj:Yj:Zj)` iff `Xp·Zj² ≡ Xj·Zp ∧ Yp·Zj³ ≡ Yj·Zp (mod m)`. -/
def projJacEqM (m : Nat) (Pp Pj : Nat × Nat × Nat) : Bool :=
  let Zj2 := Pj.2.2 * Pj.2.2 % m
  (Pp.1 * Zj2) % m == (Pj.1 * Pp.2.2) % m
    && (Pp.2.1 * (Zj2 * Pj.2.2 % m)) % m == (Pj.2.1 * Pp.2.2) % m

/-! ### Completeness KATs — the RCB REFERENCE handles the exceptional cases (Pallas mod p).

These are exactly the inputs `add-2007-bl` (K2) canNOT: `P = Q`, `P + O`, `O + P`, `P + (−P)`,
`O + O`. `[2]G`/`[3]G` are cross-tied to K2's already-verified Jacobian `Gp2`/`Gp3`. -/

/-- `G` in projective coords. -/
def GpP : Nat × Nat × Nat := (Gp.1, Gp.2, 1)
def GvP : Nat × Nat × Nat := (Gv.1, Gv.2, 1)
/-- `−G` in projective coords. -/
def negGpP : Nat × Nat × Nat := (Gp.1, (pN - Gp.2) % pN, 1)
def negGvP : Nat × Nat × Nat := (Gv.1, (qN - Gv.2) % qN, 1)

-- The inputs are on the curve (projective form).
#guard projOnCurveM pN curveB GpP == true
#guard projOnCurveM qN curveB GvP == true
-- DOUBLING via the SAME add (strong unification): `G + G` equals K2's Jacobian `[2]G`.
#guard projJacEqM pN (rcbAddM pN curveB3 GpP GpP) Gp2 == true
#guard projJacEqM qN (rcbAddM qN curveB3 GvP GvP) Gv2 == true
-- GENERIC add: `[2]G + G` (2G fed via `jacToProjM`, inverse-free) equals K2's Jacobian `[3]G`.
#guard projJacEqM pN (rcbAddM pN curveB3 (jacToProjM pN Gp2) GpP) Gp3 == true
#guard projJacEqM qN (rcbAddM qN curveB3 (jacToProjM qN Gv2) GvP) Gv3 == true
-- IDENTITY: `P + O = P`, `O + P = P` (RCB is complete at infinity; add-2007-bl is not).
#guard projEqM pN (rcbAddM pN curveB3 GpP Oproj) GpP == true
#guard projEqM pN (rcbAddM pN curveB3 Oproj GpP) GpP == true
#guard projEqM qN (rcbAddM qN curveB3 GvP Oproj) GvP == true
#guard projEqM qN (rcbAddM qN curveB3 Oproj GvP) GvP == true
-- INVERSE: `P + (−P) = O` (`Z ≡ 0`); `O + O = O`.
#guard isInfM pN (rcbAddM pN curveB3 GpP negGpP) == true
#guard isInfM qN (rcbAddM qN curveB3 GvP negGvP) == true
#guard isInfM pN (rcbAddM pN curveB3 Oproj Oproj) == true
-- The RCB double/add outputs stay ON the curve (non-vacuity of the formula).
#guard projOnCurveM pN curveB (rcbAddM pN curveB3 GpP GpP) == true
#guard projOnCurveM pN curveB (rcbAddM pN curveB3 (jacToProjM pN Gp2) GpP) == true
-- NEGATIVE control: `[2]G` is NOT `[3]G` (a real, discriminating check).
#guard projJacEqM pN (rcbAddM pN curveB3 GpP GpP) Gp3 == false

/-! ## §3 — The GENERATED unified complete-add gadget.

One generic Alg. 7 builder, parameterized by the four field-core constructors (`mulC addC subC :
Nat→Nat→Nat→Nat→VmConstraint2` and `smulC : ℤ→Nat→Nat→Nat→VmConstraint2`), instantiated with K1's
`fp*Core` (Pallas) and `fq*Core` (Vesta) plus this file's `f{p,q}SMulCore`. Layout: inputs
`X1..Z2` (9-limb groups given by caller); 33 intermediates at `fresh + 9·idx`; 14 quotient groups at
`fresh + 297 + 9·qidx`; 19 carry/borrow bits at `fresh + 423 + bidx`; next fresh `fresh + 442`. -/

/-- **Generic RCB complete addition** (Algorithm 7, `a = 0`): 12 mul + 2 const-mul + 14 add + 5 sub
= **33 core gates**. Strongly unified (feed `P P` to double) and complete (handles `O`, `±Q`). -/
def swCompleteAddGadget (mulC addC subC : Nat → Nat → Nat → Nat → VmConstraint2)
    (smulC : ℤ → Nat → Nat → Nat → VmConstraint2) (b3 : ℤ)
    (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat) : List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  let t0a := fresh; let t1a := fresh+9; let t2a := fresh+18; let t3a := fresh+27
  let t4a := fresh+36; let t3b := fresh+45; let t4b := fresh+54; let t3c := fresh+63
  let t4c := fresh+72; let X3a := fresh+81; let t4d := fresh+90; let X3b := fresh+99
  let t4e := fresh+108; let X3c := fresh+117; let Y3a := fresh+126; let X3d := fresh+135
  let Y3b := fresh+144; let Y3c := fresh+153; let X3e := fresh+162; let t0b := fresh+171
  let t2b := fresh+180; let Z3a := fresh+189; let t1b := fresh+198; let Y3d := fresh+207
  let X3f := fresh+216; let t2c := fresh+225; let X3g := fresh+234; let Y3e := fresh+243
  let t1c := fresh+252; let Y3f := fresh+261; let t0c := fresh+270; let Z3b := fresh+279
  let Z3c := fresh+288
  let q0 := fresh+297   -- 14 quotient groups
  let b0 := fresh+423   -- 19 carry/borrow bits
  ( [ mulC X1 X2 t0a q0                       -- t0a = X1·X2
    , mulC Y1 Y2 t1a (q0+9)                    -- t1a = Y1·Y2
    , mulC Z1 Z2 t2a (q0+18)                   -- t2a = Z1·Z2
    , addC X1 Y1 t3a b0                        -- t3a = X1+Y1
    , addC X2 Y2 t4a (b0+1)                    -- t4a = X2+Y2
    , mulC t3a t4a t3b (q0+27)                 -- t3b = t3a·t4a
    , addC t0a t1a t4b (b0+2)                  -- t4b = t0a+t1a
    , subC t3b t4b t3c (b0+3)                  -- t3c = t3b−t4b
    , addC Y1 Z1 t4c (b0+4)                    -- t4c = Y1+Z1
    , addC Y2 Z2 X3a (b0+5)                    -- X3a = Y2+Z2
    , mulC t4c X3a t4d (q0+36)                 -- t4d = t4c·X3a
    , addC t1a t2a X3b (b0+6)                  -- X3b = t1a+t2a
    , subC t4d X3b t4e (b0+7)                  -- t4e = t4d−X3b
    , addC X1 Z1 X3c (b0+8)                    -- X3c = X1+Z1
    , addC X2 Z2 Y3a (b0+9)                    -- Y3a = X2+Z2
    , mulC X3c Y3a X3d (q0+45)                 -- X3d = X3c·Y3a
    , addC t0a t2a Y3b (b0+10)                 -- Y3b = t0a+t2a
    , subC X3d Y3b Y3c (b0+11)                 -- Y3c = X3d−Y3b
    , addC t0a t0a X3e (b0+12)                 -- X3e = t0a+t0a
    , addC X3e t0a t0b (b0+13)                 -- t0b = X3e+t0a
    , smulC b3 t2a t2b (q0+54)                 -- t2b = b3·t2a
    , addC t1a t2b Z3a (b0+14)                 -- Z3a = t1a+t2b
    , subC t1a t2b t1b (b0+15)                 -- t1b = t1a−t2b
    , smulC b3 Y3c Y3d (q0+63)                 -- Y3d = b3·Y3c
    , mulC t4e Y3d X3f (q0+72)                 -- X3f = t4e·Y3d
    , mulC t3c t1b t2c (q0+81)                 -- t2c = t3c·t1b
    , subC t2c X3f X3g (b0+16)                 -- X3g = t2c−X3f  (= X3)
    , mulC Y3d t0b Y3e (q0+90)                 -- Y3e = Y3d·t0b
    , mulC t1b Z3a t1c (q0+99)                 -- t1c = t1b·Z3a
    , addC t1c Y3e Y3f (b0+17)                 -- Y3f = t1c+Y3e  (= Y3)
    , mulC t0b t3c t0c (q0+108)                -- t0c = t0b·t3c
    , mulC Z3a t4e Z3b (q0+117)                -- Z3b = Z3a·t4e
    , addC Z3b t0c Z3c (b0+18)                 -- Z3c = Z3b+t0c  (= Z3)
    ], (X3g, Y3f, Z3c), fresh + 442 )

/-- **`pallasCompleteAdd`** — Pallas RCB add over Fp (33 core gates, K1's `fp*Core`, `b3 = 15`). -/
def pallasCompleteAdd := swCompleteAddGadget fpMulCore fpAddCore fpSubCore fpSMulCore (curveB3 : ℤ)
/-- **`vestaCompleteAdd`** — Vesta RCB add over Fq (33 core gates, `fq*Core`, `b3 = 15`). -/
def vestaCompleteAdd := swCompleteAddGadget fqMulCore fqAddCore fqSubCore fqSMulCore (curveB3 : ℤ)

/-! ## §4 — Forcing: the gadget's 33 gates force the ℤ RCB formula (mod the real prime).

`CZm`/`CZp`/`CZq` and the algebra `CZm.refl/symm/trans/add/sub/mul` are REUSED from `PastaCurve`
(single source). The field-op bridges (`mulCZp` etc.) are `private` there, so they are re-derived
here from K1's public `*_forces` — the same 2-liners. -/

/-- Fp bridge: `fpMulCore` sat ⟹ `z ≡ x·y (mod p)`. -/
private theorem mulCZp {a : Assignment} {x y z qb : Nat}
    (h : evalH (fpMulHead x y z qb) a = 0) : CZp (fpVal a z) (fpVal a x * fpVal a y) :=
  CZm.symm (fpMulCore_forces a x y z qb h)
private theorem addCZp {a : Assignment} {x y z c : Nat}
    (h : evalH (fpAddHead x y z c) a = 0) : CZp (fpVal a z) (fpVal a x + fpVal a y) :=
  CZm.symm (fpAddCore_forces a x y z c h)
private theorem subCZp {a : Assignment} {x y z c : Nat}
    (h : evalH (fpSubHead x y z c) a = 0) : CZp (fpVal a z) (fpVal a x - fpVal a y) :=
  CZm.symm (fpSubCore_forces a x y z c h)
private theorem smulCZp {a : Assignment} {x z qb : Nat} {m : ℤ}
    (h : evalH (fpSMulHead m x z qb) a = 0) : CZp (fpVal a z) (m * fpVal a x) :=
  CZm.symm (fpSMulCore_forces a m x z qb h)
private theorem mulCZq {a : Assignment} {x y z qb : Nat}
    (h : evalH (fqMulHead x y z qb) a = 0) : CZq (fpVal a z) (fpVal a x * fpVal a y) :=
  CZm.symm (fqMulCore_forces a x y z qb h)
private theorem addCZq {a : Assignment} {x y z c : Nat}
    (h : evalH (fqAddHead x y z c) a = 0) : CZq (fpVal a z) (fpVal a x + fpVal a y) :=
  CZm.symm (fqAddCore_forces a x y z c h)
private theorem subCZq {a : Assignment} {x y z c : Nat}
    (h : evalH (fqSubHead x y z c) a = 0) : CZq (fpVal a z) (fpVal a x - fpVal a y) :=
  CZm.symm (fqSubCore_forces a x y z c h)
private theorem smulCZq {a : Assignment} {x z qb : Nat} {m : ℤ}
    (h : evalH (fqSMulHead m x z qb) a = 0) : CZq (fpVal a z) (m * fpVal a x) :=
  CZm.symm (fqSMulCore_forces a m x z qb h)

/-- **`pallasCompleteAdd_forces`** — the 33 raw gate satisfactions force
`(X3,Y3,Z3) ≡ rcbTraceZ b3 (P,Q)` mod `p` (`b3 = 15`), via the `CZm` chain (the K2/BLS pattern). -/
theorem pallasCompleteAdd_forces (a : Assignment)
    {X1c Y1c Z1c X2c Y2c Z2c
     t0ac t1ac t2ac t3ac t4ac t3bc t4bc t3cc t4cc X3ac t4dc X3bc t4ec X3cc Y3ac X3dc Y3bc Y3cc
     X3ec t0bc t2bc Z3ac t1bc Y3dc X3fc t2cc X3gc Y3ec t1cc Y3fc t0cc Z3bc Z3cc
     q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
     b0 b1 b2 b3' b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 : Nat}
    (ht0a : evalH (fpMulHead X1c X2c t0ac q0) a = 0)
    (ht1a : evalH (fpMulHead Y1c Y2c t1ac q1) a = 0)
    (ht2a : evalH (fpMulHead Z1c Z2c t2ac q2) a = 0)
    (ht3a : evalH (fpAddHead X1c Y1c t3ac b0) a = 0)
    (ht4a : evalH (fpAddHead X2c Y2c t4ac b1) a = 0)
    (ht3b : evalH (fpMulHead t3ac t4ac t3bc q3) a = 0)
    (ht4b : evalH (fpAddHead t0ac t1ac t4bc b2) a = 0)
    (ht3c : evalH (fpSubHead t3bc t4bc t3cc b3') a = 0)
    (ht4c : evalH (fpAddHead Y1c Z1c t4cc b4) a = 0)
    (hX3a : evalH (fpAddHead Y2c Z2c X3ac b5) a = 0)
    (ht4d : evalH (fpMulHead t4cc X3ac t4dc q4) a = 0)
    (hX3b : evalH (fpAddHead t1ac t2ac X3bc b6) a = 0)
    (ht4e : evalH (fpSubHead t4dc X3bc t4ec b7) a = 0)
    (hX3c : evalH (fpAddHead X1c Z1c X3cc b8) a = 0)
    (hY3a : evalH (fpAddHead X2c Z2c Y3ac b9) a = 0)
    (hX3d : evalH (fpMulHead X3cc Y3ac X3dc q5) a = 0)
    (hY3b : evalH (fpAddHead t0ac t2ac Y3bc b10) a = 0)
    (hY3c : evalH (fpSubHead X3dc Y3bc Y3cc b11) a = 0)
    (hX3e : evalH (fpAddHead t0ac t0ac X3ec b12) a = 0)
    (ht0b : evalH (fpAddHead X3ec t0ac t0bc b13) a = 0)
    (ht2b : evalH (fpSMulHead (curveB3 : ℤ) t2ac t2bc q6) a = 0)
    (hZ3a : evalH (fpAddHead t1ac t2bc Z3ac b14) a = 0)
    (ht1b : evalH (fpSubHead t1ac t2bc t1bc b15) a = 0)
    (hY3d : evalH (fpSMulHead (curveB3 : ℤ) Y3cc Y3dc q7) a = 0)
    (hX3f : evalH (fpMulHead t4ec Y3dc X3fc q8) a = 0)
    (ht2c : evalH (fpMulHead t3cc t1bc t2cc q9) a = 0)
    (hX3g : evalH (fpSubHead t2cc X3fc X3gc b16) a = 0)
    (hY3e : evalH (fpMulHead Y3dc t0bc Y3ec q10) a = 0)
    (ht1c : evalH (fpMulHead t1bc Z3ac t1cc q11) a = 0)
    (hY3f : evalH (fpAddHead t1cc Y3ec Y3fc b17) a = 0)
    (ht0c : evalH (fpMulHead t0bc t3cc t0cc q12) a = 0)
    (hZ3b : evalH (fpMulHead Z3ac t4ec Z3bc q13) a = 0)
    (hZ3c : evalH (fpAddHead Z3bc t0cc Z3cc b18) a = 0) :
    CZp (fpVal a X3gc) (rcbTraceZ (curveB3 : ℤ) (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                          (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).X3g
    ∧ CZp (fpVal a Y3fc) (rcbTraceZ (curveB3 : ℤ) (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                          (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).Y3f
    ∧ CZp (fpVal a Z3cc) (rcbTraceZ (curveB3 : ℤ) (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                          (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).Z3c := by
  let T := rcbTraceZ (curveB3 : ℤ) (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
             (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)
  have f0a : CZp (fpVal a t0ac) T.t0a := mulCZp ht0a
  have f1a : CZp (fpVal a t1ac) T.t1a := mulCZp ht1a
  have f2a : CZp (fpVal a t2ac) T.t2a := mulCZp ht2a
  have f3a : CZp (fpVal a t3ac) T.t3a := addCZp ht3a
  have f4a : CZp (fpVal a t4ac) T.t4a := addCZp ht4a
  have f3b : CZp (fpVal a t3bc) T.t3b := CZm.trans (mulCZp ht3b) (CZm.mul f3a f4a)
  have f4b : CZp (fpVal a t4bc) T.t4b := CZm.trans (addCZp ht4b) (CZm.add f0a f1a)
  have f3c : CZp (fpVal a t3cc) T.t3c := CZm.trans (subCZp ht3c) (CZm.sub f3b f4b)
  have f4c : CZp (fpVal a t4cc) T.t4c := addCZp ht4c
  have fX3a : CZp (fpVal a X3ac) T.X3a := addCZp hX3a
  have f4d : CZp (fpVal a t4dc) T.t4d := CZm.trans (mulCZp ht4d) (CZm.mul f4c fX3a)
  have fX3b : CZp (fpVal a X3bc) T.X3b := CZm.trans (addCZp hX3b) (CZm.add f1a f2a)
  have f4e : CZp (fpVal a t4ec) T.t4e := CZm.trans (subCZp ht4e) (CZm.sub f4d fX3b)
  have fX3c : CZp (fpVal a X3cc) T.X3c := addCZp hX3c
  have fY3a : CZp (fpVal a Y3ac) T.Y3a := addCZp hY3a
  have fX3d : CZp (fpVal a X3dc) T.X3d := CZm.trans (mulCZp hX3d) (CZm.mul fX3c fY3a)
  have fY3b : CZp (fpVal a Y3bc) T.Y3b := CZm.trans (addCZp hY3b) (CZm.add f0a f2a)
  have fY3c : CZp (fpVal a Y3cc) T.Y3c := CZm.trans (subCZp hY3c) (CZm.sub fX3d fY3b)
  have fX3e : CZp (fpVal a X3ec) T.X3e := CZm.trans (addCZp hX3e) (CZm.add f0a f0a)
  have f0b : CZp (fpVal a t0bc) T.t0b := CZm.trans (addCZp ht0b) (CZm.add fX3e f0a)
  have f2b : CZp (fpVal a t2bc) T.t2b := CZm.trans (smulCZp ht2b) (CZm.mul (CZm.refl _) f2a)
  have fZ3a : CZp (fpVal a Z3ac) T.Z3a := CZm.trans (addCZp hZ3a) (CZm.add f1a f2b)
  have f1b : CZp (fpVal a t1bc) T.t1b := CZm.trans (subCZp ht1b) (CZm.sub f1a f2b)
  have fY3d : CZp (fpVal a Y3dc) T.Y3d := CZm.trans (smulCZp hY3d) (CZm.mul (CZm.refl _) fY3c)
  have fX3f : CZp (fpVal a X3fc) T.X3f := CZm.trans (mulCZp hX3f) (CZm.mul f4e fY3d)
  have f2c : CZp (fpVal a t2cc) T.t2c := CZm.trans (mulCZp ht2c) (CZm.mul f3c f1b)
  have fX3g : CZp (fpVal a X3gc) T.X3g := CZm.trans (subCZp hX3g) (CZm.sub f2c fX3f)
  have fY3e : CZp (fpVal a Y3ec) T.Y3e := CZm.trans (mulCZp hY3e) (CZm.mul fY3d f0b)
  have f1c : CZp (fpVal a t1cc) T.t1c := CZm.trans (mulCZp ht1c) (CZm.mul f1b fZ3a)
  have fY3f : CZp (fpVal a Y3fc) T.Y3f := CZm.trans (addCZp hY3f) (CZm.add f1c fY3e)
  have f0c : CZp (fpVal a t0cc) T.t0c := CZm.trans (mulCZp ht0c) (CZm.mul f0b f3c)
  have fZ3b : CZp (fpVal a Z3bc) T.Z3b := CZm.trans (mulCZp hZ3b) (CZm.mul fZ3a f4e)
  have fZ3c : CZp (fpVal a Z3cc) T.Z3c := CZm.trans (addCZp hZ3c) (CZm.add fZ3b f0c)
  exact ⟨fX3g, fY3f, fZ3c⟩

/-- **`vestaCompleteAdd_forces`** — the Vesta RCB gadget forces the ℤ RCB formula mod `q`. -/
theorem vestaCompleteAdd_forces (a : Assignment)
    {X1c Y1c Z1c X2c Y2c Z2c
     t0ac t1ac t2ac t3ac t4ac t3bc t4bc t3cc t4cc X3ac t4dc X3bc t4ec X3cc Y3ac X3dc Y3bc Y3cc
     X3ec t0bc t2bc Z3ac t1bc Y3dc X3fc t2cc X3gc Y3ec t1cc Y3fc t0cc Z3bc Z3cc
     q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
     b0 b1 b2 b3' b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 : Nat}
    (ht0a : evalH (fqMulHead X1c X2c t0ac q0) a = 0)
    (ht1a : evalH (fqMulHead Y1c Y2c t1ac q1) a = 0)
    (ht2a : evalH (fqMulHead Z1c Z2c t2ac q2) a = 0)
    (ht3a : evalH (fqAddHead X1c Y1c t3ac b0) a = 0)
    (ht4a : evalH (fqAddHead X2c Y2c t4ac b1) a = 0)
    (ht3b : evalH (fqMulHead t3ac t4ac t3bc q3) a = 0)
    (ht4b : evalH (fqAddHead t0ac t1ac t4bc b2) a = 0)
    (ht3c : evalH (fqSubHead t3bc t4bc t3cc b3') a = 0)
    (ht4c : evalH (fqAddHead Y1c Z1c t4cc b4) a = 0)
    (hX3a : evalH (fqAddHead Y2c Z2c X3ac b5) a = 0)
    (ht4d : evalH (fqMulHead t4cc X3ac t4dc q4) a = 0)
    (hX3b : evalH (fqAddHead t1ac t2ac X3bc b6) a = 0)
    (ht4e : evalH (fqSubHead t4dc X3bc t4ec b7) a = 0)
    (hX3c : evalH (fqAddHead X1c Z1c X3cc b8) a = 0)
    (hY3a : evalH (fqAddHead X2c Z2c Y3ac b9) a = 0)
    (hX3d : evalH (fqMulHead X3cc Y3ac X3dc q5) a = 0)
    (hY3b : evalH (fqAddHead t0ac t2ac Y3bc b10) a = 0)
    (hY3c : evalH (fqSubHead X3dc Y3bc Y3cc b11) a = 0)
    (hX3e : evalH (fqAddHead t0ac t0ac X3ec b12) a = 0)
    (ht0b : evalH (fqAddHead X3ec t0ac t0bc b13) a = 0)
    (ht2b : evalH (fqSMulHead (curveB3 : ℤ) t2ac t2bc q6) a = 0)
    (hZ3a : evalH (fqAddHead t1ac t2bc Z3ac b14) a = 0)
    (ht1b : evalH (fqSubHead t1ac t2bc t1bc b15) a = 0)
    (hY3d : evalH (fqSMulHead (curveB3 : ℤ) Y3cc Y3dc q7) a = 0)
    (hX3f : evalH (fqMulHead t4ec Y3dc X3fc q8) a = 0)
    (ht2c : evalH (fqMulHead t3cc t1bc t2cc q9) a = 0)
    (hX3g : evalH (fqSubHead t2cc X3fc X3gc b16) a = 0)
    (hY3e : evalH (fqMulHead Y3dc t0bc Y3ec q10) a = 0)
    (ht1c : evalH (fqMulHead t1bc Z3ac t1cc q11) a = 0)
    (hY3f : evalH (fqAddHead t1cc Y3ec Y3fc b17) a = 0)
    (ht0c : evalH (fqMulHead t0bc t3cc t0cc q12) a = 0)
    (hZ3b : evalH (fqMulHead Z3ac t4ec Z3bc q13) a = 0)
    (hZ3c : evalH (fqAddHead Z3bc t0cc Z3cc b18) a = 0) :
    CZq (fpVal a X3gc) (rcbTraceZ (curveB3 : ℤ) (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                          (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).X3g
    ∧ CZq (fpVal a Y3fc) (rcbTraceZ (curveB3 : ℤ) (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                          (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).Y3f
    ∧ CZq (fpVal a Z3cc) (rcbTraceZ (curveB3 : ℤ) (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
                          (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)).Z3c := by
  let T := rcbTraceZ (curveB3 : ℤ) (fpVal a X1c) (fpVal a Y1c) (fpVal a Z1c)
             (fpVal a X2c) (fpVal a Y2c) (fpVal a Z2c)
  have f0a : CZq (fpVal a t0ac) T.t0a := mulCZq ht0a
  have f1a : CZq (fpVal a t1ac) T.t1a := mulCZq ht1a
  have f2a : CZq (fpVal a t2ac) T.t2a := mulCZq ht2a
  have f3a : CZq (fpVal a t3ac) T.t3a := addCZq ht3a
  have f4a : CZq (fpVal a t4ac) T.t4a := addCZq ht4a
  have f3b : CZq (fpVal a t3bc) T.t3b := CZm.trans (mulCZq ht3b) (CZm.mul f3a f4a)
  have f4b : CZq (fpVal a t4bc) T.t4b := CZm.trans (addCZq ht4b) (CZm.add f0a f1a)
  have f3c : CZq (fpVal a t3cc) T.t3c := CZm.trans (subCZq ht3c) (CZm.sub f3b f4b)
  have f4c : CZq (fpVal a t4cc) T.t4c := addCZq ht4c
  have fX3a : CZq (fpVal a X3ac) T.X3a := addCZq hX3a
  have f4d : CZq (fpVal a t4dc) T.t4d := CZm.trans (mulCZq ht4d) (CZm.mul f4c fX3a)
  have fX3b : CZq (fpVal a X3bc) T.X3b := CZm.trans (addCZq hX3b) (CZm.add f1a f2a)
  have f4e : CZq (fpVal a t4ec) T.t4e := CZm.trans (subCZq ht4e) (CZm.sub f4d fX3b)
  have fX3c : CZq (fpVal a X3cc) T.X3c := addCZq hX3c
  have fY3a : CZq (fpVal a Y3ac) T.Y3a := addCZq hY3a
  have fX3d : CZq (fpVal a X3dc) T.X3d := CZm.trans (mulCZq hX3d) (CZm.mul fX3c fY3a)
  have fY3b : CZq (fpVal a Y3bc) T.Y3b := CZm.trans (addCZq hY3b) (CZm.add f0a f2a)
  have fY3c : CZq (fpVal a Y3cc) T.Y3c := CZm.trans (subCZq hY3c) (CZm.sub fX3d fY3b)
  have fX3e : CZq (fpVal a X3ec) T.X3e := CZm.trans (addCZq hX3e) (CZm.add f0a f0a)
  have f0b : CZq (fpVal a t0bc) T.t0b := CZm.trans (addCZq ht0b) (CZm.add fX3e f0a)
  have f2b : CZq (fpVal a t2bc) T.t2b := CZm.trans (smulCZq ht2b) (CZm.mul (CZm.refl _) f2a)
  have fZ3a : CZq (fpVal a Z3ac) T.Z3a := CZm.trans (addCZq hZ3a) (CZm.add f1a f2b)
  have f1b : CZq (fpVal a t1bc) T.t1b := CZm.trans (subCZq ht1b) (CZm.sub f1a f2b)
  have fY3d : CZq (fpVal a Y3dc) T.Y3d := CZm.trans (smulCZq hY3d) (CZm.mul (CZm.refl _) fY3c)
  have fX3f : CZq (fpVal a X3fc) T.X3f := CZm.trans (mulCZq hX3f) (CZm.mul f4e fY3d)
  have f2c : CZq (fpVal a t2cc) T.t2c := CZm.trans (mulCZq ht2c) (CZm.mul f3c f1b)
  have fX3g : CZq (fpVal a X3gc) T.X3g := CZm.trans (subCZq hX3g) (CZm.sub f2c fX3f)
  have fY3e : CZq (fpVal a Y3ec) T.Y3e := CZm.trans (mulCZq hY3e) (CZm.mul fY3d f0b)
  have f1c : CZq (fpVal a t1cc) T.t1c := CZm.trans (mulCZq ht1c) (CZm.mul f1b fZ3a)
  have fY3f : CZq (fpVal a Y3fc) T.Y3f := CZm.trans (addCZq hY3f) (CZm.add f1c fY3e)
  have f0c : CZq (fpVal a t0cc) T.t0c := CZm.trans (mulCZq ht0c) (CZm.mul f0b f3c)
  have fZ3b : CZq (fpVal a Z3bc) T.Z3b := CZm.trans (mulCZq hZ3b) (CZm.mul fZ3a f4e)
  have fZ3c : CZq (fpVal a Z3cc) T.Z3c := CZm.trans (addCZq hZ3c) (CZm.add fZ3b f0c)
  exact ⟨fX3g, fY3f, fZ3c⟩

#assert_axioms fpSMulCore_forces
#assert_axioms fqSMulCore_forces
#assert_axioms pallasCompleteAdd_forces
#assert_axioms vestaCompleteAdd_forces

/-! ## §5 — KAT: the generated gadget ACCEPTS the honest RCB trace and REJECTS a bump.

Reuses K1's `acceptB`/`bumpAt`. The witness is derived from `rcbTraceM` (all 33 intermediates, 14
quotients, 19 carry/borrow bits) at the layout `swCompleteAddGadget … 0 9 18 27 36 45 54`. -/

/-- The RCB gadget witness (generic in modulus + `b3`). Layout: inputs `0..53`; intermediates
`54..350`; quotients `351..476`; bits `477..495`. -/
def rcbAsg (m b3 : Nat) (X1v Y1v Z1v X2v Y2v Z2v : Nat) : Assignment := fun col =>
  let t := rcbTraceM m b3 X1v Y1v Z1v X2v Y2v Z2v
  let vals : List Nat :=
    [t.t0a, t.t1a, t.t2a, t.t3a, t.t4a, t.t3b, t.t4b, t.t3c, t.t4c, t.X3a, t.t4d, t.X3b, t.t4e,
     t.X3c, t.Y3a, t.X3d, t.Y3b, t.Y3c, t.X3e, t.t0b, t.t2b, t.Z3a, t.t1b, t.Y3d, t.X3f, t.t2c,
     t.X3g, t.Y3e, t.t1c, t.Y3f, t.t0c, t.Z3b, t.Z3c]
  let qs : List Nat :=
    [ (X1v * X2v - t.t0a) / m, (Y1v * Y2v - t.t1a) / m, (Z1v * Z2v - t.t2a) / m,
      (t.t3a * t.t4a - t.t3b) / m, (t.t4c * t.X3a - t.t4d) / m, (t.X3c * t.Y3a - t.X3d) / m,
      (b3 * t.t2a - t.t2b) / m, (b3 * t.Y3c - t.Y3d) / m, (t.t4e * t.Y3d - t.X3f) / m,
      (t.t3c * t.t1b - t.t2c) / m, (t.Y3d * t.t0b - t.Y3e) / m, (t.t1b * t.Z3a - t.t1c) / m,
      (t.t0b * t.t3c - t.t0c) / m, (t.Z3a * t.t4e - t.Z3b) / m ]
  let bs : List Nat :=
    [ (X1v + Y1v - t.t3a) / m, (X2v + Y2v - t.t4a) / m, (t.t0a + t.t1a - t.t4b) / m,
      (t.t3c + t.t4b - t.t3b) / m, (Y1v + Z1v - t.t4c) / m, (Y2v + Z2v - t.X3a) / m,
      (t.t1a + t.t2a - t.X3b) / m, (t.t4e + t.X3b - t.t4d) / m, (X1v + Z1v - t.X3c) / m,
      (X2v + Z2v - t.Y3a) / m, (t.t0a + t.t2a - t.Y3b) / m, (t.Y3c + t.Y3b - t.X3d) / m,
      (t.t0a + t.t0a - t.X3e) / m, (t.X3e + t.t0a - t.t0b) / m, (t.t1a + t.t2b - t.Z3a) / m,
      (t.t1b + t.t2b - t.t1a) / m, (t.X3g + t.X3f - t.t2c) / m, (t.t1c + t.Y3e - t.Y3f) / m,
      (t.Z3b + t.t0c - t.Z3c) / m ]
  if col < 9 then limbOf X1v col
  else if col < 18 then limbOf Y1v (col - 9)
  else if col < 27 then limbOf Z1v (col - 18)
  else if col < 36 then limbOf X2v (col - 27)
  else if col < 45 then limbOf Y2v (col - 36)
  else if col < 54 then limbOf Z2v (col - 45)
  else if col < 351 then limbOf (vals.getD ((col - 54) / 9) 0) ((col - 54) % 9)
  else if col < 477 then limbOf (qs.getD ((col - 351) / 9) 0) ((col - 351) % 9)
  else if col < 496 then ((bs.getD (col - 477) 0 : Nat) : ℤ)
  else 0

/-- The Pallas RCB gadget at the KAT layout. -/
def pallasCompleteAddGad : List VmConstraint2 :=
  (pallasCompleteAdd 0 9 18 27 36 45 54).1
/-- The Vesta RCB gadget at the KAT layout. -/
def vestaCompleteAddGad : List VmConstraint2 :=
  (vestaCompleteAdd 0 9 18 27 36 45 54).1

-- Pallas: the honest trace of `[2]G` (via strong unification, `G + G`) is ACCEPTED; bumps REJECTED.
#guard acceptB pallasCompleteAddGad (rcbAsg pN curveB3 Gp.1 Gp.2 1 Gp.1 Gp.2 1) == true
#guard acceptB pallasCompleteAddGad (bumpAt (rcbAsg pN curveB3 Gp.1 Gp.2 1 Gp.1 Gp.2 1) 234) == false -- X3 limb
#guard acceptB pallasCompleteAddGad (bumpAt (rcbAsg pN curveB3 Gp.1 Gp.2 1 Gp.1 Gp.2 1) 261) == false -- Y3 limb
#guard acceptB pallasCompleteAddGad (bumpAt (rcbAsg pN curveB3 Gp.1 Gp.2 1 Gp.1 Gp.2 1) 288) == false -- Z3 limb
#guard acceptB pallasCompleteAddGad (bumpAt (rcbAsg pN curveB3 Gp.1 Gp.2 1 Gp.1 Gp.2 1) 54) == false  -- t0a limb
#guard acceptB pallasCompleteAddGad (bumpAt (rcbAsg pN curveB3 Gp.1 Gp.2 1 Gp.1 Gp.2 1) 180) == false -- t2b (smul) limb
-- Pallas: a GENERIC add `2G + G` (inputs 2G-proj, G) is also ACCEPTED (non-degenerate trace).
#guard acceptB pallasCompleteAddGad
  (rcbAsg pN curveB3 (jacToProjM pN Gp2).1 (jacToProjM pN Gp2).2.1 (jacToProjM pN Gp2).2.2 Gp.1 Gp.2 1) == true
-- Vesta: the honest trace of `[2]G` is ACCEPTED; bumps REJECTED.
#guard acceptB vestaCompleteAddGad (rcbAsg qN curveB3 Gv.1 Gv.2 1 Gv.1 Gv.2 1) == true
#guard acceptB vestaCompleteAddGad (bumpAt (rcbAsg qN curveB3 Gv.1 Gv.2 1 Gv.1 Gv.2 1) 234) == false
#guard acceptB vestaCompleteAddGad (bumpAt (rcbAsg qN curveB3 Gv.1 Gv.2 1 Gv.1 Gv.2 1) 288) == false
#guard acceptB vestaCompleteAddGad (bumpAt (rcbAsg qN curveB3 Gv.1 Gv.2 1 Gv.1 Gv.2 1) 180) == false

/-! ## §6 — Structural `#guard`s (the budgeted shapes) + AIR packaging + the named residuals. -/

#guard (pallasCompleteAdd 0 9 18 27 36 45 54).1.length == 33
#guard (pallasCompleteAdd 0 9 18 27 36 45 54).2.2 == 496
#guard (pallasCompleteAdd 0 9 18 27 36 45 54).2.1 == (288, 315, 342)  -- (X3,Y3,Z3) = fresh+{234,261,288}
#guard (vestaCompleteAdd 0 9 18 27 36 45 54).1.length == 33
#guard (vestaCompleteAdd 0 9 18 27 36 45 54).2.2 == 496

/-- A Pallas RCB complete-add packaged as an `EffectVmDescriptor2` (drops into the deployed
vocabulary). -/
def pallasCompleteAddDesc : EffectVmDescriptor2 :=
  { name        := "dregg-pasta-pallas-complete-add::demo"
  , traceWidth  := 496
  , piCount     := 0
  , tables      := []
  , constraints := (pallasCompleteAdd 0 9 18 27 36 45 54).1
  , hashSites   := []
  , ranges      := [] }

#guard pallasCompleteAddDesc.constraints.length == 33
#guard pallasCompleteAddDesc.traceWidth == 496

/-! ### The PRECISE named residuals.

  1. **RCB completeness is INHERITED, not machine-checked.** That Algorithm 7 computes the group
     law for ALL inputs on a prime-order `a=0` curve is Renes–Costello–Batina 2015 (Thm 1). What is
     machine-checked here: the gadget FORCES the RCB formula (`pallas/vestaCompleteAdd_forces`),
     and the formula AGREES with the real group law on the representative exceptional inputs
     `add-2007-bl` cannot handle (`P=Q`, `P+O`, `O+P`, `P+(−P)`, `O+O`, cross-tied to K2's `Gp2`/
     `Gp3`/`Gv2`/`Gv3`). Cofactor 1 (prime order) — the hypothesis of RCB completeness — is
     inherited from `mina-curves` (K1/K2 named it).
  2. **The `z < p` / `z < q` canonical compare is NOT generated** (inherited from K1/K2): the gates
     force the CONGRUENCE (proved), not the canonical representative; per-output limb ranges
     (`pastaLimbRange`) + the final compare compose on top unchanged.
  3. **The `ℤ ↔ p_felt` field-width gap** (inherited from K1): the gates are read over ℤ (the
     schoolbook cross-sums overflow BabyBear); native-field soundness is the shared residual.

CONTINUATION: `PastaScalarMul` composes THIS gadget over the GLV/Shamir bit-fold (the same op for
double and add — no case splits, because RCB is complete); `PastaIPA` uses the scalar mul in the
log(n) folding rounds. Honest gate count: one RCB add = `12·559 (mul) + 2·(1+279) (smul, degree-1)
+ 14·281 (add) + 5·281 (sub) ≈ 12.6K` gates at K1's full-generator counts — comparable to K2's
`add-2007-bl` but EXCEPTION-FREE, which is what makes the unified scalar-mul ladder possible.
-/

end Dregg2.Circuit.Emit.PastaCurveComplete
