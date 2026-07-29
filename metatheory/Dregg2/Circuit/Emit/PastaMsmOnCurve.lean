/-
# Dregg2.Circuit.Emit.PastaMsmOnCurve — the ON-CURVE GATE, and the death of the absorbing state.

## Substrate, said out loud

**Lean-authored AIR.** Every constraint here is produced by a `def` returning `List VmConstraint2`,
and every theorem is about that ACTUALLY EMITTED list. Rust hand-writes no constraint, no builder
gadget and no `air_accepts` predicate: it parses the emitted descriptor, fills trace CELLS and runs
the deployed prover. The row template is **not re-authored** — `onCurveRowDesc_extends_bound` proves
`PastaMsmBound.boundRowDesc`'s 82 constraints are still a PREFIX of the emitted 98.

## The hole this file closes, and it was a LIVE FORGERY, not a bookkeeping residual

Every `Pasta*` rung up to `PastaMsmScalarBound` forces `PastaMsmLayouts.hornerRefFrom` — a fold of
the RCB **FORMULA** (`PastaScalarMul.rcbAddZmod`) over projective triples in `ZMod p`. That the
formula computes the Pallas GROUP LAW is RCB'15 Theorem 1, whose hypothesis is that the operands are
points **on the curve** — and **nothing in the emitted constraints said so**.

`PastaMsmWindowed` §6.3 named the concrete consequence and left it standing: RCB Alg. 7 at `Q = O`
returns `Y₁·(X₁, Y₁, Z₁)`, so at `Y₁ = 0` it collapses to `(0, 0, 0)`, and `(0,0,0)` is **ABSORBING**
— `rcbAddZmod (0,0,0) Q = (0,0,0)` for every `Q`. So a prover could take the free initial
accumulator to `(0,0,0)`, carry the REAL Mina generators in `SRC`, the REAL block digits in `BIT`,
satisfy every one of the 82 emitted constraints exactly, and publish a final accumulator of `(0,0,0)`
— which satisfies `PastaMsmAir`'s terminal `X ≡ 0 ∧ Z ≡ 0` predicate. That is not a weakened claim;
it is the Mina claim, forged, with every binding rung green. `circuit/tests/pasta_oncurve_gate.rs`
PROVES AND VERIFIES exactly that trace against the contents-bound descriptor.

⚠ Note WHY the curve equation alone does not close it. The projective equation `Y²Z = X³ + bZ³` is
HOMOGENEOUS of degree 3, so `(0,0,0)` **satisfies it**. `(0,0,0)` is not a point of `P²` at all, and
no equation over the coordinates can say so. What says so is a NON-DEGENERACY witness.

## What is emitted, and why `Y ≠ 0` is exactly the right non-degeneracy

Two families per point, 8 gates:

  * the **curve equation** `Y²·Z ≡ X³ + b·Z³ (mod p)`, `b = 5` — five `fpMulCore`s, one
    `fpSMulCore`, and one bespoke degree-2 head carrying the reduction quotient;
  * the **`Y ≠ 0` inverse witness** `Y·YINV ≡ 1 (mod p)` — one bespoke degree-2 head.

`Y ≠ 0` is not a stronger condition than "is a point": on Pallas it is EQUIVALENT to it, given the
curve equation. A representative with `Y = 0` and `Z ≠ 0` is an affine point of order 2, and Pallas
has PRIME (odd) order, so there is none; a representative with `Y = 0` and `Z = 0` forces `X³ = 0`,
i.e. `(0,0,0)`, which is not a point. So the pair (curve equation, `Y` invertible) says exactly
"this triple is a point of the Pallas curve" — and it is the SAME condition RCB Alg. 7 needs for
`P + O` to return a correct projective representative (§5). One gate closes both.

## What it costs, measured against the current object

`PastaMsmBound.boundRowDesc` is 82 constraints / 529 columns. This file gates BOTH operands of every
row's add — the threaded accumulator `ACC` and the row's source `SRC` — at 8 gates and 135 columns
each: **98 constraints / 799 columns**, `+16` constraints and `+270` columns, row count and manifest
UNCHANGED. `OP` needs no gate: `PastaMsmLayouts.condPoint_forces` makes it `condRef bit SRC`, and
`condRef_is_a_curve_point` derives its curve-membership from `SRC`'s. `OUT` needs no gate: the
emitted thread makes it the NEXT row's `ACC` (§4.3 names the one row this does not cover).

## Satisfiability at birth

A gadget demanding more than an honest proof supplies is TRUE BECAUSE NOTHING SATISFIES IT. §3
exhibits the emitted gates ACCEPTING the Pallas generator, the identity `O = (0:1:0)`, and a
NON-AFFINE representative `(2X : 2Y : 2)` — the shape the honest fold actually produces, since RCB
rescales — and REFUSING `(0,0,0)`, an off-curve point, and a bumped limb.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard`s reduce in the kernel. Imports read-only. Import line:
`import Dregg2.Circuit.Emit.PastaMsmOnCurve`
-/
import Dregg2.Circuit.Emit.PastaMsmBound

namespace Dregg2.Circuit.Emit.PastaMsmOnCurve

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.Bls12381Tower (evalH_mul)
open Dregg2.Circuit.Emit.PastaField (p pN fpValue fpVal fpVal_eq acceptB bumpAt fpMulCore fpMulHead
  fpMulCore_forces numLimbs limbBits)
open Dregg2.Circuit.Emit.PastaCurve (curveB Gp)
open Dregg2.Circuit.Emit.PastaCurveComplete (fpSMulCore fpSMulHead fpSMulCore_forces)
open Dregg2.Circuit.Emit.PastaScalarMul (PtP PointIsZ rcbAddZmod rcbOutG zmod_eq_of_dvd
  acceptB_prefix acceptB_suffix gateBodyEvalZero_cgH)
open Dregg2.Circuit.Emit.PastaMsmLayouts (condRef bitAt)
open Dregg2.Circuit.Emit.PastaMsmWindowed (ACCX ACCY ACCZ SRCX SRCY SRCZ BIT WTrace Threaded
  rowGates windowedRef windowedRows_forces)
open Dregg2.Circuit.Emit.PastaMsmSliced (PI_COUNT)
open Dregg2.Circuit.Emit.PastaMsmBound (WB bMaxVar boundRowDesc Pt)

set_option autoImplicit false

/-! ## §0 — `ZMod pN` is nontrivial, decided in the kernel.

The `Y ≠ 0` conclusion is "`1 ≠ 0` in `ZMod pN`", which is exactly `1 < pN`. Decided rather than
assumed, because a vacuously-trivial ring would make every non-degeneracy claim below TRUE AND
EMPTY. -/

/-- The Pallas base modulus exceeds one — so `ZMod pN` is not the zero ring. -/
theorem one_lt_pN : 1 < pN := by decide

/-! ## §1 — THE EMITTED BLOCK.

One point's on-curve certificate occupies `OC_COLS = 135` columns at a caller-chosen `f`, in the
same 9-limb-group discipline every `Pasta*` gadget uses (`numLimbs = 9`, `limbBits = 30`).

Reading the layout as arithmetic, with every intermediate REDUCED (`< p`) by its own gate:

```text
  f +   0 : XX   = X·X        f +   9 : its quotient
  f +  18 : YY   = Y·Y        f +  27 : its quotient
  f +  36 : ZZ   = Z·Z        f +  45 : its quotient
  f +  54 : X3   = XX·X       f +  63 : its quotient
  f +  72 : Z3   = ZZ·Z       f +  81 : its quotient
  f +  90 : BZ3  = b·Z3       f +  99 : its quotient
  f + 108 : QC   — the CURVE-equation reduction quotient
  f + 117 : YINV               f + 126 : the `Y·YINV ≡ 1` quotient
```

`X3` and `Z3` exist so the curve head's own slack is bounded: with `X3, BZ3 < p` reduced, the head's
value lies in `(−2p, p²)` and ONE non-negative 9×30 quotient group plus the constant `2p` covers it.
Folding `X³` and `b·Z³` into the head directly would need a quotient near `7p`, which the honest
witness generator cannot carry in 256 bits. -/

/-- `X·X`, reduced. -/            def OC_XX   : Nat := 0
/-- its reduction quotient. -/    def OC_QXX  : Nat := 9
/-- `Y·Y`, reduced. -/            def OC_YY   : Nat := 18
/-- its reduction quotient. -/    def OC_QYY  : Nat := 27
/-- `Z·Z`, reduced. -/            def OC_ZZ   : Nat := 36
/-- its reduction quotient. -/    def OC_QZZ  : Nat := 45
/-- `X³`, reduced. -/             def OC_X3   : Nat := 54
/-- its reduction quotient. -/    def OC_QX3  : Nat := 63
/-- `Z³`, reduced. -/             def OC_Z3   : Nat := 72
/-- its reduction quotient. -/    def OC_QZ3  : Nat := 81
/-- `b·Z³`, reduced. -/           def OC_BZ3  : Nat := 90
/-- its reduction quotient. -/    def OC_QBZ3 : Nat := 99
/-- the curve head's quotient. -/ def OC_QC   : Nat := 108
/-- `Y⁻¹ mod p`. -/               def OC_YINV : Nat := 117
/-- the `Y·YINV` quotient. -/     def OC_QINV : Nat := 126
/-- Columns one point's on-curve certificate occupies. -/
def OC_COLS : Nat := 135

/-- ⚑ **The CURVE-EQUATION head** — `YY·Z − X3 − BZ3 + 2p − p·QC`. Degree 2 (the `Head.mul`
cross-product, exactly `fpMulHead`'s shape), so it adds no degree to the descriptor. Zero forces
`YY·Z ≡ X3 + BZ3 (mod p)`; §2 composes that with the six reduction gates into `Y²Z ≡ X³ + b·Z³`.

The `+2p` is what lets ONE non-negative quotient group carry a head whose value is negative for
most honest inputs: `YY·Z − X3 − BZ3 ∈ (−2p, p²)`, so `YY·Z − X3 − BZ3 + 2p ∈ (0, p² + 2p)` and its
`p`-quotient fits `9 × 30 = 270` bits with room. It is a CONSTANT, not a column, so it costs
nothing and cannot be chosen by a prover. -/
def curveHead (bZ f : Nat) : Head :=
  (((((fpValue (f + OC_YY)).mul (fpValue bZ)).append ((fpValue (f + OC_X3)).scale (-1))).append
      ((fpValue (f + OC_BZ3)).scale (-1))).append
        ((fpValue (f + OC_QC)).scale (-p))).addConst (2 * p)

/-- ⚑ **The NON-DEGENERACY head** — `Y·YINV − p·QINV − 1`. Zero forces `Y·YINV ≡ 1 (mod p)`, so `Y`
is a UNIT and in particular `Y ≠ 0`. This is the gate the curve equation cannot be: the projective
equation is homogeneous, so `(0,0,0)` satisfies it, and only an inverse witness excludes it. -/
def nonZeroHead (bY f : Nat) : Head :=
  (((fpValue bY).mul (fpValue (f + OC_YINV))).append
    ((fpValue (f + OC_QINV)).scale (-p))).addConst (-1)

/-- ⚑⚑ **THE ON-CURVE GATE** — 8 emitted constraints certifying that the triple at
`(bX, bY, bZ)` is a POINT of the Pallas curve `Y²Z = X³ + 5Z³` and is not the degenerate `(0,0,0)`.
Six are K1/K4a cores (`fpMulCore`, `fpSMulCore`) reused verbatim; two are the heads above. -/
def onCurveGates (bX bY bZ f : Nat) : List VmConstraint2 :=
  [ fpMulCore bX bX (f + OC_XX) (f + OC_QXX)
  , fpMulCore bY bY (f + OC_YY) (f + OC_QYY)
  , fpMulCore bZ bZ (f + OC_ZZ) (f + OC_QZZ)
  , fpMulCore (f + OC_XX) bX (f + OC_X3) (f + OC_QX3)
  , fpMulCore (f + OC_ZZ) bZ (f + OC_Z3) (f + OC_QZ3)
  , fpSMulCore (curveB : ℤ) (f + OC_Z3) (f + OC_BZ3) (f + OC_QBZ3)
  , cgH (curveHead bZ f)
  , cgH (nonZeroHead bY f) ]

/-- The emitted block is 8 constraints, at every layout. -/
theorem onCurveGates_length (bX bY bZ f : Nat) : (onCurveGates bX bY bZ f).length = 8 := rfl

/-! ## §2 — THE FORCING: the emitted gates say "this triple is a Pallas point".

`OnCurveZ` is the HOMOGENEOUS curve equation over `ZMod pN` — the projective form
`Y²·Z = X³ + b·Z³`, which is what `PastaCurveComplete.projOnCurveM` decides and what RCB'15 Thm 1
takes as its hypothesis. -/

/-- The projective Pallas curve equation over `ZMod pN`: `Y²·Z = X³ + b·Z³`, `b = 5`. -/
def OnCurveZ (P : PtP) : Prop :=
  P.2.1 * P.2.1 * P.2.2
    = P.1 * P.1 * P.1 + ((curveB : Nat) : ZMod pN) * (P.2.2 * P.2.2 * P.2.2)

/-- ⚑⚑ **`onCurve_forces`** — **the deliverable.** Any assignment satisfying the EMITTED
`onCurveGates`, whose `(bX, bY, bZ)` groups represent `P`, has `P` on the Pallas curve AND `P`'s
`Y` coordinate a unit — so `P` is a genuine point of `P²` on the curve, not a degenerate triple.

`bX`, `bY`, `bZ` and `f` are universally quantified: the statement at the accumulator's layout is
the statement at the source's. -/
theorem onCurve_forces (a : Assignment) (bX bY bZ f : Nat) {P : PtP}
    (hP : PointIsZ a bX bY bZ P)
    (hacc : acceptB (onCurveGates bX bY bZ f) a = true) :
    OnCurveZ P ∧ P.2.1 ≠ 0 := by
  haveI : Fact (1 < pN) := ⟨one_lt_pN⟩
  obtain ⟨hx, hy, hz⟩ := hP
  simp only [onCurveGates, fpMulCore, fpSMulCore, acceptB, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, gateBodyEvalZero_cgH] at hacc
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hacc
  -- the six reduction gates, cast into `ZMod pN`
  have hXX : ((fpVal a (f + OC_XX) : ℤ) : ZMod pN)
      = ((fpVal a bX : ℤ) : ZMod pN) * ((fpVal a bX : ℤ) : ZMod pN) := by
    have := zmod_eq_of_dvd (fpMulCore_forces a bX bX (f + OC_XX) (f + OC_QXX)
      (of_decide_eq_true g1))
    push_cast at this ⊢; exact this
  have hYY : ((fpVal a (f + OC_YY) : ℤ) : ZMod pN)
      = ((fpVal a bY : ℤ) : ZMod pN) * ((fpVal a bY : ℤ) : ZMod pN) := by
    have := zmod_eq_of_dvd (fpMulCore_forces a bY bY (f + OC_YY) (f + OC_QYY)
      (of_decide_eq_true g2))
    push_cast at this ⊢; exact this
  have hZZ : ((fpVal a (f + OC_ZZ) : ℤ) : ZMod pN)
      = ((fpVal a bZ : ℤ) : ZMod pN) * ((fpVal a bZ : ℤ) : ZMod pN) := by
    have := zmod_eq_of_dvd (fpMulCore_forces a bZ bZ (f + OC_ZZ) (f + OC_QZZ)
      (of_decide_eq_true g3))
    push_cast at this ⊢; exact this
  have hX3 : ((fpVal a (f + OC_X3) : ℤ) : ZMod pN)
      = ((fpVal a (f + OC_XX) : ℤ) : ZMod pN) * ((fpVal a bX : ℤ) : ZMod pN) := by
    have := zmod_eq_of_dvd (fpMulCore_forces a (f + OC_XX) bX (f + OC_X3) (f + OC_QX3)
      (of_decide_eq_true g4))
    push_cast at this ⊢; exact this
  have hZ3 : ((fpVal a (f + OC_Z3) : ℤ) : ZMod pN)
      = ((fpVal a (f + OC_ZZ) : ℤ) : ZMod pN) * ((fpVal a bZ : ℤ) : ZMod pN) := by
    have := zmod_eq_of_dvd (fpMulCore_forces a (f + OC_ZZ) bZ (f + OC_Z3) (f + OC_QZ3)
      (of_decide_eq_true g5))
    push_cast at this ⊢; exact this
  have hBZ3 : ((fpVal a (f + OC_BZ3) : ℤ) : ZMod pN)
      = ((curveB : Nat) : ZMod pN) * ((fpVal a (f + OC_Z3) : ℤ) : ZMod pN) := by
    have := zmod_eq_of_dvd (fpSMulCore_forces a (curveB : ℤ) (f + OC_Z3) (f + OC_BZ3)
      (f + OC_QBZ3) (of_decide_eq_true g6))
    push_cast at this ⊢; exact this
  -- the curve head: `p ∣ YY·Z − (X3 + BZ3)`, with quotient `QC − 2`
  have hCz : ((fpVal a (f + OC_X3) + fpVal a (f + OC_BZ3) : ℤ) : ZMod pN)
      = ((fpVal a (f + OC_YY) * fpVal a bZ : ℤ) : ZMod pN) := by
    refine zmod_eq_of_dvd ⟨fpVal a (f + OC_QC) - 2, ?_⟩
    have h := of_decide_eq_true g7
    simp only [curveHead, evalH_addConst, evalH_append, evalH_scale, evalH_mul, fpVal_eq] at h
    ring_nf
    ring_nf at h
    linarith
  have hC : ((fpVal a (f + OC_X3) : ℤ) : ZMod pN) + ((fpVal a (f + OC_BZ3) : ℤ) : ZMod pN)
      = ((fpVal a (f + OC_YY) : ℤ) : ZMod pN) * ((fpVal a bZ : ℤ) : ZMod pN) := by
    push_cast at hCz; exact hCz
  -- the non-degeneracy head: `p ∣ Y·YINV − 1`, with quotient `QINV`
  have hIz : ((1 : ℤ) : ZMod pN)
      = ((fpVal a bY * fpVal a (f + OC_YINV) : ℤ) : ZMod pN) := by
    refine zmod_eq_of_dvd ⟨fpVal a (f + OC_QINV), ?_⟩
    have h := of_decide_eq_true g8
    simp only [nonZeroHead, evalH_addConst, evalH_append, evalH_scale, evalH_mul, fpVal_eq] at h
    linarith
  have hI : (1 : ZMod pN)
      = ((fpVal a bY : ℤ) : ZMod pN) * ((fpVal a (f + OC_YINV) : ℤ) : ZMod pN) := by
    push_cast at hIz; exact hIz
  -- eliminate every intermediate group from the curve gate, leaving it in the coordinates alone
  rw [hX3, hXX, hBZ3, hZ3, hZZ, hYY] at hC
  constructor
  · show P.2.1 * P.2.1 * P.2.2
      = P.1 * P.1 * P.1 + ((curveB : Nat) : ZMod pN) * (P.2.2 * P.2.2 * P.2.2)
    rw [← hx, ← hy, ← hz]
    exact hC.symm
  · intro h0
    rw [h0] at hy
    rw [hy, zero_mul] at hI
    exact one_ne_zero hI

#assert_axioms one_lt_pN
#assert_axioms onCurve_forces

/-! ### §2b — what the gate BUYS, stated as points rather than triples.

Three consequences, each one line, and each one closes a named hole. -/

/-- Projective equality over `ZMod pN`: `Q` is a nonzero rescale of `P`. This is the relation
`PastaCurveComplete.projEqM` cross-multiplies; stated with an explicit unit so it stays an
equivalence at the degenerate triple, which cross-multiplication does not. -/
def ProjEqZ (P Q : PtP) : Prop :=
  ∃ c : ZMod pN, c ≠ 0 ∧ Q = (c * P.1, c * P.2.1, c * P.2.2)

/-- ⚑ **`no_absorbing_state`** — a gated point is NOT `(0,0,0)`. The one-line consequence that kills
the forgery: `(0,0,0)` is absorbing under `rcbAddZmod`, and the gate refuses it. -/
theorem no_absorbing_state {P : PtP} (hy : P.2.1 ≠ 0) : P ≠ (0, 0, 0) := by
  intro h
  exact hy (by rw [h])

/-- ⚑ **`skip_is_rescale`** — RCB Alg. 7 at `Q = O` returns `Y₁ · (X₁, Y₁, Z₁)`. A `ring` identity
over `ZMod pN`, not a KAT: this is the exact shape `PastaMsmWindowed` §6.3 named as the wound. -/
theorem skip_is_rescale (P : PtP) :
    rcbAddZmod P (0, 1, 0) = (P.2.1 * P.1, P.2.1 * P.2.1, P.2.1 * P.2.2) := by
  simp only [rcbAddZmod, rcbOutG]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> try ring

/-- ⚑⚑ **`skip_is_projective_identity`** — **with the gate, the SKIP is a no-op.** On an unset digit
`PastaMsmLayouts.condRef` hands the add `O = (0:1:0)`, and the fold's accumulator is REPLACED by
`Y₁·(X₁,Y₁,Z₁)`. That is the same projective point exactly when `Y₁` is a unit — which the emitted
`nonZeroHead` now forces. Without the gate, `Y₁ = 0` sends it to `(0,0,0)` instead. -/
theorem skip_is_projective_identity (P : PtP) (hy : P.2.1 ≠ 0) :
    ProjEqZ P (rcbAddZmod P (0, 1, 0)) := by
  refine ⟨P.2.1, hy, ?_⟩
  rw [skip_is_rescale]

/-- ⚑⚑ **`terminal_is_the_identity`** — **the terminal predicate finally MEANS the identity.**
`PastaMsmAir`'s terminal check is `X ≡ 0 ∧ Z ≡ 0`; with the gate's `Y ≠ 0` that triple IS the
projective point at infinity. -/
theorem terminal_is_the_identity (P : PtP) (hy : P.2.1 ≠ 0) (hX : P.1 = 0) (hZ : P.2.2 = 0) :
    ProjEqZ ((0 : ZMod pN), 1, 0) P := by
  refine ⟨P.2.1, hy, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [hX, hZ]

/-- ⚑ **`origin_is_not_the_identity`** — and WITHOUT the gate it did not: `(0,0,0)` satisfies
`X ≡ 0 ∧ Z ≡ 0` while being no point at all, so the terminal predicate accepted it. This is the
refutation half; the pair is what makes the previous theorem a repair rather than a restatement. -/
theorem origin_is_not_the_identity :
    ¬ ProjEqZ ((0 : ZMod pN), 1, 0) (0, 0, 0) := by
  rintro ⟨c, hc, h⟩
  have : (0 : ZMod pN) = c * 1 := congrArg (fun t => t.2.1) h
  exact hc (by simpa using this.symm)

/-- ⚑ **`origin_satisfies_the_terminal_predicate`** — said as an object, so the hole above is not
merely asserted: the degenerate triple passes `X ≡ 0 ∧ Z ≡ 0`. -/
theorem origin_satisfies_the_terminal_predicate :
    ((0 : ZMod pN), (0 : ZMod pN), (0 : ZMod pN)).1 = 0
      ∧ ((0 : ZMod pN), (0 : ZMod pN), (0 : ZMod pN)).2.2 = 0 := ⟨rfl, rfl⟩

/-- ⚑ **`origin_is_absorbing`** — and it is not merely a bad terminal value, it is a SINK: once the
fold reaches `(0,0,0)` every further RCB add leaves it there, whatever the addend. A `ring` identity
over `ZMod pN`, so it holds for every `Q` rather than at exhibited ones. -/
theorem origin_is_absorbing (Q : PtP) :
    rcbAddZmod ((0 : ZMod pN), (0 : ZMod pN), (0 : ZMod pN)) Q = (0, 0, 0) := by
  simp only [rcbAddZmod, rcbOutG]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

/-- ⚑ **`condRef_is_a_curve_point`** — the row's ADDEND needs no gate of its own. The selector's
output is `condRef bit SRC` (`PastaMsmLayouts.condPoint_forces`), which is either `SRC` — gated —
or the identity `O = (0:1:0)`, which is on the curve with `Y = 1`. -/
theorem condRef_is_a_curve_point (b : Bool) {S : PtP} (h : OnCurveZ S) (hy : S.2.1 ≠ 0) :
    OnCurveZ (condRef b S) ∧ (condRef b S).2.1 ≠ 0 := by
  haveI : Fact (1 < pN) := ⟨one_lt_pN⟩
  cases b with
  | false => exact ⟨by simp [condRef, OnCurveZ], by simpa [condRef] using one_ne_zero⟩
  | true  => exact ⟨by simpa [condRef] using h, by simpa [condRef] using hy⟩

#assert_axioms no_absorbing_state
#assert_axioms skip_is_rescale
#assert_axioms skip_is_projective_identity
#assert_axioms terminal_is_the_identity
#assert_axioms origin_is_not_the_identity
#assert_axioms origin_satisfies_the_terminal_predicate
#assert_axioms origin_is_absorbing
#assert_axioms condRef_is_a_curve_point

/-! ## §3 — ⚑ THE GATE BITES: SATISFIABLE and REFUTABLE, in the kernel, over the EMITTED list.

`AirBuilder.rangeNonneg` sat in this tree for months as a shape every consumer read as a check, so
both polarities are exhibited here rather than argued. The layout is the point at `0 / 9 / 18` with
its block at `27`; `ocAsg` computes every witness slot from the coordinates the same way the Rust
witness generator does, so a divergence between the two shows up as a red `#guard` here and a
refused proof there.

The inverse `YINV` is the one slot no `%`-arithmetic produces in the kernel, so it is a PASTED
literal and the kernel CHECKS it (`Y · YINV ≡ 1`) rather than trusting it. -/

open Dregg2.Circuit.Emit.PastaField.Ref (limbOf)

/-- The KAT block base. -/
def KF : Nat := 27

/-- The on-curve witness for a triple, every slot derived. `Yinv` is supplied because a modular
inverse is not a kernel `%`-computation; the guards below check the one that is used. -/
def ocAsg (Xv Yv Zv Yinv : Nat) : Assignment :=
  let XX := (Xv * Xv) % pN
  let YY := (Yv * Yv) % pN
  let ZZ := (Zv * Zv) % pN
  let X3 := (XX * Xv) % pN
  let Z3 := (ZZ * Zv) % pN
  let BZ3 := (curveB * Z3) % pN
  let S := YY * Zv
  let R := S % pN + 2 * pN - X3 - BZ3
  let vals : List Nat :=
    [ XX, (Xv * Xv) / pN, YY, (Yv * Yv) / pN, ZZ, (Zv * Zv) / pN
    , X3, (XX * Xv) / pN, Z3, (ZZ * Zv) / pN, BZ3, (curveB * Z3) / pN
    , S / pN + R / pN, Yinv, (Yv * Yinv - 1) / pN ]
  fun col =>
    if col < 9 then limbOf Xv col
    else if col < 18 then limbOf Yv (col - 9)
    else if col < 27 then limbOf Zv (col - 18)
    else if col < KF + OC_COLS then limbOf (vals.getD ((col - KF) / 9) 0) ((col - KF) % 9)
    else 0

/-- The emitted gate at the KAT layout. -/
def ocGates : List VmConstraint2 := onCurveGates 0 9 18 KF

/-- `Gp.2⁻¹ mod p`, a pasted witness the next `#guard` CHECKS. -/
def GP_YINV : Nat :=
  16543786951811745360182113530594221113008777143079358598737104616437013339253
/-- The `Y` of the NON-AFFINE representative `(2X : 2Y : 2)` of the generator. -/
def SC2_Y : Nat :=
  24837309565766651186828884854098791575926986825302938889117194811144354289014
/-- …and its inverse, likewise checked. -/
def SC2_YINV : Nat :=
  22745904630570397108037429891383099038185916812510459657345890690393490484795

-- The pasted inverses are CHECKED, not trusted.
#guard (Gp.2 * GP_YINV) % pN == 1
#guard (SC2_Y * SC2_YINV) % pN == 1
#guard SC2_Y == (2 * Gp.2) % pN

-- SATISFIABLE — the Pallas generator, affine.
#guard acceptB ocGates (ocAsg Gp.1 Gp.2 1 GP_YINV) == true
-- SATISFIABLE — the identity `O = (0 : 1 : 0)`, which the SKIP encoding feeds the add on every
-- unset digit. It is on the curve (the equation is homogeneous: `1·0 = 0 + 5·0`) and `Y = 1`.
#guard acceptB ocGates (ocAsg 0 1 0 1) == true
-- ⚑ SATISFIABLE — a NON-AFFINE representative `(2X : 2Y : 2)`. This is the shape the honest fold
-- actually produces (RCB rescales), so a gate that only accepted `Z = 1` would refuse every honest
-- trace after the first row.
#guard acceptB ocGates (ocAsg 2 SC2_Y 2 SC2_YINV) == true

-- ⚑⚑ REFUTABLE — **THE ABSORBING STATE.** `(0,0,0)` satisfies the homogeneous curve equation and
-- the terminal `X ≡ 0 ∧ Z ≡ 0` predicate; the non-degeneracy head is what refuses it, at every
-- claimed inverse.
#guard acceptB ocGates (ocAsg 0 0 0 0) == false
#guard acceptB ocGates (ocAsg 0 0 0 1) == false
#guard acceptB ocGates (ocAsg 0 0 0 GP_YINV) == false
-- ⚑ REFUTABLE — a forged `Y = 0` at a real `X`: this is the state the `O`-skip collapses from.
#guard acceptB ocGates (ocAsg Gp.1 0 1 1) == false
-- ⚑ REFUTABLE — an OFF-CURVE point with a PERFECTLY VALID `Y` inverse, so the refusal is the CURVE
-- head's and not the non-degeneracy head's.
#guard acceptB ocGates (ocAsg (Gp.1 + 1) Gp.2 1 GP_YINV) == false
-- REFUTABLE — a bumped witness limb, at each of the three bespoke slots.
#guard acceptB ocGates (bumpAt (ocAsg Gp.1 Gp.2 1 GP_YINV) (KF + OC_XX)) == false
#guard acceptB ocGates (bumpAt (ocAsg Gp.1 Gp.2 1 GP_YINV) (KF + OC_QC)) == false
#guard acceptB ocGates (bumpAt (ocAsg Gp.1 Gp.2 1 GP_YINV) (KF + OC_YINV)) == false
-- REFUTABLE — a bumped COORDINATE limb: the certificate no longer matches its own point.
#guard acceptB ocGates (bumpAt (ocAsg Gp.1 Gp.2 1 GP_YINV) 0) == false
#guard acceptB ocGates (bumpAt (ocAsg Gp.1 Gp.2 1 GP_YINV) 9) == false
#guard acceptB ocGates (bumpAt (ocAsg Gp.1 Gp.2 1 GP_YINV) 18) == false

/-! ## §4 — THE EMITTED DESCRIPTOR: `PastaMsmBound.boundRowDesc`, gated.

Both operands of the row's add are gated. `ACC` is the threaded accumulator coming in; `SRC` is the
row's source point. Nothing else is re-authored — §4.1 proves the 82 constraints are still a
prefix. -/

/-- The `ACC` point's on-curve block, immediately above `PastaMsmBound.WB = 529`. -/
def OC_ACC : Nat := WB
/-- The `SRC` point's on-curve block. -/
def OC_SRC : Nat := WB + OC_COLS
/-- The gated row template's width: `529 + 2 × 135`. -/
def WOC : Nat := WB + 2 * OC_COLS

/-- ⚑ **The emitted on-curve row gates** — both operands, 16 constraints. -/
def onCurveRowGates : List VmConstraint2 :=
  onCurveGates ACCX ACCY ACCZ OC_ACC ++ onCurveGates SRCX SRCY SRCZ OC_SRC

/-- ⚑⚑ **The CURVE-GATED contents-bound sliced descriptor.** `PastaMsmBound.boundRowDesc`'s 82
constraints and its exact-public manifest verbatim, plus the 16 on-curve constraints. Same table,
same wire id, same manifest arity, same public inputs, same row count. -/
def onCurveRowDesc (n k w planes : Nat) (gens : List Pt) (scal : List Nat) : EffectVmDescriptor2 :=
  { name        := "dregg-pasta-rcb-sg-oncurve-" ++ toString k ++ "-of-" ++ toString n ++ "::v1"
  , traceWidth  := WOC
  , piCount     := PI_COUNT
  , tables      := (boundRowDesc n k w planes gens scal).tables
  , constraints := (boundRowDesc n k w planes gens scal).constraints ++ onCurveRowGates
  , hashSites   := []
  , ranges      := [] }

/-! ### §4.1 — nothing was re-authored. -/

/-- ⚑ **`onCurveRowDesc_extends_bound`** — the emitted list still has the CONTENTS-BOUND
descriptor's 82 constraints as a PREFIX, hence (transitively) `PastaMsmSliced`'s 78 and
`PastaMsmWindowed`'s 45. Every forcing theorem of those files applies to this descriptor unchanged,
by `acceptB_prefix`. -/
theorem onCurveRowDesc_extends_bound (n k w planes : Nat) (gens : List Pt) (scal : List Nat) :
    (boundRowDesc n k w planes gens scal).constraints <+:
      (onCurveRowDesc n k w planes gens scal).constraints :=
  ⟨onCurveRowGates, rfl⟩

/-- …and the table is the same object, so the CONTENTS forcing is inherited rather than restated. -/
theorem onCurveRowDesc_tables (n k w planes : Nat) (gens : List Pt) (scal : List Nat) :
    (onCurveRowDesc n k w planes gens scal).tables
      = (boundRowDesc n k w planes gens scal).tables := rfl

/-- The emitted constraint count: 82 + 16. Still a CONSTANT — independent of the slice width, the
plane count and the row count. -/
theorem onCurveRowDesc_constraints_length (n k w planes : Nat) (gens : List Pt) (scal : List Nat) :
    (onCurveRowDesc n k w planes gens scal).constraints.length = 98 := by
  simp [onCurveRowDesc, onCurveRowGates, onCurveGates_length,
    Dregg2.Circuit.Emit.PastaMsmBound.boundRowDesc_constraints_length]

set_option maxRecDepth 400000 in
/-- ⚑ **`onCurveRowDesc_columns_in_bounds`** — every column every emitted constraint addresses,
including the two new degree-2 heads' 81-term cross products, is `≤ traceWidth`. This is
`descriptor_ir2.rs`'s `chk` closure, decided in the kernel before the prover sees the descriptor. -/
theorem onCurveRowDesc_columns_in_bounds :
    (onCurveRowDesc 4 0 31 4 [] []).constraints.all
        (fun c => decide (bMaxVar c ≤ (onCurveRowDesc 4 0 31 4 [] []).traceWidth)) = true := by
  decide

set_option maxRecDepth 400000 in
/-- ⚑ **`onCurveRowDesc_pi_indices_in_bounds`** — every `pi_binding` names a declared public input
(`descriptor_ir2.rs:1581`). The gate adds none, and this re-decides it rather than assuming it. -/
theorem onCurveRowDesc_pi_indices_in_bounds :
    (onCurveRowDesc 4 0 31 4 [] []).constraints.all
        (fun c => decide (Dregg2.Circuit.Emit.PastaMsmSliced.sMaxPi c
                            ≤ (onCurveRowDesc 4 0 31 4 [] []).piCount)) = true := by decide

#guard (onCurveRowDesc 4 0 31 4 [] []).traceWidth == 799
#guard (onCurveRowDesc 4 0 31 4 [] []).piCount == 29
#guard (onCurveRowDesc 4 0 31 4 [] []).constraints.length == 98
#guard (onCurveRowDesc 4 2 31 4 [] []).name == "dregg-pasta-rcb-sg-oncurve-2-of-4::v1"
-- ⚑ THE PRICE, as an object: +16 constraints and +270 columns against the contents-bound cut.
#guard (onCurveRowDesc 4 0 31 4 [] []).constraints.length
         - (boundRowDesc 4 0 31 4 [] []).constraints.length == 16
#guard (onCurveRowDesc 4 0 31 4 [] []).traceWidth - (boundRowDesc 4 0 31 4 [] []).traceWidth == 270
#guard OC_COLS * 2 == 270
-- …and the manifest is UNTOUCHED: same rows, same arity, so the exact-public tooth's own bounds
-- are unmoved by this rung.
#guard ((onCurveRowDesc 4 0 31 4 [] []).tables.map (fun t => t.arity))
         == ((boundRowDesc 4 0 31 4 [] []).tables.map (fun t => t.arity))

#assert_axioms onCurveGates_length
#assert_axioms onCurveRowDesc_extends_bound
#assert_axioms onCurveRowDesc_tables
#assert_axioms onCurveRowDesc_constraints_length
#assert_axioms onCurveRowDesc_columns_in_bounds
#assert_axioms onCurveRowDesc_pi_indices_in_bounds

/-! ### §4.2 — THE ROW, and then THE FOLD.

`onCurve_forces` is stated at one point and one layout. These two compose it: first across the two
operands of one row, then — through `PastaMsmWindowed.windowedRows_forces`, unmodified — across
every accumulator the whole fold passes through. -/

/-- ⚑ **`row_operands_are_curve_points`** — on a row satisfying the emitted on-curve gates, BOTH
operands of that row's RCB add are points of the Pallas curve with `Y` a unit. -/
theorem row_operands_are_curve_points (a : Assignment) {acc S : PtP}
    (hacc : PointIsZ a ACCX ACCY ACCZ acc) (hS : PointIsZ a SRCX SRCY SRCZ S)
    (hrow : acceptB onCurveRowGates a = true) :
    (OnCurveZ acc ∧ acc.2.1 ≠ 0) ∧ (OnCurveZ S ∧ S.2.1 ≠ 0) :=
  ⟨onCurve_forces a ACCX ACCY ACCZ OC_ACC hacc (acceptB_prefix _ _ a hrow),
   onCurve_forces a SRCX SRCY SRCZ OC_SRC hS (acceptB_suffix _ _ a hrow)⟩

/-- ⚑ **`row_addend_is_a_curve_point`** — and therefore so is what the row actually ADDS. -/
theorem row_addend_is_a_curve_point (a : Assignment) {acc S : PtP}
    (hacc : PointIsZ a ACCX ACCY ACCZ acc) (hS : PointIsZ a SRCX SRCY SRCZ S)
    (hrow : acceptB onCurveRowGates a = true) :
    OnCurveZ (condRef (bitAt a BIT) S) ∧ (condRef (bitAt a BIT) S).2.1 ≠ 0 := by
  obtain ⟨-, hSc, hSy⟩ := row_operands_are_curve_points a hacc hS hrow
  exact condRef_is_a_curve_point (bitAt a BIT) hSc hSy

/-- ⚑⚑ **`fold_accumulator_is_a_curve_point`** — **the composition, and the theorem the transport
wants.** On a windowed trace whose rows satisfy `PastaMsmWindowed.rowGates`, the emitted thread AND
the emitted on-curve gates, the accumulator the fold has reached after `i` rows — which
`windowedRows_forces` already proves is `windowedRef`, unchanged and not restated — is a POINT of
the Pallas curve with `Y` a unit.

So every operand of every RCB add in the whole fold is a curve point: the addend by
`row_addend_is_a_curve_point`, the accumulator by this. That is RCB'15 Thm 1's hypothesis, FORCED by
the emitted constraints instead of assumed. §5 says precisely what is left. -/
theorem fold_accumulator_is_a_curve_point (T : WTrace) (Sv : Nat → PtP) (acc0 : PtP)
    (h0 : PointIsZ (T 0) ACCX ACCY ACCZ acc0) (h : Nat)
    (hrows : ∀ i < h, acceptB rowGates (T i) = true)
    (hthr : ∀ i < h, Threaded T i)
    (hsrc : ∀ i < h, PointIsZ (T i) SRCX SRCY SRCZ (Sv i))
    (hoc : acceptB onCurveRowGates (T h) = true) :
    OnCurveZ (windowedRef Sv (fun i => bitAt (T i) BIT) acc0 h)
      ∧ (windowedRef Sv (fun i => bitAt (T i) BIT) acc0 h).2.1 ≠ 0 :=
  onCurve_forces (T h) ACCX ACCY ACCZ OC_ACC
    (windowedRows_forces T Sv acc0 h0 h hrows hthr hsrc)
    (acceptB_prefix _ _ (T h) hoc)

/-- ⚑ **`fold_never_reaches_the_absorbing_state`** — said as the attack rather than as the
invariant: the accumulator of a gated trace is never `(0,0,0)`, at any row. -/
theorem fold_never_reaches_the_absorbing_state (T : WTrace) (Sv : Nat → PtP) (acc0 : PtP)
    (h0 : PointIsZ (T 0) ACCX ACCY ACCZ acc0) (h : Nat)
    (hrows : ∀ i < h, acceptB rowGates (T i) = true)
    (hthr : ∀ i < h, Threaded T i)
    (hsrc : ∀ i < h, PointIsZ (T i) SRCX SRCY SRCZ (Sv i))
    (hoc : acceptB onCurveRowGates (T h) = true) :
    windowedRef Sv (fun i => bitAt (T i) BIT) acc0 h ≠ (0, 0, 0) :=
  no_absorbing_state
    (fold_accumulator_is_a_curve_point T Sv acc0 h0 h hrows hthr hsrc hoc).2

#assert_axioms row_operands_are_curve_points
#assert_axioms row_addend_is_a_curve_point
#assert_axioms fold_accumulator_is_a_curve_point
#assert_axioms fold_never_reaches_the_absorbing_state

/-! ## §5 — ⚑ THE TRANSPORT: what a verified proof now establishes, and the ONE thing it does not.

### §5.1 — what moved

Before this file, `PastaMsmScalarBound` §7.1's residual (1) read: *"the emitted adds are the
complete-addition FORMULA, and that the formula computes the Pallas group law is assumed, not
discharged."* Read carefully that named TWO things, and they have very different status:

  * **(a) the HYPOTHESES of RCB'15 Thm 1** — that the operands are points of the curve. These were
    not assumed by a proof, they were **not checked by anything**, and `PastaMsmWindowed` §6.3
    exhibited the forgery that fact permits. **(a) IS NOW FORCED**, by
    `fold_accumulator_is_a_curve_point` + `row_addend_is_a_curve_point` over the emitted gates, and
    the forgery is REFUSED by the deployed verifier (`circuit/tests/pasta_oncurve_gate.rs`).
  * **(b) the CONCLUSION of RCB'15 Thm 1** — that `rcbOutG`, at on-curve inputs, is a projective
    representative of the group sum. **(b) IS STILL INHERITED.** It is a cited theorem, not a
    machine-checked one.

So the transport is not discharged, and the honest one-line answer is that a verified proof of this
AIR constrains **a formula fold over CURVE POINTS** — not yet a group-law MSM, but no longer a fold
over arbitrary triples with a live absorbing-state escape.

### §5.2 — exactly what (b) needs, so the next lane does not have to re-derive it

Two objects, and neither is a gate:

  1. **A formal Pallas group law.** Mathlib's `WeierstrassCurve.Projective` carries an
     `AddCommGroup` on point classes; nothing in this tree instantiates it at `p`, `a = 0`, `b = 5`,
     and `PtP`/`rcbAddZmod` are this file family's own vocabulary. Instantiating it is ordinary work.
  2. **The identity itself, with a certificate.** `OnCurve(rcbOutG P Q)` must be shown to lie in the
     ideal generated by `OnCurve P` and `OnCurve Q`, and `rcbOutG P Q` shown to be a rescale of the
     mathlib sum. `rcbOutG`'s coordinates are degree 4 in the six inputs, so `Y₃²Z₃ − X₃³ − bZ₃³` is
     degree 12 in 6 variables: `ring` will not close it blind, and the discharge is a
     cofactor-certificate (`linear_combination` with explicitly computed `α`, `β`) produced OUTSIDE
     Lean and checked INSIDE it. **That is the shape of the work; it is not a proof this file
     deferred for lack of time, it is a distinct formalization.**

  ⚠ And one hypothesis of RCB completeness is NOT a gate and cannot become one: **Pallas has
  cofactor 1**. That is a fact about the curve's ORDER, inherited from `mina-curves`, not a property
  of a trace row. It is what makes "no affine point has `Y = 0`" true, and therefore what makes the
  emitted `nonZeroHead` a NON-DEGENERACY gate rather than an extra restriction that would refuse
  honest 2-torsion points on some other curve. Stated here so the reuse of this gadget on a
  cofactor > 1 curve is a visible error rather than a silent one.

### §5.3 — what this file does NOT touch, unchanged and named

  1. **ℤ ↔ felt (K1).** These theorems read a gate body as an INTEGER zero; the deployed prover
     reads it in BabyBear. Shared residual (`Dregg2/Bignum.lean`), unmoved.
  2. **P10, opening soundness.** Relation holding ≠ prover knowing. Untouched.
  3. **`gens` provenance.** That the manifest's generators are o1-labs' `srs.g` is the extractor's,
     checked differentially in `pasta_bound_sg_prove.rs`. ⚑ Note the gate does add something here:
     an off-curve DECLARED generator is now REFUSED BY THE AIR rather than only by a Rust test.
  4. **The LAST row's output.** `ACC` is gated on every row, and the emitted thread makes row `i`'s
     output row `i+1`'s `ACC` — so every output is gated except the final row's, whose value is not
     published (`PastaMsmSliced.outPiGates` binds the last row's `ACC`, which IS gated) and not
     consumed. Named rather than left to be discovered.
  5. **The `2^15`-term scale.** Unchanged by this rung: same rows, same manifest.
-/

end Dregg2.Circuit.Emit.PastaMsmOnCurve
