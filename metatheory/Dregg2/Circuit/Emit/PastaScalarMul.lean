/-
# Dregg2.Circuit.Emit.PastaScalarMul — the GLV scalar-mult ladder over the unified RCB complete add
(the `[k]P` primitive the IPA opening folds; task K4 of `docs/MINA-KIMCHI-VERIFIER-PLAN.md`).

## What this file IS

K4a (`PastaCurveComplete`, commit `fbdfad15c`) built the UNIFIED RCB complete-add gadget and FORCED
it (both curves) + completeness-KAT'd the exceptional cases. This file builds `[k]P` ON that gadget:
a **double-and-add ladder** where BOTH the double and the add are the SAME exception-free RCB
gadget (strong unification — `[2]acc` is `RCB(acc, acc)`), so there is NO case split at any step,
and the accumulator can START at the identity `O` (RCB is complete there). This is exactly kimi's
K4 decision (`docs/…PLAN.md` "K4 design": one unified gadget for double AND add).

The headline theorem is the **fold forcing** `pallasLadder_forces` — the ladder gadget's accepted
gates FORCE the accumulator columns to represent (projectively, in `ZMod p`) the reference
double-and-add fold of the digits, by a `List.range` induction that composes the per-step RCB
forcing (`PastaPoseidon.perm_forces` / `Sha256FoldForcing.foldl_cstep_forces` at curve-op
granularity). The single composable unit is `pallasRcbStep_forces`: one RCB step preserves the
point relation.

## GLV (the "as fast as possible" scalar mul)

K2 proved `φ(P) = [λ]·P` (`pallasEndo`, `φ(G) = λ·G` KAT) with `λ` a cube root of unity in the
scalar field. GLV decomposes `k ≡ k1 + k2·λ (mod r)` into two ~128-bit halves (`|k1|,|k2| ≈ √r ≈
2^127.5`; the lattice split is PROVER-side preprocessing, no gates), so `[k]P = [k1]P + [k2]φ(P)`
runs a JOINT (Shamir) ladder over 128 bits instead of 255 — half the serial doubling depth. This
file forces the ladder shape; the digit at each step is the selected combination of `{P, φ(P),
P+φ(P)}` (a Shamir window). For v1 the digits are threaded as represented inputs (`PointIsZ`
hypotheses), exactly as `perm_forces` threads the message words — the GLV lattice split + the
digit selection are named prover-side residuals (§6).

## Honest gate count

Per RCB add (K1 full generators): `12·559 (mul) + 2·280 (const-mul) + 14·281 (add) + 5·281 (sub)
≈ 12.6K` gates. Per ladder step = 1 double + 1 add = **2 RCB adds ≈ 25K** gates. So:
  * naive 255-bit double-and-add: `255·2·12.6K ≈ 6.4M` (a double AND a conditional add per bit);
  * GLV joint over 128 bits (Shamir, one add per step): `128·(12.6K + 12.6K) ≈ 3.2M`, and with the
    endo digit-precompute amortized ≈ **2.46M** (kimi's estimate) — the number this file's ladder
    realizes structurally. The endo `φ` costs ONE `fpMul` per digit (K2's `pallasEndoGadget`).

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard` KATs reduce in the kernel. NEW file; imports read-only
(`PastaCurveComplete`, transitively `PastaCurve`/`PastaField`); standalone (NOT imported by the
truncated `Dregg2` root; built directly as `Dregg2.Circuit.Emit.PastaScalarMul`).
-/
import Dregg2.Circuit.Emit.PastaCurveComplete

namespace Dregg2.Circuit.Emit.PastaScalarMul

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.PastaField (pN p qN fpVal gateBodyEvalZero acceptB bumpAt
  fpMulCore fpAddCore fpSubCore)
open Dregg2.Circuit.Emit.PastaCurve (CZp CZm Gp Gv GpJ GvJ curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete

set_option autoImplicit false

/-! ## §0 — The ring-generic RCB output (same formula as `rcbTraceZ.out`, over any `CommRing`).

Lets the forcing recast the ℤ-congruence conclusion of `pallasCompleteAdd_forces` into a `ZMod p`
equality the fold composes over. `rcbOutG_eq` pins it to the committed reference; `rcbOutG_cast` is
the ring-hom commute (the probe-verified `push_cast; ring`). -/

/-- The RCB Alg. 7 output `(X3, Y3, Z3)` as a ring expression (generic in `R`). -/
def rcbOutG {R : Type} [CommRing R] (b3 X1 Y1 Z1 X2 Y2 Z2 : R) : R × R × R :=
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
  (X3g, Y3f, Z3c)

/-- `rcbOutG` over ℤ IS the committed `rcbTraceZ.out` (definitional). -/
theorem rcbOutG_eq (b3 X1 Y1 Z1 X2 Y2 Z2 : ℤ) :
    rcbOutG b3 X1 Y1 Z1 X2 Y2 Z2 = (rcbTraceZ b3 X1 Y1 Z1 X2 Y2 Z2).out := rfl

/-- Abbrev: three `ZMod pN` coordinates. -/
abbrev PtP := ZMod pN × ZMod pN × ZMod pN

/-- The RCB add over `ZMod pN` (the reference the fold folds), constant `b3 = 15`. -/
def rcbAddZmod (P Q : PtP) : PtP :=
  rcbOutG ((curveB3 : Nat) : ZMod pN) P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2

/-! ## §1 — The point relation + the ZMod bridge. -/

/-- The three column groups `bx, by, bz` represent (in `ZMod pN`) the projective point `P`. -/
def PointIsZ (a : Assignment) (bX bY bZ : Nat) (P : PtP) : Prop :=
  ((fpVal a bX : ℤ) : ZMod pN) = P.1 ∧ ((fpVal a bY : ℤ) : ZMod pN) = P.2.1 ∧
  ((fpVal a bZ : ℤ) : ZMod pN) = P.2.2

/-- Bridge: `p ∣ u − v` IS `(v : ZMod pN) = (u : ZMod pN)` (`PastaPoseidon.zmod_eq_of_dvd`). -/
theorem zmod_eq_of_dvd {u v : ℤ} (h : (p : ℤ) ∣ u - v) : (v : ZMod pN) = (u : ZMod pN) := by
  rw [ZMod.intCast_eq_intCast_iff]; exact Int.modEq_iff_dvd.mpr h

/-! ## §2 — acceptB algebra (the `Sha256FoldForcing` discipline, re-derived over K1's `acceptB`). -/

theorem acceptB_append (l1 l2 : List VmConstraint2) (a : Assignment) :
    acceptB (l1 ++ l2) a = (acceptB l1 a && acceptB l2 a) := by simp [acceptB, List.all_append]
theorem acceptB_cons (g : VmConstraint2) (rest : List VmConstraint2) (a : Assignment) :
    acceptB (g :: rest) a = (gateBodyEvalZero a g && acceptB rest a) := by simp [acceptB]
theorem gateBodyEvalZero_cgH (a : Assignment) (h : Head) :
    gateBodyEvalZero a (cgH h) = decide (evalH h a = 0) := by
  simp only [cgH, cg, gateBodyEvalZero, headToExpr_eval]
theorem acceptB_prefix (l m : List VmConstraint2) (a : Assignment)
    (h : acceptB (l ++ m) a = true) : acceptB l a = true := by
  rw [acceptB_append, Bool.and_eq_true] at h; exact h.1
theorem acceptB_suffix (l m : List VmConstraint2) (a : Assignment)
    (h : acceptB (l ++ m) a = true) : acceptB m a = true := by
  rw [acceptB_append, Bool.and_eq_true] at h; exact h.2

/-! ## §3 — The step forcing: one RCB gadget preserves `PointIsZ` (the composable unit). -/

/-- **`pallasRcbStep_forces`** — the RCB complete-add gadget's accepted gates FORCE its output
columns to represent `rcbAddZmod P Q`, given its inputs represent `P` and `Q`. Wraps the committed
33-gate `pallasCompleteAdd_forces` (extracted from `acceptB`) through the `ZMod` bridge + the
ring-hom cast of the RCB formula. -/
theorem pallasRcbStep_forces (a : Assignment) (X1 Y1 Z1 X2 Y2 Z2 fresh : Nat) {P Q : PtP}
    (hP : PointIsZ a X1 Y1 Z1 P) (hQ : PointIsZ a X2 Y2 Z2 Q)
    (hacc : acceptB (pallasCompleteAdd X1 Y1 Z1 X2 Y2 Z2 fresh).1 a = true) :
    PointIsZ a (fresh + 234) (fresh + 261) (fresh + 288) (rcbAddZmod P Q) := by
  simp only [pallasCompleteAdd, swCompleteAddGadget, fpMulCore, fpAddCore, fpSubCore, fpSMulCore,
    acceptB, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    gateBodyEvalZero_cgH] at hacc
  obtain ⟨e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,e20,e21,e22,e23,
    e24,e25,e26,e27,e28,e29,e30,e31,e32⟩ := hacc
  obtain ⟨cX, cY, cZ⟩ := pallasCompleteAdd_forces a (of_decide_eq_true e0) (of_decide_eq_true e1)
    (of_decide_eq_true e2) (of_decide_eq_true e3) (of_decide_eq_true e4) (of_decide_eq_true e5)
    (of_decide_eq_true e6) (of_decide_eq_true e7) (of_decide_eq_true e8) (of_decide_eq_true e9)
    (of_decide_eq_true e10) (of_decide_eq_true e11) (of_decide_eq_true e12) (of_decide_eq_true e13)
    (of_decide_eq_true e14) (of_decide_eq_true e15) (of_decide_eq_true e16) (of_decide_eq_true e17)
    (of_decide_eq_true e18) (of_decide_eq_true e19) (of_decide_eq_true e20) (of_decide_eq_true e21)
    (of_decide_eq_true e22) (of_decide_eq_true e23) (of_decide_eq_true e24) (of_decide_eq_true e25)
    (of_decide_eq_true e26) (of_decide_eq_true e27) (of_decide_eq_true e28) (of_decide_eq_true e29)
    (of_decide_eq_true e30) (of_decide_eq_true e31) (of_decide_eq_true e32)
  obtain ⟨hPx, hPy, hPz⟩ := hP
  obtain ⟨hQx, hQy, hQz⟩ := hQ
  refine ⟨?_, ?_, ?_⟩
  · rw [(zmod_eq_of_dvd cX).symm]
    show (((rcbTraceZ (curveB3 : ℤ) (fpVal a X1) (fpVal a Y1) (fpVal a Z1)
            (fpVal a X2) (fpVal a Y2) (fpVal a Z2)).out.1 : ℤ) : ZMod pN) = (rcbAddZmod P Q).1
    rw [← rcbOutG_eq]
    show _ = (rcbOutG ((curveB3 : Nat) : ZMod pN) P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2).1
    rw [← hPx, ← hPy, ← hPz, ← hQx, ← hQy, ← hQz]
    simp only [rcbOutG]; push_cast; ring
  · rw [(zmod_eq_of_dvd cY).symm]
    show (((rcbTraceZ (curveB3 : ℤ) (fpVal a X1) (fpVal a Y1) (fpVal a Z1)
            (fpVal a X2) (fpVal a Y2) (fpVal a Z2)).out.2.1 : ℤ) : ZMod pN) = (rcbAddZmod P Q).2.1
    rw [← rcbOutG_eq]
    show _ = (rcbOutG ((curveB3 : Nat) : ZMod pN) P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2).2.1
    rw [← hPx, ← hPy, ← hPz, ← hQx, ← hQy, ← hQz]
    simp only [rcbOutG]; push_cast; ring
  · rw [(zmod_eq_of_dvd cZ).symm]
    show (((rcbTraceZ (curveB3 : ℤ) (fpVal a X1) (fpVal a Y1) (fpVal a Z1)
            (fpVal a X2) (fpVal a Y2) (fpVal a Z2)).out.2.2 : ℤ) : ZMod pN) = (rcbAddZmod P Q).2.2
    rw [← rcbOutG_eq]
    show _ = (rcbOutG ((curveB3 : Nat) : ZMod pN) P.1 P.2.1 P.2.2 Q.1 Q.2.1 Q.2.2).2.2
    rw [← hPx, ← hPy, ← hPz, ← hQx, ← hQy, ← hQz]
    simp only [rcbOutG]; push_cast; ring

/-! ## §4 — The ladder: `List.range` fold of (double via strong unification, add the digit). -/

/-- One ladder step: double `acc` (`RCB(acc, acc)`), then add the digit `dg` (`RCB(dbl, dg)`).
Two RCB complete-add gadgets, exception-free. Returns (gates, new-acc-bases, next-fresh). -/
def ladderStep (accX accY accZ dgX dgY dgZ fresh : Nat) :
    List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  let dbl := pallasCompleteAdd accX accY accZ accX accY accZ fresh
  let add := pallasCompleteAdd (fresh + 234) (fresh + 261) (fresh + 288) dgX dgY dgZ (fresh + 442)
  (dbl.1 ++ add.1, add.2.1, add.2.2)

/-- The fold body over `List.range` (digit index `i`; digit bases from `digitBases.getD i`). -/
def dstep (digitBases : List (Nat × Nat × Nat)) :
    List VmConstraint2 × (Nat × Nat × Nat) × Nat → Nat →
    List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  fun st i =>
    let dg := digitBases.getD i (0, 0, 0)
    let step := ladderStep st.2.1.1 st.2.1.2.1 st.2.1.2.2 dg.1 dg.2.1 dg.2.2 st.2.2
    (st.1 ++ step.1, step.2.1, step.2.2)

/-- The whole ladder's gates over `n` digits (start acc `acc0`, first fresh `fresh0`). -/
def ladderGatesFrom (digitBases : List (Nat × Nat × Nat)) (n : Nat)
    (acc0 : Nat × Nat × Nat) (fresh0 : Nat) : List VmConstraint2 × (Nat × Nat × Nat) × Nat :=
  (List.range n).foldl (dstep digitBases) ([], acc0, fresh0)

/-- The reference double-and-add fold over `ZMod pN` (`acc ↦ RCB(RCB(acc,acc), digit)`). -/
def ladderRefFrom (digitVals : List PtP) (n : Nat) (acc0 : PtP) : PtP :=
  (List.range n).foldl (fun acc i => rcbAddZmod (rcbAddZmod acc acc) (digitVals.getD i (0,0,0))) acc0

/-! ## §5 — The FOLD FORCING (mirror `Sha256FoldForcing.foldl_cstep_forces`). -/

/-- The accumulated constraints keep the starting list as a prefix. -/
theorem dstep_prefix (digitBases : List (Nat × Nat × Nat)) : ∀ (ts : List Nat)
    (X : List VmConstraint2) (acc : Nat × Nat × Nat) (fr : Nat),
    ∃ Y, (ts.foldl (dstep digitBases) (X, acc, fr)).1 = X ++ Y := by
  intro ts
  induction ts with
  | nil => intro X acc fr; exact ⟨[], by simp⟩
  | cons t rest ih =>
    intro X acc fr
    rw [List.foldl_cons]
    obtain ⟨Y, hY⟩ := ih (dstep digitBases (X, acc, fr) t).1 (dstep digitBases (X, acc, fr) t).2.1
      (dstep digitBases (X, acc, fr) t).2.2
    refine ⟨(ladderStep acc.1 acc.2.1 acc.2.2 (digitBases.getD t (0,0,0)).1
      (digitBases.getD t (0,0,0)).2.1 (digitBases.getD t (0,0,0)).2.2 fr).1 ++ Y, ?_⟩
    rw [show (dstep digitBases (X, acc, fr) t) = ((dstep digitBases (X, acc, fr) t).1,
        (dstep digitBases (X, acc, fr) t).2.1, (dstep digitBases (X, acc, fr) t).2.2) from rfl] at hY
    rw [hY]; dsimp only [dstep, ladderStep]; rw [List.append_assoc]

/-- **The `n`-digit fold forces the reference ladder** — by induction over the digit-index list,
composing `pallasRcbStep_forces` twice per step (double + add). -/
theorem foldl_dstep_forces (a : Assignment) (digitBases : List (Nat × Nat × Nat))
    (digitVals : List PtP) :
    ∀ (ts : List Nat) (cs0 : List VmConstraint2) (acc0 : Nat × Nat × Nat) (fr0 : Nat) (av0 : PtP),
      PointIsZ a acc0.1 acc0.2.1 acc0.2.2 av0 →
      (∀ t ∈ ts, PointIsZ a (digitBases.getD t (0,0,0)).1 (digitBases.getD t (0,0,0)).2.1
        (digitBases.getD t (0,0,0)).2.2 (digitVals.getD t (0,0,0))) →
      acceptB ((ts.foldl (dstep digitBases) (cs0, acc0, fr0)).1) a = true →
      PointIsZ a (ts.foldl (dstep digitBases) (cs0, acc0, fr0)).2.1.1
        (ts.foldl (dstep digitBases) (cs0, acc0, fr0)).2.1.2.1
        (ts.foldl (dstep digitBases) (cs0, acc0, fr0)).2.1.2.2
        (ts.foldl (fun acc i => rcbAddZmod (rcbAddZmod acc acc) (digitVals.getD i (0,0,0))) av0) := by
  intro ts
  induction ts with
  | nil => intro cs0 acc0 fr0 av0 hacc0 _ _; exact hacc0
  | cons t rest ih =>
    intro cs0 acc0 fr0 av0 hav0 hD hacc
    rw [List.foldl_cons] at hacc ⊢
    rw [List.foldl_cons]
    set dg := digitBases.getD t (0,0,0) with hdg
    set stepGates := (ladderStep acc0.1 acc0.2.1 acc0.2.2 dg.1 dg.2.1 dg.2.2 fr0).1 with hsg
    have hstep : dstep digitBases (cs0, acc0, fr0) t
        = (cs0 ++ stepGates,
           (ladderStep acc0.1 acc0.2.1 acc0.2.2 dg.1 dg.2.1 dg.2.2 fr0).2.1,
           (ladderStep acc0.1 acc0.2.1 acc0.2.2 dg.1 dg.2.1 dg.2.2 fr0).2.2) := rfl
    rw [hstep] at hacc ⊢
    -- extract acceptance of this step's gates
    obtain ⟨Y, hY⟩ := dstep_prefix digitBases rest (cs0 ++ stepGates) _ _
    have haccStep : acceptB stepGates a = true := by
      have h1 : acceptB (cs0 ++ stepGates) a = true :=
        acceptB_prefix (cs0 ++ stepGates) Y a (by rw [hY] at hacc; exact hacc)
      exact acceptB_suffix cs0 stepGates a h1
    -- the two RCB gadgets of the step
    have haccDbl : acceptB (pallasCompleteAdd acc0.1 acc0.2.1 acc0.2.2 acc0.1 acc0.2.1 acc0.2.2 fr0).1 a = true := by
      rw [hsg, ladderStep] at haccStep; exact acceptB_prefix _ _ a haccStep
    have haccAdd : acceptB (pallasCompleteAdd (fr0+234) (fr0+261) (fr0+288) dg.1 dg.2.1 dg.2.2 (fr0+442)).1 a = true := by
      rw [hsg, ladderStep] at haccStep; exact acceptB_suffix _ _ a haccStep
    -- double: acc0 (= av0) doubled
    have hdbl := pallasRcbStep_forces a acc0.1 acc0.2.1 acc0.2.2 acc0.1 acc0.2.1 acc0.2.2 fr0 hav0 hav0 haccDbl
    -- add: (double) + digit
    have hdgv : PointIsZ a dg.1 dg.2.1 dg.2.2 (digitVals.getD t (0,0,0)) := hD t List.mem_cons_self
    have hadd := pallasRcbStep_forces a (fr0+234) (fr0+261) (fr0+288) dg.1 dg.2.1 dg.2.2 (fr0+442)
      hdbl hdgv haccAdd
    -- the step's output acc bases are (fr0+442+234, +261, +288)
    have hnext : PointIsZ a
        (ladderStep acc0.1 acc0.2.1 acc0.2.2 dg.1 dg.2.1 dg.2.2 fr0).2.1.1
        (ladderStep acc0.1 acc0.2.1 acc0.2.2 dg.1 dg.2.1 dg.2.2 fr0).2.1.2.1
        (ladderStep acc0.1 acc0.2.1 acc0.2.2 dg.1 dg.2.1 dg.2.2 fr0).2.1.2.2
        (rcbAddZmod (rcbAddZmod av0 av0) (digitVals.getD t (0,0,0))) := hadd
    exact ih (cs0 ++ stepGates) _ _ _ hnext
      (fun t' ht' => hD t' (List.mem_cons_of_mem t ht')) hacc

/-- **`pallasLadder_forces`** — the whole ladder's accepted gates FORCE the accumulator to represent
the reference double-and-add fold of the digits, in `ZMod pN`. The `perm_forces` analog for the
Pasta scalar-mult ladder: gate-count-independent, composed from the per-step RCB forcing. -/
theorem pallasLadder_forces (a : Assignment) (digitBases : List (Nat × Nat × Nat))
    (digitVals : List PtP) (n : Nat) (acc0 : Nat × Nat × Nat) (fresh0 : Nat) (av0 : PtP)
    (hav0 : PointIsZ a acc0.1 acc0.2.1 acc0.2.2 av0)
    (hD : ∀ t < n, PointIsZ a (digitBases.getD t (0,0,0)).1 (digitBases.getD t (0,0,0)).2.1
      (digitBases.getD t (0,0,0)).2.2 (digitVals.getD t (0,0,0)))
    (hacc : acceptB (ladderGatesFrom digitBases n acc0 fresh0).1 a = true) :
    PointIsZ a (ladderGatesFrom digitBases n acc0 fresh0).2.1.1
      (ladderGatesFrom digitBases n acc0 fresh0).2.1.2.1
      (ladderGatesFrom digitBases n acc0 fresh0).2.1.2.2
      (ladderRefFrom digitVals n av0) :=
  foldl_dstep_forces a digitBases digitVals (List.range n) [] acc0 fresh0 av0 hav0
    (fun t ht => hD t (List.mem_range.mp ht)) hacc

#assert_axioms rcbOutG_eq
#assert_axioms zmod_eq_of_dvd
#assert_axioms pallasRcbStep_forces
#assert_axioms foldl_dstep_forces
#assert_axioms pallasLadder_forces

/-! ## §6 — The `Nat` reference ladder + KATs: `[k]G` vs K2's already-verified scalar mul.

The reference `scMulLadderM` is the SAME double-and-add fold (over `rcbAddM`), starting at `O`, with
digits `= if bit then G else O`. KAT: it equals K2's Jacobian `[k]G` (`Gp2`/`Gp3` and
`PastaCurve.scMulM`) via `projJacEqM`, for small `k` on both curves. -/

open Dregg2.Circuit.Emit.PastaCurve (Gp2 Gp3 Gv2 Gv3)

/-- `Nat` ladder over explicit digit points (per-op reduced mod `m`). -/
def ladderM (m b3 : Nat) (digits : List (Nat × Nat × Nat)) (acc0 : Nat × Nat × Nat) :
    Nat × Nat × Nat :=
  digits.foldl (fun acc d => rcbAddM m b3 (rcbAddM m b3 acc acc) d) acc0

/-- The `nbits` digits of `k` (MSB first): `G` where the bit is set, else `O`. -/
def kDigits (k : Nat) (P : Nat × Nat × Nat) (nbits : Nat) : List (Nat × Nat × Nat) :=
  (List.range nbits).reverse.map (fun i => if k.testBit i then P else Oproj)

/-- `[k]·P` by the RCB double-and-add ladder over `nbits`, starting at `O`. -/
def scMulLadderM (m b3 k : Nat) (P : Nat × Nat × Nat) (nbits : Nat) : Nat × Nat × Nat :=
  ladderM m b3 (kDigits k P nbits) Oproj

/-- `G` in projective coords. -/
def GpP : Nat × Nat × Nat := (Gp.1, Gp.2, 1)
def GvP : Nat × Nat × Nat := (Gv.1, Gv.2, 1)

-- `[2]G`, `[3]G` equal K2's Jacobian `Gp2`/`Gp3` (both curves).
#guard projJacEqM pN (scMulLadderM pN curveB3 2 GpP 8) Gp2 == true
#guard projJacEqM pN (scMulLadderM pN curveB3 3 GpP 8) Gp3 == true
#guard projJacEqM qN (scMulLadderM qN curveB3 2 GvP 8) Gv2 == true
#guard projJacEqM qN (scMulLadderM qN curveB3 3 GvP 8) Gv3 == true
-- `[5]G`, `[7]G` equal K2's 255-bit Jacobian `scMulM` (independent double-and-add).
#guard projJacEqM pN (scMulLadderM pN curveB3 5 GpP 8) ((Dregg2.Circuit.Emit.PastaCurve.scMulM pN 5 GpJ).getD (0,0,0)) == true
#guard projJacEqM pN (scMulLadderM pN curveB3 7 GpP 8) ((Dregg2.Circuit.Emit.PastaCurve.scMulM pN 7 GpJ).getD (0,0,0)) == true
#guard projJacEqM qN (scMulLadderM qN curveB3 5 GvP 8) ((Dregg2.Circuit.Emit.PastaCurve.scMulM qN 5 GvJ).getD (0,0,0)) == true
-- the ladder output stays on the curve; negative control: `[5]G ≠ [3]G`.
#guard projOnCurveM pN curveB (scMulLadderM pN curveB3 5 GpP 8) == true
#guard projJacEqM pN (scMulLadderM pN curveB3 5 GpP 8) Gp3 == false

/-! ## §7 — Structural `#guard`s (the ladder is the fold of the RCB gadget) + AIR packaging. -/

-- Per step = 2 RCB gadgets = 66 core gates; the double reads acc, the add reads the digit.
#guard (ladderStep 0 9 18 27 36 45 54).1.length == 66
#guard (ladderStep 0 9 18 27 36 45 54).2.2 == 54 + 884             -- 884 fresh columns per step
#guard (ladderStep 0 9 18 27 36 45 54).2.1 == (54 + 442 + 234, 54 + 442 + 261, 54 + 442 + 288)
-- A 4-digit ladder: 4·66 = 264 core gates.
#guard (ladderGatesFrom [(100,109,118),(127,136,145),(154,163,172),(181,190,199)] 4 (0,9,18) 300).1.length == 264

/-- A single ladder STEP (double + add) packaged as an `EffectVmDescriptor2`. -/
def ladderStepDesc : EffectVmDescriptor2 :=
  { name        := "dregg-pasta-scalarmul-step::demo"
  , traceWidth  := 54 + 884
  , piCount     := 0
  , tables      := []
  , constraints := (ladderStep 0 9 18 27 36 45 54).1
  , hashSites   := []
  , ranges      := [] }

#guard ladderStepDesc.constraints.length == 66

/-! ## §8 — The PRECISE named residuals (toward K5).

  1. **The GLV lattice split + digit selection are PROVER-SIDE, not forced here.** The forcing
     threads the digits as REPRESENTED inputs (`PointIsZ` hypotheses), exactly as `perm_forces`
     threads the message words. Which combination of `{P, φ(P), P+φ(P)}` each digit is (the Shamir
     window over the two half-scalars `k1, k2`) — and that `k = k1 + k2·λ` — is prover-side
     preprocessing; a verifier that must CHECK the decomposition needs the endo-scalar recomposition
     gate (K2's `pallasEndo` forces `φ(P) = ζ·P`; `to_field(endo_r)` is the 128-bit challenge map,
     K3's transcript). Named, not built.
  2. **The `[k]P = [k]G` identity is at the REFERENCE level (KAT), the FORCING is to the RCB
     formula-fold.** `pallasLadder_forces` proves the gates force the `rcbAddZmod`-fold of the
     digits; that this fold IS `[k]P` as a group element rests on RCB completeness (K4a's inherited
     residual — RCB'15 Thm 1) applied at each step. The KATs (`scMulLadderM … == [k]G`) close the
     small-`k` cases concretely, cross-tied to K2's verified points.
  3. **Vesta ladder forcing is NOT built** (only the Nat KAT). `pallasLadder_forces` is Pallas
     (mod `p`); the Vesta ladder forcing is the identical construction over `vestaCompleteAdd` +
     `ZMod qN` — a mechanical mirror, named for the side the Kimchi wrap actually needs.
  4. **The shared K1/K2 residuals** — the `z < p` canonical compare, the `ℤ ↔ p_felt` field-width
     gap, inherited modulus primality/cofactor-1 — stand unchanged.

CONTINUATION: `PastaIPA` folds this scalar mul over the log(n) IPA rounds (each round: 2 EC ops for
`Lᵢ/Rᵢ` + the Poseidon challenge (K3) + the `(endo_q, endo_r)` fold), and DEFERS the `2^k`-element
`⟨s, G⟩` MSM as an accumulated obligation (the ~10⁸-gate check, done once outside recursion).
-/

end Dregg2.Circuit.Emit.PastaScalarMul
