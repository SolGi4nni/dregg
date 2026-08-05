/-
# `Dregg2.Circuit.Emit.PastaLadderThread` — the sound RCB accumulator THREADED ACROSS ROWS, and the
composition theorem a thread buys that a re-pin does not.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every column index, every window body and the emitted descriptor are
authored here and go through `EffectLower.lowerAir` of an `EffectAirIR.EffectAir`. There is no
hand-written `VmConstraint2` in this file. Rust PROVES the artifact and authors no constraint.
House Law #1.

## THE BLOCKER THIS CLOSES, quoted from the file that raised it

`PastaCurveSound.lean:1057-1067`:

> *"⚑ **WHAT BLOCKS IT IS THE LAYOUT, AND THE NUMBER SAYS SO.** `PastaMsmAir.ladderGatesFrom_counts`
> proves the ladder is ROW-LOCAL: `66·n` gates and `884·n` FRESH COLUMNS, all in ONE row. On the
> sound gate a step is `2 · 4 284 = 8 568` constraints and `2 · 2 856 = 5 712` columns, so a
> 128-step GLV joint ladder is **731 136 columns in a single row** … So a sound ladder needs the
> accumulator threaded ACROSS rows through an `AirLeg.window .transition` gate."*

`sound_ladder_does_not_fit_a_row` is that wall as a number. This file is the other side of it: the
accumulator is threaded, so **depth is ROWS and the width is a CONSTANT `3 048` at every depth**
(`threaded_width_is_flat`). The row-local ladder's `731 136` columns at GLV depth become `3 048`
columns × `256` rows, and `the_thread_is_what_makes_it_fit` states both halves against the deployed
geometry rather than describing them.

⚠ **AND THE SAME WALL WAS ALREADY BLOCKING A SHIPPED DESCRIPTOR.** `Dregg2.lean:1677` records that
`PastaMsmAir.minaOpeningCheckDesc` — the bulletproof opening check — **would be refused by the
deployed prover**: `traceWidth := 442` while its constraints address columns near `10^7`, and
`circuit/src/descriptor_ir2.rs:1555` rejects `column ≥ trace_width`. That refusal is the row-local
layout, not the arithmetic. A threaded accumulator is the shape that answers it.

## ⚑ WHAT A THREAD ESTABLISHES THAT A RE-PIN DOES NOT

The lesson this campaign already paid for, from the phase-2 chain: *"a fold that just re-pins the
same public inputs closes nothing; the chain must carry state from leaf i to leaf i+1 INSIDE the
recursion."* The AIR-level form of that distinction is exactly the difference between

* pinning row `r+1`'s accumulator input to a **public input** — which forces nothing about row `r`,
  because a prover picks the public input; and
* a `.transition` window gate `nxt(ACC + i) − loc(OUT + i) = 0` — which is checked **between**
  the two rows by the same constraint system that checks each row.

`threadedLadder_forces` is the theorem that the second one composes: `n` rows of DEPLOYED
satisfaction plus `n` threads force the accumulator at row `n` to be congruent to the `n`-fold RCB
chain of the per-row addends. No row's output is ever quoted; each is *forced*, and the thread is
what carries the forcing forward.

## ⚑ THE ENABLING LEMMA, and it did not exist

`pallasCompleteAddSound_forces` concludes a CONGRUENCE (`CZp out (rcbTraceZ … in)`), not an
equality. Chaining `n` of them needs `rcbTraceZ` to RESPECT that congruence — if row `r`'s
accumulator is only congruent to the chain value, row `r+1`'s output is congruent to the chain's
next value only because the RCB formula is a polynomial. `rcbTraceZ_congr` is that fact, and it is
the whole reason the induction closes. It is proved from `CZm.add`/`CZm.sub`/`CZm.mul` alone —
`rcbTraceZ` has no division, which is the property that makes a COMPLETE addition formula
threadable at all.

## What is proved here

* `rcbTraceZ_congr` — the RCB formula respects congruence in all six coordinates.
* `threadedLadder_forces` — the `n`-row induction: rows satisfied + threads held ⟹ the accumulator
  is the `n`-fold chain, mod the real Pallas prime.
* `threaded_width_is_flat` / `the_thread_is_what_makes_it_fit` — the layout facts, as numbers.
* `pallasThreadAir_mainRailOk`, and the shape census (`pallasThreadAir_window_selectors`) so a
  `.transition → .all` re-scope, which accepts strictly more, moves a number.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`; zero `#guard`s.
-/
import Dregg2.Circuit.Emit.PastaCurveSound

namespace Dregg2.Circuit.Emit.PastaLadderThread

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 TableDef WindowExpr VmConstraint2)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg WindowLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.EffectLower (lowerAir)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK sVal pLimb)
open Dregg2.Circuit.Emit.PastaCurve (CZm CZp)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3 rcbTraceZ)
open Dregg2.Circuit.Emit.PastaCurveSound

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## §1 — THE ROW, and the two blocks the thread ties.

One row is ONE sound RCB complete addition — `PastaCurveSound`'s row, unmoved, so `RCB_WIDTH`,
`rcbTables`, `pallasCompleteAddSoundLegs` and `pallasCompleteAddSound_forces` are all inherited
rather than re-derived. What is new is the pair of column ROLES:

* the three input blocks at `0, SK, 2·SK` are the **accumulator in**;
* the three at `3·SK, 4·SK, 5·SK` are the **addend** — a fresh, range-checked witness each row;
* `vBase IN_BASE 26/29/32` are `(X3, Y3, Z3)`, the **accumulator out**.

The thread says the first is the third, one row down. -/

/-- The accumulator's X block on the row's input side. -/
def ACC_X : Nat := 0
/-- …Y. -/
def ACC_Y : Nat := SK
/-- …Z. -/
def ACC_Z : Nat := 2 * SK

/-- The addend's X block. -/
def ADD_X : Nat := 3 * SK
/-- …Y. -/
def ADD_Y : Nat := 4 * SK
/-- …Z. -/
def ADD_Z : Nat := 5 * SK

/-- `X3` — the SSA intermediate `v 26` the gadget names as the result's X. -/
def OUT_X : Nat := vBase IN_BASE 26
/-- `Y3` — `v 29`. -/
def OUT_Y : Nat := vBase IN_BASE 29
/-- `Z3` — `v 32`. -/
def OUT_Z : Nat := vBase IN_BASE 32

theorem out_bases_eq : OUT_X = 1024 ∧ OUT_Y = 1120 ∧ OUT_Z = 1216 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §2 — ⚑ THE THREAD.

`nxt(dst + i) − loc(src + i) = 0` under `RowSel.transition`, one leg per limb. `.transition` is the
ONLY selector under which `nxt` is the genuine successor (`WindowLeg.mainRailOk`); under `.all` the
last row's `nxt` is the WRAP row, so an every-row thread would say something different exactly where
padding hides. The census theorem below is what keeps that honest. -/

/-- One carry leg: the `i`-th limb of the block at `dst` on the NEXT row is the `i`-th limb of the
block at `src` on THIS row. -/
def carryLeg (dst src i : Nat) : AirLeg :=
  .window ⟨RowSel.transition,
    .add (.nxt (dst + i)) (.mul (.const (-1)) (.loc (src + i)))⟩

/-- ⚑ **THE 96 TRANSITION LEGS** — three coordinates × `SK = 32` limbs. This is the whole thread,
and `96` is the same width the phase-2 chain carries its state on (`45 × 96` in-circuit connects):
a projective Pasta point in the sound encoding is 96 felts either way. -/
def threadLegs : List AirLeg :=
  (List.range SK).flatMap (fun i =>
    [carryLeg ACC_X OUT_X i, carryLeg ACC_Y OUT_Y i, carryLeg ACC_Z OUT_Z i])

theorem threadLegs_length : threadLegs.length = 96 := by decide

/-! ## §3 — THE AIR, and the width fact that is the point of the file. -/

/-- **The threaded sound Pallas RCB row.** The standalone row's legs, plus the thread. -/
def pallasThreadAir : EffectAir :=
  { tables := rcbTables
  , legs := inputLimbLegs
      ++ (pallasCompleteAddSoundLegs ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE).1
      ++ threadLegs }

/-- …and the Vesta twin, because the accumulator leg is Step/Tick on Vesta. -/
def vestaThreadAir : EffectAir :=
  { tables := rcbTables
  , legs := inputLimbLegs
      ++ (vestaCompleteAddSoundLegs ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE).1
      ++ threadLegs }

/-- ⚑ **THE COMPILER ACCEPTS THE THREADED BLOCK.** Every window leg is `.transition`, which is the
one selector that admits a `nxt` read; a `.first`/`.last`/`.all` thread would lower to
`refuseConstraints` and this would be false. -/
theorem pallasThreadAir_mainRailOk : pallasThreadAir.mainRailOk = true := by decide

theorem vestaThreadAir_mainRailOk : vestaThreadAir.mainRailOk = true := by decide

/-- ⚑ **THE SELECTOR CENSUS.** All 96 window legs are `.transition` and NONE is `.all`. A
`.transition → .all` re-scope is byte-identical algebra that accepts STRICTLY MORE
(`TableAirIR.TableGate.transition_strictly_weaker`), so it is invisible to a gate count and visible
here. -/
theorem pallasThreadAir_window_selectors :
    pallasThreadAir.windowCountSel RowSel.transition = 96
    ∧ pallasThreadAir.windowCountSel RowSel.all = 0
    ∧ pallasThreadAir.windowCountSel RowSel.first = 0
    ∧ pallasThreadAir.windowCountSel RowSel.last = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The emitted descriptors. `RCB_WIDTH = 3 048` — the SAME width as the standalone row, at every
ladder depth, because the depth is rows. -/
def pallasThreadDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-pasta-pallas-rcb-thread::v1" RCB_WIDTH 0 [] pallasThreadAir

def vestaThreadDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-pasta-vesta-rcb-thread::v1" RCB_WIDTH 0 [] vestaThreadAir

/-- The threaded row is the standalone row plus exactly 96 constraints — the 4 476 the sound row
already measured, and one window gate per threaded limb. -/
theorem pallasThreadDesc_constraint_count :
    pallasThreadDesc.constraints.length = 4476 + 96 := by decide

theorem vestaThreadDesc_constraint_count :
    vestaThreadDesc.constraints.length = 4476 + 96 := by decide

theorem pallasThreadDesc_width : pallasThreadDesc.traceWidth = 3048 := rfl
theorem vestaThreadDesc_width : vestaThreadDesc.traceWidth = 3048 := rfl

/-! ## §4 — ⚑ THE LAYOUT FACT, as numbers rather than as a worry.

`sound_ladder_does_not_fit_a_row` prices the row-local sound ladder at GLV depth: `731 136` columns
in ONE row. The threaded ladder's width does not depend on the depth at all. -/

/-- The row-local sound ladder's width at depth `n` (`PastaCurveSound.SOUND_LADDER_STEP_COLUMNS`
per step, all in one row). -/
def rowLocalLadderWidth (n : Nat) : Nat := n * SOUND_LADDER_STEP_COLUMNS

/-- The threaded ladder's width at depth `n` — the row width, whatever `n` is. -/
def threadedLadderWidth (_n : Nat) : Nat := RCB_WIDTH

/-- Rows the threaded ladder needs at depth `n`: two complete adds a ladder step, one per row. -/
def threadedLadderRows (n : Nat) : Nat := 2 * n

/-- ⚑ **THE WIDTH IS FLAT.** Not "smaller" — INDEPENDENT of the depth, which is the property a
`.transition` thread buys and a wider row never can. -/
theorem threaded_width_is_flat : ∀ n : Nat, threadedLadderWidth n = 3048 := fun _ => rfl

/-- ⚑ **THE THREAD IS WHAT MAKES IT FIT**, at the GLV depth the wall was priced at.

`731 136` columns in one row against `3 048` columns × `256` rows — and the deployed
`pasta_derive_prove` measures `2 131` columns, so the row-local figure is `343×` past a measured
descriptor and the threaded one is inside `1.5×` of it. -/
theorem the_thread_is_what_makes_it_fit :
    rowLocalLadderWidth GLV_STEPS = 731136
    ∧ threadedLadderWidth GLV_STEPS = 3048
    ∧ threadedLadderRows GLV_STEPS = 256
    -- the row-local layout is 239× wider than the threaded one at this depth
    ∧ 239 * threadedLadderWidth GLV_STEPS < rowLocalLadderWidth GLV_STEPS
    ∧ rowLocalLadderWidth GLV_STEPS < 240 * threadedLadderWidth GLV_STEPS := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **AND THE CELL COUNT IS THE SAME TRADE, NOT A SAVING.** Threading moves the work from columns
to rows; it does not remove it. The threaded ladder's cells at GLV depth are `3 048 × 256`, which is
MORE than the row-local `731 136` — because every row re-pays the six input range blocks. Saying so
is the difference between a layout fact and a cost claim. -/
theorem threading_trades_columns_for_rows_and_cells :
    threadedLadderWidth GLV_STEPS * threadedLadderRows GLV_STEPS = 780288
    ∧ rowLocalLadderWidth GLV_STEPS < threadedLadderWidth GLV_STEPS * threadedLadderRows GLV_STEPS
    := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §5 — ⚑ THE ENABLING LEMMA: the RCB formula respects congruence.

`pallasCompleteAddSound_forces` gives `CZp out (rcbTraceZ … in)`. To chain it the formula must send
congruent inputs to congruent outputs — otherwise row `r+1`'s conclusion is about a different point
than row `r`'s. `rcbTraceZ` is built from `+`, `−`, `·` and nothing else (there is no inversion in a
complete addition formula), so the three `CZm` homomorphism lemmas are the whole proof. -/

/-- The projective triple a complete addition produces. -/
def rcbOutZ (b3 X1 Y1 Z1 X2 Y2 Z2 : ℤ) : ℤ × ℤ × ℤ :=
  let T := rcbTraceZ b3 X1 Y1 Z1 X2 Y2 Z2
  (T.X3g, T.Y3f, T.Z3c)

/-- Congruence of a projective triple, coordinatewise. -/
def CZ3 (m : ℤ) (P Q : ℤ × ℤ × ℤ) : Prop :=
  CZm m P.1 Q.1 ∧ CZm m P.2.1 Q.2.1 ∧ CZm m P.2.2 Q.2.2

theorem CZ3.refl {m : ℤ} (P : ℤ × ℤ × ℤ) : CZ3 m P P :=
  ⟨CZm.refl _, CZm.refl _, CZm.refl _⟩

theorem CZ3.trans {m : ℤ} {P Q R : ℤ × ℤ × ℤ} (h1 : CZ3 m P Q) (h2 : CZ3 m Q R) : CZ3 m P R :=
  ⟨CZm.trans h1.1 h2.1, CZm.trans h1.2.1 h2.2.1, CZm.trans h1.2.2 h2.2.2⟩

/-- ⚑ **`rcbTraceZ_congr`** — the RCB complete addition respects congruence in all six coordinates.

This is what a COMPLETE formula gives and an incomplete one does not: no branch, no inversion, so
the output is a polynomial in the inputs and a ring congruence passes straight through it. It is the
lemma the threaded induction turns on. -/
theorem rcbTraceZ_congr {m : ℤ} (b3 : ℤ) {X1 Y1 Z1 X2 Y2 Z2 X1' Y1' Z1' X2' Y2' Z2' : ℤ}
    (hX1 : CZm m X1 X1') (hY1 : CZm m Y1 Y1') (hZ1 : CZm m Z1 Z1')
    (hX2 : CZm m X2 X2') (hY2 : CZm m Y2 Y2') (hZ2 : CZm m Z2 Z2') :
    CZ3 m (rcbOutZ b3 X1 Y1 Z1 X2 Y2 Z2) (rcbOutZ b3 X1' Y1' Z1' X2' Y2' Z2') := by
  -- Every intermediate of `rcbTraceZ`, in SSA order, congruence-transported.
  have rb3 : CZm m b3 b3 := CZm.refl _
  have t0a := CZm.mul hX1 hX2
  have t1a := CZm.mul hY1 hY2
  have t2a := CZm.mul hZ1 hZ2
  have t3a := CZm.add hX1 hY1
  have t4a := CZm.add hX2 hY2
  have t3b := CZm.mul t3a t4a
  have t4b := CZm.add t0a t1a
  have t3c := CZm.sub t3b t4b
  have t4c := CZm.add hY1 hZ1
  have X3a := CZm.add hY2 hZ2
  have t4d := CZm.mul t4c X3a
  have X3b := CZm.add t1a t2a
  have t4e := CZm.sub t4d X3b
  have X3c := CZm.add hX1 hZ1
  have Y3a := CZm.add hX2 hZ2
  have X3d := CZm.mul X3c Y3a
  have Y3b := CZm.add t0a t2a
  have Y3c := CZm.sub X3d Y3b
  have X3e := CZm.add t0a t0a
  have t0b := CZm.add X3e t0a
  have t2b := CZm.mul rb3 t2a
  have Z3a := CZm.add t1a t2b
  have t1b := CZm.sub t1a t2b
  have Y3d := CZm.mul rb3 Y3c
  have X3f := CZm.mul t4e Y3d
  have t2c := CZm.mul t3c t1b
  have X3g := CZm.sub t2c X3f
  have Y3e := CZm.mul Y3d t0b
  have t1c := CZm.mul t1b Z3a
  have Y3f := CZm.add t1c Y3e
  have t0c := CZm.mul t0b t3c
  have Z3b := CZm.mul Z3a t4e
  have Z3c := CZm.add Z3b t0c
  exact ⟨X3g, Y3f, Z3c⟩

/-! ## §6 — ⚑ THE THREADED CHAIN, and what its satisfaction forces.

A TRACE is `Nat → Assignment`: row `r`'s columns are `tr r`. That is the shape the deployed prover
fills and the shape `.transition` reads two of at a time. -/

/-- A multi-row trace: row index to that row's column assignment. -/
abbrev Trace := Nat → Assignment

/-- The accumulator this trace carries INTO row `r`. -/
def accIn (tr : Trace) (r : Nat) : ℤ × ℤ × ℤ :=
  (sVal (tr r) ACC_X, sVal (tr r) ACC_Y, sVal (tr r) ACC_Z)

/-- The addend row `r` adds. -/
def addend (tr : Trace) (r : Nat) : ℤ × ℤ × ℤ :=
  (sVal (tr r) ADD_X, sVal (tr r) ADD_Y, sVal (tr r) ADD_Z)

/-- The accumulator row `r` produces. -/
def accOut (tr : Trace) (r : Nat) : ℤ × ℤ × ℤ :=
  (sVal (tr r) OUT_X, sVal (tr r) OUT_Y, sVal (tr r) OUT_Z)

/-- ⚑ **THE THREAD, AS THE PROVER SATISFIES IT.** The 96 `.transition` window bodies vanish between
rows `r` and `r+1` exactly when every limb of the next row's accumulator input equals the matching
limb of this row's output. This is `carryLeg`'s body read as a fact about the trace. -/
def Threaded (tr : Trace) (r : Nat) : Prop :=
  ∀ i, i < SK →
    tr (r + 1) (ACC_X + i) = tr r (OUT_X + i)
    ∧ tr (r + 1) (ACC_Y + i) = tr r (OUT_Y + i)
    ∧ tr (r + 1) (ACC_Z + i) = tr r (OUT_Z + i)

/-- `sVal` reads only the `SK` columns at its base, so limbwise equality is value equality. -/
theorem sVal_congr (a b : Assignment) (base base' : Nat)
    (h : ∀ i, i < SK → a (base + i) = b (base' + i)) : sVal a base = sVal b base' := by
  unfold sVal Dregg2.Circuit.Emit.PastaFieldSound.sumL
  refine congrArg List.sum ?_
  refine List.map_congr_left ?_
  intro i hi
  rw [h i (List.mem_range.mp hi)]

/-- ⚑ **A HELD THREAD MOVES THE VALUE, NOT JUST THE LIMBS.** -/
theorem threaded_carries (tr : Trace) (r : Nat) (h : Threaded tr r) :
    accIn tr (r + 1) = accOut tr r := by
  unfold accIn accOut
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    exact sVal_congr _ _ _ _ (fun i hi => by
      first
        | exact (h i hi).1
        | exact (h i hi).2.1
        | exact (h i hi).2.2)

/-- ⚑ **THE ROW'S DEPLOYED SATISFACTION**, packaged so the induction quantifies over rows rather
than re-listing 39 range blocks each time. Field for field this is exactly what
`pallasCompleteAddSound_forces` consumes. -/
structure RowSound (tr : Trace) (r : Nat) : Prop where
  hX1 : Ranged (tr r) ACC_X
  hY1 : Ranged (tr r) ACC_Y
  hZ1 : Ranged (tr r) ACC_Z
  hX2 : Ranged (tr r) ADD_X
  hY2 : Ranged (tr r) ADD_Y
  hZ2 : Ranged (tr r) ADD_Z
  hv  : ∀ i, i < 33 → Ranged (tr r) (vBase IN_BASE i)
  hm  : ∀ k, k < 12 → MulWitRanged (tr r) (mWit IN_BASE k)
  hs  : ∀ k, k < 2 → SmulWitRanged (tr r) (sWit IN_BASE k)
  hb  : ∀ k, k < 19 → AddSubWitRanged (tr r) (aWit IN_BASE k)
  hG  : RcbSat (tr r) pLimb (curveB3 : ℤ) ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE

/-- One row, forced: the output triple is congruent to the RCB of this row's two inputs. -/
theorem row_forces (tr : Trace) (r : Nat) (hR : RowSound tr r) :
    CZ3 (pN : ℤ) (accOut tr r)
      (rcbOutZ (curveB3 : ℤ) (accIn tr r).1 (accIn tr r).2.1 (accIn tr r).2.2
        (addend tr r).1 (addend tr r).2.1 (addend tr r).2.2) :=
  pallasCompleteAddSound_forces (tr r) ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE
    hR.hX1 hR.hY1 hR.hZ1 hR.hX2 hR.hY2 hR.hZ2 hR.hv hR.hm hR.hs hR.hb hR.hG

/-- **The reference chain** — fold the RCB complete addition over the per-row addends, starting from
the accumulator the trace carries into row 0. This is what the ladder CLAIMS to compute; nothing
below asserts it, the theorem forces it. -/
def chainRef (tr : Trace) : Nat → ℤ × ℤ × ℤ
  | 0 => accIn tr 0
  | n + 1 =>
      let P := chainRef tr n
      rcbOutZ (curveB3 : ℤ) P.1 P.2.1 P.2.2
        (addend tr n).1 (addend tr n).2.1 (addend tr n).2.2

/-- ⚑ **`threadedLadder_forces` — THE COMPOSITION THEOREM.**

`n` rows of DEPLOYED satisfaction, plus `n` held threads, force the accumulator entering row `n` to
be congruent — mod the real Pallas-base prime — to the `n`-fold RCB chain of the addends the trace
supplied. The accumulator is never read from a public input and never re-pinned; each row's output
is FORCED by that row's gates and CARRIED by that row's thread.

⚠ What it does NOT say: nothing here forces the ADDENDS to be anything in particular. A ladder that
means `[k]P` additionally needs the addend of row `r` to be the right multiple of the base — that is
the digit-selection half, and it lives in the caller. This theorem is the accumulator half, which is
the half the layout wall was blocking. -/
theorem threadedLadder_forces (tr : Trace) : ∀ n : Nat,
    (∀ r, r < n → RowSound tr r) → (∀ r, r < n → Threaded tr r) →
    CZ3 (pN : ℤ) (accIn tr n) (chainRef tr n)
  | 0, _, _ => CZ3.refl _
  | n + 1, hrow, hthread => by
      have ih : CZ3 (pN : ℤ) (accIn tr n) (chainRef tr n) :=
        threadedLadder_forces tr n (fun r hr => hrow r (Nat.lt_succ_of_lt hr))
          (fun r hr => hthread r (Nat.lt_succ_of_lt hr))
      have hcarry : accIn tr (n + 1) = accOut tr n :=
        threaded_carries tr n (hthread n (Nat.lt_succ_self n))
      have hrowf := row_forces tr n (hrow n (Nat.lt_succ_self n))
      -- the row's own conclusion, then the chain's step transported along the IH
      have hstep : CZ3 (pN : ℤ)
          (rcbOutZ (curveB3 : ℤ) (accIn tr n).1 (accIn tr n).2.1 (accIn tr n).2.2
            (addend tr n).1 (addend tr n).2.1 (addend tr n).2.2)
          (chainRef tr (n + 1)) :=
        rcbTraceZ_congr (curveB3 : ℤ) ih.1 ih.2.1 ih.2.2
          (CZm.refl _) (CZm.refl _) (CZm.refl _)
      rw [hcarry]
      exact CZ3.trans hrowf hstep

/-- ⚑ **AND IT IS NOT VACUOUS.** At `n = 0` the statement is reflexivity, so the content is entirely
in the step — which is why this instance is stated: `n = 1` says the FIRST row's forced output is
the chain's first value, and it consumes both a `RowSound` and a `Threaded`. A theorem that held for
every trace with no rows satisfied would prove nothing; this one needs the hypotheses at `r = 0`. -/
theorem threadedLadder_forces_one (tr : Trace)
    (hrow : RowSound tr 0) (hthread : Threaded tr 0) :
    CZ3 (pN : ℤ) (accIn tr 1)
      (rcbOutZ (curveB3 : ℤ) (accIn tr 0).1 (accIn tr 0).2.1 (accIn tr 0).2.2
        (addend tr 0).1 (addend tr 0).2.1 (addend tr 0).2.2) :=
  threadedLadder_forces tr 1
    (fun r hr => by rwa [Nat.lt_one_iff.mp hr])
    (fun r hr => by rwa [Nat.lt_one_iff.mp hr])

#assert_axioms threadLegs_length
#assert_axioms pallasThreadAir_mainRailOk
#assert_axioms vestaThreadAir_mainRailOk
#assert_axioms pallasThreadAir_window_selectors
#assert_axioms pallasThreadDesc_constraint_count
#assert_axioms vestaThreadDesc_constraint_count
#assert_axioms threaded_width_is_flat
#assert_axioms the_thread_is_what_makes_it_fit
#assert_axioms threading_trades_columns_for_rows_and_cells
#assert_axioms rcbTraceZ_congr
#assert_axioms sVal_congr
#assert_axioms threaded_carries
#assert_axioms row_forces
#assert_axioms threadedLadder_forces
#assert_axioms threadedLadder_forces_one

end Dregg2.Circuit.Emit.PastaLadderThread
