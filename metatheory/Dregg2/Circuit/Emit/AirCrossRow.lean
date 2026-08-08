/-
# `Dregg2.Circuit.Emit.AirCrossRow` — ⚑⚑ THE CROSS-ROW ASSIGNMENT RECONSTRUCTION.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Nothing here is a Rust gate, a Rust builder, or a Rust
`air_accepts`. House Law #1.

## ⚑ THE GAP THIS CLOSES, NAMED BY THE TWO FILES THAT LEFT IT

`PastaCurveScheduled` and `AirSchedule` both flag the same hole in the same words:

> `PastaCurveSound.RcbSat.apply` chains the 33 op blocks over **ONE** assignment `a`. On the
> scheduled layout the 33 blocks live on 33 different rows, so the chain needs one more theorem —
> *the carried trace induces a single assignment on which the unscheduled block is satisfied.*

That theorem is `rcbSat_of_rows` (§5), and `scheduledRows_force_the_rcb_formula` /
`vestaScheduledRows_force_the_rcb_formula` (§6) are it composed with
`PastaCurveSound.pallasCompleteAddSound_forces` — so the **scheduled** trace forces the RCB
formula, at the real Pasta primes, for the same reason the 3 048-column row does.

## ⚑ WHAT MAKES 33 ASSIGNMENTS INTO 1 — the gather, and why it is well-defined

`gather tr` (§4) reads each one-row column off **the row that owns it**: a value block off the row
where the value is defined, an op's private witness block off the op's own row. That is a
*definition*, and it would be worthless on its own — the content is that every op's gate, read at
**its own** row, is the one-row gate read at `gather tr`:

* **Values** — `carried_constant` (§1). The carry legs make a slot constant across the transitions
  inside a live range, so the value the definition row wrote is the value every consumer row reads.
  ⚑ This is the ONLY induction in the file and it is the whole cross-row content.
* **Witness** — no transfer needed. Op `i`'s private witness is read at row `i` and nowhere else,
  so the gather is the identity on it.

⚠ **Congruence, not equality.** `AirLeg.forces` on a `window` is `body ≡ 0 [ZMOD PMOD]`, so the
carry leg buys `tr (t+1) c ≡ tr t c [ZMOD P]` and NOT `tr (t+1) c = tr t c`. Every lemma here is
therefore stated mod `P`, which is also the reading `prove_vm_descriptor2` performs — the same
distinction `PastaCurveSound` §6 draws against `PastaCurveComplete`'s ℤ-equalities. Weakening it to
an ℤ-equality would be assuming exactly the thing the falsifiers exist to catch.

## ⚑ THE BASE SHIFT IS A THEOREM, NOT A RENAMING — and it is general

`renameLeg_forces` cannot do this job, and saying why is the point. A renaming `σ` is applied to
ONE row window; here the ONE-ROW block's five column blocks are read off **five different rows**.
So §3 proves the shift on the *bodies* the prover evaluates — `coefBody`, `adBody`, `smBody` — from
a `BlockAgree` hypothesis per block, and `MulSat_shift` / `AddSubSat_shift` / `SmulSat_shift` are
the op-level statements. They are general over both layouts' bases: nothing in §3 knows what a
schedule is, which is what lets an affine row inherit them.

## ⚑ THE CARRY PREMISE IS DISCHARGED — §7, from the legs

`SlotsCarry` would be a hole with a name if §5 only consumed it. `slotsCarry_of_carryLegs` (§7)
PROVES it from `PastaCurveScheduled.carryLegs` read through `AirLeg.forces`, via
`carryMask_is_one`: the mask is a one-hot sum over `carryPhases k`, and
`live_transitions_are_carry_phases` checks — across all 39 values × 33 rows — that every transition
inside a live range is one the slot's own mask fires on. ⚑ `indicator_sum` is the general fact
underneath, and it is also why the mask is `0` on the HANDOVER transition where a slot changes
hands: exactly the discipline `alloc_disjoint` makes reachable.

## ⚑⚑ THE TWO SELECTOR PREMISES ARE DISCHARGED — in `Emit.AirSelectorForcing`, 2026-08-08

`PhaseIndicator` and `RowsSat` were the two things §6 was conditional on. Both are now theorems of
the emitted block's own legs (`AirSelectorForcing.phaseIndicator_of_selectorLegs`,
`AirSelectorForcing.rowsSat_of_scheduleLegs`), and
`AirSelectorForcing.pallasScheduledBlock_forces_the_rcb_formula` is §6 with no selector premise
left. **Do not quote §6 as conditional on the selector reading honestly.**

⚠ **AND `PhaseIndicator` WAS NOT MERELY UNDONE — ITS OLD STATEMENT WAS FALSE OF THE DESCRIPTOR.**
It read `tr t (SEL i) = if i = t then 1 else 0` over **ℤ**. `AirLeg.forces` on a window is
`body ≡ 0 [ZMOD PMOD]`, so a trace with `tr 0 (SEL 0) = 1 + P` satisfies every selector leg and
refutes the ℤ form: nothing could ever have forced it, and a proof of it would have been a proof
about a different object. It is now stated mod `P`, which pulled `indicator_sum_modEq`,
`carryMask_is_one` and `carried_of_carryLeg` into the same reading. **No soundness is relaxed by
that** — the congruence is what `prove_vm_descriptor2` performs, and it is the same reading every
other lemma in this file was already in.

The shift half of the phase register is a plain induction; the half that needed the argument is
`sᵢ ≡ 0` at row 0 for `i ≥ 1`, and that is booleanity + sum-to-one **over a prime field** —
`AirSelectorForcing.bits_onehot`, on `Prime (2013265921 : ℤ)`.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`; zero `#guard`s.
Nothing is emitted by name; no VK rotates; nothing re-emits.
-/
import Dregg2.Circuit.Emit.PastaCurveScheduled

namespace Dregg2.Circuit.Emit.AirCrossRow

open Dregg2.Circuit (Assignment Expr)
open Dregg2.Circuit.Emit.EffectLower (P)
open Dregg2.Circuit.Emit.PastaFieldSound
  (SK SB CB NG COFF sumL sumL_cons digitVal chainVal coefBody coefExpr coefExpr_eval
   convPairs convPairs_mem sVal)
open Dregg2.Circuit.Emit.PastaAddSubSound
  (NA ACB CBITS ACOFF adDigit adChain adBody adExpr adExpr_eval)
open Dregg2.Circuit.Emit.PastaCurveSound
  (Ranged RangedAt MulSat AddSubSat SmulSat MulWitRanged AddSubWitRanged SmulWitRanged
   smDigit smChain smBody smExpr smExpr_eval RcbSat vBase mWit sWit aWit IN_BASE)
open Dregg2.Circuit.Emit.AirColumnAlloc
  (V SsaOp LiveRange allocate liveRanges liveRangesHeld defTime lastUse
   rcbOpsScheduled rcbOuts rcbScheduledRanges)
open Dregg2.Circuit.Emit.PastaCurveScheduled
  (OpKind VAL_BASE valueCol slotOf MUL_WIT ADDSUB_WIT SMUL_WIT rcbSchedule carryPhases carryMask
   SEL sumLoc carryLegs)
open Dregg2.Circuit.Emit.PastaCurve (CZm CZp CZq)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3 rcbTraceZ)
open Dregg2.Circuit.Emit.PastaFieldSound (pLimb qLimb)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 — ⚑⚑ THE CARRIED TRACE, AND THE ONE INDUCTION.

Nothing here knows what a curve is. A trace is a row-indexed family of assignments; a column is
*carried* across a window when the transition gate ties it to its own next row. -/

/-- A multi-row trace: the assignment each row presents. -/
abbrev RowTrace := Nat → Assignment

/-- ⚑ **THE CARRY DISCIPLINE ON ONE COLUMN, IN THE READING THE PROVER PERFORMS.** Mod `P`, because
that is what a `window` leg's `forces` gives; an ℤ-equality here would be a stronger hypothesis
than the descriptor can supply. -/
def CarriedOn (tr : RowTrace) (c lo hi : Nat) : Prop :=
  ∀ t, lo ≤ t → t < hi → tr (t + 1) c ≡ tr t c [ZMOD P]

/-- ⚑⚑ **THE CROSS-ROW STEP: A CARRIED COLUMN READS THE SAME FIELD ELEMENT AT EVERY ROW OF ITS
WINDOW.** One induction, general over the trace, the column and the window — this is what turns
33 assignments into 1, and every other theorem in the file is bookkeeping around it. -/
theorem carried_constant {tr : RowTrace} {c lo hi : Nat} (h : CarriedOn tr c lo hi) :
    ∀ t, lo ≤ t → t ≤ hi → tr t c ≡ tr lo c [ZMOD P] := by
  intro t hlo
  induction t, hlo using Nat.le_induction with
  | base => intro _; exact Int.ModEq.refl _
  | succ n hn ih => intro hhi; exact (h n hn (by omega)).trans (ih (by omega))

/-! ## §2 — ⚑ BLOCK AGREEMENT.

The one-row layout and the scheduled layout give a value DIFFERENT column bases. `BlockAgree` is
the statement that the two readings coincide — the only hypothesis §3 ever takes. -/

/-- ⚑ **`a`'s block at `B` reads what `b`'s block at `B'` reads**, for `n` limbs, mod `P`. -/
def BlockAgree (a b : Assignment) (B B' n : Nat) : Prop :=
  ∀ j, j < n → a (B + j) ≡ b (B' + j) [ZMOD P]

theorem BlockAgree.refl (a : Assignment) (B n : Nat) : BlockAgree a a B B n :=
  fun _ _ => Int.ModEq.refl _

/-- Narrow a block agreement to a shorter prefix — the multiply's carry pool is read at `NG − 1`
and the add/sub's at `NA − 1`, off the same physical pool. -/
theorem BlockAgree.mono {a b : Assignment} {B B' n m : Nat} (h : BlockAgree a b B B' n)
    (hm : m ≤ n) : BlockAgree a b B B' m :=
  fun j hj => h j (Nat.lt_of_lt_of_le hj hm)

/-- Sums agree when their summands do. -/
theorem sumL_modEq {α : Type} (l : List α) (f g : α → ℤ)
    (h : ∀ x ∈ l, f x ≡ g x [ZMOD P]) : sumL l f ≡ sumL l g [ZMOD P] := by
  induction l with
  | nil => exact Int.ModEq.refl _
  | cons x xs ih =>
      simp only [sumL_cons]
      exact (h x (by simp)).add (ih (fun y hy => h y (by simp [hy])))

/-! ## §3 — ⚑⚑ THE BASE SHIFT, ON THE BODIES THE PROVER EVALUATES.

`renameLeg_forces` relabels ONE row window. This is the other move: the same gate body, read at
two different sets of bases by two different assignments, agreeing because the blocks agree. It is
general over the bases — neither layout is named — so an affine row inherits §3 unchanged. -/

/-- The multiply's digit is base-shift stable. -/
theorem digitVal_shift {a b : Assignment} {pl : Nat → ℤ} {xB yB zB qB xB' yB' zB' qB' : Nat}
    (hx : BlockAgree a b xB xB' SK) (hy : BlockAgree a b yB yB' SK)
    (hz : BlockAgree a b zB zB' SK) (hq : BlockAgree a b qB qB' SK) (m : Nat) :
    digitVal a xB yB zB qB pl m ≡ digitVal b xB' yB' zB' qB' pl m [ZMOD P] := by
  unfold digitVal
  refine Int.ModEq.sub (Int.ModEq.sub ?_ ?_) ?_
  · refine sumL_modEq _ _ _ (fun pr hpr => ?_)
    obtain ⟨p1, p2, _⟩ := convPairs_mem hpr
    exact (hx pr.1 p1).mul (hy pr.2 p2)
  · refine sumL_modEq _ _ _ (fun pr hpr => ?_)
    obtain ⟨p1, _, _⟩ := convPairs_mem hpr
    exact (hq pr.1 p1).mul (Int.ModEq.refl _)
  · by_cases hm : m < SK
    · simp only [if_pos hm]; exact hz m hm
    · simp only [if_neg hm]; exact Int.ModEq.refl _

/-- The multiply's carry chain is base-shift stable. Both ends are pinned closed by construction,
so the shift never reaches for a column that does not exist. -/
theorem chainVal_shift {a b : Assignment} {cB cB' : Nat}
    (h : BlockAgree a b cB cB' (NG - 1)) (m : Nat) :
    chainVal a cB m ≡ chainVal b cB' m [ZMOD P] := by
  unfold chainVal
  by_cases h0 : m = 0
  · simp only [if_pos h0]; exact Int.ModEq.refl _
  · simp only [if_neg h0]
    by_cases h1 : m ≤ NG - 1
    · simp only [if_pos h1]
      have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr h0
      have he : cB + m - 1 = cB + (m - 1) := by omega
      have he' : cB' + m - 1 = cB' + (m - 1) := by omega
      rw [he, he']
      exact (h (m - 1) (by omega)).sub (Int.ModEq.refl _)
    · simp only [if_neg h1]; exact Int.ModEq.refl _

/-- ⚑ **THE MULTIPLY'S GATE BODY IS BASE-SHIFT STABLE.** -/
theorem coefBody_shift {a b : Assignment} {pl : Nat → ℤ}
    {xB yB zB qB cB xB' yB' zB' qB' cB' : Nat}
    (hx : BlockAgree a b xB xB' SK) (hy : BlockAgree a b yB yB' SK)
    (hz : BlockAgree a b zB zB' SK) (hq : BlockAgree a b qB qB' SK)
    (hc : BlockAgree a b cB cB' (NG - 1)) (m : Nat) :
    coefBody a xB yB zB qB cB pl m ≡ coefBody b xB' yB' zB' qB' cB' pl m [ZMOD P] :=
  ((digitVal_shift hx hy hz hq m).add (chainVal_shift hc m)).sub
    ((Int.ModEq.refl _).mul (chainVal_shift hc (m + 1)))

/-- ⚑⚑ **THE MULTIPLY TRANSFERS.** If the scheduled row's blocks agree with the one-row layout's,
`MulSat` at the scheduled bases IS `MulSat` at the one-row bases. -/
theorem MulSat_shift {a b : Assignment} {pl : Nat → ℤ} {xB yB zB wB xB' yB' zB' wB' : Nat}
    (hx : BlockAgree a b xB xB' SK) (hy : BlockAgree a b yB yB' SK)
    (hz : BlockAgree a b zB zB' SK) (hq : BlockAgree a b wB wB' SK)
    (hc : BlockAgree a b (wB + SK) (wB' + SK) (NG - 1))
    (h : Dregg2.Circuit.Emit.PastaCurveSound.MulSat b pl xB' yB' zB' wB') :
    Dregg2.Circuit.Emit.PastaCurveSound.MulSat a pl xB yB zB wB := by
  intro m hm
  have hb := h m hm
  rw [coefExpr_eval] at hb ⊢
  exact Int.modEq_zero_iff_dvd.mp
    ((coefBody_shift hx hy hz hq hc m).trans (Int.modEq_zero_iff_dvd.mpr hb))

/-- The add/sub's digit is base-shift stable. ⚑ The carry BIT is a single column, so it takes a
scalar hypothesis rather than a block one — a one-column block is exactly where an off-by-one in
the pool arithmetic would hide. -/
theorem adDigit_shift {a b : Assignment} {pl : Nat → ℤ} {sy sc : ℤ}
    {xB yB zB cCol xB' yB' zB' cCol' : Nat}
    (hx : BlockAgree a b xB xB' SK) (hy : BlockAgree a b yB yB' SK)
    (hz : BlockAgree a b zB zB' SK) (hcc : a cCol ≡ b cCol' [ZMOD P]) (m : Nat) :
    adDigit a xB yB zB cCol pl sy sc m ≡ adDigit b xB' yB' zB' cCol' pl sy sc m [ZMOD P] := by
  unfold adDigit
  by_cases hm : m < SK
  · simp only [if_pos hm]
    exact (((hx m hm).add ((Int.ModEq.refl sy).mul (hy m hm))).sub (hz m hm)).add
      ((Int.ModEq.refl sc).mul ((Int.ModEq.refl (pl m)).mul hcc))
  · simp only [if_neg hm]; exact Int.ModEq.refl _

/-- The add/sub's carry chain is base-shift stable. -/
theorem adChain_shift {a b : Assignment} {cB cB' : Nat}
    (h : BlockAgree a b cB cB' (NA - 1)) (m : Nat) :
    adChain a cB m ≡ adChain b cB' m [ZMOD P] := by
  unfold adChain
  by_cases h0 : m = 0
  · simp only [if_pos h0]; exact Int.ModEq.refl _
  · simp only [if_neg h0]
    by_cases h1 : m ≤ NA - 1
    · simp only [if_pos h1]
      have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr h0
      have he : cB + m - 1 = cB + (m - 1) := by omega
      have he' : cB' + m - 1 = cB' + (m - 1) := by omega
      rw [he, he']
      exact (h (m - 1) (by omega)).sub (Int.ModEq.refl _)
    · simp only [if_neg h1]; exact Int.ModEq.refl _

/-- ⚑ **THE ADD/SUB'S GATE BODY IS BASE-SHIFT STABLE.** -/
theorem adBody_shift {a b : Assignment} {pl : Nat → ℤ} {sy sc : ℤ}
    {xB yB zB cCol cB xB' yB' zB' cCol' cB' : Nat}
    (hx : BlockAgree a b xB xB' SK) (hy : BlockAgree a b yB yB' SK)
    (hz : BlockAgree a b zB zB' SK) (hcc : a cCol ≡ b cCol' [ZMOD P])
    (hc : BlockAgree a b cB cB' (NA - 1)) (m : Nat) :
    adBody a xB yB zB cCol cB pl sy sc m ≡ adBody b xB' yB' zB' cCol' cB' pl sy sc m [ZMOD P] :=
  ((adDigit_shift hx hy hz hcc m).add (adChain_shift hc m)).sub
    ((Int.ModEq.refl _).mul (adChain_shift hc (m + 1)))

/-- ⚑⚑ **THE ADD/SUB TRANSFERS.** -/
theorem AddSubSat_shift {a b : Assignment} {pl : Nat → ℤ} {sy sc : ℤ}
    {xB yB zB wB xB' yB' zB' wB' : Nat}
    (hx : BlockAgree a b xB xB' SK) (hy : BlockAgree a b yB yB' SK)
    (hz : BlockAgree a b zB zB' SK) (hcc : a wB ≡ b wB' [ZMOD P])
    (hc : BlockAgree a b (wB + 1) (wB' + 1) (NA - 1))
    (h : Dregg2.Circuit.Emit.PastaCurveSound.AddSubSat b pl sy sc xB' yB' zB' wB') :
    Dregg2.Circuit.Emit.PastaCurveSound.AddSubSat a pl sy sc xB yB zB wB := by
  intro m hm
  have hb := h m hm
  rw [adExpr_eval] at hb ⊢
  exact Int.modEq_zero_iff_dvd.mp
    ((adBody_shift hx hy hz hcc hc m).trans (Int.modEq_zero_iff_dvd.mpr hb))

/-- The constant multiply's digit is base-shift stable. -/
theorem smDigit_shift {a b : Assignment} {pl : Nat → ℤ} {cx : ℤ}
    {xB zB qCol xB' zB' qCol' : Nat}
    (hx : BlockAgree a b xB xB' SK) (hz : BlockAgree a b zB zB' SK)
    (hq : a qCol ≡ b qCol' [ZMOD P]) (m : Nat) :
    Dregg2.Circuit.Emit.PastaCurveSound.smDigit a xB zB qCol pl cx m
      ≡ Dregg2.Circuit.Emit.PastaCurveSound.smDigit b xB' zB' qCol' pl cx m [ZMOD P] := by
  unfold Dregg2.Circuit.Emit.PastaCurveSound.smDigit
  by_cases hm : m < SK
  · simp only [if_pos hm]
    exact (((Int.ModEq.refl cx).mul (hx m hm)).sub (hz m hm)).sub
      ((Int.ModEq.refl (pl m)).mul hq)
  · simp only [if_neg hm]; exact Int.ModEq.refl _

/-- The constant multiply's carry chain is base-shift stable. -/
theorem smChain_shift {a b : Assignment} {cB cB' : Nat}
    (h : BlockAgree a b cB cB' (SK - 1)) (m : Nat) :
    Dregg2.Circuit.Emit.PastaCurveSound.smChain a cB m
      ≡ Dregg2.Circuit.Emit.PastaCurveSound.smChain b cB' m [ZMOD P] := by
  unfold Dregg2.Circuit.Emit.PastaCurveSound.smChain
  by_cases h0 : m = 0
  · simp only [if_pos h0]; exact Int.ModEq.refl _
  · simp only [if_neg h0]
    by_cases h1 : m ≤ SK - 1
    · simp only [if_pos h1]
      have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr h0
      have he : cB + m - 1 = cB + (m - 1) := by omega
      have he' : cB' + m - 1 = cB' + (m - 1) := by omega
      rw [he, he']
      exact (h (m - 1) (by omega)).sub (Int.ModEq.refl _)
    · simp only [if_neg h1]; exact Int.ModEq.refl _

/-- ⚑ **THE CONSTANT MULTIPLY'S GATE BODY IS BASE-SHIFT STABLE.** -/
theorem smBody_shift {a b : Assignment} {pl : Nat → ℤ} {cx : ℤ}
    {xB zB qCol cB xB' zB' qCol' cB' : Nat}
    (hx : BlockAgree a b xB xB' SK) (hz : BlockAgree a b zB zB' SK)
    (hq : a qCol ≡ b qCol' [ZMOD P]) (hc : BlockAgree a b cB cB' (SK - 1)) (m : Nat) :
    Dregg2.Circuit.Emit.PastaCurveSound.smBody a xB zB qCol cB pl cx m
      ≡ Dregg2.Circuit.Emit.PastaCurveSound.smBody b xB' zB' qCol' cB' pl cx m [ZMOD P] :=
  ((smDigit_shift hx hz hq m).add (smChain_shift hc m)).sub
    ((Int.ModEq.refl _).mul (smChain_shift hc (m + 1)))

/-- ⚑⚑ **THE CONSTANT MULTIPLY TRANSFERS.** -/
theorem SmulSat_shift {a b : Assignment} {pl : Nat → ℤ} {cx : ℤ}
    {xB zB wB xB' zB' wB' : Nat}
    (hx : BlockAgree a b xB xB' SK) (hz : BlockAgree a b zB zB' SK)
    (hq : a wB ≡ b wB' [ZMOD P]) (hc : BlockAgree a b (wB + 1) (wB' + 1) (SK - 1))
    (h : Dregg2.Circuit.Emit.PastaCurveSound.SmulSat b pl cx xB' zB' wB') :
    Dregg2.Circuit.Emit.PastaCurveSound.SmulSat a pl cx xB zB wB := by
  intro m hm
  have hb := h m hm
  rw [Dregg2.Circuit.Emit.PastaCurveSound.smExpr_eval] at hb ⊢
  exact Int.modEq_zero_iff_dvd.mp
    ((smBody_shift hx hz hq hc m).trans (Int.modEq_zero_iff_dvd.mpr hb))

/-! ## §4 — ⚑⚑ THE GATHER, AT THE DEPLOYED ONE-ROW BASES.

`pallasCompleteAddSoundAir` puts the six input blocks at `0, SK, …, 5·SK` and `fresh = IN_BASE =
SK·6`, so `vBase IN_BASE k = SK · (6 + k)`: **the one-row block of value id `v` is `SK · v`,
uniformly, inputs included.** That is what makes the gather a three-line case split on a column
rather than a table lookup. -/

/-- ⚑ The one-row layout's value blocks are `SK · v` for every value id, inputs and SSA alike. -/
theorem oneRow_value_block_is_uniform : ∀ k, k < 33 → vBase IN_BASE k = SK * (6 + k) := by decide

/-- The allocated live range of value id `v`, as the allocator computed it. -/
def rangeOf (v : Nat) : LiveRange :=
  (rcbScheduledRanges.find? (fun r => r.val == v)).getD ⟨v, 0, 0⟩

/-- The row value `v` is defined on — its slot's first resident row. -/
def loOf (v : Nat) : Nat := (rangeOf v).lo
/-- The last row value `v` must still be resident on. The three published outputs are held to the
block's last row, because the thread gate reads them there. -/
def hiOf (v : Nat) : Nat := (rangeOf v).hi

/-- ⚑ **THE ONE-ROW MULTIPLY-WITNESS BLOCKS, BY THE VALUE THEY BELONG TO** — `mulC.legs` call order
in `swCompleteAddSoundLegs`, which is what fixes `mWit IN_BASE k`. -/
def mulVal : List Nat :=
  [V 0, V 1, V 2, V 5, V 10, V 15, V 24, V 25, V 27, V 28, V 30, V 31]
/-- …`smulC.legs` call order. -/
def smulVal : List Nat := [V 20, V 23]
/-- …`addC`/`subC.legs` call order. -/
def addVal : List Nat :=
  [V 3, V 4, V 6, V 7, V 8, V 9, V 11, V 12, V 13, V 14, V 16, V 17, V 18, V 19, V 21, V 22,
   V 26, V 29, V 32]

/-- ⚑ **THE CENSUS THE ONE-ROW LAYOUT ASSUMES** — 12 + 2 + 19 = 33 witness blocks, one per op,
and the three lists partition the 33 SSA values. A transcription slip in a witness list would put
an op's private witness on the wrong row, so it is pinned rather than trusted. -/
theorem the_witness_lists_partition_the_ssa_values :
    mulVal.length = 12 ∧ smulVal.length = 2 ∧ addVal.length = 19
      ∧ ∀ k, k < 33 → (mulVal ++ smulVal ++ addVal).count (V k) = 1 := by decide

/-- The row op `k` of each kind fires on: the row its destination is defined on. -/
def mulRow (k : Nat) : Nat := loOf (mulVal.getD k 0)
def smulRow (k : Nat) : Nat := loOf (smulVal.getD k 0)
def addRow (k : Nat) : Nat := loOf (addVal.getD k 0)

/-- ⚑⚑ **THE GATHER: ONE ASSIGNMENT, READ OFF 33 ROWS.**

Every one-row column is read at **the row that owns it** — a value block at the row where the value
is defined, an op's private witness block at the op's own row. The four arms are the four block
families of `RCB_WIDTH = 3 048`: 39 value blocks (`0 … 1 247`), 12 multiply witnesses of 94
(`1 248 … 2 375`), 2 constant-multiply witnesses of 32 (`2 376 … 2 439`), 19 add/sub witnesses of
32 (`2 440 … 3 047`). -/
def gather (tr : RowTrace) : Assignment := fun c =>
  if c < 1248 then tr (loOf (c / SK)) (valueCol (c / SK) + c % SK)
  else if c < 2376 then tr (mulRow ((c - 1248) / 94)) (MUL_WIT + (c - 1248) % 94)
  else if c < 2440 then tr (smulRow ((c - 2376) / SK)) (SMUL_WIT + (c - 2376) % SK)
  else tr (addRow ((c - 2440) / SK)) (ADDSUB_WIT + (c - 2440) % SK)

/-- Block arithmetic, once. -/
theorem block_divmod {s i j : Nat} (hs : 0 < s) (hj : j < s) :
    (s * i + j) / s = i ∧ (s * i + j) % s = j := by
  constructor
  · rw [Nat.mul_add_div hs, Nat.div_eq_of_lt hj, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem gather_val (tr : RowTrace) {v j : Nat} (hv : v < 39) (hj : j < SK) :
    gather tr (SK * v + j) = tr (loOf v) (valueCol v + j) := by
  have hs : SK = 32 := rfl
  obtain ⟨hd, hm⟩ := block_divmod (s := SK) (i := v) (j := j) (by rw [hs]; omega) hj
  have hlt : SK * v + j < 1248 := by rw [hs] at hj ⊢; omega
  simp only [gather, if_pos hlt, hd, hm]

theorem gather_mul (tr : RowTrace) {k j : Nat} (hk : k < 12) (hj : j < 94) :
    gather tr (mWit IN_BASE k + j) = tr (mulRow k) (MUL_WIT + j) := by
  have he : mWit IN_BASE k + j = 1248 + (94 * k + j) := by
    simp only [mWit, IN_BASE, SK, NG]; omega
  obtain ⟨hd, hm⟩ := block_divmod (s := 94) (i := k) (j := j) (by omega) hj
  rw [he]
  have h1 : ¬ (1248 + (94 * k + j) < 1248) := by omega
  have h2 : 1248 + (94 * k + j) < 2376 := by omega
  have h3 : 1248 + (94 * k + j) - 1248 = 94 * k + j := by omega
  simp only [gather, if_neg h1, if_pos h2, h3, hd, hm]

theorem gather_smul (tr : RowTrace) {k j : Nat} (hk : k < 2) (hj : j < SK) :
    gather tr (sWit IN_BASE k + j) = tr (smulRow k) (SMUL_WIT + j) := by
  have hs : SK = 32 := rfl
  have he : sWit IN_BASE k + j = 2376 + (SK * k + j) := by
    simp only [sWit, IN_BASE, SK, NG]; omega
  obtain ⟨hd, hm⟩ := block_divmod (s := SK) (i := k) (j := j) (by rw [hs]; omega) hj
  rw [he]
  rw [hs] at hj
  have h1 : ¬ (2376 + (SK * k + j) < 1248) := by rw [hs]; omega
  have h2 : ¬ (2376 + (SK * k + j) < 2376) := by omega
  have h3 : ¬ (2376 + (SK * k + j) < 2440) → False := by rw [hs]; omega
  have h4 : 2376 + (SK * k + j) < 2440 := by rw [hs]; omega
  have h5 : 2376 + (SK * k + j) - 2376 = SK * k + j := by omega
  simp only [gather, if_neg h1, if_neg h2, if_pos h4, h5, hd, hm]

theorem gather_add (tr : RowTrace) {k j : Nat} (hk : k < 19) (hj : j < SK) :
    gather tr (aWit IN_BASE k + j) = tr (addRow k) (ADDSUB_WIT + j) := by
  have hs : SK = 32 := rfl
  have he : aWit IN_BASE k + j = 2440 + (SK * k + j) := by
    simp only [aWit, IN_BASE, SK, NG]; omega
  obtain ⟨hd, hm⟩ := block_divmod (s := SK) (i := k) (j := j) (by rw [hs]; omega) hj
  rw [he]
  rw [hs] at hj
  have h1 : ¬ (2440 + (SK * k + j) < 1248) := by rw [hs]; omega
  have h2 : ¬ (2440 + (SK * k + j) < 2376) := by omega
  have h3 : ¬ (2440 + (SK * k + j) < 2440) := by omega
  have h5 : 2440 + (SK * k + j) - 2440 = SK * k + j := by omega
  simp only [gather, if_neg h1, if_neg h2, if_neg h3, h5, hd, hm]

/-! ## §5 — ⚑⚑⚑ THE RECONSTRUCTION: 33 ROWS, ONE ASSIGNMENT. -/

/-- ⚑ **WHAT THE CARRY LEGS BUY.** Every value's limbs read the same field element on every row of
its live range. §7 derives this from `carryLegs`; §5 only consumes it. -/
def SlotsCarry (tr : RowTrace) : Prop :=
  ∀ v, v < 39 → ∀ j, j < SK → CarriedOn tr (valueCol v + j) (loOf v) (hiOf v)

/-- ⚑ **WHAT ONE ROW'S GATES SAY** — the op's core at the ALLOCATED value columns and the SHARED
witness pools. The four arms are `PastaCurveScheduled.coreOf`'s four, at `witOf`'s three bases. -/
def OpSat (tr : RowTrace) (pl : Nat → ℤ) (b3 : ℤ) (i : Nat)
    (t : OpKind × Nat × Nat × Nat) : Prop :=
  match t.1 with
  | .mul  => MulSat (tr i) pl (valueCol t.2.2.1) (valueCol t.2.2.2) (valueCol t.2.1) MUL_WIT
  | .add  =>
      AddSubSat (tr i) pl 1 (-1) (valueCol t.2.2.1) (valueCol t.2.2.2) (valueCol t.2.1) ADDSUB_WIT
  | .sub  =>
      AddSubSat (tr i) pl (-1) 1 (valueCol t.2.2.1) (valueCol t.2.2.2) (valueCol t.2.1) ADDSUB_WIT
  | .smul => SmulSat (tr i) pl b3 (valueCol t.2.2.1) (valueCol t.2.1) SMUL_WIT

/-- ⚑ **EVERY SCHEDULED ROW SATISFIES ITS OWN OP'S GATES.** Indexed through `rcbSchedule` so a
caller cannot supply a row for an op the schedule does not have. -/
def RowsSat (tr : RowTrace) (pl : Nat → ℤ) (b3 : ℤ) : Prop :=
  ∀ i t, rcbSchedule[i]? = some t → OpSat tr pl b3 i t

/-- ⚑⚑ **A VALUE'S BLOCK, GATHERED, IS THE BLOCK ROW `i` READS** — whenever `i` is inside the
value's live range. This is `carried_constant` at the RCB layout and it is the whole bridge. -/
theorem block_value (tr : RowTrace) (hc : SlotsCarry tr) {v i B : Nat}
    (hv : v < 39) (hB : B = SK * v) (hlo : loOf v ≤ i) (hhi : i ≤ hiOf v) :
    BlockAgree (gather tr) (tr i) B (valueCol v) SK := by
  intro j hj
  rw [hB, gather_val tr hv hj]
  exact (carried_constant (hc v hv j hj) i hlo hhi).symm

/-- The multiply's private witness needs no transfer at all: it is read on the op's own row. -/
theorem block_mulwit (tr : RowTrace) {k i W : Nat} (hk : k < 12) (hi : mulRow k = i)
    (hW : W = mWit IN_BASE k) :
    BlockAgree (gather tr) (tr i) W MUL_WIT SK
      ∧ BlockAgree (gather tr) (tr i) (W + SK) (MUL_WIT + SK) (NG - 1) := by
  subst hW; subst hi
  have hs : SK = 32 := rfl
  have hn : NG - 1 = 62 := rfl
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [gather_mul tr hk (by rw [hs] at hj; omega)]
  · have he : mWit IN_BASE k + SK + j = mWit IN_BASE k + (SK + j) := by omega
    have he2 : MUL_WIT + SK + j = MUL_WIT + (SK + j) := by omega
    rw [he, he2, gather_mul tr hk (by rw [hn] at hj; rw [hs]; omega)]

/-- The constant multiply's: one quotient column then 31 carries. -/
theorem block_smulwit (tr : RowTrace) {k i W : Nat} (hk : k < 2) (hi : smulRow k = i)
    (hW : W = sWit IN_BASE k) :
    gather tr W ≡ tr i SMUL_WIT [ZMOD P]
      ∧ BlockAgree (gather tr) (tr i) (W + 1) (SMUL_WIT + 1) (SK - 1) := by
  subst hW; subst hi
  have hs : SK = 32 := rfl
  refine ⟨?_, fun j hj => ?_⟩
  · have h := gather_smul tr (k := k) (j := 0) hk (by rw [hs]; omega)
    simp only [Nat.add_zero] at h
    rw [h]
  · have he : sWit IN_BASE k + 1 + j = sWit IN_BASE k + (1 + j) := by omega
    have he2 : SMUL_WIT + 1 + j = SMUL_WIT + (1 + j) := by omega
    rw [he, he2, gather_smul tr hk (by rw [hs] at hj ⊢; omega)]

/-- The add/sub's: the carry BIT then 31 carries. -/
theorem block_addwit (tr : RowTrace) {k i W : Nat} (hk : k < 19) (hi : addRow k = i)
    (hW : W = aWit IN_BASE k) :
    gather tr W ≡ tr i ADDSUB_WIT [ZMOD P]
      ∧ BlockAgree (gather tr) (tr i) (W + 1) (ADDSUB_WIT + 1) (NA - 1) := by
  subst hW; subst hi
  have hs : SK = 32 := rfl
  have hn : NA - 1 = 31 := rfl
  refine ⟨?_, fun j hj => ?_⟩
  · have h := gather_add tr (k := k) (j := 0) hk (by rw [hs]; omega)
    simp only [Nat.add_zero] at h
    rw [h]
  · have he : aWit IN_BASE k + 1 + j = aWit IN_BASE k + (1 + j) := by omega
    have he2 : ADDSUB_WIT + 1 + j = ADDSUB_WIT + (1 + j) := by omega
    rw [he, he2, gather_add tr hk (by rw [hn] at hj; rw [hs]; omega)]

/-! ### §5a — ⚑ THE PER-OP SIDE CONDITION, AS ONE DECIDABLE PREDICATE.

Everything an op placement has to satisfy is closed nat arithmetic: the value ids are in range, the
op's row is the row its witness block belongs to, **both operands and the destination are resident
on that row**, and the one-row bases are the ones `RcbSat` names. Bundling them makes each of the
33 call sites one `by decide` — and makes a wrong placement a RED, not a silent mis-wiring. -/

/-- The placement conditions for one multiply. ⚑ An `abbrev` so instance resolution unfolds it and
`by decide` reaches the arithmetic; `∧` is right-associative, so a flat `obtain` destructures it. -/
abbrev MulOk (i k d s1 s2 xB yB zB wB : Nat) : Prop :=
  d < 39 ∧ s1 < 39 ∧ s2 < 39 ∧ k < 12 ∧ mulRow k = i
    ∧ loOf d ≤ i ∧ i ≤ hiOf d
    ∧ loOf s1 ≤ i ∧ i ≤ hiOf s1 ∧ loOf s2 ≤ i ∧ i ≤ hiOf s2
    ∧ xB = SK * s1 ∧ yB = SK * s2 ∧ zB = SK * d ∧ wB = mWit IN_BASE k

/-- The placement conditions for one add or subtract. -/
abbrev AddOk (i k d s1 s2 xB yB zB wB : Nat) : Prop :=
  d < 39 ∧ s1 < 39 ∧ s2 < 39 ∧ k < 19 ∧ addRow k = i
    ∧ loOf d ≤ i ∧ i ≤ hiOf d
    ∧ loOf s1 ≤ i ∧ i ≤ hiOf s1 ∧ loOf s2 ≤ i ∧ i ≤ hiOf s2
    ∧ xB = SK * s1 ∧ yB = SK * s2 ∧ zB = SK * d ∧ wB = aWit IN_BASE k

/-- The placement conditions for one constant multiply. -/
abbrev SmulOk (i k d s1 xB zB wB : Nat) : Prop :=
  d < 39 ∧ s1 < 39 ∧ k < 2 ∧ smulRow k = i
    ∧ loOf d ≤ i ∧ i ≤ hiOf d ∧ loOf s1 ≤ i ∧ i ≤ hiOf s1
    ∧ xB = SK * s1 ∧ zB = SK * d ∧ wB = sWit IN_BASE k

/-- ⚑ **ONE MULTIPLY, TRANSFERRED FROM ITS ROW TO THE ONE-ROW LAYOUT.** -/
theorem mul_transfer (tr : RowTrace) (pl : Nat → ℤ) (hc : SlotsCarry tr)
    (i k d s1 s2 : Nat) {xB yB zB wB : Nat} (hok : MulOk i k d s1 s2 xB yB zB wB)
    (h : MulSat (tr i) pl (valueCol s1) (valueCol s2) (valueCol d) MUL_WIT) :
    MulSat (gather tr) pl xB yB zB wB := by
  obtain ⟨hd39, hs139, hs239, hk, hrow, hdl, hdh, h1l, h1h, h2l, h2h, hx, hy, hz, hw⟩ := hok
  obtain ⟨hw8, hw16⟩ := block_mulwit tr hk hrow hw
  exact MulSat_shift (block_value tr hc hs139 hx h1l h1h) (block_value tr hc hs239 hy h2l h2h)
    (block_value tr hc hd39 hz hdl hdh) hw8 hw16 h

/-- ⚑ **ONE ADD OR SUBTRACT, TRANSFERRED.** `sy`/`sc` ride through untouched, so this one theorem
covers both polarities exactly as `addSubCore` does. -/
theorem addsub_transfer (tr : RowTrace) (pl : Nat → ℤ) (sy sc : ℤ) (hc : SlotsCarry tr)
    (i k d s1 s2 : Nat) {xB yB zB wB : Nat} (hok : AddOk i k d s1 s2 xB yB zB wB)
    (h : AddSubSat (tr i) pl sy sc (valueCol s1) (valueCol s2) (valueCol d) ADDSUB_WIT) :
    AddSubSat (gather tr) pl sy sc xB yB zB wB := by
  obtain ⟨hd39, hs139, hs239, hk, hrow, hdl, hdh, h1l, h1h, h2l, h2h, hx, hy, hz, hw⟩ := hok
  obtain ⟨hwb, hwc⟩ := block_addwit tr hk hrow hw
  exact AddSubSat_shift (block_value tr hc hs139 hx h1l h1h) (block_value tr hc hs239 hy h2l h2h)
    (block_value tr hc hd39 hz hdl hdh) hwb hwc h

/-- ⚑ **ONE CONSTANT MULTIPLY, TRANSFERRED.** -/
theorem smul_transfer (tr : RowTrace) (pl : Nat → ℤ) (cx : ℤ) (hc : SlotsCarry tr)
    (i k d s1 : Nat) {xB zB wB : Nat} (hok : SmulOk i k d s1 xB zB wB)
    (h : SmulSat (tr i) pl cx (valueCol s1) (valueCol d) SMUL_WIT) :
    SmulSat (gather tr) pl cx xB zB wB := by
  obtain ⟨hd39, hs139, hk, hrow, hdl, hdh, h1l, h1h, hx, hz, hw⟩ := hok
  obtain ⟨hwq, hwc⟩ := block_smulwit tr hk hrow hw
  exact SmulSat_shift (block_value tr hc hs139 hx h1l h1h)
    (block_value tr hc hd39 hz hdl hdh) hwq hwc h

/-! ### §5b — ⚑⚑⚑ THE THEOREM THE TWO FLAGGED FILES ASKED FOR. -/

/-- ⚑⚑⚑ **THE CARRIED SCHEDULED TRACE INDUCES A SINGLE ASSIGNMENT ON WHICH THE UNSCHEDULED BLOCK
IS SATISFIED.**

`RcbSat` is the 33-field object `RcbSat.apply` consumes, at the DEPLOYED one-row bases
(`0, SK, …, 5·SK`, `fresh = IN_BASE`) — the ones `pallasCompleteAddSoundAir` is emitted at. Every
field is one `*_transfer`, so the 33 lines below ARE the 33 ops and a mis-placed one is a `decide`
that goes red rather than a proof that quietly proves the wrong circuit.

⚑ The row index in each line is the `rcbSchedule` position, and the witness index is the
`swCompleteAddSoundLegs` call order. Those two orders are DIFFERENT — that difference is precisely
what the reconstruction has to get right, and `MulOk`/`AddOk`/`SmulOk` are what check it. -/
theorem rcbSat_of_rows (tr : RowTrace) (pl : Nat → ℤ) (b3 : ℤ)
    (hc : SlotsCarry tr) (hrows : RowsSat tr pl b3) :
    RcbSat (gather tr) pl b3 0 SK (2*SK) (3*SK) (4*SK) (5*SK) IN_BASE where
  hg0  := mul_transfer    tr pl        hc  3  0 (V 0)  0     3     (by decide)
            (hrows 3  (OpKind.mul,  V 0,  0,     3)     rfl)
  hg1  := mul_transfer    tr pl        hc  4  1 (V 1)  1     4     (by decide)
            (hrows 4  (OpKind.mul,  V 1,  1,     4)     rfl)
  hg2  := mul_transfer    tr pl        hc  7  2 (V 2)  2     5     (by decide)
            (hrows 7  (OpKind.mul,  V 2,  2,     5)     rfl)
  hg3  := addsub_transfer tr pl 1 (-1) hc  0  0 (V 3)  0     1     (by decide)
            (hrows 0  (OpKind.add,  V 3,  0,     1)     rfl)
  hg4  := addsub_transfer tr pl 1 (-1) hc  1  1 (V 4)  3     4     (by decide)
            (hrows 1  (OpKind.add,  V 4,  3,     4)     rfl)
  hg5  := mul_transfer    tr pl        hc  2  3 (V 5)  (V 3) (V 4) (by decide)
            (hrows 2  (OpKind.mul,  V 5,  V 3,   V 4)   rfl)
  hg6  := addsub_transfer tr pl 1 (-1) hc  5  2 (V 6)  (V 0) (V 1) (by decide)
            (hrows 5  (OpKind.add,  V 6,  V 0,   V 1)   rfl)
  hg7  := addsub_transfer tr pl (-1) 1 hc  6  3 (V 7)  (V 5) (V 6) (by decide)
            (hrows 6  (OpKind.sub,  V 7,  V 5,   V 6)   rfl)
  hg8  := addsub_transfer tr pl 1 (-1) hc  8  4 (V 8)  1     2     (by decide)
            (hrows 8  (OpKind.add,  V 8,  1,     2)     rfl)
  hg9  := addsub_transfer tr pl 1 (-1) hc  9  5 (V 9)  4     5     (by decide)
            (hrows 9  (OpKind.add,  V 9,  4,     5)     rfl)
  hg10 := mul_transfer    tr pl        hc 10  4 (V 10) (V 8) (V 9) (by decide)
            (hrows 10 (OpKind.mul,  V 10, V 8,   V 9)   rfl)
  hg11 := addsub_transfer tr pl 1 (-1) hc 11  6 (V 11) (V 1) (V 2) (by decide)
            (hrows 11 (OpKind.add,  V 11, V 1,   V 2)   rfl)
  hg12 := addsub_transfer tr pl (-1) 1 hc 12  7 (V 12) (V 10) (V 11) (by decide)
            (hrows 12 (OpKind.sub,  V 12, V 10,  V 11)  rfl)
  hg13 := addsub_transfer tr pl 1 (-1) hc 13  8 (V 13) 0     2     (by decide)
            (hrows 13 (OpKind.add,  V 13, 0,     2)     rfl)
  hg14 := addsub_transfer tr pl 1 (-1) hc 14  9 (V 14) 3     5     (by decide)
            (hrows 14 (OpKind.add,  V 14, 3,     5)     rfl)
  hg15 := mul_transfer    tr pl        hc 15  5 (V 15) (V 13) (V 14) (by decide)
            (hrows 15 (OpKind.mul,  V 15, V 13,  V 14)  rfl)
  hg16 := addsub_transfer tr pl 1 (-1) hc 16 10 (V 16) (V 0) (V 2) (by decide)
            (hrows 16 (OpKind.add,  V 16, V 0,   V 2)   rfl)
  hg17 := addsub_transfer tr pl (-1) 1 hc 17 11 (V 17) (V 15) (V 16) (by decide)
            (hrows 17 (OpKind.sub,  V 17, V 15,  V 16)  rfl)
  hg18 := addsub_transfer tr pl 1 (-1) hc 18 12 (V 18) (V 0) (V 0) (by decide)
            (hrows 18 (OpKind.add,  V 18, V 0,   V 0)   rfl)
  hg19 := addsub_transfer tr pl 1 (-1) hc 19 13 (V 19) (V 18) (V 0) (by decide)
            (hrows 19 (OpKind.add,  V 19, V 18,  V 0)   rfl)
  hg20 := smul_transfer   tr pl b3     hc 20  0 (V 20) (V 2)       (by decide)
            (hrows 20 (OpKind.smul, V 20, V 2,   V 2)   rfl)
  hg21 := addsub_transfer tr pl 1 (-1) hc 21 14 (V 21) (V 1) (V 20) (by decide)
            (hrows 21 (OpKind.add,  V 21, V 1,   V 20)  rfl)
  hg22 := addsub_transfer tr pl (-1) 1 hc 22 15 (V 22) (V 1) (V 20) (by decide)
            (hrows 22 (OpKind.sub,  V 22, V 1,   V 20)  rfl)
  hg23 := smul_transfer   tr pl b3     hc 23  1 (V 23) (V 17)      (by decide)
            (hrows 23 (OpKind.smul, V 23, V 17,  V 17)  rfl)
  hg24 := mul_transfer    tr pl        hc 24  6 (V 24) (V 12) (V 23) (by decide)
            (hrows 24 (OpKind.mul,  V 24, V 12,  V 23)  rfl)
  hg25 := mul_transfer    tr pl        hc 25  7 (V 25) (V 7) (V 22) (by decide)
            (hrows 25 (OpKind.mul,  V 25, V 7,   V 22)  rfl)
  hg26 := addsub_transfer tr pl (-1) 1 hc 26 16 (V 26) (V 25) (V 24) (by decide)
            (hrows 26 (OpKind.sub,  V 26, V 25,  V 24)  rfl)
  hg27 := mul_transfer    tr pl        hc 27  8 (V 27) (V 23) (V 19) (by decide)
            (hrows 27 (OpKind.mul,  V 27, V 23,  V 19)  rfl)
  hg28 := mul_transfer    tr pl        hc 28  9 (V 28) (V 22) (V 21) (by decide)
            (hrows 28 (OpKind.mul,  V 28, V 22,  V 21)  rfl)
  hg29 := addsub_transfer tr pl 1 (-1) hc 29 17 (V 29) (V 28) (V 27) (by decide)
            (hrows 29 (OpKind.add,  V 29, V 28,  V 27)  rfl)
  hg30 := mul_transfer    tr pl        hc 30 10 (V 30) (V 19) (V 7) (by decide)
            (hrows 30 (OpKind.mul,  V 30, V 19,  V 7)   rfl)
  hg31 := mul_transfer    tr pl        hc 31 11 (V 31) (V 21) (V 12) (by decide)
            (hrows 31 (OpKind.mul,  V 31, V 21,  V 12)  rfl)
  hg32 := addsub_transfer tr pl 1 (-1) hc 32 18 (V 32) (V 31) (V 30) (by decide)
            (hrows 32 (OpKind.add,  V 32, V 31,  V 30)  rfl)

/-! ## §6 — ⚑⚑⚑ THE SCHEDULED TRACE FORCES THE RCB FORMULA.

`rcbSat_of_rows` composed with `PastaCurveSound.pallasCompleteAddSound_forces`. The conclusion is
about the **scheduled** trace and no other object: the three published values are read off
`gather tr`, whose value blocks are the ALLOCATED columns of the rows the schedule puts them on.

⚑ **The one-row block is not re-proved and does not need to be.** `RcbSat.apply`'s 33-link `CZm`
chain is used exactly as written; what §5 supplies is the assignment it chains over. -/

/-- ⚑ **THE POOLS ARE BYTE-RANGED AT THE GATHERED ASSIGNMENT.** `valuePoolLegs` range-checks all
11 value slots and `witnessPoolLegs` all three witness pools on EVERY row — strictly more than the
one-row block asserted, which is why the hypotheses the forcing lemmas take are available at each
op's own row and therefore at the gather. -/
def PoolsRanged (tr : RowTrace) : Prop :=
  (∀ v, v < 39 → Ranged (gather tr) (SK * v))
  ∧ (∀ k, k < 12 → MulWitRanged (gather tr) (mWit IN_BASE k))
  ∧ (∀ k, k < 2 → SmulWitRanged (gather tr) (sWit IN_BASE k))
  ∧ (∀ k, k < 19 → AddSubWitRanged (gather tr) (aWit IN_BASE k))

/-- The 33 SSA value blocks, from the uniform `SK · v` form. -/
theorem poolsRanged_ssa {tr : RowTrace} (hr : PoolsRanged tr) :
    ∀ i, i < 33 → Ranged (gather tr) (vBase IN_BASE i) := by
  intro i hi
  rw [oneRow_value_block_is_uniform i hi]
  exact hr.1 (6 + i) (by omega)

/-- ⚑⚑⚑ **THE SCHEDULED ROWS FORCE `(X3, Y3, Z3) ≡ rcbTraceZ 15 (P, Q)` MOD THE PALLAS-BASE
PRIME.** The 33 blocks live on 33 rows; the theorem that used to need them on one is discharged
through `gather`. -/
theorem scheduledRows_force_the_rcb_formula (tr : RowTrace)
    (hc : SlotsCarry tr) (hr : PoolsRanged tr)
    (hrows : RowsSat tr pLimb (curveB3 : ℤ)) :
    CZp (sVal (gather tr) (vBase IN_BASE 26))
        (rcbTraceZ (curveB3 : ℤ) (sVal (gather tr) 0) (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK)) (sVal (gather tr) (3*SK)) (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).X3g
    ∧ CZp (sVal (gather tr) (vBase IN_BASE 29))
        (rcbTraceZ (curveB3 : ℤ) (sVal (gather tr) 0) (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK)) (sVal (gather tr) (3*SK)) (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).Y3f
    ∧ CZp (sVal (gather tr) (vBase IN_BASE 32))
        (rcbTraceZ (curveB3 : ℤ) (sVal (gather tr) 0) (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK)) (sVal (gather tr) (3*SK)) (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).Z3c :=
  Dregg2.Circuit.Emit.PastaCurveSound.pallasCompleteAddSound_forces (gather tr)
    0 SK (2*SK) (3*SK) (4*SK) (5*SK) IN_BASE
    (hr.1 0 (by decide)) (hr.1 1 (by decide)) (hr.1 2 (by decide))
    (hr.1 3 (by decide)) (hr.1 4 (by decide)) (hr.1 5 (by decide))
    (poolsRanged_ssa hr) hr.2.1 hr.2.2.1 hr.2.2.2
    (rcbSat_of_rows tr pLimb (curveB3 : ℤ) hc hrows)

/-- ⚑⚑ **…AND THE VESTA TWIN**, because the accumulator leg is Step/Tick on Vesta and a
Pallas-only reconstruction would leave half the recursion boundary un-transferred. -/
theorem vestaScheduledRows_force_the_rcb_formula (tr : RowTrace)
    (hc : SlotsCarry tr) (hr : PoolsRanged tr)
    (hrows : RowsSat tr qLimb (curveB3 : ℤ)) :
    CZq (sVal (gather tr) (vBase IN_BASE 26))
        (rcbTraceZ (curveB3 : ℤ) (sVal (gather tr) 0) (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK)) (sVal (gather tr) (3*SK)) (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).X3g
    ∧ CZq (sVal (gather tr) (vBase IN_BASE 29))
        (rcbTraceZ (curveB3 : ℤ) (sVal (gather tr) 0) (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK)) (sVal (gather tr) (3*SK)) (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).Y3f
    ∧ CZq (sVal (gather tr) (vBase IN_BASE 32))
        (rcbTraceZ (curveB3 : ℤ) (sVal (gather tr) 0) (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK)) (sVal (gather tr) (3*SK)) (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).Z3c :=
  Dregg2.Circuit.Emit.PastaCurveSound.vestaCompleteAddSound_forces (gather tr)
    0 SK (2*SK) (3*SK) (4*SK) (5*SK) IN_BASE
    (hr.1 0 (by decide)) (hr.1 1 (by decide)) (hr.1 2 (by decide))
    (hr.1 3 (by decide)) (hr.1 4 (by decide)) (hr.1 5 (by decide))
    (poolsRanged_ssa hr) hr.2.1 hr.2.2.1 hr.2.2.2
    (rcbSat_of_rows tr qLimb (curveB3 : ℤ) hc hrows)

/-! ## §7 — ⚑⚑ WHERE `SlotsCarry` COMES FROM: `carryLegs`, AT THE SOURCE SEMANTICS.

§5 consumes `SlotsCarry` as a premise; a premise nothing supplies is a hole with a name. This
section supplies it, from `PastaCurveScheduled.carryLegs` read through `AirLeg.forces` — the same
source vocabulary `renameLeg_forces` and `pallasScheduledDesc_certified` speak, so it composes with
the certificate the emit already hands back.

⚠ The one thing §7 does **not** prove is `PhaseIndicator`. See the header. -/

/-- The row window a trace presents at row `t`: this row local, the next row as `nxt`. -/
def rowEnv (tr : RowTrace) (pub chal : Assignment) (t : Nat) :
    Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv :=
  { loc := tr t, nxt := tr (t + 1), pub := pub, chal := chal }

/-- ⚑ **THE PHASE REGISTER READS AS THE ONE-HOT ROW INDICATOR** — `AirSelectorForcing` proves it
from `selShiftLegs` + `selBooleanLegs` + `selOneHotLeg`, so this is no longer a premise anything
assumes silently.

⚠ **MOD `P`, AND THE ℤ-EQUALITY FORM WAS UNFORCEABLE.** Until 2026-08-08 this read
`tr t (SEL i) = if i = t then 1 else 0` over ℤ. No leg can supply that: `AirLeg.forces` on a window
is `body ≡ 0 [ZMOD PMOD]`, so a trace with `tr 0 (SEL 0) = 1 + P` satisfies every selector leg and
refutes the ℤ form. The premise was not merely undone work — it was **false of the descriptor**, and
a proof of it would have been a proof about a different object. -/
def PhaseIndicator (tr : RowTrace) : Prop :=
  ∀ t, t < 33 → ∀ i, i < 34 → tr t (SEL i) ≡ (if i = t then 1 else 0) [ZMOD P]

theorem sumLoc_eval (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv) :
    ∀ l : List Nat, (sumLoc l).eval env = (l.map env.loc).sum
  | []      => rfl
  | c :: cs => by
      simp [sumLoc, Dregg2.Circuit.DescriptorIR2.WindowExpr.eval, sumLoc_eval env cs]

/-- ⚑ **A ONE-HOT SUM OVER A DUPLICATE-FREE INDEX LIST IS THE MEMBERSHIP INDICATOR** — in the
congruence reading, which is the only one a window leg can supply. This is what makes `carryMask`
read `1` on a transition the slot must hold across, and `0` on the handover transition where the
slot changes hands — the property `alloc_disjoint` is there to make reachable. -/
theorem indicator_sum_modEq (f : Nat → ℤ) (t : Nat) :
    ∀ l : List Nat, l.Nodup → (∀ i ∈ l, f i ≡ (if i = t then 1 else 0) [ZMOD P]) →
      (l.map f).sum ≡ (if t ∈ l then 1 else 0) [ZMOD P] := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons c cs ih =>
      intro hnd hf
      have hnc : c ∉ cs := (List.nodup_cons.mp hnd).1
      have hcs := ih (List.nodup_cons.mp hnd).2 (fun i hi => hf i (List.mem_cons_of_mem _ hi))
      have hhead := hf c (List.mem_cons_self ..)
      rw [List.map_cons, List.sum_cons]
      by_cases hc : c = t
      · have htc : t ∉ cs := by rw [← hc]; exact hnc
        have hmem : t ∈ c :: cs := List.mem_cons.mpr (Or.inl hc.symm)
        rw [if_pos hc] at hhead
        rw [if_neg htc] at hcs
        rw [if_pos hmem]
        simpa using hhead.add hcs
      · have hne : ¬ (t = c) := fun h => hc h.symm
        rw [if_neg hc] at hhead
        simp only [List.mem_cons, hne, false_or]
        simpa using hhead.add hcs

theorem carryPhases_nodup (k : Nat) : (carryPhases k).Nodup :=
  List.Nodup.filter _ (List.nodup_range)

/-- `SEL` is the identity on column indices, so the mask is a sum over the phase list itself. -/
theorem map_SEL (l : List Nat) : l.map SEL = l := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [SEL, ih]

theorem carryMask_eq (k : Nat) : carryMask k = sumLoc (carryPhases k) := by
  rw [carryMask, map_SEL]

theorem carryPhases_lt {k i : Nat} (h : i ∈ carryPhases k) : i < 33 :=
  List.mem_range.mp (List.mem_of_mem_filter h)

/-- ⚑⚑ **THE CARRY MASK READS `1` ON A TRANSITION THE SLOT MUST HOLD ACROSS** — mod `P`, because
`PhaseIndicator` is mod `P` and nothing sharper is forceable. -/
theorem carryMask_is_one (tr : RowTrace) (pub chal : Assignment) (hp : PhaseIndicator tr)
    {k t : Nat} (ht : t < 33) (hmem : t ∈ carryPhases k) :
    (carryMask k).eval (rowEnv tr pub chal t) ≡ 1 [ZMOD P] := by
  have hval : ∀ i ∈ carryPhases k,
      (rowEnv tr pub chal t).loc i ≡ (if i = t then 1 else 0) [ZMOD P] := by
    intro i hi
    exact hp t ht i (by have := carryPhases_lt hi; omega)
  rw [carryMask_eq, sumLoc_eval]
  have h := indicator_sum_modEq _ t _ (carryPhases_nodup k) hval
  rwa [if_pos hmem] at h

/-- ⚑ **ONE CARRY LEG, CASHED.** `AirLeg.forces` on a `.transition` window is `body ≡ 0 [ZMOD
PMOD]`; with the mask congruent to `1` that is exactly `nxt c ≡ loc c`. ⚑ The `isFirst` flag is
free: the `.transition` arm of `forces` does not read it, and taking it as a parameter is what lets
one hypothesis about **row `t` of the emitted block** serve both this and the selector legs. -/
theorem carried_of_carryLeg (tr : RowTrace) (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily)
    (pub chal : Assignment) (hp : PhaseIndicator tr) {k c t : Nat} {isFirst : Bool}
    (ht : t < 33) (hmem : t ∈ carryPhases k)
    (hleg : (Dregg2.Circuit.EffectAirIR.AirLeg.window
              ⟨.transition, .mul (carryMask k)
                (.add (.nxt c) (.mul (.const (-1)) (.loc c)))⟩).forces
              tf (rowEnv tr pub chal t) isFirst false) :
    tr (t + 1) c ≡ tr t c [ZMOD P] := by
  have hb0 := hleg rfl
  rw [Dregg2.Circuit.DescriptorIR2.WindowExpr.eval] at hb0
  simp only [Dregg2.Circuit.DescriptorIR2.WindowExpr.eval] at hb0
  have hm := carryMask_is_one tr pub chal hp ht hmem
  have hb : (rowEnv tr pub chal t).nxt c + -1 * (rowEnv tr pub chal t).loc c ≡ 0 [ZMOD P] := by
    have h1 := Int.ModEq.mul_right
      ((rowEnv tr pub chal t).nxt c + -1 * (rowEnv tr pub chal t).loc c) hm.symm
    rw [one_mul] at h1
    exact h1.trans hb0
  have hdvd : P ∣ (tr (t + 1) c + -1 * tr t c) := Int.modEq_zero_iff_dvd.mp hb
  have : P ∣ (tr t c - tr (t + 1) c) := by
    have := dvd_neg.mpr hdvd
    simpa [neg_add, sub_eq_add_neg, add_comm] using this
  exact Int.modEq_iff_dvd.mpr this

/-- The 39 value blocks live in the 11 allocated slots, and no live range outruns the block. -/
theorem slotOf_lt_eleven : ∀ v, v < 39 → slotOf v < 11 := by decide
theorem hiOf_le_32 : ∀ v, v < 39 → hiOf v ≤ 32 := by decide
theorem valueCol_is_the_slot_block :
    ∀ v, v < 39 → valueCol v = VAL_BASE + SK * slotOf v := by decide

/-- ⚑⚑ **EVERY TRANSITION INSIDE A VALUE'S LIVE RANGE IS ONE ITS SLOT'S MASK FIRES ON.** The
allocation put the value in that slot, so the slot's own `carryPhases` covers its window — checked
across all 39 values × 33 rows rather than argued. -/
theorem live_transitions_are_carry_phases :
    ∀ v, v < 39 → ∀ t, t < 33 → loOf v ≤ t → t < hiOf v →
      (carryPhases (slotOf v)).contains t = true := by decide

/-- ⚑ **THE CARRY LEGS, FORCED AT EVERY TRANSITION ROW OF THE BLOCK** — what a caller holding a
trace that satisfies `pallasScheduledDesc` has, via `pallasScheduledDesc_certified`. -/
def CarryLegsHold (tr : RowTrace) (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily)
    (pub chal : Assignment) : Prop :=
  ∀ t, t < 33 → ∀ l ∈ carryLegs, l.forces tf (rowEnv tr pub chal t) (decide (t = 0)) false

/-- ⚑⚑⚑ **`SlotsCarry` IS A THEOREM, NOT A PREMISE.** The premise §5 consumes is discharged from
the emitted block's own carry legs. -/
theorem slotsCarry_of_carryLegs (tr : RowTrace) (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily)
    (pub chal : Assignment) (hp : PhaseIndicator tr) (h : CarryLegsHold tr tf pub chal) :
    SlotsCarry tr := by
  intro v hv j hj t hlo hhi
  have ht32 : t < 33 := by have := hiOf_le_32 v hv; omega
  have hk : slotOf v < 11 := slotOf_lt_eleven v hv
  have hmem : t ∈ carryPhases (slotOf v) :=
    List.mem_of_elem_eq_true (live_transitions_are_carry_phases v hv t ht32 hlo hhi)
  have hcol : valueCol v + j = VAL_BASE + SK * slotOf v + j := by
    rw [valueCol_is_the_slot_block v hv]
  rw [hcol]
  refine carried_of_carryLeg tr tf pub chal hp ht32 hmem (h t ht32 _ ?_)
  refine List.mem_flatMap.mpr ⟨slotOf v, List.mem_range.mpr hk, ?_⟩
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

#assert_axioms indicator_sum_modEq
#assert_axioms carryMask_is_one
#assert_axioms carried_of_carryLeg
#assert_axioms live_transitions_are_carry_phases
#assert_axioms slotsCarry_of_carryLegs
#assert_axioms carried_constant
#assert_axioms sumL_modEq
#assert_axioms coefBody_shift
#assert_axioms adBody_shift
#assert_axioms smBody_shift
#assert_axioms MulSat_shift
#assert_axioms AddSubSat_shift
#assert_axioms SmulSat_shift
#assert_axioms oneRow_value_block_is_uniform
#assert_axioms the_witness_lists_partition_the_ssa_values
#assert_axioms gather_val
#assert_axioms gather_mul
#assert_axioms gather_smul
#assert_axioms gather_add
#assert_axioms block_value
#assert_axioms mul_transfer
#assert_axioms addsub_transfer
#assert_axioms smul_transfer
#assert_axioms rcbSat_of_rows
#assert_axioms scheduledRows_force_the_rcb_formula
#assert_axioms vestaScheduledRows_force_the_rcb_formula

end Dregg2.Circuit.Emit.AirCrossRow
