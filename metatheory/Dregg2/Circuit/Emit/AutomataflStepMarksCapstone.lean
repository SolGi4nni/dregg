/-
# `AutomataflStepMarksCapstone` — LEG A (the AUTOMATON STEP) CARRYING A **FROZEN MARKS WINDOW** (braid **M6′**).

`docs/reference/AUTOMATAFL-MULTIROUND-BRAID-DESIGN.md` §4.3, §10. The multi-round braid's CLEAN round
is a sub-chain `RM → A`: the resolve-marks leg (`automataflResolveMarksDescN`, M6) adjudicates the two
moves against the accumulated marks and hands its `[board ‖ marks ‖ auto]` window to the automaton-step
leg (Leg A, `automataflStepDescN`). But the step descriptor publishes NO marks — its windows are
11-lane `[board ‖ auto]`, so the clean sub-chain `RM(20) → A(11)` is MIXED-WIDTH and the nested
sub-root `[RM.IN(20) ‖ A.OUT(11)]` is not the symmetric shape the uniform fold reads.

## THE FIX — a marks-carrying step descriptor with a FROZEN marks window

`automataflStepMarksDescN n` is `automataflStepDescN n`'s constraints VERBATIM plus a MARKS WINDOW (the
accumulated `marksIn` commitment `AutomataflMarks.marksCommitFamilyAt`) at fresh columns above
`A_WIDTH_N n` and PIs above `A_PI_COUNT_N n`. The window is FROZEN: the step publishes the marks ONCE,
and BOTH the leg's IN window (`[pack(old) ‖ pack(marks) ‖ (ax,ay)]`) and its OUT window
(`[pack(new) ‖ pack(marks) ‖ (nax,nay)]`) read that same published window — `marksOut = marksIn` by
construction, exactly as Leg C freezes the board and exactly as M6's resolve-marks freezes marks (a
single `pi_marks_in` window serving both slices).

## THE KEY OBSERVATION — the automaton step is MARKS-INDEPENDENT

`AutomataflRules.automatonStepCfg` never reads marks (the automaton senses particles, not marks). So
the emitted `new` board is UNCHANGED by the marks carry, and the whole step capstone
(`astep_sat_imp_automatonStepCfgN`) REUSES verbatim on the RESTRICTED trace (via `stepMarks_restrict`):
the step constraints are a PREFIX of the marks constraints, and the marks window carries NO memOp /
mapOp / hash / range, so every memory / table leg transfers. This is the same restriction argument
`AutomataflResolveMarksCapstone.resolveMarks_restrict` makes — the marks window here is even simpler
(no legality re-check: that already happened at the resolve-marks leg; the step only CARRIES marks).

⚑ **SUBSTRATE, SAID OUT LOUD.** This is **LEAN-AUTHORED AIR**. Every gate is a `VmConstraint2` emitted
here; Rust only fills traces. `dregg-automatafl/src/{air,moves,builder}.rs` stays DEBT.

## Axiom hygiene
`#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`, no
assumed-hypothesis, no weakened capstone.
-/
import Dregg2.Circuit.Emit.AutomataflStepStep
import Dregg2.Circuit.Emit.AutomataflMarks
import Dregg2.Circuit.Emit.AutomataflLegCEmit

namespace Dregg2.Circuit.Emit.AutomataflStepMarksCapstone

open Dregg2.Circuit.Emit.AutomataflStepEmit
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.AutomataflStepRefine (StepCanon codeToParticle)
open Dregg2.Circuit.Emit.AutomataflStepCapstone (boardDecodeN)
open Dregg2.Circuit.Emit.AutomataflStepStep (astep_sat_imp_automatonStepCfgN)
open Dregg2.Circuit.Emit.AutomataflMarks (marksCommitFamilyAt marksDecodeAt marksCode
  marksWindowLanes marksAlpha_of_mem marksPack_pi_of_mem)
open Dregg2.Circuit.Emit.AutomataflCommit (feltCount packCell)
open Dregg2.Games.AutomataflRules (automatonStepCfg)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## §1 — THE COLUMN LAYOUT (a marks window above `A_WIDTH_N n`).

The step descriptor occupies `[0, A_WIDTH_N n)`. The marks window begins at `SM0 n = A_WIDTH_N n`, so
the two never collide and the step descriptor's own columns keep their numerals. -/

/-- The marks window's base column. -/
def SM0 (n : Nat) : Nat := A_WIDTH_N n
/-- `marksIn` indicator cell `c` (linear index `y·n + x`). -/
def sMarksInCell (n : Nat) (c : Nat) : Nat := SM0 n + c
/-- `marksIn` packed felt `j`. -/
def sMarksInFelt (n : Nat) (j : Nat) : Nat := SM0 n + n * n + j
/-- The marks-carrying step descriptor's trace width (`n²` indicator cells then `⌈n²/15⌉` felts). -/
def SM_WIDTH (n : Nat) : Nat := SM0 n + n * n + feltCount n

/-- `marksIn`'s published window base (append-only past the step descriptor's PIs). -/
def sPiMarksIn (n : Nat) : Nat := A_PI_COUNT_N n
/-- `marksOut`'s published window base. The step FREEZES marks: it publishes the window ONCE, so the
OUT window's marks slice reads the SAME PIs as the IN window's. (Single window ⇒ `marksOut = marksIn`
by construction — the analog of M6's resolve-marks, whose `pi_marks_in` likewise serves both slices.) -/
def sPiMarksOut (n : Nat) : Nat := sPiMarksIn n

/-! ## §2 — THE MARKS WINDOW (all `.base`; NO memOp / mapOp / hash site). -/

/-- The `marksIn` commitment — M0's `marksCommitFamilyAt`: `{0,1}` range gates ‖ base-4 pack gates ‖
packed-felt PI bindings. The WHOLE marks tail (no legality re-check — the step only carries marks). -/
def stepMarksTail (n : Nat) : List VmConstraint2 :=
  marksCommitFamilyAt n (sMarksInCell n) (sMarksInFelt n) (sPiMarksIn n)

/-- **`automataflStepMarksDescN n`** — the marks-carrying automaton-step descriptor. Additive: the step
constraints VERBATIM, then the frozen marks window. -/
def automataflStepMarksDescN (n : Nat) : EffectVmDescriptor2 :=
  { name        := "dregg-automatafl-step-marks-n" ++ toString n
  , traceWidth  := SM_WIDTH n
  , piCount     := A_PI_COUNT_N n + feltCount n
  , tables      := []
  , constraints := (automataflStepDescN n).constraints ++ stepMarksTail n
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — THE TAIL IS memOp/mapOp-FREE (the restriction-lemma obligation). -/

/-- A generic "every element of `l.map g` is `.base`" step. -/
theorem base_of_mem_map {α : Type} {l : List α} {g : α → VmConstraint2}
    (hg : ∀ a, ∃ b, g a = VmConstraint2.base b) {c : VmConstraint2} (hc : c ∈ l.map g) :
    ∃ b, c = VmConstraint2.base b := by
  rw [List.mem_map] at hc; obtain ⟨a, _, rfl⟩ := hc; exact hg a

/-- The frozen marks window is all `.base` (the three commitment sub-families are maps into `.base`). -/
theorem tail_all_base (n : Nat) : ∀ c ∈ stepMarksTail n, ∃ b, c = VmConstraint2.base b := by
  intro c hc
  simp only [stepMarksTail, marksCommitFamilyAt,
    Dregg2.Circuit.Emit.AutomataflMarks.marksRangeCellsAt,
    Dregg2.Circuit.Emit.AutomataflMarks.marksPackConstraintsAt,
    Dregg2.Circuit.Emit.AutomataflMarks.marksCommitConstraintsAt,
    Dregg2.Circuit.Emit.AutomataflCommit.packBoardConstraintsAt,
    Dregg2.Circuit.Emit.AutomataflCommit.commitBoardConstraintsAt, List.mem_append] at hc
  rcases hc with (h | h) | h <;>
    · exact base_of_mem_map (fun _ => ⟨_, rfl⟩) h

theorem tail_memfree (n : Nat) :
    (stepMarksTail n).filterMap
      (fun c => match c with | .memOp m => some m | _ => none) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro c hc; obtain ⟨b, rfl⟩ := tail_all_base n c hc; rfl

theorem tail_mapfree (n : Nat) :
    (stepMarksTail n).filterMap
      (fun c => match c with | .mapOp m => some m | _ => none) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro c hc; obtain ⟨b, rfl⟩ := tail_all_base n c hc; rfl

/-! ## §4 — THE RESTRICTION LEMMA. -/

section Restrict
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- `x ++ y = x` when `y = []` (lambda-free, so the remaining subgoal keeps the goal's own term). -/
theorem append_eq_self_nil {α : Type} {x y : List α} (h : y = []) : x ++ y = x := by
  rw [h, List.append_nil]

theorem memOpsOf_restrict :
    memOpsOf (automataflStepMarksDescN n) = memOpsOf (automataflStepDescN n) := by
  show ((automataflStepDescN n).constraints ++ stepMarksTail n).filterMap _
      = (automataflStepDescN n).constraints.filterMap _
  rw [List.filterMap_append]
  refine append_eq_self_nil ?_
  apply List.filterMap_eq_nil_iff.mpr
  intro c hc; obtain ⟨b, rfl⟩ := tail_all_base n c hc; rfl

theorem mapOpsOf_restrict :
    mapOpsOf (automataflStepMarksDescN n) = mapOpsOf (automataflStepDescN n) := by
  show ((automataflStepDescN n).constraints ++ stepMarksTail n).filterMap _
      = (automataflStepDescN n).constraints.filterMap _
  rw [List.filterMap_append]
  refine append_eq_self_nil ?_
  apply List.filterMap_eq_nil_iff.mpr
  intro c hc; obtain ⟨b, rfl⟩ := tail_all_base n c hc; rfl

theorem memLog_restrict :
    memLog (automataflStepMarksDescN n) t = memLog (automataflStepDescN n) t := by
  simp only [memLog, memOpsOf_restrict]

theorem mapLog_restrict :
    mapLog (automataflStepMarksDescN n) t = mapLog (automataflStepDescN n) t := by
  simp only [mapLog, mapOpsOf_restrict]

/-- **`stepMarks_restrict` — the reuse enabler.** A satisfying marks-descriptor trace restricts to a
satisfying step-descriptor trace on the SAME `t` / `minit` / `mfin` / `maddrs`. The step constraints
are a prefix of the marks constraints (`mem_append_left`); the frozen marks window adds no memOp /
mapOp / hash / range, so every memory / table leg transfers by rewriting the logs. -/
theorem stepMarks_restrict
    (hsat : Satisfied2 hash (automataflStepMarksDescN n) minit mfin maddrs t) :
    Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t := by
  refine ⟨?_, ?_, ?_, hsat.memAddrsNodup, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    exact hsat.rowConstraints i hi c (List.mem_append_left _ hc)
  · intro i _; trivial
  · intro i _ r hr; cases hr
  · intro op hop
    exact hsat.memClosed op (by rw [memLog_restrict]; exact hop)
  · rw [← memLog_restrict]; exact hsat.memDisciplined
  · rw [← memLog_restrict]; exact hsat.memBalanced
  · rw [← memLog_restrict]; exact hsat.memTableFaithful
  · rw [← mapLog_restrict]; exact hsat.mapTableFaithful

end Restrict

/-! ## §5 — MEMBERSHIP OF THE MARKS WINDOW in the marks descriptor. -/

theorem mem_sm_step {n : Nat} {g : VmConstraint2} (hg : g ∈ (automataflStepDescN n).constraints) :
    g ∈ (automataflStepMarksDescN n).constraints := List.mem_append_left _ hg

theorem mem_sm_tail {n : Nat} {g : VmConstraint2} (hg : g ∈ stepMarksTail n) :
    g ∈ (automataflStepMarksDescN n).constraints := List.mem_append_right _ hg

/-! ## §6 — THE FROZEN-MARKS WINDOW CARRY (the seam ingredient).

`marksPack_pi_of_mem` (M0), fed the window's three ingredients, pins the published `marksIn` window to
the base-4 pack of the decoded `marksIn` indicator — so `RM.OUT.marks == A.IN.marks` is a base-4
injective (hash-free) window equality, exactly as the resolve-marks marks seam. -/

section WindowCarry
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- The `{0,1}` range gate of `marksIn` cell `idx` is emitted. -/
theorem mem_sm_marks_range (idx : Nat) (hidx : idx < n * n) :
    (.base (.gate (Dregg2.Circuit.Emit.AutomataflCommit.memberExpr (sMarksInCell n idx) [0, 1]))
      : VmConstraint2) ∈ (automataflStepMarksDescN n).constraints :=
  mem_sm_tail
    (Dregg2.Circuit.Emit.AutomataflLegCEmit.mem_marks_range hidx (sMarksInCell n) (sMarksInFelt n)
      (sPiMarksIn n))

/-- The base-4 pack gate of `marksIn` felt `j` is emitted. -/
theorem mem_sm_marks_pack (j : Nat) (hj : j < feltCount n) :
    Dregg2.Circuit.Emit.AutomataflCommit.linGate
        (Dregg2.Circuit.Emit.AutomataflCommit.packTermsAt n j (sMarksInCell n) (sMarksInFelt n)) 0
      ∈ (automataflStepMarksDescN n).constraints :=
  mem_sm_tail
    (Dregg2.Circuit.Emit.AutomataflLegCEmit.mem_marks_pack hj (sMarksInCell n) (sMarksInFelt n)
      (sPiMarksIn n))

/-- The `.piBinding` of `marksIn` felt `j` is emitted. -/
theorem mem_sm_marks_pi (j : Nat) (hj : j < feltCount n) :
    (.base (.piBinding VmRow.first (sMarksInFelt n j) (sPiMarksIn n + j)) : VmConstraint2)
      ∈ (automataflStepMarksDescN n).constraints :=
  mem_sm_tail
    (Dregg2.Circuit.Emit.AutomataflLegCEmit.mem_marks_pi hj (sMarksInCell n) (sMarksInFelt n)
      (sPiMarksIn n))

/-- The `marksIn` cells are indicator bits (from the emitted `{0,1}` gate). -/
theorem sm_marksAlpha_of_sat
    (hsat : Satisfied2 hash (automataflStepMarksDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (idx : Nat) (hidx : idx < n * n) :
    (envAt t 0).loc (sMarksInCell n idx) = 0 ∨ (envAt t 0).loc (sMarksInCell n idx) = 1 :=
  marksAlpha_of_mem hsat hc hlen (sMarksInCell n) idx (mem_sm_marks_range idx hidx)

/-- **`stepMarks_marksIn_pi_of_sat` — THE WINDOW CARRY.** The published `marksIn` window
`PI[sPiMarksIn + j]` IS (mod `p`) the `j`-th packed felt of the `marksIn` indicator decoded off the
descriptor's own cell columns. Base-4 injective, hash-free — the seam to the resolve-marks leg's
`marksOut`. -/
theorem stepMarks_marksIn_pi_of_sat
    (hsat : Satisfied2 hash (automataflStepMarksDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    t.pub (sPiMarksIn n + j)
      ≡ packCell (marksCode (marksDecodeAt n (sMarksInCell n) (envAt t 0)) n) j [ZMOD 2013265921] :=
  marksPack_pi_of_mem hsat hlen (sMarksInCell n) (sMarksInFelt n)
    (sPiMarksIn n) j (fun i hi => sm_marksAlpha_of_sat hsat hc hlen i hi)
    (mem_sm_marks_pack j hj) (mem_sm_marks_pi j hj)

/-- **`stepMarks_marksOut_eq_marksIn` — THE FREEZE.** The step publishes the marks window ONCE. Its OUT
window's marks slice (`sPiMarksOut`) reads the SAME PIs as its IN window's (`sPiMarksIn`), so the marks
the leg carries OUT are the marks it carried IN — `marksOut = marksIn`, by construction. The first
conjunct restates the window carry AT the OUT window (so the OUT marks felts genuinely ARE the pack of
the frozen indicator); the second is the value-level identity the fold's clean sub-chain reads. -/
theorem stepMarks_marksOut_eq_marksIn
    (hsat : Satisfied2 hash (automataflStepMarksDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) (j : Nat) (hj : j < feltCount n) :
    (t.pub (sPiMarksOut n + j)
      ≡ packCell (marksCode (marksDecodeAt n (sMarksInCell n) (envAt t 0)) n) j [ZMOD 2013265921])
    ∧ t.pub (sPiMarksOut n + j) = t.pub (sPiMarksIn n + j) :=
  ⟨stepMarks_marksIn_pi_of_sat hsat hc hlen j hj, rfl⟩

end WindowCarry

/-! ## §7 — THE BOARD HALF, REUSED (the KEY OBSERVATION exploited).

`automatonStepCfg` is marks-independent, so the emitted `new` board is UNCHANGED by the marks carry:
the automaton-step capstone is `astep_sat_imp_automatonStepCfgN` on the RESTRICTED step trace, verbatim. -/

section BoardHalf
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **`astep_marks_sat_imp_automatonStepCfgN` — THE M6′ STEP CAPSTONE.** Off the marks-carrying step
descriptor, the decoded NEW board cell IS `AutomataflRules.automatonStepCfg`'s cell (the DEPLOYED
`.column` tie-break) — the SAME conclusion as `astep_sat_imp_automatonStepCfgN`, off the marks
descriptor, because the automaton step never reads marks. -/
theorem astep_marks_sat_imp_automatonStepCfgN (n : Nat) (hn1 : 1 ≤ n) (hn : (n : ℤ) < 2013265921)
    (hn99 : (n : ℤ) ≤ 99) (hwin : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921)
    (hsat : Satisfied2 hash (automataflStepMarksDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (automatonStepCfg ⟨.column⟩ (boardDecodeN n (envAt t i))).size = n
    ∧ (∀ x y : Nat, x < n → y < n →
        codeToParticle ((envAt t i).loc (NGen.new n (y * n + x)))
          = (automatonStepCfg ⟨.column⟩ (boardDecodeN n (envAt t i))).cellAt ⟨x, y⟩) :=
  astep_sat_imp_automatonStepCfgN n hn1 hn hn99 hwin (stepMarks_restrict hsat) hc i hi

/-- The step capstone at the deployed `n = 11`. -/
theorem astep_marks_sat_imp_automatonStepCfg11
    (hsat : Satisfied2 hash (automataflStepMarksDescN 11) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (automatonStepCfg ⟨.column⟩ (boardDecodeN 11 (envAt t i))).size = 11
    ∧ (∀ x y : Nat, x < 11 → y < 11 →
        codeToParticle ((envAt t i).loc (NGen.new 11 (y * 11 + x)))
          = (automatonStepCfg ⟨.column⟩ (boardDecodeN 11 (envAt t i))).cellAt ⟨x, y⟩) :=
  astep_marks_sat_imp_automatonStepCfgN 11 (by norm_num) (by norm_num) (by norm_num)
    (by decide) hsat hc i hi

/-- The step capstone at `n = 2` (the minimal instance). -/
theorem astep_marks_sat_imp_automatonStepCfg2
    (hsat : Satisfied2 hash (automataflStepMarksDescN 2) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (automatonStepCfg ⟨.column⟩ (boardDecodeN 2 (envAt t i))).size = 2
    ∧ (∀ x y : Nat, x < 2 → y < 2 →
        codeToParticle ((envAt t i).loc (NGen.new 2 (y * 2 + x)))
          = (automatonStepCfg ⟨.column⟩ (boardDecodeN 2 (envAt t i))).cellAt ⟨x, y⟩) :=
  astep_marks_sat_imp_automatonStepCfgN 2 (by norm_num) (by norm_num) (by norm_num)
    (by decide) hsat hc i hi

end BoardHalf

/-! ## §8 — SHAPE CANARIES. -/

#guard (automataflStepMarksDescN 11).name == "dregg-automatafl-step-marks-n11"
#guard (automataflStepMarksDescN 11).tables.length == 0
#guard (automataflStepMarksDescN 11).hashSites.length == 0
#guard (automataflStepMarksDescN 11).ranges.length == 0
#guard (automataflStepMarksDescN 11).traceWidth == A_WIDTH_N 11 + 11 * 11 + feltCount 11
#guard (automataflStepMarksDescN 11).piCount == A_PI_COUNT_N 11 + feltCount 11
#guard feltCount 11 == 9
#guard marksWindowLanes 11 == 9
-- The marks window sits ABOVE the step columns / PIs (no collision with the board/auto seam).
#guard SM0 11 == A_WIDTH_N 11
#guard sPiMarksIn 11 == A_PI_COUNT_N 11
#guard sPiMarksOut 11 == sPiMarksIn 11

/-! ## §9 — Axiom hygiene. -/

#assert_axioms tail_all_base
#assert_axioms tail_memfree
#assert_axioms tail_mapfree
#assert_axioms memOpsOf_restrict
#assert_axioms stepMarks_restrict
#assert_axioms stepMarks_marksIn_pi_of_sat
#assert_axioms stepMarks_marksOut_eq_marksIn
#assert_axioms astep_marks_sat_imp_automatonStepCfgN
#assert_axioms astep_marks_sat_imp_automatonStepCfg11
#assert_axioms astep_marks_sat_imp_automatonStepCfg2

end Dregg2.Circuit.Emit.AutomataflStepMarksCapstone
