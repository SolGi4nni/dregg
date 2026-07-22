/-
# `AutomataflTurnCapstone` — THE WHOLE TURN as ONE theorem, at the deployed `n = 11`.

Both legs are proven at `n = 11` (committed elsewhere):

* **Leg R** (`AutomataflResolveMovesCapstone.resolve_sat_imp_roundBoard11`): the decoded FINAL
  corrected board cell `cMidV4` IS the board `AutomataflRules.roundStep` resolves FROM — `old` on a
  clash, the VALIDATED `resolveMoves` cell otherwise (the PRE-automaton board).
* **Leg A** (`AutomataflStepStep.astep_sat_imp_automatonStepCfgN`): the STEP descriptor's new board
  is `AutomataflRules.automatonStepCfg ⟨.column⟩` of its decoded OLD board.

This file COMPOSES them into the whole turn, on a CLEAN round (`clashCoords = []`, the completed
round that actually resolves — see `## The clash branch`), via the mid-board seam:

    codeToParticle(new)                                   -- Leg A's claimed new cell
      = (automatonStepCfg ⟨.column⟩ (boardDecodeN 11 tA)).cellAt        -- Leg A capstone
      = (automatonStepCfg ⟨.column⟩ (resolveMoves bR [ma,mb])).cellAt   -- SEAM + Leg R capstone
      = outcomeBoard (roundStep ⟨.column⟩ g (openRound bR seats) [ma,mb]).cellAt  -- roundStep_pair

The middle equality is `automatonStep_congr`: Leg A's decoded old board and Leg R's decoded mid
board (`= resolveMoves bR [ma,mb]` on the clean round) agree on size, automaton, `useColumnRule`, and
CELLS. The cell agreement is the SEAM the fold enforces: Leg A consumes as its OLD board exactly the
mid board Leg R published.

## The seam, and how it is discharged

The main theorem `turn_sat_imp_roundStep` carries the seam as the fold-enforced BOARD AGREEMENT
(cells `hseamCell`, automaton `hseamAuto`). Two companions show that agreement is DISCHARGEABLE
crypto-free from PUBLIC-INPUT equality — the thing a fold / light client actually reads and
constrains — with NO hash and NO chip-table soundness assumption:

* `seamAuto_of_pi` — the automaton coordinate, from the two EMITTED `.piBinding`s
  (`astep_autoX/Y_pi_of_sat` on Leg A, `resolve_autoX/Y_pi_of_sat` on Leg R) plus the fold's PI
  equality. Fully emitted; no residual.
* `seamCell_of_cMidV4_pack` — the cells, via `AutomataflCommitRefine.seam_of_pack_congr` (whose
  engine is `pack_injective_modp`: base-4 positional decode, `packed < 4^15 < p`, no modular
  collision). Its Leg-R ingredient is `cMidV4` pack transport — now an EMITTED theorem (below).

`turn_sat_imp_roundStep_pi` threads all three into a single PI-carried statement.

## THE COMMITMENT PACKS `cMidV4` — the whole turn is fully emitted-crypto-free

`AutomataflResolveEmit.commitBoardsConstraints` packs the `NGen.cMidV4` columns (the THIRD-wound-fixed
FINAL board the roundStep-faithful capstone `resolve_sat_imp_roundBoard11` characterizes as the
`AutomataflRules.roundStep` resolve board), and `cMidV4` carries an `assert_member(cMidV4,{0,1,2,3})`
range gate. So `AutomataflResolveRefine.resolve_midPack_pi_of_sat` is an EMITTED transport
`PI[16+fc+j] = pack(cMidV4)`, and `turn_sat_imp_roundStep_pi` DISCHARGES the former `hRmidPack`
hypothesis from it — the whole turn takes ONLY the fold PI-equalities (`hseamPack`, `hseamAutoX`,
`hseamAutoY`), with NO hash, NO chip-table soundness, and NO un-emitted ingredient. `seamCell_of_
cMidV4_pack` keeps its general `hRmidPack` parameter (it is a crypto-free lemma with no descriptor
knowledge); the PI-carried capstone supplies the emitted transport for it. This file re-emits nothing.

(HISTORICAL: the resolve commitment used to pack `NGen.mid` — the V2 `write_mid_witnessed` board,
which differs from `cMidV4` whenever an occlusion / 2-cycle correction bites, so it committed the
WRONG board root and the cell seam carried `hRmidPack` as an un-emitted hypothesis. The re-point to
`cMidV4` closed that.)

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every exported theorem.
-/
import Dregg2.Circuit.Emit.AutomataflStepStep
import Dregg2.Circuit.Emit.AutomataflResolveMovesCapstone
import Dregg2.Circuit.Emit.AutomataflCommitRefine

namespace Dregg2.Circuit.Emit.AutomataflTurnCapstone

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt)
open Dregg2.Circuit.Emit.AutomataflStepRefine (StepCanon codeToParticle canon_loc eq_of_modEq_canon)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)
open Dregg2.Games.Automatafl (Board Coord Particle Move Pid automatonStep automatonStep_congr)
open Dregg2.Games.AutomataflRules
  (roundStep openRound automatonStepCfg automatonStepCfg_column_eq resolveMoves clashCoords
   moveLegalB resolvableB GameConfig GoalAssignment RoundOutcome)
open Dregg2.Circuit.Emit.AutomataflStepStep (astep_sat_imp_automatonStepCfgN)
open Dregg2.Circuit.Emit.AutomataflStepCapstone (boardDecodeN boardDecodeN_size)
open Dregg2.Circuit.Emit.AutomataflResolveMovesCapstone
  (resolve_sat_imp_roundBoard11 roundStep_pair_outcomeBoard outcomeBoard)
open Dregg2.Circuit.Emit.AutomataflResolveRefine (boardDecodeOldN moveDecodeN)
open Dregg2.Circuit.Emit.AutomataflCommitRefine
  (boardDecodeCommitAt seam_of_pack_congr astep_oldPack_pi_of_sat
   astep_autoX_pi_of_sat astep_autoY_pi_of_sat)
open Dregg2.Circuit.Emit.AutomataflCommit (boardCode packCell feltCount)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §0 — `resolveMoves` preserves every board field except the cells. -/

theorem resolveMoves_size (b : Board) (ms : List Move) :
    (resolveMoves b ms).size = b.size := by
  unfold resolveMoves; split <;> rfl

theorem resolveMoves_automaton (b : Board) (ms : List Move) :
    (resolveMoves b ms).automaton = b.automaton := by
  unfold resolveMoves; split <;> rfl

theorem resolveMoves_useColumnRule (b : Board) (ms : List Move) :
    (resolveMoves b ms).useColumnRule = b.useColumnRule := by
  unfold resolveMoves; split <;> rfl

/-! ## §1 — cell-decode reductions. -/

/-- `boardDecodeN`'s in-bounds cell IS the felt-decode of the `old` column. -/
theorem boardDecodeN_cellAt (n : Nat) (e : VmRowEnv) (x y : Nat) (hx : x < n) (hy : y < n) :
    (boardDecodeN n e).cellAt ⟨x, y⟩
      = codeToParticle (e.loc (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.old n (y * n + x))) := by
  simp only [Board.cellAt, boardDecodeN]
  rw [if_pos ⟨hx, hy⟩]

/-- `boardDecodeCommitAt`'s in-bounds cell IS the felt-decode of its cell column. -/
theorem boardDecodeCommitAt_cellAt (n : Nat) (cellCol : Nat → Nat) (e : VmRowEnv)
    (x y : Nat) (hx : x < n) (hy : y < n) :
    (boardDecodeCommitAt n cellCol e).cellAt ⟨x, y⟩
      = codeToParticle (e.loc (cellCol (y * n + x))) := by
  simp only [Board.cellAt, boardDecodeCommitAt]
  rw [if_pos ⟨hx, hy⟩]

/-! ## §2 — THE WHOLE TURN (clean round), seam carried as the fold-enforced board agreement. -/

/-- **`turn_sat_imp_roundStep` — THE PROOF CAPSTONE, at the deployed `n = 11`.**

Given a satisfying, canonical Leg-R (resolve) first row and a satisfying, canonical Leg-A (step)
first row, joined by the FOLD-ENFORCED mid-board seam (`hseamCell` cells + `hseamAuto` automaton:
Leg A's decoded OLD board equals Leg R's decoded `cMidV4` board / the round's resolved board), the
STEP descriptor's decoded NEW board IS the board `AutomataflRules.roundStep` produces this round,
cell-wise, on a CLEAN round (`hclean : clashCoords = []`).

Spec-side round preconditions `hfresh` (both submissions are fresh & legal) and `hres` (the round is
resolvable) are exactly `roundStep_pair_outcomeBoard`'s. The tie-break is the DEPLOYED default
(`⟨.column⟩`). See `## The seam` and `## HONEST RESIDUAL` for how the seam discharges. -/
theorem turn_sat_imp_roundStep
    {hashR : List ℤ → ℤ} {minitR : ℤ → ℤ} {mfinR : ℤ → ℤ × Nat} {maddrsR : List ℤ} {tR : VmTrace}
    {hashA : List ℤ → ℤ} {minitA : ℤ → ℤ} {mfinA : ℤ → ℤ × Nat} {maddrsA : List ℤ} {tA : VmTrace}
    (g : GoalAssignment) (seats : List Pid)
    (hsatR : Satisfied2 hashR
      (Dregg2.Circuit.Emit.AutomataflResolveEmit.automataflResolveDescN 11) minitR mfinR maddrsR tR)
    (hcR : StepCanon tR) (hlenR : 1 < tR.rows.length)
    (hsatA : Satisfied2 hashA
      (Dregg2.Circuit.Emit.AutomataflStepEmit.automataflStepDescN 11) minitA mfinA maddrsA tA)
    (hcA : StepCanon tA) (hlenA : 1 < tA.rows.length)
    (hclean : clashCoords (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = [])
    (hfresh : ([moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1].filter
        (fun m => seats.contains m.who
          && moveLegalB (boardDecodeOldN 11 (envAt tR 0)) [] m))
        = [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1])
    (hres : resolvableB (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = true)
    (hseamCell : ∀ x y : Nat, x < 11 → y < 11 →
        (boardDecodeN 11 (envAt tA 0)).cellAt ⟨x, y⟩
          = codeToParticle ((envAt tR 0).loc
              (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.cMidV4 11 (y * 11 + x))))
    (hseamAuto : (boardDecodeN 11 (envAt tA 0)).automaton
        = (boardDecodeOldN 11 (envAt tR 0)).automaton) :
    ∀ x y : Nat, x < 11 → y < 11 →
      codeToParticle ((envAt tA 0).loc
          (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.new 11 (y * 11 + x)))
        = (outcomeBoard (roundStep ⟨.column⟩ g
              (openRound (boardDecodeOldN 11 (envAt tR 0)) seats)
              [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1])).cellAt ⟨x, y⟩ := by
  set bR := boardDecodeOldN 11 (envAt tR 0) with hbR
  set mv0 := moveDecodeN 11 (envAt tR 0) 0 with hmv0
  set mv1 := moveDecodeN 11 (envAt tR 0) 1 with hmv1
  set bA := boardDecodeN 11 (envAt tA 0) with hbA
  -- (i) roundStep's outcome board, on the clean round, IS `automatonStepCfg ⟨.column⟩ (resolveMoves …)`.
  have hround := roundStep_pair_outcomeBoard ⟨.column⟩ g bR seats mv0 mv1 hfresh hres
  rw [if_pos hclean] at hround
  -- (ii) the two input boards agree on every field: size, automaton, useColumnRule, cells.
  have hcells : ∀ c : Coord, c.x < bA.size → c.y < bA.size →
      bA.cellAt c = (resolveMoves bR [mv0, mv1]).cellAt c := by
    rintro ⟨cx, cy⟩ hcx hcy
    have hx : cx < 11 := by simpa [hbA, boardDecodeN_size] using hcx
    have hy : cy < 11 := by simpa [hbA, boardDecodeN_size] using hcy
    have hcap := resolve_sat_imp_roundBoard11 hsatR hcR 0 (by omega) cx cy hx hy
    rw [if_neg (fun hne => hne hclean)] at hcap
    exact (hseamCell cx cy hx hy).trans hcap
  have hsz : bA.size = (resolveMoves bR [mv0, mv1]).size := by
    rw [resolveMoves_size]; simp [hbA, hbR, boardDecodeN_size, boardDecodeOldN]
  have hau : bA.automaton = (resolveMoves bR [mv0, mv1]).automaton := by
    rw [resolveMoves_automaton]; exact hseamAuto
  have hcol : bA.useColumnRule = (resolveMoves bR [mv0, mv1]).useColumnRule := by
    rw [resolveMoves_useColumnRule]; simp [hbA, hbR, boardDecodeN, boardDecodeOldN]
  obtain ⟨-, -, hcongr⟩ := automatonStep_congr bA (resolveMoves bR [mv0, mv1]) hsz hau hcol hcells
  -- (iii) bridge `automatonStepCfg ⟨.column⟩` to `automatonStep` on both boards (both use the column rule).
  have hbrA : automatonStepCfg ⟨.column⟩ bA = automatonStep bA :=
    automatonStepCfg_column_eq ⟨.column⟩ bA rfl (by simp [hbA, boardDecodeN])
  have hbrR : automatonStepCfg ⟨.column⟩ (resolveMoves bR [mv0, mv1])
      = automatonStep (resolveMoves bR [mv0, mv1]) :=
    automatonStepCfg_column_eq ⟨.column⟩ _ rfl
      (by rw [resolveMoves_useColumnRule]; simp [hbR, boardDecodeOldN])
  -- (iv) compose: Leg A's new cell → roundStep's outcome cell.
  intro x y hx hy
  obtain ⟨-, hAcell⟩ := astep_sat_imp_automatonStepCfgN 11 (by norm_num) (by norm_num)
    (by norm_num) (by decide) hsatA hcA 0 (by omega)
  have hAxy := hAcell x y hx hy
  rw [hround, hbrR, ← hcongr ⟨x, y⟩ (by simpa [hbA, boardDecodeN_size] using hx)
      (by simpa [hbA, boardDecodeN_size] using hy), ← hbrA]
  exact hAxy

/-! ## §3 — THE SEAM, DISCHARGED CRYPTO-FREE FROM PUBLIC-INPUT EQUALITY. -/

/-- **`seamAuto_of_pi` — the automaton coordinate seam, fully from EMITTED `.piBinding`s.** Leg A's
decoded old-board automaton equals Leg R's decoded old-board automaton, derived from the two emitted
automaton `.piBinding`s on each side and the fold's PI equality. No residual: the AUTO commitment is
emitted on both `descN`. -/
theorem seamAuto_of_pi
    {hashR : List ℤ → ℤ} {minitR : ℤ → ℤ} {mfinR : ℤ → ℤ × Nat} {maddrsR : List ℤ} {tR : VmTrace}
    {hashA : List ℤ → ℤ} {minitA : ℤ → ℤ} {mfinA : ℤ → ℤ × Nat} {maddrsA : List ℤ} {tA : VmTrace}
    (hsatR : Satisfied2 hashR
      (Dregg2.Circuit.Emit.AutomataflResolveEmit.automataflResolveDescN 11) minitR mfinR maddrsR tR)
    (hcR : StepCanon tR) (hlenR : 1 < tR.rows.length)
    (hsatA : Satisfied2 hashA
      (Dregg2.Circuit.Emit.AutomataflStepEmit.automataflStepDescN 11) minitA mfinA maddrsA tA)
    (hcA : StepCanon tA) (hlenA : 1 < tA.rows.length)
    (hseamAutoX : tR.pub (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.AUTO_PI_BASE 11)
      = tA.pub (Dregg2.Circuit.Emit.AutomataflStepEmit.AUTO_PI_BASE 11))
    (hseamAutoY : tR.pub (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.AUTO_PI_BASE 11 + 1)
      = tA.pub (Dregg2.Circuit.Emit.AutomataflStepEmit.AUTO_PI_BASE 11 + 1)) :
    (boardDecodeN 11 (envAt tA 0)).automaton
      = (boardDecodeOldN 11 (envAt tR 0)).automaton := by
  have haX : (envAt tA 0).loc (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.AX 11)
      = (envAt tR 0).loc (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.AX_C 11) :=
    eq_of_modEq_canon (canon_loc hcA 0 _) (canon_loc hcR 0 _)
      (((astep_autoX_pi_of_sat hsatA hlenA).trans
        (hseamAutoX ▸ (Dregg2.Circuit.Emit.AutomataflResolveRefine.resolve_autoX_pi_of_sat
          hsatR hlenR).symm)))
  have haY : (envAt tA 0).loc (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.AY 11)
      = (envAt tR 0).loc (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.AY_C 11) :=
    eq_of_modEq_canon (canon_loc hcA 0 _) (canon_loc hcR 0 _)
      (((astep_autoY_pi_of_sat hsatA hlenA).trans
        (hseamAutoY ▸ (Dregg2.Circuit.Emit.AutomataflResolveRefine.resolve_autoY_pi_of_sat
          hsatR hlenR).symm)))
  simp only [boardDecodeN, boardDecodeOldN, haX, haY]

/-- **`seamCell_of_cMidV4_pack` — the cell seam, crypto-free via base-4 pack injectivity.** Given
Leg A's EMITTED old-board pack transport and Leg R's `cMidV4` pack transport (`hRmidPack` — now the
EMITTED `AutomataflResolveRefine.resolve_midPack_pi_of_sat`, which the PI-carried capstone supplies),
both pinned to the SAME published PI slot by the fold (`hseamPack`), `seam_of_pack_congr` (engine:
`pack_injective_modp`, no modular collision) yields Leg A's decoded old cell = Leg R's decoded
`cMidV4` cell at every in-bounds coordinate. This lemma keeps `hRmidPack` as a general parameter so it
stays a pure crypto-free statement with no descriptor knowledge. -/
theorem seamCell_of_cMidV4_pack
    {tR : VmTrace}
    {hashA : List ℤ → ℤ} {minitA : ℤ → ℤ} {mfinA : ℤ → ℤ × Nat} {maddrsA : List ℤ} {tA : VmTrace}
    {seamBase : Nat}
    (hsatA : Satisfied2 hashA
      (Dregg2.Circuit.Emit.AutomataflStepEmit.automataflStepDescN 11) minitA mfinA maddrsA tA)
    (hcA : StepCanon tA) (hlenA : 1 < tA.rows.length)
    (hRmidPack : ∀ j, j < feltCount 11 →
      tR.pub (seamBase + j)
        ≡ packCell (boardCode (boardDecodeCommitAt 11
            (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.cMidV4 11) (envAt tR 0)) 11) j
          [ZMOD 2013265921])
    (hseamPack : ∀ j, j < feltCount 11 → tR.pub (seamBase + j) = tA.pub (16 + j)) :
    ∀ x y : Nat, x < 11 → y < 11 →
      (boardDecodeN 11 (envAt tA 0)).cellAt ⟨x, y⟩
        = codeToParticle ((envAt tR 0).loc
            (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.cMidV4 11 (y * 11 + x))) := by
  have hpack := seam_of_pack_congr (n := 11)
    (boardDecodeCommitAt 11 (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.old 11) (envAt tA 0))
    (boardDecodeCommitAt 11 (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.cMidV4 11) (envAt tR 0))
    (fun j => tA.pub (16 + j)) (fun j => tR.pub (seamBase + j))
    (fun j hj => astep_oldPack_pi_of_sat hsatA hcA hlenA j hj)
    (fun j hj => hRmidPack j hj)
    (fun j hj => (hseamPack j hj).symm)
  intro x y hx hy
  rw [boardDecodeN_cellAt 11 (envAt tA 0) x y hx hy,
    ← boardDecodeCommitAt_cellAt 11 (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.old 11)
        (envAt tA 0) x y hx hy,
    hpack x y hx hy,
    boardDecodeCommitAt_cellAt 11 (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.cMidV4 11)
        (envAt tR 0) x y hx hy]

/-- **`turn_sat_imp_roundStep_pi` — the whole turn with the seam reduced to PUBLIC-INPUT equalities,
now FULLY EMITTED-CRYPTO-FREE.** Same conclusion as `turn_sat_imp_roundStep`, but the board-agreement
seam is DISCHARGED inside from ONLY the fold's cell/automaton PI equalities (`hseamPack`,
`hseamAutoX`, `hseamAutoY`). Leg R's `cMidV4` pack transport — the ingredient that used to be carried
as the un-emitted hypothesis `hRmidPack` — is now the EMITTED theorem
`AutomataflResolveRefine.resolve_midPack_pi_of_sat` (the commitment packs `cMidV4`), discharged
below. The seam window is the deployed MID commitment slot `[16 + fc, 16 + 2·fc)` with
`fc = feltCount 11`. Everything on this path is emitted-and-proven: NO hash, NO chip-table soundness,
NO un-emitted hypothesis — the whole turn takes only the fold PI-equalities. -/
theorem turn_sat_imp_roundStep_pi
    {hashR : List ℤ → ℤ} {minitR : ℤ → ℤ} {mfinR : ℤ → ℤ × Nat} {maddrsR : List ℤ} {tR : VmTrace}
    {hashA : List ℤ → ℤ} {minitA : ℤ → ℤ} {mfinA : ℤ → ℤ × Nat} {maddrsA : List ℤ} {tA : VmTrace}
    (g : GoalAssignment) (seats : List Pid)
    (hsatR : Satisfied2 hashR
      (Dregg2.Circuit.Emit.AutomataflResolveEmit.automataflResolveDescN 11) minitR mfinR maddrsR tR)
    (hcR : StepCanon tR) (hlenR : 1 < tR.rows.length)
    (hsatA : Satisfied2 hashA
      (Dregg2.Circuit.Emit.AutomataflStepEmit.automataflStepDescN 11) minitA mfinA maddrsA tA)
    (hcA : StepCanon tA) (hlenA : 1 < tA.rows.length)
    (hclean : clashCoords (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = [])
    (hfresh : ([moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1].filter
        (fun m => seats.contains m.who
          && moveLegalB (boardDecodeOldN 11 (envAt tR 0)) [] m))
        = [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1])
    (hres : resolvableB (boardDecodeOldN 11 (envAt tR 0))
        [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1] = true)
    (hseamPack : ∀ j, j < feltCount 11 → tR.pub (16 + feltCount 11 + j) = tA.pub (16 + j))
    (hseamAutoX : tR.pub (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.AUTO_PI_BASE 11)
      = tA.pub (Dregg2.Circuit.Emit.AutomataflStepEmit.AUTO_PI_BASE 11))
    (hseamAutoY : tR.pub (Dregg2.Circuit.Emit.AutomataflResolveEmit.NGen.AUTO_PI_BASE 11 + 1)
      = tA.pub (Dregg2.Circuit.Emit.AutomataflStepEmit.AUTO_PI_BASE 11 + 1)) :
    ∀ x y : Nat, x < 11 → y < 11 →
      codeToParticle ((envAt tA 0).loc
          (Dregg2.Circuit.Emit.AutomataflStepEmit.NGen.new 11 (y * 11 + x)))
        = (outcomeBoard (roundStep ⟨.column⟩ g
              (openRound (boardDecodeOldN 11 (envAt tR 0)) seats)
              [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1])).cellAt ⟨x, y⟩ :=
  turn_sat_imp_roundStep g seats hsatR hcR hlenR hsatA hcA hlenA hclean hfresh hres
    (seamCell_of_cMidV4_pack (seamBase := 16 + feltCount 11) hsatA hcA hlenA
      (fun j hj => Dregg2.Circuit.Emit.AutomataflResolveRefine.resolve_midPack_pi_of_sat
        hsatR hcR hlenR j hj)
      hseamPack)
    (seamAuto_of_pi hsatR hcR hlenR hsatA hcA hlenA hseamAutoX hseamAutoY)

/-! ## The clash branch (honest scope).

On a CLASH (`clashCoords ≠ []`), `roundStep` returns `.again { board := bR, … }`: the round
re-enters with the OLD board UNCHANGED and NO automaton step happens (`roundStep_pair_outcomeBoard`
gives `outcomeBoard = bR`). There is no Leg-A composition on a clash — Leg A runs only on a resolved
board. So the whole-turn (resolve∘step) theorem is inherently the CLEAN / completed round, which is
what `turn_sat_imp_roundStep` states. The clash outcome board is `roundStep_pair_outcomeBoard`'s `bR`
branch, already proven, needing no seam. -/

/-! ## §4 — Axiom hygiene. -/

#assert_axioms resolveMoves_size
#assert_axioms resolveMoves_automaton
#assert_axioms resolveMoves_useColumnRule
#assert_axioms boardDecodeN_cellAt
#assert_axioms boardDecodeCommitAt_cellAt
#assert_axioms turn_sat_imp_roundStep
#assert_axioms seamAuto_of_pi
#assert_axioms seamCell_of_cMidV4_pack
#assert_axioms turn_sat_imp_roundStep_pi

end Dregg2.Circuit.Emit.AutomataflTurnCapstone
