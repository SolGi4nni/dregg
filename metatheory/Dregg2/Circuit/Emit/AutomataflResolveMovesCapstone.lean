/-
# Dregg2.Circuit.Emit.AutomataflResolveMovesCapstone — LEG R'S CAPSTONE AGAINST THE VALIDATED GAME.

The OLD capstone (`AutomataflResolveCapstone.resolve_sat_imp_resolveMid`) closes only at `NN = 2` and
against the OLD `Automatafl.resolveMid`, and §6 of that file documents WHY it is not restatable at
`n ≥ 3`: the OLD descriptor and the FIXED reference disagree on the OCCLUDED-STAYER class (defect #8).

This file is the CHUNK-4 landing that closes the DIRECT half of that wound IN THE CIRCUIT (the
occluded STAYER — a piece whose own move is blocked keeps its cell). The chunk-1/chunk-3 emitter grew
the corrected columns:

  * `cOccIncl` — the INCLUSIVE occlusion (destination endpoint included), which chunk 2
    (`AutomataflOcclusionBridgeN.occ_iff_blocked_of_sat`) proved equals the VALIDATED-game predicate
    `AutomataflRules.blockedB`.
  * `cCarryV2 i = surv · nz_i · (1 − occIncl_i) · (1 − nonLeave_i)` — the corrected carry, which now
    KEEPS the stayer: an occluded piece has `occIncl = 1`, so `cCarryV2 = 0`, so the emitted board
    rewrite no longer overwrites it.
  * `cNonLeave i`, `cResolvable`, `cWBoardV2`, `cMidV2` — the non-leaver bit, the resolvable surface,
    and the `cResolvable`-gated corrected board.

This file consumes those columns off `Satisfied2 (automataflResolveDescN n)`. It is downstream of the
bridge and of the OLD capstone, and is strictly ADDITIVE — it touches neither the OLD capstone nor the
chunk-1/2/3 emit/bridge objects.

The full `resolve_sat_imp_resolveMovesN` capstone is NOT assembled here: §7 exhibits a SECOND wound,
disjoint from defect #8, that makes the unconditional statement FALSE at `n ≥ 3` against this
descriptor. The DIRECT carry was corrected to inclusive occlusion (`cCarryV2` reads `cOccIncl =
blockedB`), but the FLOW-THROUGH bit `cFtA`/`cFtB` — and the `cBadA`/`cBadB`/`cResolvable` surface it
gates — still ride the EXCLUSIVE `cOcc = occluded`, so a piece riding into a downstream edge that is
inclusive-blocked (a non-mover sits on the downstream destination) is mishandled and the round is
wrongly declared unresolvable. `flowThroughOcclusionGap_witness_n3` is the executable falsifier.
Assembling the capstone is chunk 5's obligation and requires re-emitting the flow-through / resolvable
columns onto `cOccIncl` first.

## Axiom hygiene
`#assert_axioms` subset `{propext, Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`.
-/
import Dregg2.Circuit.Emit.AutomataflResolveCapstone
import Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN

namespace Dregg2.Circuit.Emit.AutomataflResolveMovesCapstone

open Dregg2.Circuit.Emit.AutomataflResolveEmit
open Dregg2.Circuit.Emit.AutomataflResolveMembership
open Dregg2.Circuit.Emit.AutomataflCoord
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)
open Dregg2.Circuit.Emit.AutomataflStepRefine
open Dregg2.Circuit.Emit.AutomataflResolveRefine
open Dregg2.Circuit.Emit.AutomataflResolveCapstone (BoardWindow mvLift occLift)
open Dregg2.Games.Automatafl (Board Coord Particle Move MoveValid occluded)

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! ## §1 — the board-size window for the chunk-4 landing.

A superset of the OLD `BoardWindow`: it adds the INCLUSIVE occlusion masked-sum bound `3n + 3 ≤ 999`
that `occ_iff_blocked_of_sat` needs (the exclusive `occluded` used `3n ≤ 999`; the inclusive
`blockedB` adds the destination line felt). Every field is EXPLICIT board arithmetic — decidable at a
concrete `n`, holding at `n = 2`, `n = 3`, `n = 11`. NON-VACUOUS at `n = 3` (a 3-line has an interior
cell, and a piece ON the destination now fires `blockedB`, which the exclusive `occluded` misses). -/
structure MovesWindow (n : Nat) : Prop where
  /-- The full OLD board window (drives `validMoveN_of_sat`, the coordinate decode, the exclusive
  occlusion bridge, and the pattern/selection extractions). -/
  base   : BoardWindow n
  /-- The INCLUSIVE occlusion masked-sum window (`3n + 3 ≤ 999`). -/
  msumI  : 3 * (n : ℤ) + 3 ≤ 999

theorem movesWindow_two : MovesWindow 2 :=
  ⟨Dregg2.Circuit.Emit.AutomataflResolveCapstone.boardWindow_two, by norm_num⟩
theorem movesWindow_three : MovesWindow 3 :=
  ⟨Dregg2.Circuit.Emit.AutomataflResolveCapstone.boardWindow_three, by norm_num⟩
theorem movesWindow_eleven : MovesWindow 11 :=
  ⟨Dregg2.Circuit.Emit.AutomataflResolveCapstone.boardWindow_eleven, by norm_num⟩

/-! ## §2 — `blockedV2N_of_sat`: the emitted INCLUSIVE occlusion column IS the VALIDATED-game
`AutomataflRules.blockedB`.

This wires chunk 2 (`occ_iff_blocked_of_sat`) through the membership navigators and the reference
`MoveValid` (from `validMoveN_of_sat`), off nothing but `Satisfied2 (automataflResolveDescN n)` and
the board window — no `resolvableB` hypothesis. It is the occlusion half of the defect-#8 closure:
the corrected carry reads THIS column, so the circuit's "is my move blocked" question is answered by
exactly the validated game's `blockedB`. -/
section Blocked
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- The two board decodes (this-file's re-export of `ResolveRefine`'s, and `OcclusionBridgeN`'s) are
the SAME structure literal, so `MoveValid` transports along `rfl`. -/
theorem bdMove_eq (which : Nat) (e : VmRowEnv) :
    MoveValid (boardDecodeOldN n e) (moveDecodeN n e which)
      ↔ MoveValid (Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.boardDecodeOldN n e)
          (Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.moveDecodeN n e which) := Iff.rfl

/-- **`blockedV2N_of_sat`.** `cOccIncl[which] = 1` iff the VALIDATED-game `blockedB` of the decoded
board / two decoded moves / decoded move `which` is `true`. UNCONDITIONAL (only the window). -/
theorem blockedV2N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (which : Nat) (hw : which < 2) :
    (envAt t i).loc (NGen.cOccIncl n which) = 1
      ↔ Dregg2.Games.AutomataflRules.blockedB (boardDecodeOldN n (envAt t i))
          [moveDecodeN n (envAt t i) which, moveDecodeN n (envAt t i) (1 - which)]
          (moveDecodeN n (envAt t i) which) = true := by
  have hvalid : Dregg2.Games.Automatafl.MoveValid
      (Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.boardDecodeOldN n (envAt t i))
      (Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.moveDecodeN n (envAt t i) which) :=
    (bdMove_eq which (envAt t i)).mp
      (validMoveN_of_sat hsat hc i hi which ((n : ℤ) - 1) W.base.pos W.base.lt_p rfl W.base.sqM
        W.base.rbits (mvLift n which hw))
  have h := Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.occ_iff_blocked_of_sat n which
    W.base.lt_p W.base.sq511 W.msumI hsat hc i hi (occLift n which hw)
    (Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.inclLiftN n which (NGen.occBase n which) hw rfl)
    (mvLift n which hw) (mvLift n (1 - which) (by omega)) hvalid
  exact h

end Blocked

/-! ## §3 — `carryV2ArithN_of_sat`: the corrected carry column is EXACTLY
`surv ∧ nz ∧ ¬occIncl ∧ ¬nonLeave`.

Pure gate algebra over columns already known boolean (`cCv1 = surv·nz`, `cCv2 = cCv1·(1−occIncl)`,
`cCarryV2 = cCv2·(1−nonLeave)`), the four-conjunct twin of `carryN_of_sat`. This is the CIRCUIT side of
the defect-#8 closure: `occIncl = 1` (occluded, via §2) OR `nonLeave = 1` (landing holds a non-mover)
each force `cCarryV2 = 0`, i.e. the piece is KEPT. -/
section CarryV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- Membership lift into `carryV2One n which` at either piece index. -/
theorem cv2Lift (which : Nat) (hw : which < 2) {g : VmConstraint2}
    (h : g ∈ NGen.carryV2One n which) : g ∈ (automataflResolveDescN n).constraints := by
  apply mem_resolve_of_mem_carryV2
  rw [NGen.carryV2Constraints]
  interval_cases which
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ h

/-- **`carryV2ArithN_of_sat`.** With the four inputs boolean, `cCarryV2[which]` is boolean and is `1`
iff all four of `surv`, `nz`, `¬occIncl`, `¬nonLeave` hold. -/
theorem carryV2ArithN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1)
    (hnz : (envAt t i).loc (NGen.nzCol n which) = 0 ∨ (envAt t i).loc (NGen.nzCol n which) = 1)
    (hoccI : (envAt t i).loc (NGen.cOccIncl n which) = 0
        ∨ (envAt t i).loc (NGen.cOccIncl n which) = 1)
    (hnl : (envAt t i).loc (NGen.cNonLeave n which) = 0
        ∨ (envAt t i).loc (NGen.cNonLeave n which) = 1) :
    ((envAt t i).loc (NGen.cCarryV2 n which) = 0 ∨ (envAt t i).loc (NGen.cCarryV2 n which) = 1)
      ∧ ((envAt t i).loc (NGen.cCarryV2 n which) = 1 ↔
          ((envAt t i).loc (NGen.cSurv n) = 1 ∧ (envAt t i).loc (NGen.nzCol n which) = 1
            ∧ (envAt t i).loc (NGen.cOccIncl n which) = 0
            ∧ (envAt t i).loc (NGen.cNonLeave n which) = 0)) := by
  set e := envAt t i with he
  -- cCv1 = surv · nz
  have hcv1 : e.loc (NGen.cCv1 n which) = e.loc (NGen.cSurv n) * e.loc (NGen.nzCol n which) := by
    have hmem : prodPin (NGen.cCv1 n which) (NGen.cSurv n) (NGen.nzCol n which)
        ∈ (automataflResolveDescN n).constraints :=
      cv2Lift which hw (List.mem_cons_self)
    exact prodN_of_sat hsat hc i hi (NGen.cCv1 n which) (NGen.cSurv n) (NGen.nzCol n which)
      hmem hsurv hnz
  have hcv1B : e.loc (NGen.cCv1 n which) = 0 ∨ e.loc (NGen.cCv1 n which) = 1 := by
    rcases hsurv with a | a <;> rcases hnz with b | b <;> rw [hcv1, a, b] <;> norm_num
  -- cCv2 = cCv1 · (1 − occIncl)
  have hcv2 : e.loc (NGen.cCv2 n which)
      = e.loc (NGen.cCv1 n which) - e.loc (NGen.cCv1 n which) * e.loc (NGen.cOccIncl n which) := by
    have hmem : cgH (NGen.cv2Head n which) ∈ (automataflResolveDescN n).constraints :=
      cv2Lift which hw (List.mem_cons_of_mem _ (List.mem_cons_self))
    have hg := rgateHN hsat i hi hmem
    have hE : (headToExpr (NGen.cv2Head n which)).eval e.loc
        = e.loc (NGen.cCv2 n which) + (-1) * e.loc (NGen.cCv1 n which)
          + e.loc (NGen.cCv1 n which) * e.loc (NGen.cOccIncl n which) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hcv1B with a | a <;> rcases hoccI with c | c <;> rw [a, c] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hcv2B : e.loc (NGen.cCv2 n which) = 0 ∨ e.loc (NGen.cCv2 n which) = 1 := by
    rcases hcv1B with a | a <;> rcases hoccI with c | c <;> rw [hcv2, a, c] <;> norm_num
  -- cCarryV2 = cCv2 · (1 − nonLeave)
  have hcarry : e.loc (NGen.cCarryV2 n which)
      = e.loc (NGen.cCv2 n which) - e.loc (NGen.cCv2 n which) * e.loc (NGen.cNonLeave n which) := by
    have hmem : cgH (NGen.carryV2Head n which) ∈ (automataflResolveDescN n).constraints :=
      cv2Lift which hw (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
    have hg := rgateHN hsat i hi hmem
    have hE : (headToExpr (NGen.carryV2Head n which)).eval e.loc
        = e.loc (NGen.cCarryV2 n which) + (-1) * e.loc (NGen.cCv2 n which)
          + e.loc (NGen.cCv2 n which) * e.loc (NGen.cNonLeave n which) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hcv2B with a | a <;> rcases hnl with d | d <;> rw [a, d] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hval : e.loc (NGen.cCarryV2 n which)
      = e.loc (NGen.cSurv n) * e.loc (NGen.nzCol n which)
        - e.loc (NGen.cSurv n) * e.loc (NGen.nzCol n which) * e.loc (NGen.cOccIncl n which)
        - (e.loc (NGen.cSurv n) * e.loc (NGen.nzCol n which)
            - e.loc (NGen.cSurv n) * e.loc (NGen.nzCol n which) * e.loc (NGen.cOccIncl n which))
          * e.loc (NGen.cNonLeave n which) := by rw [hcarry, hcv2, hcv1]
  refine ⟨?_, ?_⟩
  · rcases hcv2B with a | a <;> rcases hnl with d | d <;> rw [hcarry, a, d] <;> norm_num
  · rw [hval]
    rcases hsurv with a | a <;> rcases hnz with b | b <;> rcases hoccI with c | c <;>
      rcases hnl with d | d <;> rw [a, b, c, d] <;> norm_num

end CarryV2

/-! ## §4 — `nonLeaveGateN_of_sat`: the non-leaver bit is `landNz ∧ ¬carry_other`.

The circuit's rendering, at `m = 2`, of "piece `which`'s landing square is held by a piece that does
not itself leave": the landing square is non-vacuum (`cLandNz`) and the OTHER piece (the only other
mover) does not carry out of it (`carryCol (1−which) = 0`). Together with `carryV2ArithN_of_sat` this
pins the full corrected carry `cCarryV2 = surv·nz·(1−occIncl)·(1 − landNz·(1−carry_other))`. -/
section NonLeave
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- Membership lift into `nonLeaveOne n which` at either piece index. -/
theorem nlLift (which : Nat) (hw : which < 2) {g : VmConstraint2}
    (h : g ∈ NGen.nonLeaveOne n which) : g ∈ (automataflResolveDescN n).constraints := by
  apply mem_resolve_of_mem_nonLeave
  rw [NGen.nonLeaveConstraints]
  interval_cases which
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ h

/-- **`nonLeaveGateN_of_sat`.** `cNonLeave[which]` is boolean and is `1` iff `cLandNz[which] = 1` and
`carryCol (1−which) = 0`. -/
theorem nonLeaveGateN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hlandnz : (envAt t i).loc (NGen.cLandNz n which) = 0
        ∨ (envAt t i).loc (NGen.cLandNz n which) = 1)
    (hcarryOther : (envAt t i).loc (NGen.carryCol n (1 - which)) = 0
        ∨ (envAt t i).loc (NGen.carryCol n (1 - which)) = 1) :
    ((envAt t i).loc (NGen.cNonLeave n which) = 0 ∨ (envAt t i).loc (NGen.cNonLeave n which) = 1)
      ∧ ((envAt t i).loc (NGen.cNonLeave n which) = 1 ↔
          ((envAt t i).loc (NGen.cLandNz n which) = 1
            ∧ (envAt t i).loc (NGen.carryCol n (1 - which)) = 0)) := by
  set e := envAt t i with he
  have hmem : cgH (((Head.lin 1 (NGen.cNonLeave n which)).addLin (-1) (NGen.cLandNz n which)).addProd 1
              [(NGen.cLandNz n which), (NGen.carryCol n (1 - which))])
      ∈ (automataflResolveDescN n).constraints :=
    nlLift which hw (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have hg := rgateHN hsat i hi hmem
  have hE : (headToExpr (((Head.lin 1 (NGen.cNonLeave n which)).addLin (-1)
        (NGen.cLandNz n which)).addProd 1
        [(NGen.cLandNz n which), (NGen.carryCol n (1 - which))])).eval e.loc
      = e.loc (NGen.cNonLeave n which) + (-1) * e.loc (NGen.cLandNz n which)
        + e.loc (NGen.cLandNz n which) * e.loc (NGen.carryCol n (1 - which)) := rfl
  rw [hE] at hg
  have hnl : e.loc (NGen.cNonLeave n which)
      = e.loc (NGen.cLandNz n which)
        - e.loc (NGen.cLandNz n which) * e.loc (NGen.carryCol n (1 - which)) := by
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hlandnz with a | a <;> rcases hcarryOther with b | b <;> rw [a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_⟩
  · rcases hlandnz with a | a <;> rcases hcarryOther with b | b <;> rw [hnl, a, b] <;> norm_num
  · rw [hnl]
    rcases hlandnz with a | a <;> rcases hcarryOther with b | b <;> rw [a, b] <;> norm_num

end NonLeave

/-! ## §5 — `midV2CellN_of_sat`: the corrected board is the `cResolvable`-gated selection.

The emitted `cMidV2[c]` is `cResolvable · cWBoardV2[c] + (1 − cResolvable) · old[c]` — the circuit
analog of `resolveMoves b ms = if resolvableB then writeBoard … else b`, one cell at a time. -/
section MidV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- **`midV2CellN_of_sat`.** The corrected-board cell gate, rearranged (stated mod `p`). -/
theorem midV2CellN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) (c : Nat) (hcK : c < NGen.KK n) :
    (envAt t i).loc (NGen.cMidV2 n c)
      ≡ (envAt t i).loc (NGen.cResolvable n) * (envAt t i).loc (NGen.cWBoardV2 n c)
        + (envAt t i).loc (NGen.old n c)
        - (envAt t i).loc (NGen.cResolvable n) * (envAt t i).loc (NGen.old n c)
      [ZMOD 2013265921] := by
  have hmem : cgH (NGen.midV2CellHead n c) ∈ (automataflResolveDescN n).constraints := by
    apply mem_resolve_of_mem_midV2
    rw [NGen.midV2Constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hcK, rfl⟩)
  have hg := rgateHN hsat i hi hmem
  have hE : (headToExpr (NGen.midV2CellHead n c)).eval (envAt t i).loc
      = (envAt t i).loc (NGen.cMidV2 n c)
        + (-1) * ((envAt t i).loc (NGen.cResolvable n) * (envAt t i).loc (NGen.cWBoardV2 n c))
        + (-1) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.cResolvable n) * (envAt t i).loc (NGen.old n c) := rfl
  rw [hE] at hg
  exact (gate_modEq_iff (by ring)).mp hg

end MidV2

/-! ## §6 — `writeCellV2N_of_sat`: the corrected writeBoard-cell rewrite.

`NGen.writeCellV2Head n c` is `writeCellHead` with the OLD `carryCol` replaced by the corrected
`carryV2Col` and the output cell `cWBoardV2 c`. So the gate has the SAME degree-7 shape the proven
`writeCellN_of_sat` normalises — the MID cell is the OLD cell KEPT (unless it is a cleared source or a
landing target), plus each landing piece's particle, with the swap-restore term — but driven by the
corrected carry that keeps the occluded stayer. Stated mod `p`; `x`/`y` are the cell's column/row. -/
section WriteCellV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- **`writeCellV2N_of_sat`.** The emitted corrected `cWBoardV2` cell gate, rearranged. -/
theorem writeCellV2N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) (c y x : Nat) (hy : y = c / n) (hx : x = c % n)
    (hcK : c < NGen.KK n) :
    (envAt t i).loc (NGen.cWBoardV2 n c)
      ≡ (1 - (envAt t i).loc (NGen.carryV2Col n 0) * ((envAt t i).loc (NGen.wSrcRow n 0 y)
                * (envAt t i).loc (NGen.wSrcCol n 0 x))
           - (envAt t i).loc (NGen.carryV2Col n 0) * ((envAt t i).loc (NGen.wDstRow n 0 y)
                * (envAt t i).loc (NGen.wDstCol n 0 x))
           - (envAt t i).loc (NGen.carryV2Col n 1) * ((envAt t i).loc (NGen.wSrcRow n 1 y)
                * (envAt t i).loc (NGen.wSrcCol n 1 x))
           - (envAt t i).loc (NGen.carryV2Col n 1) * ((envAt t i).loc (NGen.wDstRow n 1 y)
                * (envAt t i).loc (NGen.wDstCol n 1 x))
           + (envAt t i).loc (NGen.carryV2Col n 0) * ((envAt t i).loc (NGen.wSrcRow n 0 y)
                * (envAt t i).loc (NGen.wSrcCol n 0 x)) * ((envAt t i).loc (NGen.carryV2Col n 1)
                * ((envAt t i).loc (NGen.wDstRow n 1 y) * (envAt t i).loc (NGen.wDstCol n 1 x)))
           + (envAt t i).loc (NGen.carryV2Col n 1) * ((envAt t i).loc (NGen.wSrcRow n 1 y)
                * (envAt t i).loc (NGen.wSrcCol n 1 x)) * ((envAt t i).loc (NGen.carryV2Col n 0)
                * ((envAt t i).loc (NGen.wDstRow n 0 y) * (envAt t i).loc (NGen.wDstCol n 0 x)))
           + (envAt t i).loc (NGen.carryV2Col n 0) * ((envAt t i).loc (NGen.wSrcRow n 0 y)
                * (envAt t i).loc (NGen.wSrcCol n 0 x)) * ((envAt t i).loc (NGen.carryV2Col n 1)
                * ((envAt t i).loc (NGen.wSrcRow n 1 y) * (envAt t i).loc (NGen.wSrcCol n 1 x)))
           + (envAt t i).loc (NGen.carryV2Col n 0) * ((envAt t i).loc (NGen.wDstRow n 0 y)
                * (envAt t i).loc (NGen.wDstCol n 0 x)) * ((envAt t i).loc (NGen.carryV2Col n 1)
                * ((envAt t i).loc (NGen.wDstRow n 1 y) * (envAt t i).loc (NGen.wDstCol n 1 x))))
          * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV2Col n 0) * ((envAt t i).loc (NGen.wDstRow n 0 y)
            * (envAt t i).loc (NGen.wDstCol n 0 x)) * (envAt t i).loc (NGen.particleCol n 0)
        + (envAt t i).loc (NGen.carryV2Col n 1) * ((envAt t i).loc (NGen.wDstRow n 1 y)
            * (envAt t i).loc (NGen.wDstCol n 1 x)) * (envAt t i).loc (NGen.particleCol n 1)
        - (envAt t i).loc (NGen.carryV2Col n 0) * ((envAt t i).loc (NGen.wDstRow n 0 y)
            * (envAt t i).loc (NGen.wDstCol n 0 x)) * ((envAt t i).loc (NGen.carryV2Col n 1)
            * ((envAt t i).loc (NGen.wDstRow n 1 y) * (envAt t i).loc (NGen.wDstCol n 1 x)))
            * (envAt t i).loc (NGen.particleCol n 1)
        [ZMOD 2013265921] := by
  subst hy; subst hx
  have hmem : cgH (NGen.writeCellV2Head n c) ∈ (automataflResolveDescN n).constraints := by
    apply mem_resolve_of_mem_midV2
    rw [NGen.midV2Constraints]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hcK, rfl⟩)
  have hg := rgateHN hsat i hi hmem
  have hshape : (headToExpr (NGen.writeCellV2Head n c)).eval (envAt t i).loc
      = (envAt t i).loc (NGen.cWBoardV2 n c) + (-1) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV2Col n 0) * (envAt t i).loc (NGen.wSrcRow n 0 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 0 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV2Col n 0) * (envAt t i).loc (NGen.wDstRow n 0 (c / n))
            * (envAt t i).loc (NGen.wDstCol n 0 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (-1) * ((envAt t i).loc (NGen.carryV2Col n 0) * (envAt t i).loc (NGen.wDstRow n 0 (c / n))
            * (envAt t i).loc (NGen.wDstCol n 0 (c % n)) * (envAt t i).loc (NGen.particleCol n 0))
        + (envAt t i).loc (NGen.carryV2Col n 1) * (envAt t i).loc (NGen.wSrcRow n 1 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 1 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV2Col n 1) * (envAt t i).loc (NGen.wDstRow n 1 (c / n))
            * (envAt t i).loc (NGen.wDstCol n 1 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (-1) * ((envAt t i).loc (NGen.carryV2Col n 1) * (envAt t i).loc (NGen.wDstRow n 1 (c / n))
            * (envAt t i).loc (NGen.wDstCol n 1 (c % n)) * (envAt t i).loc (NGen.particleCol n 1))
        + (-1) * ((envAt t i).loc (NGen.carryV2Col n 0) * (envAt t i).loc (NGen.wSrcRow n 0 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 0 (c % n)) * (envAt t i).loc (NGen.carryV2Col n 1)
            * (envAt t i).loc (NGen.wDstRow n 1 (c / n)) * (envAt t i).loc (NGen.wDstCol n 1 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (-1) * ((envAt t i).loc (NGen.carryV2Col n 1) * (envAt t i).loc (NGen.wSrcRow n 1 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 1 (c % n)) * (envAt t i).loc (NGen.carryV2Col n 0)
            * (envAt t i).loc (NGen.wDstRow n 0 (c / n)) * (envAt t i).loc (NGen.wDstCol n 0 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (-1) * ((envAt t i).loc (NGen.carryV2Col n 0) * (envAt t i).loc (NGen.wSrcRow n 0 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 0 (c % n)) * (envAt t i).loc (NGen.carryV2Col n 1)
            * (envAt t i).loc (NGen.wSrcRow n 1 (c / n)) * (envAt t i).loc (NGen.wSrcCol n 1 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (-1) * ((envAt t i).loc (NGen.carryV2Col n 0) * (envAt t i).loc (NGen.wDstRow n 0 (c / n))
            * (envAt t i).loc (NGen.wDstCol n 0 (c % n)) * (envAt t i).loc (NGen.carryV2Col n 1)
            * (envAt t i).loc (NGen.wDstRow n 1 (c / n)) * (envAt t i).loc (NGen.wDstCol n 1 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (envAt t i).loc (NGen.carryV2Col n 0) * (envAt t i).loc (NGen.wDstRow n 0 (c / n))
            * (envAt t i).loc (NGen.wDstCol n 0 (c % n)) * (envAt t i).loc (NGen.carryV2Col n 1)
            * (envAt t i).loc (NGen.wDstRow n 1 (c / n)) * (envAt t i).loc (NGen.wDstCol n 1 (c % n))
            * (envAt t i).loc (NGen.particleCol n 1) := rfl
  rw [hshape] at hg
  exact (gate_modEq_iff (by ring)).mp hg

end WriteCellV2

/-! ## §7 — THE FLOW-THROUGH OCCLUSION GAP: why `resolve_sat_imp_resolveMovesN` is NOT assembled
here, and which descriptor column is STILL WRONG. (A SECOND wound, disjoint from defect #8.)

Chunk 4 corrected the DIRECT carry: `cCarryV2 = surv · nz · (1 − cOccIncl) · (1 − cNonLeave)` reads
the INCLUSIVE occlusion `cOccIncl = blockedB` (§2), so an occluded piece that STAYS is now kept — the
defect-#8 occluded-stayer (`AutomataflResolveCapstone.occludedStayer_witness_n3`) resolves correctly.

But the CONFLUENCE / FLOW-THROUGH surface was NOT switched to inclusive occlusion. The descriptor's
flow-through bit `cFtA`/`cFtB` (`resolveFactsN_of_sat.ftAIff`/`ftBIff`) rides the EXCLUSIVE `occluded`
of the OTHER piece — `occluded bd [sa, sb] mb = false` — to decide whether A rides through B's vacated
source and continues along B's edge. `occluded` is INTERIOR-ONLY; the reference `landMap` uses
`blockedB` = `pathCells = interior ++ [dst]`, DESTINATION INCLUDED. They disagree exactly when the
downstream piece's move is clear through its interior but its DESTINATION holds a non-mover.

THE CLASS (n ≥ 3, `flowThroughOcclusionGap_witness_n3`).  A on `sa` wants `da = sb`, B's EMPTY source;
B nominally moves `sb → db` with `db` held by a non-mover `C`.  Then:

  * `blockedB bd [ma,mb] mb = true` (C on B's destination) but `occluded bd [sa,sb] mb = false`
    (B's interior is clear) — the exclusive/inclusive gap.
  * The REFERENCE: B's edge is blocked, so A's walk dead-ends on the emptied waypoint `sb`, and
    `landMap sa = da = sb`; the round is `resolvableB` and A moves `sa → sb`.
  * The DESCRIPTOR: `ftAIff` fires (`da = sb`, `bnz = 0`, `surv = 1`, `¬occluded_b`, `db ≠ sa`), so the
    ft-selected destination of A is `db` — the WRONG landing (it flows A through a blocked edge).
    `cLandNz 0 = 1` (`db` occupied) and `cCarryB = 0` (`sb` vacuum ⇒ `bnz = 0`) force `cNonLeave 0 = 1`
    (§4), hence `cBadA = cCarryA · cNonLeave 0 = 1`, hence `cResolvable = 0` (`resolvableConstraints`).
    So `cMidV2 = cResolvable · cWBoardV2 + (1 − cResolvable) · old = old` — the circuit declares the
    round UNRESOLVABLE and falls back to the IDENTITY board, while the reference moves A.

So `codeToParticle (cMidV2 …) = (resolveMoves …).cellAt …` is FALSE at `sa` for this witness: LHS
`= attractor` (A kept), RHS `= vacuum` (A vacated). The unconditional capstone is therefore NOT
provable at `n ≥ 3` (hence not at `n = 11`) against THIS descriptor — not for want of assembly, but
because `cFtA`/`cFtB` (and the `cBadA`/`cBadB`/`cResolvable` surface they gate) must be re-emitted to
ride the INCLUSIVE `cOccIncl = blockedB`, not the exclusive `cOcc = occluded`. That re-emit is chunk
5's obligation; the witness below is its executable falsifier — `decide`d entirely on the reference
semantics and the exact `ftAIff` antecedent, so it goes red the moment the fixed descriptor makes the
flow-through respect the blocked downstream destination. -/

section FlowThroughGap
open Dregg2.Games.AutomataflRules (blockedB carAt landMap resolvableB resolveMoves)

/-- 3×3 witness. A at `(2,0)` (attractor) wants `(1,0)` — B's EMPTY source and A's own dead-end
waypoint. B at `(1,0)` (vacuum source) nominally moves to `(0,0)`, held by a non-mover repulsor `C`.
A's onward edge through `(1,0)` into `(0,0)` is INCLUSIVE-blocked (`C` on B's destination) but
EXCLUSIVE-clear (B's interior is empty). The automaton sits at `(2,2)`, off both moves. -/
def ftBoard : Board :=
  Dregg2.Games.Automatafl.mkBoard 3
    [(⟨2, 0⟩, Particle.attractor), (⟨0, 0⟩, Particle.repulsor)] ⟨2, 2⟩
def ftMA : Move := Move.mk 0 ⟨2, 0⟩ ⟨1, 0⟩
def ftMB : Move := Move.mk 1 ⟨1, 0⟩ ⟨0, 0⟩

/-- **THE FLOW-THROUGH GAP IS NOT EMPTY, AT `n = 3`.** Both moves are legal with distinct sources and
distinct raw destinations. B's move is INCLUSIVE-blocked yet EXCLUSIVE-clear (the gap), and the exact
`cFtA` antecedent (`ftAIff`) holds — `da = sb`, `carAt sb = false` (`bnz = 0`), `¬occluded_b`,
`db ≠ sa` — with `db` occupied by a non-mover, so the descriptor sets `cLandNz 0 = 1 ⇒ cBadA = 1 ⇒
cResolvable = 0` and emits the IDENTITY board. The REFERENCE instead resolves cleanly
(`resolvableB = true`) and lands A on the emptied waypoint (`landMap sa = da`, `resolveMoves` moves
A off `sa`). Every clause `decide`d on the reference semantics. -/
theorem flowThroughOcclusionGap_witness_n3 :
    MoveValid ftBoard ftMA ∧ MoveValid ftBoard ftMB
      ∧ ftMA.frm ≠ ftMB.frm ∧ ftMA.to ≠ ftMB.to
      ∧ ftMA.frm ≠ ftMA.to ∧ ftMB.frm ≠ ftMB.to
      -- THE GAP: B's move is inclusive-blocked but exclusive-clear.
      ∧ blockedB ftBoard [ftMA, ftMB] ftMB = true
      ∧ occluded ftBoard [ftMA.frm, ftMB.frm] ftMB = false
      -- the exact `ftAIff` antecedent, so the descriptor's flow-through FIRES and points A at `db`:
      ∧ ftMA.to = ftMB.frm
      ∧ carAt ftBoard ftMB.frm = false
      ∧ ftMB.to ≠ ftMA.frm
      -- the ft-selected landing `db` is occupied by a non-mover, firing `cLandNz`/`cBadA`:
      ∧ carAt ftBoard ftMB.to = true
      ∧ carAt ftBoard ftMA.frm = true
      -- yet the REFERENCE resolves cleanly and MOVES A onto the emptied waypoint:
      ∧ resolvableB ftBoard [ftMA, ftMB] = true
      ∧ landMap ftBoard [ftMA, ftMB] ftMA.frm = ftMA.to
      ∧ (resolveMoves ftBoard [ftMA, ftMB]).cellAt ftMA.frm = Particle.vacuum
      ∧ (resolveMoves ftBoard [ftMA, ftMB]).cellAt ftMA.to = Particle.attractor
      ∧ ftBoard.cellAt ftMA.frm = Particle.attractor := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end FlowThroughGap

/-! ## §9 — `ftV2{A,B}N_of_sat`: the CORRECTED FLOW-THROUGH bit reads INCLUSIVE occlusion.

This is the SECOND WOUND's fix, extracted off `Satisfied2` at arbitrary `n`. The chunk-5 emitter's
`cFtV2A = eqAb · ¬bnz · surv · ¬occIncl_b · ¬eqBa` is the OLD five-conjunct `cFtA` with the OTHER
piece's block read as the INCLUSIVE `cOccIncl` (`= blockedB`, via §2) instead of the exclusive `cOcc`
(`= occluded`). The gate SHAPE is identical to the OLD flow-through chain, so Leg 6's `ftN_of_sat`
(fully column-parametric) applies verbatim — only the occlusion NOT-bit column changes from `cNOccb`
to `cNOccIb`. The conclusion's occlusion conjunct is the emitted `cOccIncl` column, which
`blockedV2N_of_sat` (§2) has already pinned to the VALIDATED-game `blockedB` — so on the
`flowThroughOcclusionGap` class (B interior-clear but destination inclusive-blocked) the corrected
`cFtV2A` fires iff `blockedB … mb = false`, where the OLD `cFtA` fired on `occluded … mb = false`. -/
section FtV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- Membership lift into the CHUNK-5 corrected flow-through family. -/
theorem ftV2Lift {g : VmConstraint2} (h : g ∈ NGen.flowThroughV2Constraints n) :
    g ∈ (automataflResolveDescN n).constraints := mem_resolve_of_mem_flowThroughV2 h

/-- Membership lift into the OLD flow-through family (source of the shared `cNBnz`/`cNAnz`/`cNEqba`/
`cNEqab` NOT-bits the corrected chain reuses). -/
theorem ftLift {g : VmConstraint2} (h : g ∈ NGen.flowThroughConstraints n) :
    g ∈ (automataflResolveDescN n).constraints := mem_resolve_of_mem_flowThrough h

/-- **`ftV2AN_of_sat`.** The corrected A-side flow-through bit is `1` iff A's dest is B's source, B's
source is vacuum (`bnz = 0`), the round survives, B's move is NOT inclusive-blocked (`cOccIncl 1 = 0`)
and B does not point back at A (`eqBa = 0`). Every conjunct is a column already known boolean; the
occlusion conjunct is the INCLUSIVE `cOccIncl 1` (`= blockedB … mb`, §2), not the exclusive `cOcc`. -/
theorem ftV2AN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hab : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1)
    (hbnz : (envAt t i).loc (NGen.cBnz n) = 0 ∨ (envAt t i).loc (NGen.cBnz n) = 1)
    (hocc : (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 1) = 1)
    (hba : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1) :
    ((envAt t i).loc (NGen.cFtV2A n) = 0 ∨ (envAt t i).loc (NGen.cFtV2A n) = 1)
      ∧ ((envAt t i).loc (NGen.cFtV2A n) = 1 ↔
          ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1 ∧ (envAt t i).loc (NGen.cBnz n) = 0
            ∧ (envAt t i).loc (NGen.cSurv n) = 1 ∧ (envAt t i).loc (NGen.cOccIncl n 1) = 0
            ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0)) :=
  ftN_of_sat hsat hc i hi (NGen.cNBnz n) (NGen.cNOccIb n) (NGen.cNEqba n) (NGen.cFtV2a1 n)
    (NGen.cFtV2a2 n) (NGen.cFtV2a3 n) (NGen.cFtV2A n) (NGen.cEqBit n (NGen.eqBase n 2)) (NGen.cBnz n)
    (NGen.cOccIncl n 1) (NGen.cEqBit n (NGen.eqBase n 3)) (NGen.cSurv n)
    (ftLift (by rw [NGen.flowThroughConstraints]; exact List.mem_cons_self))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]; exact List.mem_cons_self))
    (ftLift (by rw [NGen.flowThroughConstraints]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
    hab hbnz hocc hba hsurv

/-- **`ftV2BN_of_sat`.** The corrected B-side flow-through bit — the mirror, reading `cOccIncl 0`
(`= blockedB … ma`). -/
theorem ftV2BN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hba : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1)
    (hanz : (envAt t i).loc (NGen.cAnz n) = 0 ∨ (envAt t i).loc (NGen.cAnz n) = 1)
    (hocc : (envAt t i).loc (NGen.cOccIncl n 0) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 0) = 1)
    (hab : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1) :
    ((envAt t i).loc (NGen.cFtV2B n) = 0 ∨ (envAt t i).loc (NGen.cFtV2B n) = 1)
      ∧ ((envAt t i).loc (NGen.cFtV2B n) = 1 ↔
          ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1 ∧ (envAt t i).loc (NGen.cAnz n) = 0
            ∧ (envAt t i).loc (NGen.cSurv n) = 1 ∧ (envAt t i).loc (NGen.cOccIncl n 0) = 0
            ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0)) :=
  ftN_of_sat hsat hc i hi (NGen.cNAnz n) (NGen.cNOccIa n) (NGen.cNEqab n) (NGen.cFtV2b1 n)
    (NGen.cFtV2b2 n) (NGen.cFtV2b3 n) (NGen.cFtV2B n) (NGen.cEqBit n (NGen.eqBase n 3)) (NGen.cAnz n)
    (NGen.cOccIncl n 0) (NGen.cEqBit n (NGen.eqBase n 2)) (NGen.cSurv n)
    (ftLift (by rw [NGen.flowThroughConstraints]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
    (ftLift (by rw [NGen.flowThroughConstraints]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))))
    (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))))
    hba hanz hocc hab hsurv

end FtV2

/-! ## §10 — `nonLeaveV2GateN_of_sat`: the CORRECTED non-leaver bit is `landNzV2 ∧ ¬cCv2_other`.

The chunk-5 twin of §4, but recomputed on the CORRECTED landing (`cLandNzV2` reads the OLD board at
the `wDstV2` = corrected-flow-through landing) and on the CORRECTED journeys bit (`cCv2 (1−which)`, the
inclusive-occlusion carry, in place of the OLD exclusive-occlusion `carryCol`). Pure gate algebra. -/
section NonLeaveV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- Membership lift into `nonLeaveV2One n which` at either piece index. -/
theorem nlV2Lift (which : Nat) (hw : which < 2) {g : VmConstraint2}
    (h : g ∈ NGen.nonLeaveV2One n which) : g ∈ (automataflResolveDescN n).constraints := by
  apply mem_resolve_of_mem_nonLeaveV2
  rw [NGen.nonLeaveV2Constraints]
  interval_cases which
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ h

/-- **`nonLeaveV2GateN_of_sat`.** `cNonLeaveV2[which]` is boolean and is `1` iff the CORRECTED landing
is non-vacuum (`cLandNzV2 = 1`) and the OTHER piece's inclusive-occlusion carry is zero
(`cCv2 (1−which) = 0`). -/
theorem nonLeaveV2GateN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hlandnz : (envAt t i).loc (NGen.cLandNzV2 n which) = 0
        ∨ (envAt t i).loc (NGen.cLandNzV2 n which) = 1)
    (hcv2Other : (envAt t i).loc (NGen.cCv2 n (1 - which)) = 0
        ∨ (envAt t i).loc (NGen.cCv2 n (1 - which)) = 1) :
    ((envAt t i).loc (NGen.cNonLeaveV2 n which) = 0 ∨ (envAt t i).loc (NGen.cNonLeaveV2 n which) = 1)
      ∧ ((envAt t i).loc (NGen.cNonLeaveV2 n which) = 1 ↔
          ((envAt t i).loc (NGen.cLandNzV2 n which) = 1
            ∧ (envAt t i).loc (NGen.cCv2 n (1 - which)) = 0)) := by
  set e := envAt t i with he
  have hmem : cgH (((Head.lin 1 (NGen.cNonLeaveV2 n which)).addLin (-1) (NGen.cLandNzV2 n which)).addProd 1
              [(NGen.cLandNzV2 n which), (NGen.cCv2 n (1 - which))])
      ∈ (automataflResolveDescN n).constraints :=
    nlV2Lift which hw (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have hg := rgateHN hsat i hi hmem
  have hE : (headToExpr (((Head.lin 1 (NGen.cNonLeaveV2 n which)).addLin (-1)
        (NGen.cLandNzV2 n which)).addProd 1
        [(NGen.cLandNzV2 n which), (NGen.cCv2 n (1 - which))])).eval e.loc
      = e.loc (NGen.cNonLeaveV2 n which) + (-1) * e.loc (NGen.cLandNzV2 n which)
        + e.loc (NGen.cLandNzV2 n which) * e.loc (NGen.cCv2 n (1 - which)) := rfl
  rw [hE] at hg
  have hnl : e.loc (NGen.cNonLeaveV2 n which)
      = e.loc (NGen.cLandNzV2 n which)
        - e.loc (NGen.cLandNzV2 n which) * e.loc (NGen.cCv2 n (1 - which)) := by
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hlandnz with a | a <;> rcases hcv2Other with b | b <;> rw [a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_⟩
  · rcases hlandnz with a | a <;> rcases hcv2Other with b | b <;> rw [hnl, a, b] <;> norm_num
  · rw [hnl]
    rcases hlandnz with a | a <;> rcases hcv2Other with b | b <;> rw [a, b] <;> norm_num

end NonLeaveV2

/-! ## §11 — `cv2ValN_of_sat` and `carryV3ArithN_of_sat`: the CORRECTED carry rides the CORRECTED
non-leaver.

`cCv2 = surv · nz · (1 − occIncl)` is the chunk-3 inclusive-occlusion carry seed (already correct on
the occluded STAYER). `cCarryV3 = cCv2 · (1 − cNonLeaveV2)` rides the CORRECTED non-leaver (§10), so
on the `flowThroughOcclusionGap` class A now CARRIES (`cCarryV3 0 = 1`) onto the emptied waypoint,
where the chunk-3 `cCarryV2` (riding the OLD `cNonLeave`) kept A. Pure gate algebra. -/
section CarryV3
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- Membership lift into `carryV3Constraints`. -/
theorem cv3Lift (which : Nat) (hw : which < 2) {g : VmConstraint2}
    (h : g ∈ NGen.carryV3Constraints n) : g ∈ (automataflResolveDescN n).constraints :=
  mem_resolve_of_mem_carryV3 h

/-- **`cv2ValN_of_sat`.** The chunk-3 journeys seed `cCv2 = cCv1 · (1 − occIncl) = surv · nz ·
(1 − occIncl)` is boolean, as a standalone value (extracted from the chunk-3 carryV2 family). -/
theorem cv2ValN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1)
    (hnz : (envAt t i).loc (NGen.nzCol n which) = 0 ∨ (envAt t i).loc (NGen.nzCol n which) = 1)
    (hoccI : (envAt t i).loc (NGen.cOccIncl n which) = 0
        ∨ (envAt t i).loc (NGen.cOccIncl n which) = 1) :
    ((envAt t i).loc (NGen.cCv2 n which) = 0 ∨ (envAt t i).loc (NGen.cCv2 n which) = 1)
      ∧ ((envAt t i).loc (NGen.cCv2 n which) = 1 ↔
          ((envAt t i).loc (NGen.cSurv n) = 1 ∧ (envAt t i).loc (NGen.nzCol n which) = 1
            ∧ (envAt t i).loc (NGen.cOccIncl n which) = 0)) := by
  set e := envAt t i with he
  have hcv1 : e.loc (NGen.cCv1 n which) = e.loc (NGen.cSurv n) * e.loc (NGen.nzCol n which) := by
    have hmem : prodPin (NGen.cCv1 n which) (NGen.cSurv n) (NGen.nzCol n which)
        ∈ (automataflResolveDescN n).constraints :=
      cv2Lift which hw (List.mem_cons_self)
    exact prodN_of_sat hsat hc i hi (NGen.cCv1 n which) (NGen.cSurv n) (NGen.nzCol n which)
      hmem hsurv hnz
  have hcv1B : e.loc (NGen.cCv1 n which) = 0 ∨ e.loc (NGen.cCv1 n which) = 1 := by
    rcases hsurv with a | a <;> rcases hnz with b | b <;> rw [hcv1, a, b] <;> norm_num
  have hcv2 : e.loc (NGen.cCv2 n which)
      = e.loc (NGen.cCv1 n which) - e.loc (NGen.cCv1 n which) * e.loc (NGen.cOccIncl n which) := by
    have hmem : cgH (NGen.cv2Head n which) ∈ (automataflResolveDescN n).constraints :=
      cv2Lift which hw (List.mem_cons_of_mem _ (List.mem_cons_self))
    have hg := rgateHN hsat i hi hmem
    have hE : (headToExpr (NGen.cv2Head n which)).eval e.loc
        = e.loc (NGen.cCv2 n which) + (-1) * e.loc (NGen.cCv1 n which)
          + e.loc (NGen.cCv1 n which) * e.loc (NGen.cOccIncl n which) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hcv1B with a | a <;> rcases hoccI with c | c <;> rw [a, c] <;>
      exact ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_⟩
  · rcases hcv1B with a | a <;> rcases hoccI with c | c <;> rw [hcv2, a, c] <;> norm_num
  · rw [hcv2, hcv1]
    rcases hsurv with a | a <;> rcases hnz with b | b <;> rcases hoccI with c | c <;>
      rw [a, b, c] <;> norm_num

/-- **`carryV3ArithN_of_sat`.** `cCarryV3[which] = cCv2 · (1 − cNonLeaveV2)` is boolean and is `1` iff
`cCv2 = 1` and `cNonLeaveV2 = 0`. -/
theorem carryV3ArithN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hcv2 : (envAt t i).loc (NGen.cCv2 n which) = 0 ∨ (envAt t i).loc (NGen.cCv2 n which) = 1)
    (hnl : (envAt t i).loc (NGen.cNonLeaveV2 n which) = 0
        ∨ (envAt t i).loc (NGen.cNonLeaveV2 n which) = 1) :
    ((envAt t i).loc (NGen.cCarryV3 n which) = 0 ∨ (envAt t i).loc (NGen.cCarryV3 n which) = 1)
      ∧ ((envAt t i).loc (NGen.cCarryV3 n which) = 1 ↔
          ((envAt t i).loc (NGen.cCv2 n which) = 1
            ∧ (envAt t i).loc (NGen.cNonLeaveV2 n which) = 0)) := by
  set e := envAt t i with he
  have hmem : cgH (NGen.carryV3Head n which) ∈ (automataflResolveDescN n).constraints := by
    refine cv3Lift which hw ?_
    rw [NGen.carryV3Constraints]
    interval_cases which
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  have hg := rgateHN hsat i hi hmem
  have hE : (headToExpr (NGen.carryV3Head n which)).eval e.loc
      = e.loc (NGen.cCarryV3 n which) + (-1) * e.loc (NGen.cCv2 n which)
        + e.loc (NGen.cCv2 n which) * e.loc (NGen.cNonLeaveV2 n which) := rfl
  rw [hE] at hg
  have hcarry : e.loc (NGen.cCarryV3 n which)
      = e.loc (NGen.cCv2 n which) - e.loc (NGen.cCv2 n which) * e.loc (NGen.cNonLeaveV2 n which) := by
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hcv2 with a | a <;> rcases hnl with d | d <;> rw [a, d] <;>
      exact ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_⟩
  · rcases hcv2 with a | a <;> rcases hnl with d | d <;> rw [hcarry, a, d] <;> norm_num
  · rw [hcarry]
    rcases hcv2 with a | a <;> rcases hnl with d | d <;> rw [a, d] <;> norm_num

end CarryV3

/-! ## §12 — `midV3CellN_of_sat`: the corrected board is the `cResolvableV2`-gated selection.

The chunk-5 twin of §5: `cMidV3[c] = cResolvableV2 · cWBoardV3[c] + (1 − cResolvableV2) · old[c]` — the
circuit analog of `resolveMoves b ms = if resolvableB then writeBoard … else b`, on the CORRECTED
resolvable surface and the CORRECTED board rewrite. -/
section MidV3
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- **`midV3CellN_of_sat`.** The corrected-board cell gate, rearranged (stated mod `p`). -/
theorem midV3CellN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) (c : Nat) (hcK : c < NGen.KK n) :
    (envAt t i).loc (NGen.cMidV3 n c)
      ≡ (envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.cWBoardV3 n c)
        + (envAt t i).loc (NGen.old n c)
        - (envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.old n c)
      [ZMOD 2013265921] := by
  have hmem : cgH (NGen.midV3CellHead n c) ∈ (automataflResolveDescN n).constraints := by
    apply mem_resolve_of_mem_midV3
    rw [NGen.midV3Constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hcK, rfl⟩)
  have hg := rgateHN hsat i hi hmem
  have hE : (headToExpr (NGen.midV3CellHead n c)).eval (envAt t i).loc
      = (envAt t i).loc (NGen.cMidV3 n c)
        + (-1) * ((envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.cWBoardV3 n c))
        + (-1) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.old n c) := rfl
  rw [hE] at hg
  exact (gate_modEq_iff (by ring)).mp hg

end MidV3

/-! ## §13 — `writeCellV3N_of_sat`: the corrected writeBoard-cell rewrite.

`NGen.writeCellV3Head n c` is `writeCellHead` with the OLD `carryCol` replaced by the corrected
`carryV3Col` (§11) and the OLD landing one-hots `wDstRow`/`wDstCol` replaced by the CORRECTED
`wDstV2Row`/`wDstV2Col` (driven by `cFtV2`), output cell `cWBoardV3 c`. Same degree-7 shape as §6's
`writeCellV2N_of_sat` normalises — the MID cell is the OLD cell KEPT (unless a cleared source or a
landing target), plus each landing piece's particle, with the swap-restore term — driven by the carry
that rides the CORRECTED non-leaver and the corrected landing. Stated mod `p`; `x`/`y` = column/row. -/
section WriteCellV3
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- **`writeCellV3N_of_sat`.** The emitted corrected `cWBoardV3` cell gate, rearranged. -/
theorem writeCellV3N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) (c y x : Nat) (hy : y = c / n) (hx : x = c % n)
    (hcK : c < NGen.KK n) :
    (envAt t i).loc (NGen.cWBoardV3 n c)
      ≡ (1 - (envAt t i).loc (NGen.carryV3Col n 0) * ((envAt t i).loc (NGen.wSrcRow n 0 y)
                * (envAt t i).loc (NGen.wSrcCol n 0 x))
           - (envAt t i).loc (NGen.carryV3Col n 0) * ((envAt t i).loc (NGen.wDstV2Row n 0 y)
                * (envAt t i).loc (NGen.wDstV2Col n 0 x))
           - (envAt t i).loc (NGen.carryV3Col n 1) * ((envAt t i).loc (NGen.wSrcRow n 1 y)
                * (envAt t i).loc (NGen.wSrcCol n 1 x))
           - (envAt t i).loc (NGen.carryV3Col n 1) * ((envAt t i).loc (NGen.wDstV2Row n 1 y)
                * (envAt t i).loc (NGen.wDstV2Col n 1 x))
           + (envAt t i).loc (NGen.carryV3Col n 0) * ((envAt t i).loc (NGen.wSrcRow n 0 y)
                * (envAt t i).loc (NGen.wSrcCol n 0 x)) * ((envAt t i).loc (NGen.carryV3Col n 1)
                * ((envAt t i).loc (NGen.wDstV2Row n 1 y) * (envAt t i).loc (NGen.wDstV2Col n 1 x)))
           + (envAt t i).loc (NGen.carryV3Col n 1) * ((envAt t i).loc (NGen.wSrcRow n 1 y)
                * (envAt t i).loc (NGen.wSrcCol n 1 x)) * ((envAt t i).loc (NGen.carryV3Col n 0)
                * ((envAt t i).loc (NGen.wDstV2Row n 0 y) * (envAt t i).loc (NGen.wDstV2Col n 0 x)))
           + (envAt t i).loc (NGen.carryV3Col n 0) * ((envAt t i).loc (NGen.wSrcRow n 0 y)
                * (envAt t i).loc (NGen.wSrcCol n 0 x)) * ((envAt t i).loc (NGen.carryV3Col n 1)
                * ((envAt t i).loc (NGen.wSrcRow n 1 y) * (envAt t i).loc (NGen.wSrcCol n 1 x)))
           + (envAt t i).loc (NGen.carryV3Col n 0) * ((envAt t i).loc (NGen.wDstV2Row n 0 y)
                * (envAt t i).loc (NGen.wDstV2Col n 0 x)) * ((envAt t i).loc (NGen.carryV3Col n 1)
                * ((envAt t i).loc (NGen.wDstV2Row n 1 y) * (envAt t i).loc (NGen.wDstV2Col n 1 x))))
          * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV3Col n 0) * ((envAt t i).loc (NGen.wDstV2Row n 0 y)
            * (envAt t i).loc (NGen.wDstV2Col n 0 x)) * (envAt t i).loc (NGen.particleCol n 0)
        + (envAt t i).loc (NGen.carryV3Col n 1) * ((envAt t i).loc (NGen.wDstV2Row n 1 y)
            * (envAt t i).loc (NGen.wDstV2Col n 1 x)) * (envAt t i).loc (NGen.particleCol n 1)
        - (envAt t i).loc (NGen.carryV3Col n 0) * ((envAt t i).loc (NGen.wDstV2Row n 0 y)
            * (envAt t i).loc (NGen.wDstV2Col n 0 x)) * ((envAt t i).loc (NGen.carryV3Col n 1)
            * ((envAt t i).loc (NGen.wDstV2Row n 1 y) * (envAt t i).loc (NGen.wDstV2Col n 1 x)))
            * (envAt t i).loc (NGen.particleCol n 1)
        [ZMOD 2013265921] := by
  subst hy; subst hx
  have hmem : cgH (NGen.writeCellV3Head n c) ∈ (automataflResolveDescN n).constraints := by
    apply mem_resolve_of_mem_midV3
    rw [NGen.midV3Constraints]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hcK, rfl⟩)
  have hg := rgateHN hsat i hi hmem
  have hshape : (headToExpr (NGen.writeCellV3Head n c)).eval (envAt t i).loc
      = (envAt t i).loc (NGen.cWBoardV3 n c) + (-1) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV3Col n 0) * (envAt t i).loc (NGen.wSrcRow n 0 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 0 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV3Col n 0) * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (-1) * ((envAt t i).loc (NGen.carryV3Col n 0) * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n)) * (envAt t i).loc (NGen.particleCol n 0))
        + (envAt t i).loc (NGen.carryV3Col n 1) * (envAt t i).loc (NGen.wSrcRow n 1 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 1 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV3Col n 1) * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (-1) * ((envAt t i).loc (NGen.carryV3Col n 1) * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n)) * (envAt t i).loc (NGen.particleCol n 1))
        + (-1) * ((envAt t i).loc (NGen.carryV3Col n 0) * (envAt t i).loc (NGen.wSrcRow n 0 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 0 (c % n)) * (envAt t i).loc (NGen.carryV3Col n 1)
            * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n)) * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (-1) * ((envAt t i).loc (NGen.carryV3Col n 1) * (envAt t i).loc (NGen.wSrcRow n 1 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 1 (c % n)) * (envAt t i).loc (NGen.carryV3Col n 0)
            * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n)) * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (-1) * ((envAt t i).loc (NGen.carryV3Col n 0) * (envAt t i).loc (NGen.wSrcRow n 0 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 0 (c % n)) * (envAt t i).loc (NGen.carryV3Col n 1)
            * (envAt t i).loc (NGen.wSrcRow n 1 (c / n)) * (envAt t i).loc (NGen.wSrcCol n 1 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (-1) * ((envAt t i).loc (NGen.carryV3Col n 0) * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n)) * (envAt t i).loc (NGen.carryV3Col n 1)
            * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n)) * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (envAt t i).loc (NGen.carryV3Col n 0) * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n)) * (envAt t i).loc (NGen.carryV3Col n 1)
            * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n)) * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n))
            * (envAt t i).loc (NGen.particleCol n 1) := rfl
  rw [hshape] at hg
  exact (gate_modEq_iff (by ring)).mp hg

end WriteCellV3

/-! ## §14 — `resolvableV2ArithN_of_sat`: the CORRECTED resolvable surface.

`cResolvableV2 = ¬mergeV2 · ¬badV2A · ¬badV2B`, with `badV2_i = cCv2_i · cNonLeaveV2_i` (the journeys
bit `cCv2` is the inclusive-occlusion carry; the non-leaver is the CORRECTED §10 one). Pure gate
algebra over the twelve-gate logic tail of `resolvableV2Constraints`; `cMergeV2` (the confluence bit)
is taken boolean. In the `flowThroughOcclusionGap` class the CORRECTED landing puts A on the emptied
VACUUM waypoint, so `cNonLeaveV2 0 = 0` (§10) ⇒ `badV2A = 0`, where the OLD `cResolvable` rejected the
round (`cBadA = 1`). This is the circuit analog of `AutomataflRules.resolvableB_pair` (the
NO-CONFLUENCE-at-`m = 2` collapse) — the SECOND wound's resolvable half. -/
section ResolvableV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- The twelve-gate boolean-logic tail of `resolvableV2Constraints` (`cIdentV2 … cResolvableV2`),
transcribed literally so the RIGHT operand of the outer `++` in `resolvableV2Constraints` is
syntactically this list — the four `cDestV2` gates and the `resEqV2` `eq_coords` are its left operand. -/
def resV2LogicTail : List VmConstraint2 :=
  [ prodPin (NGen.cIdentV2 n) (NGen.cEqBit n (NGen.eqBase n 0)) (NGen.cEqBit n (NGen.eqBase n 1))
  , prodPin (NGen.cBothCarryV2 n) (NGen.cCv2 n 0) (NGen.cCv2 n 1)
  , prodPin (NGen.cMc1V2 n) (NGen.cBothCarryV2 n) (NGen.cResEqV2 n)
  , notBitPin (NGen.cNotIdentV2 n) (NGen.cIdentV2 n)
  , prodPin (NGen.cMergeV2 n) (NGen.cMc1V2 n) (NGen.cNotIdentV2 n)
  , prodPin (NGen.cBadV2A n) (NGen.cCv2 n 0) (NGen.cNonLeaveV2 n 0)
  , prodPin (NGen.cBadV2B n) (NGen.cCv2 n 1) (NGen.cNonLeaveV2 n 1)
  , notBitPin (NGen.cNMergeV2 n) (NGen.cMergeV2 n)
  , notBitPin (NGen.cNBadV2A n) (NGen.cBadV2A n)
  , notBitPin (NGen.cNBadV2B n) (NGen.cBadV2B n)
  , prodPin (NGen.cR1V2 n) (NGen.cNMergeV2 n) (NGen.cNBadV2A n)
  , prodPin (NGen.cResolvableV2 n) (NGen.cR1V2 n) (NGen.cNBadV2B n) ]

/-- Membership lift into the twelve-gate logic tail: it is the RIGHT operand of the outer `++`. -/
theorem resV2Lift {g : VmConstraint2} (h : g ∈ resV2LogicTail (n := n)) :
    g ∈ (automataflResolveDescN n).constraints := by
  refine mem_resolve_of_mem_resolvableV2 ?_
  rw [NGen.resolvableV2Constraints]
  exact List.mem_append_right _ h

/-- **`resolvableV2ArithN_of_sat`.** `cResolvableV2` is boolean and is `1` iff no confluence
(`cMergeV2 = 0`) and neither piece has a bad journey (`badV2_i = cCv2_i · cNonLeaveV2_i = 0`, i.e. the
carrying piece does not land on a non-leaver). -/
theorem resolvableV2ArithN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hcv2a : (envAt t i).loc (NGen.cCv2 n 0) = 0 ∨ (envAt t i).loc (NGen.cCv2 n 0) = 1)
    (hcv2b : (envAt t i).loc (NGen.cCv2 n 1) = 0 ∨ (envAt t i).loc (NGen.cCv2 n 1) = 1)
    (hnla : (envAt t i).loc (NGen.cNonLeaveV2 n 0) = 0 ∨ (envAt t i).loc (NGen.cNonLeaveV2 n 0) = 1)
    (hnlb : (envAt t i).loc (NGen.cNonLeaveV2 n 1) = 0 ∨ (envAt t i).loc (NGen.cNonLeaveV2 n 1) = 1)
    (hmerge : (envAt t i).loc (NGen.cMergeV2 n) = 0 ∨ (envAt t i).loc (NGen.cMergeV2 n) = 1) :
    ((envAt t i).loc (NGen.cResolvableV2 n) = 0 ∨ (envAt t i).loc (NGen.cResolvableV2 n) = 1)
      ∧ ((envAt t i).loc (NGen.cResolvableV2 n) = 1 ↔
          ((envAt t i).loc (NGen.cMergeV2 n) = 0
            ∧ ((envAt t i).loc (NGen.cCv2 n 0) = 0 ∨ (envAt t i).loc (NGen.cNonLeaveV2 n 0) = 0)
            ∧ ((envAt t i).loc (NGen.cCv2 n 1) = 0 ∨ (envAt t i).loc (NGen.cNonLeaveV2 n 1) = 0))) := by
  set e := envAt t i with he
  -- badV2A = cCv2_0 · nonLeaveV2_0  (gate 5 of the logic tail)
  have hbadA : e.loc (NGen.cBadV2A n) = e.loc (NGen.cCv2 n 0) * e.loc (NGen.cNonLeaveV2 n 0) :=
    prodN_of_sat hsat hc i hi (NGen.cBadV2A n) (NGen.cCv2 n 0) (NGen.cNonLeaveV2 n 0)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
      hcv2a hnla
  have hbadAB : e.loc (NGen.cBadV2A n) = 0 ∨ e.loc (NGen.cBadV2A n) = 1 := by
    rcases hcv2a with a | a <;> rcases hnla with b | b <;> rw [hbadA, a, b] <;> norm_num
  -- badV2B = cCv2_1 · nonLeaveV2_1  (gate 6)
  have hbadB : e.loc (NGen.cBadV2B n) = e.loc (NGen.cCv2 n 1) * e.loc (NGen.cNonLeaveV2 n 1) :=
    prodN_of_sat hsat hc i hi (NGen.cBadV2B n) (NGen.cCv2 n 1) (NGen.cNonLeaveV2 n 1)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))
      hcv2b hnlb
  have hbadBB : e.loc (NGen.cBadV2B n) = 0 ∨ e.loc (NGen.cBadV2B n) = 1 := by
    rcases hcv2b with a | a <;> rcases hnlb with b | b <;> rw [hbadB, a, b] <;> norm_num
  -- ¬merge, ¬badA, ¬badB  (gates 7, 8, 9)
  have hnm : e.loc (NGen.cNMergeV2 n) = 1 - e.loc (NGen.cMergeV2 n) :=
    notBitN_of_sat hsat hc i hi (NGen.cNMergeV2 n) (NGen.cMergeV2 n)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))) hmerge
  have hnmB : e.loc (NGen.cNMergeV2 n) = 0 ∨ e.loc (NGen.cNMergeV2 n) = 1 := by
    rcases hmerge with a | a <;> rw [hnm, a] <;> norm_num
  have hnA : e.loc (NGen.cNBadV2A n) = 1 - e.loc (NGen.cBadV2A n) :=
    notBitN_of_sat hsat hc i hi (NGen.cNBadV2A n) (NGen.cBadV2A n)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))) hbadAB
  have hnAB : e.loc (NGen.cNBadV2A n) = 0 ∨ e.loc (NGen.cNBadV2A n) = 1 := by
    rcases hbadAB with a | a <;> rw [hnA, a] <;> norm_num
  have hnB : e.loc (NGen.cNBadV2B n) = 1 - e.loc (NGen.cBadV2B n) :=
    notBitN_of_sat hsat hc i hi (NGen.cNBadV2B n) (NGen.cBadV2B n)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))))) hbadBB
  have hnBB : e.loc (NGen.cNBadV2B n) = 0 ∨ e.loc (NGen.cNBadV2B n) = 1 := by
    rcases hbadBB with a | a <;> rw [hnB, a] <;> norm_num
  -- r1 = ¬merge · ¬badA  (gate 10), resolvable = r1 · ¬badB  (gate 11)
  have hr1 : e.loc (NGen.cR1V2 n) = e.loc (NGen.cNMergeV2 n) * e.loc (NGen.cNBadV2A n) :=
    prodN_of_sat hsat hc i hi (NGen.cR1V2 n) (NGen.cNMergeV2 n) (NGen.cNBadV2A n)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))))) hnmB hnAB
  have hr1B : e.loc (NGen.cR1V2 n) = 0 ∨ e.loc (NGen.cR1V2 n) = 1 := by
    rcases hnmB with a | a <;> rcases hnAB with b | b <;> rw [hr1, a, b] <;> norm_num
  have hres : e.loc (NGen.cResolvableV2 n) = e.loc (NGen.cR1V2 n) * e.loc (NGen.cNBadV2B n) :=
    prodN_of_sat hsat hc i hi (NGen.cResolvableV2 n) (NGen.cR1V2 n) (NGen.cNBadV2B n)
      (resV2Lift (by show _ ∈ resV2LogicTail (n := n)
                     exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))))))) hr1B hnBB
  refine ⟨?_, ?_⟩
  · rcases hr1B with a | a <;> rcases hnBB with b | b <;> rw [hres, a, b] <;> norm_num
  · rw [hres, hr1, hnm, hnA, hnB, hbadA, hbadB]
    rcases hcv2a with a | a <;> rcases hcv2b with b | b <;> rcases hnla with c | c <;>
      rcases hnlb with d | d <;> rcases hmerge with f | f <;> rw [a, b, c, d, f] <;>
      simp <;> omega

end ResolvableV2

/-! ## §15 — THE SECOND WOUND, CLOSED IN-CIRCUIT AGAINST THE VALIDATED GAME.

`flowThroughOcclusionGap_witness_n3` (§7) is a SPEC-side falsifier that stays green (it is `decide`d on
the reference). The IN-CIRCUIT canary is here: composing §2 (`blockedV2N_of_sat` — the emitted
`cOccIncl` IS the validated-game `blockedB`) with §9 (`ftV2AN_of_sat` — the corrected flow-through
reads `cOccIncl`), the corrected A-side flow-through bit vanishes exactly when B's move is INCLUSIVE-
blocked — the flow-through-gap condition (B interior-clear but destination holds a non-mover). The OLD
`cFtA` (chunk-3 and before) fired here because it read the EXCLUSIVE `occluded = false`; the corrected
`cFtV2A` does NOT, so A dead-ends on the emptied waypoint as `landMap` (inclusive `blockedB`) demands.
This is the wound closed against the ACTUAL emitted descriptor, unconditional in `n`. -/
section WoundClosed
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

open Dregg2.Games.AutomataflRules (blockedB)

/-- **`ftV2A_inclBlocked_kills_flowThrough`.** When B's move is INCLUSIVE-blocked (validated-game
`blockedB … mb = true`), the corrected A-side flow-through bit is `0` — the second wound closed on the
real descriptor. (Contrast: the OLD `cFtA` read the exclusive `occluded`, which is `false` on this
class, so it WRONGLY fired.) -/
theorem ftV2A_inclBlocked_kills_flowThrough
    (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (W : MovesWindow n)
    (hab : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1)
    (hbnz : (envAt t i).loc (NGen.cBnz n) = 0 ∨ (envAt t i).loc (NGen.cBnz n) = 1)
    (hocc : (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 1) = 1)
    (hba : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1)
    (hsurv : (envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1)
    (hblocked : blockedB (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 1, moveDecodeN n (envAt t i) 0]
        (moveDecodeN n (envAt t i) 1) = true) :
    (envAt t i).loc (NGen.cFtV2A n) = 0 := by
  obtain ⟨hb, hiff⟩ := ftV2AN_of_sat hsat hc i hi hab hbnz hocc hba hsurv
  have hocc1 : (envAt t i).loc (NGen.cOccIncl n 1) = 1 :=
    (blockedV2N_of_sat hsat hc i hi W 1 (by norm_num)).mpr hblocked
  rcases hb with h0 | h1
  · exact h0
  · obtain ⟨_, _, _, hoccZero, _⟩ := hiff.mp h1
    rw [hocc1] at hoccZero; exact absurd hoccZero (by norm_num)

end WoundClosed

/-! ## §16 — `dstIndV2N_of_sat`: the CORRECTED landing indicator.

The chunk-5 twin of `AutomataflResolveCapstone.dstIndN_of_sat`, over the CORRECTED destination one-hots
`wDstV2Row`/`wDstV2Col` (pinned to `destHead …(cFtV2)`) instead of the OLD `wDstRow`/`wDstCol` (pinned
to `destHead …(cFtA/cFtB)`). The row×col product IS the indicator of the square the CORRECTED
flow-through bit selects — the piece's own `to` when `cFtV2 = 0`, the OTHER piece's `to` when
`cFtV2 = 1`. This is the LANDING half of the landing-correspondence input: paired with §9 (`cFtV2` =
inclusive flow-through) it is the emitted landing that a full capstone matches to `landMap_pair`. -/
section DstIndV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

open Dregg2.Circuit.Emit.AutomataflResolveCapstone (oneHotHeadN_of_sat destHead_select oneHot_pair_ind)

/-- The j-th CORRECTED destination-ROW selector boolean of piece `i`. -/
theorem weV2_dstRow_sel (i j : Nat) (hi2 : i < 2) (hj : j < n) :
    cg (gBin (NGen.wDstV2Row n i j)) ∈ NGen.destV2OneHotConstraints n := by
  rw [NGen.destV2OneHotConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (mem_oneHot_sel ((List.range n).map (NGen.wDstV2Row n i))
    (destHead (NGen.cTy n (NGen.mvBase n i)) (NGen.cTy n (NGen.mvBase n (1 - i)))
      (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n))
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
theorem weV2_dstRow_sum (i : Nat) (hi2 : i < 2) :
    cgH (((List.range n).map (NGen.wDstV2Row n i)).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1)))
      ∈ NGen.destV2OneHotConstraints n := by
  rw [NGen.destV2OneHotConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (mem_oneHot_sumHead ((List.range n).map (NGen.wDstV2Row n i))
    (destHead (NGen.cTy n (NGen.mvBase n i)) (NGen.cTy n (NGen.mvBase n (1 - i)))
      (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n)))
theorem weV2_dstRow_idx (i : Nat) (hi2 : i < 2) :
    cgH ((((List.range n).map (NGen.wDstV2Row n i)).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append
        ((destHead (NGen.cTy n (NGen.mvBase n i)) (NGen.cTy n (NGen.mvBase n (1 - i)))
          (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n)).scale (-1)))
      ∈ NGen.destV2OneHotConstraints n := by
  rw [NGen.destV2OneHotConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_left _ (mem_oneHot_idxHead ((List.range n).map (NGen.wDstV2Row n i))
    (destHead (NGen.cTy n (NGen.mvBase n i)) (NGen.cTy n (NGen.mvBase n (1 - i)))
      (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n)))
theorem weV2_dstCol_sel (i j : Nat) (hi2 : i < 2) (hj : j < n) :
    cg (gBin (NGen.wDstV2Col n i j)) ∈ NGen.destV2OneHotConstraints n := by
  rw [NGen.destV2OneHotConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_right _ (mem_oneHot_sel ((List.range n).map (NGen.wDstV2Col n i))
    (destHead (NGen.cTx n (NGen.mvBase n i)) (NGen.cTx n (NGen.mvBase n (1 - i)))
      (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n))
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
theorem weV2_dstCol_sum (i : Nat) (hi2 : i < 2) :
    cgH (((List.range n).map (NGen.wDstV2Col n i)).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1)))
      ∈ NGen.destV2OneHotConstraints n := by
  rw [NGen.destV2OneHotConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_right _ (mem_oneHot_sumHead ((List.range n).map (NGen.wDstV2Col n i))
    (destHead (NGen.cTx n (NGen.mvBase n i)) (NGen.cTx n (NGen.mvBase n (1 - i)))
      (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n)))
theorem weV2_dstCol_idx (i : Nat) (hi2 : i < 2) :
    cgH ((((List.range n).map (NGen.wDstV2Col n i)).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append
        ((destHead (NGen.cTx n (NGen.mvBase n i)) (NGen.cTx n (NGen.mvBase n (1 - i)))
          (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n)).scale (-1)))
      ∈ NGen.destV2OneHotConstraints n := by
  rw [NGen.destV2OneHotConstraints]
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi2, ?_⟩
  exact List.mem_append_right _ (mem_oneHot_idxHead ((List.range n).map (NGen.wDstV2Col n i))
    (destHead (NGen.cTx n (NGen.mvBase n i)) (NGen.cTx n (NGen.mvBase n (1 - i)))
      (if i == 0 then NGen.cFtV2A n else NGen.cFtV2B n)))

/-- **`dstIndV2N_of_sat`.** The corrected destination row×column one-hot product IS the indicator of
the square the CORRECTED flow-through bit `cFtV2` selects — the piece's own `to` when `cFtV2 = 0`, the
OTHER piece's `to` when `cFtV2 = 1` — at every cell. -/
theorem dstIndV2N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hn : (n : ℤ) < 2013265921)
    (hft : (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 0
        ∨ (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1)
    (hx0 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which)) < (n : ℤ))
    (hy0 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which)) < (n : ℤ))
    (hx1 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which))) < (n : ℤ))
    (hy1 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which))) < (n : ℤ)) :
    ∀ x y : Nat, x < n → y < n →
      (envAt t i).loc (NGen.wDstV2Row n which y) * (envAt t i).loc (NGen.wDstV2Col n which x)
        = if (⟨x, y⟩ : Coord)
             = (if (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1
                then (moveDecodeN n (envAt t i) (1 - which)).to
                else (moveDecodeN n (envAt t i) which).to)
          then 1 else 0 := by
  set e := envAt t i with he
  set ftc := (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) with hftc
  have hcanonRow : Canon (evalH (destHead (NGen.cTy n (NGen.mvBase n which))
      (NGen.cTy n (NGen.mvBase n (1 - which))) ftc) e.loc) := by
    rw [destHead_select _ _ _ _ hft]
    by_cases h : e.loc ftc = 1
    · rw [if_pos h]; exact ⟨hy1.1, lt_trans hy1.2 hn⟩
    · rw [if_neg h]; exact ⟨hy0.1, lt_trans hy0.2 hn⟩
  have hcanonCol : Canon (evalH (destHead (NGen.cTx n (NGen.mvBase n which))
      (NGen.cTx n (NGen.mvBase n (1 - which))) ftc) e.loc) := by
    rw [destHead_select _ _ _ _ hft]
    by_cases h : e.loc ftc = 1
    · rw [if_pos h]; exact ⟨hx1.1, lt_trans hx1.2 hn⟩
    · rw [if_neg h]; exact ⟨hx0.1, lt_trans hx0.2 hn⟩
  obtain ⟨ar, harLt, harEq, hrow⟩ :=
    oneHotHeadN_of_sat hsat hc i hi n hn (NGen.wDstV2Row n which)
      (destHead (NGen.cTy n (NGen.mvBase n which)) (NGen.cTy n (NGen.mvBase n (1 - which))) ftc)
      hcanonRow
      (fun j hj => mem_resolve_of_mem_destV2OneHot (weV2_dstRow_sel which j hw hj))
      (mem_resolve_of_mem_destV2OneHot (weV2_dstRow_sum which hw))
      (mem_resolve_of_mem_destV2OneHot (weV2_dstRow_idx which hw))
  obtain ⟨ac, hacLt, hacEq, hcol⟩ :=
    oneHotHeadN_of_sat hsat hc i hi n hn (NGen.wDstV2Col n which)
      (destHead (NGen.cTx n (NGen.mvBase n which)) (NGen.cTx n (NGen.mvBase n (1 - which))) ftc)
      hcanonCol
      (fun j hj => mem_resolve_of_mem_destV2OneHot (weV2_dstCol_sel which j hw hj))
      (mem_resolve_of_mem_destV2OneHot (weV2_dstCol_sum which hw))
      (mem_resolve_of_mem_destV2OneHot (weV2_dstCol_idx which hw))
  rw [destHead_select _ _ _ _ hft] at harEq hacEq
  have hpt : (if e.loc ftc = 1
        then (moveDecodeN n e (1 - which)).to
        else (moveDecodeN n e which).to)
      = (⟨ac, ar⟩ : Coord) := by
    by_cases h : e.loc ftc = 1
    · rw [if_pos h] at harEq hacEq ⊢
      simp only [moveDecodeN, harEq, hacEq, Int.toNat_natCast]
    · rw [if_neg h] at harEq hacEq ⊢
      simp only [moveDecodeN, harEq, hacEq, Int.toNat_natCast]
  intro x y hx hy
  rw [hpt]
  exact oneHot_pair_ind hrow hcol x y hx hy

end DstIndV2

/-! ## §17 — `landOldV2N_of_sat` / `landNzV2N_of_sat`: the CORRECTED-landing occupancy read.

`cLandOldV2 i` is the OLD-board code at the square the CORRECTED flow-through bit selects (own `.to`
when `cFtV2 = 0`, the OTHER piece's `.to` when `cFtV2 = 1`): the emitted `landOldV2Head` masked
double-sum, collapsed through the corrected-landing one-hot (`dstIndV2N_of_sat`). `cLandNzV2 i` is its
`≥ 1` bit, which the particle-alphabet envelope makes exactly `carAt` at that landing square. Clean
parametric read lemmas — the flow-through boolean and the two `.to` coordinate bounds are handed in
(as `dstIndV2N_of_sat` itself takes them), so the correspondence caller supplies them off the facts. -/
section LandV2
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

open Dregg2.Circuit.Emit.AutomataflCoord (evalH evalH_foldl_step evalH_addProd evalH_lin varsVal
  dot_oneHot2 headToExpr_eval)
open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric (OneHotAt)

/-- The clean semantic value of `landOldV2Head`, the twin of `evalH_sourceReadHead`. -/
theorem evalH_landOldV2Head (a : Nat → ℤ) (i : Nat) :
    evalH (NGen.landOldV2Head n i) a
      = a (NGen.cLandOldV2 n i)
        + ((List.range n).map (fun y => ((List.range n).map (fun x =>
            a (NGen.wDstV2Row n i y) * a (NGen.wDstV2Col n i x)
              * (- a (NGen.old n (y * n + x))))).sum)).sum := by
  have hinner : ∀ (h : Head) (y : Nat),
      evalH ((List.range n).foldl (fun h2 x =>
          h2.addProd (-1) [NGen.wDstV2Row n i y, NGen.wDstV2Col n i x, NGen.old n (y * n + x)]) h) a
        = evalH h a
          + ((List.range n).map (fun x =>
              a (NGen.wDstV2Row n i y) * a (NGen.wDstV2Col n i x)
                * (- a (NGen.old n (y * n + x))))).sum := by
    intro h y
    exact evalH_foldl_step a h (List.range n)
      (fun h2 x => h2.addProd (-1) [NGen.wDstV2Row n i y, NGen.wDstV2Col n i x, NGen.old n (y * n + x)])
      (fun x => a (NGen.wDstV2Row n i y) * a (NGen.wDstV2Col n i x) * (- a (NGen.old n (y * n + x))))
      (by intro h2 x; rw [evalH_addProd]; simp only [varsVal, List.foldl_cons, List.foldl_nil]; ring)
  rw [NGen.landOldV2Head,
    evalH_foldl_step a (Head.lin 1 (NGen.cLandOldV2 n i)) (List.range n)
      (fun h y => (List.range n).foldl (fun h2 x =>
          h2.addProd (-1) [NGen.wDstV2Row n i y, NGen.wDstV2Col n i x, NGen.old n (y * n + x)]) h)
      (fun y => ((List.range n).map (fun x =>
          a (NGen.wDstV2Row n i y) * a (NGen.wDstV2Col n i x) * (- a (NGen.old n (y * n + x))))).sum)
      hinner,
    evalH_lin]
  ring

/-- **Grid collapse of a product-indicator masked double-sum.** If `row y · col x` is the indicator of
`⟨lx, ly⟩` on the `n × n` grid, the masked board double-sum picks out `payload ly lx`. Pure. -/
theorem gridProdInd_collapse (row col : Nat → ℤ) (payload : Nat → Nat → ℤ)
    (lx ly : Nat) (hlx : lx < n) (hly : ly < n)
    (hind : ∀ x y, x < n → y < n → row y * col x = if (⟨x, y⟩ : Coord) = ⟨lx, ly⟩ then 1 else 0) :
    ((List.range n).map (fun y => ((List.range n).map (fun x =>
        row y * col x * payload y x)).sum)).sum = payload ly lx := by
  have hcollapse := dot_oneHot2 (rv := fun y => if y = ly then (1:ℤ) else 0)
    (cv := fun x => if x = lx then (1:ℤ) else 0) (n := n) (ay := ly) (ax := lx)
    ⟨hly, fun j _ => rfl⟩ ⟨hlx, fun j _ => rfl⟩ payload
  rw [← hcollapse]
  refine congrArg List.sum ?_
  apply List.map_congr_left; intro y hy; have hyn := List.mem_range.mp hy
  refine congrArg List.sum ?_
  apply List.map_congr_left; intro x hx; have hxn := List.mem_range.mp hx
  rw [hind x y hxn hyn]
  by_cases hxy : (⟨x, y⟩ : Coord) = ⟨lx, ly⟩
  · have hx' : x = lx := ((Coord.mk.injEq x y lx ly).mp hxy).1
    have hy' : y = ly := ((Coord.mk.injEq x y lx ly).mp hxy).2
    rw [if_pos hxy, if_pos hy', if_pos hx']; ring
  · rw [if_neg hxy]
    have hz : (if y = ly then (1:ℤ) else 0) * (if x = lx then (1:ℤ) else 0) = 0 := by
      by_cases hy' : y = ly
      · by_cases hx' : x = lx
        · exact absurd ((Coord.mk.injEq x y lx ly).mpr ⟨hx', hy'⟩) hxy
        · rw [if_neg hx', mul_zero]
      · rw [if_neg hy', zero_mul]
    rw [hz]

/-- **`landOldV2N_of_sat`.** The corrected-landing OLD-board code column IS the OLD board cell at the
square the corrected flow-through bit selects. Stated as an exact integer equality (both sides
canonical). `which = 0` reads `cFtV2A`, `which = 1` reads `cFtV2B`. -/
theorem landOldV2N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hn : (n : ℤ) < 2013265921)
    (hft : (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 0
        ∨ (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1)
    (hx0 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which)) < (n : ℤ))
    (hy0 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which)) < (n : ℤ))
    (hx1 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which))) < (n : ℤ))
    (hy1 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which))) < (n : ℤ)) :
    (envAt t i).loc (NGen.cLandOldV2 n which)
      = (envAt t i).loc (NGen.old n
          (((if (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1
              then (moveDecodeN n (envAt t i) (1 - which)).to
              else (moveDecodeN n (envAt t i) which).to).y) * n
           + (if (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1
              then (moveDecodeN n (envAt t i) (1 - which)).to
              else (moveDecodeN n (envAt t i) which).to).x)) := by
  set e := envAt t i with he
  set ftc := (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) with hftc
  set L : Coord := (if e.loc ftc = 1 then (moveDecodeN n e (1 - which)).to
                    else (moveDecodeN n e which).to) with hL
  have hLx : L.x < n := by
    rw [hL]; by_cases hf : e.loc ftc = 1
    · rw [if_pos hf]; show (e.loc (NGen.cTx n (NGen.mvBase n (1 - which)))).toNat < n; omega
    · rw [if_neg hf]; show (e.loc (NGen.cTx n (NGen.mvBase n which))).toNat < n; omega
  have hLy : L.y < n := by
    rw [hL]; by_cases hf : e.loc ftc = 1
    · rw [if_pos hf]; show (e.loc (NGen.cTy n (NGen.mvBase n (1 - which)))).toNat < n; omega
    · rw [if_neg hf]; show (e.loc (NGen.cTy n (NGen.mvBase n which))).toNat < n; omega
  -- the corrected-landing indicator
  have hdi := dstIndV2N_of_sat hsat hc i hi which hw hn hft hx0 hy0 hx1 hy1
  rw [← he, ← hftc, ← hL] at hdi
  -- the masked double-sum gate
  have hmem : cgH (NGen.landOldV2Head n which) ∈ (automataflResolveDescN n).constraints :=
    nlV2Lift which hw (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))
  have hg := rgateHN hsat i hi hmem
  rw [headToExpr_eval, evalH_landOldV2Head] at hg
  have hcollapse : ((List.range n).map (fun y => ((List.range n).map (fun x =>
        e.loc (NGen.wDstV2Row n which y) * e.loc (NGen.wDstV2Col n which x)
          * (- e.loc (NGen.old n (y * n + x))))).sum)).sum
      = - e.loc (NGen.old n (L.y * n + L.x)) := by
    have := gridProdInd_collapse (n := n) (fun y => e.loc (NGen.wDstV2Row n which y))
      (fun x => e.loc (NGen.wDstV2Col n which x))
      (fun y x => - e.loc (NGen.old n (y * n + x))) L.x L.y hLx hLy
      (fun x y hx hy => by rw [hdi x y hx hy])
    simpa using this
  rw [hcollapse] at hg
  refine eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) ?_
  exact (gate_modEq_iff (by ring)).mp hg

/-- **`landNzV2N_of_sat`.** The corrected-landing occupancy bit is boolean and is `1` iff the OLD
board carries a piece (`carAt = true`) at the square the corrected flow-through bit selects. -/
theorem landNzV2N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hn : (n : ℤ) < 2013265921)
    (hft : (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 0
        ∨ (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1)
    (hx0 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which)) < (n : ℤ))
    (hy0 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which)) < (n : ℤ))
    (hx1 : 0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n (1 - which))) < (n : ℤ))
    (hy1 : 0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which)))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n (1 - which))) < (n : ℤ)) :
    ((envAt t i).loc (NGen.cLandNzV2 n which) = 0 ∨ (envAt t i).loc (NGen.cLandNzV2 n which) = 1)
      ∧ ((envAt t i).loc (NGen.cLandNzV2 n which) = 1 ↔
          Dregg2.Games.AutomataflRules.carAt (boardDecodeOldN n (envAt t i))
            (if (envAt t i).loc (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) = 1
             then (moveDecodeN n (envAt t i) (1 - which)).to
             else (moveDecodeN n (envAt t i) which).to) = true) := by
  set e := envAt t i with he
  set ftc := (if which == 0 then NGen.cFtV2A n else NGen.cFtV2B n) with hftc
  set L : Coord := (if e.loc ftc = 1 then (moveDecodeN n e (1 - which)).to
                    else (moveDecodeN n e which).to) with hL
  have hLx : L.x < n := by
    rw [hL]; by_cases hf : e.loc ftc = 1
    · rw [if_pos hf]; show (e.loc (NGen.cTx n (NGen.mvBase n (1 - which)))).toNat < n; omega
    · rw [if_neg hf]; show (e.loc (NGen.cTx n (NGen.mvBase n which))).toNat < n; omega
  have hLy : L.y < n := by
    rw [hL]; by_cases hf : e.loc ftc = 1
    · rw [if_pos hf]; show (e.loc (NGen.cTy n (NGen.mvBase n (1 - which)))).toNat < n; omega
    · rw [if_neg hf]; show (e.loc (NGen.cTy n (NGen.mvBase n which))).toNat < n; omega
  have hLc : L.y * n + L.x < NGen.KK n := by
    simp only [NGen.KK]
    have hle : (L.y + 1) * n ≤ n * n := Nat.mul_le_mul_right n (by omega : L.y + 1 ≤ n)
    have hexp : (L.y + 1) * n = L.y * n + n := by ring
    omega
  -- the read value: cLandOldV2 = old at the landing cell
  have hread := landOldV2N_of_sat hsat hc i hi which hw hn hft hx0 hy0 hx1 hy1
  rw [← he, ← hftc, ← hL] at hread
  -- alphabet of the landing cell
  have halpha : e.loc (NGen.old n (L.y * n + L.x)) = 0 ∨ e.loc (NGen.old n (L.y * n + L.x)) = 1
      ∨ e.loc (NGen.old n (L.y * n + L.x)) = 2 ∨ e.loc (NGen.old n (L.y * n + L.x)) = 3 :=
    Dregg2.Circuit.Emit.AutomataflStepRefine.mem4_of_gate
      (rgateN hsat i hi (mem_resolve_of_mem_boardRange (br_old n (L.y * n + L.x) hLc)))
      (canon_loc hc i _)
  have hbnd : -99 ≤ e.loc (NGen.cLandOldV2 n which) ∧ e.loc (NGen.cLandOldV2 n which) ≤ 99 := by
    rw [hread]; rcases halpha with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  -- the ≥1 bit
  obtain ⟨hb, h1, h0⟩ :=
    ge0_5N_of_sat hsat hc i hi (NGen.cLandOldV2 n which) (NGen.cLandNzV2 n which)
      (NGen.landNzV2Bit n which 0)
      (nlV2Lift which hw (List.mem_append_left _ (List.mem_append_right _ (mem_forcedGe0N_ib _ _ _ _))))
      (fun k hk => nlV2Lift which hw
        (List.mem_append_left _ (List.mem_append_right _ (mem_forcedGe0N_bit _ _ _ _ k hk))))
      (nlV2Lift which hw (List.mem_append_left _ (List.mem_append_right _ (mem_forcedGe0N_head _ _ _ _))))
      hbnd.1 hbnd.2
  rw [← he] at hb h1 h0
  -- cLandNzV2 = 1 ↔ the landing OLD cell is nonzero
  have hiff_old : e.loc (NGen.cLandNzV2 n which) = 1 ↔ e.loc (NGen.old n (L.y * n + L.x)) ≠ 0 := by
    rw [hread] at h1 h0
    rcases halpha with h | h | h | h <;> rw [h] at h1 h0 ⊢
    · constructor
      · intro hone; exact absurd (h1 hone) (by norm_num)
      · intro hne; exact absurd rfl hne
    all_goals
      constructor
      · intro _; norm_num
      · intro _
        rcases hb with hz | ho
        · exact absurd (h0 hz) (by norm_num)
        · exact ho
  -- the landing cell decodes to the OLD board cell there, and `carAt` reads its non-vacuity
  have hcarr : Dregg2.Games.AutomataflRules.carAt (boardDecodeOldN n e) L = true
      ↔ e.loc (NGen.old n (L.y * n + L.x)) ≠ 0 := by
    have hcode : (boardDecodeOldN n e).cellAt L
        = codeToParticle (e.loc (NGen.old n (L.y * n + L.x))) := by
      simp only [boardDecodeOldN, Board.cellAt]
      rw [if_pos (⟨hLx, hLy⟩ : L.x < n ∧ L.y < n)]
    rw [Dregg2.Games.AutomataflRules.carAt, hcode]
    rcases halpha with h | h | h | h <;> rw [h] <;> decide
  exact ⟨hb, hiff_old.trans hcarr.symm⟩

end LandV2

/-! ## §18 — THE THIRD WOUND: the 2-CYCLE STAY, which the V3 surface does NOT close.

Chunks 4–5 corrected two configuration classes against the VALIDATED game: the occluded STAYER
(defect #8, §2/§3/§15) and the FLOW-THROUGH gap (§7/§9/§15). Casing the CORRECTED carry `cCarryV3`
against the reference `landMap_pair_a/b` 5-config if-tree discharges FIVE of the six landing arms —
blocked-stays, independent-own-dest, occluded-stayer, caterpillar, flow-through — but the SIXTH arm,
the **2-CYCLE** (`landMap_pair_twoCycle_a/b`), MISMATCHES.

THE CLASS (n ≥ 2). A carries at `sa`, wants `da = sb`; B carries at `sb`, wants `db = sa`; both
unblocked, distinct sources, distinct raw destinations. This is the symmetric 2-cycle A→B, B→A.

  * The FIXED reference (`AutomataflRules.landMap`, ruling C / audit divergence 3.5a — *"2-cycles:
    Always stay in place"*, the `twoCyc` dead-end in `leaves`) keeps BOTH pieces: `landMap sa = sa`,
    `landMap sb = sb`, `movers = []`, `resolvableB = true`, `resolveMoves = identity`.
  * The DESCRIPTOR SWAPS. `cFtV2A = 0` (the `¬eq_ba` conjunct is false in a 2-cycle), so A's corrected
    landing is `da = sb`; `cCv2 0 = surv·carSa·¬BA = 1`; `cLandNzV2 0 = carAt sb = 1`; the corrected
    non-leaver reads the OTHER piece's SEED carry `cCv2 1 = surv·carSb·¬BB = 1`, so
    `cNonLeaveV2 0 = cLandNzV2 0 · (1 − cCv2 1) = 1 · 0 = 0`, whence `cCarryV3 0 = cCv2 0 · ¬cNonLeaveV2 0
    = 1` — A CARRIES onto `sb`. Symmetrically `cCarryV3 1 = 1` carries B onto `sa`. And
    `cResolvableV2 = 1` (no merge — the two corrected dests `da = sb`, `db = sa` are DISTINCT — and no
    bad journey). So the emitted board writes the SWAP `mid[sa] = p_b`, `mid[sb] = p_a`.

The root cause: the corrected non-leaver `cNonLeaveV2 = landNzV2 · (1 − cCv2_other)` proxies "the piece
on my landing square does not itself leave" by the OTHER piece's SEED carry `cCv2` — but in a 2-cycle
BOTH seed carries are `1` even though BOTH pieces ultimately STAY (a mutual, recursive disposition the
reference captures with its dedicated `twoCyc` bit + the `leaves` fixpoint). The V3 surface has NO
two-cycle column, so the mutual stay is unmodeled. Closing it is a FOURTH emitter obligation: a
`cTwoCyc_i = eq_ab · eq_ba · ¬BA · ¬BB · carSa · carSb` bit ANDed as `¬cTwoCyc` into each carry
(equivalently `cCarryV4 = cCarryV3 · ¬cTwoCyc`), so a detected 2-cycle forces the carry to `0` and the
pieces are kept — exactly the reference's ruling C.

`twoCycleStay_witness_n3` is the executable falsifier, `decide`d entirely on the reference semantics:
the reference STAYS (identity board) where the descriptor SWAPS, so with `p_a ≠ p_b` the unconditional
`codeToParticle (cMidV3 …) = (resolveMoves …).cellAt …` is FALSE at `sa` (LHS `= p_b` from the swap,
RHS `= p_a` from the stay). Hence the full capstone is STILL NOT assemblable at `n ≥ 3` against this
descriptor — the landing correspondence closes 5 of 6 arms; the 2-cycle arm is the residual. -/
section TwoCycleWound
open Dregg2.Games.AutomataflRules (blockedB carAt landMap resolvableB resolveMoves)

/-- 3×3 witness. A (attractor) at `(0,0)` wants `(1,0)`; B (repulsor) at `(1,0)` wants `(0,0)`. Both
carry, both unblocked (each source is the OTHER's passable waypoint), rook-aligned in row 0. The
automaton sits at `(2,2)`, off both moves. This is the symmetric 2-cycle A→B, B→A. -/
def tcBoard : Board :=
  Dregg2.Games.Automatafl.mkBoard 3
    [(⟨0, 0⟩, Particle.attractor), (⟨1, 0⟩, Particle.repulsor)] ⟨2, 2⟩
def tcMA : Move := Move.mk 0 ⟨0, 0⟩ ⟨1, 0⟩
def tcMB : Move := Move.mk 1 ⟨1, 0⟩ ⟨0, 0⟩

/-- **THE 2-CYCLE STAY IS NOT EMPTY, AT `n = 3`, AND V3 GETS IT WRONG.** Both moves are legal with
distinct sources and distinct raw destinations, both unblocked, both carrying, forming the symmetric
2-cycle (`da = sb`, `db = sa`). The REFERENCE keeps BOTH pieces in place (`landMap sa = sa`,
`landMap sb = sb`, `resolvableB = true`, `resolveMoves = identity`). The descriptor's corrected surface
instead SWAPS them (see the section note: `cCarryV3 0 = cCarryV3 1 = 1`, `cResolvableV2 = 1`), so
`codeToParticle (cMidV3 …) = (resolveMoves …).cellAt …` is FALSE at `sa` — attractor kept by the
reference, repulsor written by the descriptor. Every clause `decide`d on the reference semantics. -/
theorem twoCycleStay_witness_n3 :
    MoveValid tcBoard tcMA ∧ MoveValid tcBoard tcMB
      ∧ tcMA.frm ≠ tcMB.frm ∧ tcMA.to ≠ tcMB.to
      ∧ tcMA.frm ≠ tcMA.to ∧ tcMB.frm ≠ tcMB.to
      -- the symmetric 2-cycle, both unblocked:
      ∧ tcMA.to = tcMB.frm ∧ tcMB.to = tcMA.frm
      ∧ blockedB tcBoard [tcMA, tcMB] tcMA = false
      ∧ blockedB tcBoard [tcMA, tcMB] tcMB = false
      ∧ carAt tcBoard tcMA.frm = true ∧ carAt tcBoard tcMB.frm = true
      -- the REFERENCE STAYS both pieces (ruling C, audit 3.5a):
      ∧ landMap tcBoard [tcMA, tcMB] tcMA.frm = tcMA.frm
      ∧ landMap tcBoard [tcMA, tcMB] tcMB.frm = tcMB.frm
      ∧ resolvableB tcBoard [tcMA, tcMB] = true
      ∧ (resolveMoves tcBoard [tcMA, tcMB]).cellAt tcMA.frm = Particle.attractor
      ∧ (resolveMoves tcBoard [tcMA, tcMB]).cellAt tcMB.frm = Particle.repulsor
      ∧ tcBoard.cellAt tcMA.frm = Particle.attractor
      ∧ tcBoard.cellAt tcMB.frm = Particle.repulsor
      ∧ Particle.attractor ≠ Particle.repulsor := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end TwoCycleWound

/-! ## §19 — THE V4 EXTRACTION TWINS: the 2-CYCLE detector and the FINAL corrected board rewrite.

The chunk-6 twins of §11 (`carryV3ArithN`), §12 (`midV3CellN`) and §13 (`writeCellV3N`), over the
FINAL corrected columns. `cTwoCyc` is the mutual-2-cycle detector (`§18`'s fix); `cCarryV4 =
cCarryV3 · (1 − cTwoCyc)` forces the corrected carry to `0` on a detected 2-cycle so both pieces are
kept; `cWBoardV4`/`cMidV4` are the `cResolvableV2`-gated FINAL board rewrite driven by `cCarryV4` and
the CHUNK-5 corrected `wDstV2` landing. Pure gate algebra — the mechanical mirrors of §11–§13. -/
section V4Extract
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- Membership lift into `twoCycConstraints`. -/
theorem tcLift {g : VmConstraint2} (h : g ∈ NGen.twoCycConstraints n) :
    g ∈ (automataflResolveDescN n).constraints := mem_resolve_of_mem_twoCyc h

/-- Membership lift into `carryV4Constraints`. -/
theorem cv4Lift {g : VmConstraint2} (h : g ∈ NGen.carryV4Constraints n) :
    g ∈ (automataflResolveDescN n).constraints := mem_resolve_of_mem_carryV4 h

/-- **`twoCycN_of_sat`.** The mutual 2-cycle detector `cTwoCyc` is boolean and is `1` iff both raw
destinations point at the other source (`eqAb = eqBa = 1`), neither move is inclusive-blocked
(`cOccIncl 1 = cOccIncl 0 = 0`, the `cNOccIb`/`cNOccIa` NOT bits emitted by `flowThroughV2`) and both
sources carry (`cAnz = cBnz = 1`). This is the circuit's rendering of the reference `twoCyc` dead-end
(ruling C). -/
theorem twoCycN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hab : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1)
    (hba : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1)
    (hocc1 : (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 1) = 1)
    (hocc0 : (envAt t i).loc (NGen.cOccIncl n 0) = 0 ∨ (envAt t i).loc (NGen.cOccIncl n 0) = 1)
    (hanz : (envAt t i).loc (NGen.cAnz n) = 0 ∨ (envAt t i).loc (NGen.cAnz n) = 1)
    (hbnz : (envAt t i).loc (NGen.cBnz n) = 0 ∨ (envAt t i).loc (NGen.cBnz n) = 1) :
    ((envAt t i).loc (NGen.cTwoCyc n) = 0 ∨ (envAt t i).loc (NGen.cTwoCyc n) = 1)
      ∧ ((envAt t i).loc (NGen.cTwoCyc n) = 1 ↔
          ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 2)) = 1
            ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 3)) = 1
            ∧ (envAt t i).loc (NGen.cOccIncl n 1) = 0 ∧ (envAt t i).loc (NGen.cOccIncl n 0) = 0
            ∧ (envAt t i).loc (NGen.cAnz n) = 1 ∧ (envAt t i).loc (NGen.cBnz n) = 1)) := by
  set e := envAt t i with he
  -- the inclusive-occlusion NOT bits (gate 0 and gate 5 of `flowThroughV2Constraints`)
  have hnoccb : e.loc (NGen.cNOccIb n) = 1 - e.loc (NGen.cOccIncl n 1) :=
    notBitN_of_sat hsat hc i hi (NGen.cNOccIb n) (NGen.cOccIncl n 1)
      (ftV2Lift (by rw [NGen.flowThroughV2Constraints]; exact List.mem_cons_self)) hocc1
  have hnoccbB : e.loc (NGen.cNOccIb n) = 0 ∨ e.loc (NGen.cNOccIb n) = 1 := by
    rcases hocc1 with h | h <;> rw [hnoccb, h] <;> norm_num
  have hnocca : e.loc (NGen.cNOccIa n) = 1 - e.loc (NGen.cOccIncl n 0) :=
    notBitN_of_sat hsat hc i hi (NGen.cNOccIa n) (NGen.cOccIncl n 0)
      (ftV2Lift (by rw [NGen.flowThroughV2Constraints]
                    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))) hocc0
  have hnoccaB : e.loc (NGen.cNOccIa n) = 0 ∨ e.loc (NGen.cNOccIa n) = 1 := by
    rcases hocc0 with h | h <;> rw [hnocca, h] <;> norm_num
  -- the five-product 2-cycle chain
  have htc1 : e.loc (NGen.cTwoCyc1 n)
      = e.loc (NGen.cEqBit n (NGen.eqBase n 2)) * e.loc (NGen.cEqBit n (NGen.eqBase n 3)) :=
    prodN_of_sat hsat hc i hi (NGen.cTwoCyc1 n) (NGen.cEqBit n (NGen.eqBase n 2))
      (NGen.cEqBit n (NGen.eqBase n 3))
      (tcLift (by rw [NGen.twoCycConstraints]; exact List.mem_cons_self)) hab hba
  have htc1B : e.loc (NGen.cTwoCyc1 n) = 0 ∨ e.loc (NGen.cTwoCyc1 n) = 1 := by
    rcases hab with a | a <;> rcases hba with b | b <;> rw [htc1, a, b] <;> norm_num
  have htc2 : e.loc (NGen.cTwoCyc2 n) = e.loc (NGen.cTwoCyc1 n) * e.loc (NGen.cNOccIb n) :=
    prodN_of_sat hsat hc i hi (NGen.cTwoCyc2 n) (NGen.cTwoCyc1 n) (NGen.cNOccIb n)
      (tcLift (by rw [NGen.twoCycConstraints]; exact List.mem_cons_of_mem _ List.mem_cons_self))
      htc1B hnoccbB
  have htc2B : e.loc (NGen.cTwoCyc2 n) = 0 ∨ e.loc (NGen.cTwoCyc2 n) = 1 := by
    rcases htc1B with a | a <;> rcases hnoccbB with b | b <;> rw [htc2, a, b] <;> norm_num
  have htc3 : e.loc (NGen.cTwoCyc3 n) = e.loc (NGen.cTwoCyc2 n) * e.loc (NGen.cNOccIa n) :=
    prodN_of_sat hsat hc i hi (NGen.cTwoCyc3 n) (NGen.cTwoCyc2 n) (NGen.cNOccIa n)
      (tcLift (by rw [NGen.twoCycConstraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      htc2B hnoccaB
  have htc3B : e.loc (NGen.cTwoCyc3 n) = 0 ∨ e.loc (NGen.cTwoCyc3 n) = 1 := by
    rcases htc2B with a | a <;> rcases hnoccaB with b | b <;> rw [htc3, a, b] <;> norm_num
  have htc4 : e.loc (NGen.cTwoCyc4 n) = e.loc (NGen.cTwoCyc3 n) * e.loc (NGen.cAnz n) :=
    prodN_of_sat hsat hc i hi (NGen.cTwoCyc4 n) (NGen.cTwoCyc3 n) (NGen.cAnz n)
      (tcLift (by rw [NGen.twoCycConstraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    List.mem_cons_self)))) htc3B hanz
  have htc4B : e.loc (NGen.cTwoCyc4 n) = 0 ∨ e.loc (NGen.cTwoCyc4 n) = 1 := by
    rcases htc3B with a | a <;> rcases hanz with b | b <;> rw [htc4, a, b] <;> norm_num
  have htc : e.loc (NGen.cTwoCyc n) = e.loc (NGen.cTwoCyc4 n) * e.loc (NGen.cBnz n) :=
    prodN_of_sat hsat hc i hi (NGen.cTwoCyc n) (NGen.cTwoCyc4 n) (NGen.cBnz n)
      (tcLift (by rw [NGen.twoCycConstraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ List.mem_cons_self))))) htc4B hbnz
  have hval : e.loc (NGen.cTwoCyc n)
      = e.loc (NGen.cEqBit n (NGen.eqBase n 2)) * e.loc (NGen.cEqBit n (NGen.eqBase n 3))
        * (1 - e.loc (NGen.cOccIncl n 1)) * (1 - e.loc (NGen.cOccIncl n 0))
        * e.loc (NGen.cAnz n) * e.loc (NGen.cBnz n) := by
    rw [htc, htc4, htc3, htc2, htc1, hnoccb, hnocca]
  refine ⟨?_, ?_⟩
  · rcases hab with a | a <;> rcases hba with b | b <;> rcases hocc1 with c | c <;>
      rcases hocc0 with d | d <;> rcases hanz with f | f <;> rcases hbnz with g | g <;>
      rw [hval, a, b, c, d, f, g] <;> norm_num
  · rw [hval]
    rcases hab with a | a <;> rcases hba with b | b <;> rcases hocc1 with c | c <;>
      rcases hocc0 with d | d <;> rcases hanz with f | f <;> rcases hbnz with g | g <;>
      rw [a, b, c, d, f, g] <;> norm_num

/-- **`carryV4ArithN_of_sat`.** `cCarryV4[which] = cCarryV3[which] · (1 − cTwoCyc)` is boolean and is
`1` iff `cCarryV3[which] = 1` and `cTwoCyc = 0` — the FINAL carry, forced to `0` on a detected
2-cycle so the piece is KEPT. -/
theorem carryV4ArithN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which < 2)
    (hcv3 : (envAt t i).loc (NGen.cCarryV3 n which) = 0
        ∨ (envAt t i).loc (NGen.cCarryV3 n which) = 1)
    (htc : (envAt t i).loc (NGen.cTwoCyc n) = 0 ∨ (envAt t i).loc (NGen.cTwoCyc n) = 1) :
    ((envAt t i).loc (NGen.cCarryV4 n which) = 0 ∨ (envAt t i).loc (NGen.cCarryV4 n which) = 1)
      ∧ ((envAt t i).loc (NGen.cCarryV4 n which) = 1 ↔
          ((envAt t i).loc (NGen.cCarryV3 n which) = 1
            ∧ (envAt t i).loc (NGen.cTwoCyc n) = 0)) := by
  set e := envAt t i with he
  have hntc : e.loc (NGen.cNTwoCyc n) = 1 - e.loc (NGen.cTwoCyc n) :=
    notBitN_of_sat hsat hc i hi (NGen.cNTwoCyc n) (NGen.cTwoCyc n)
      (tcLift (by rw [NGen.twoCycConstraints]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))) htc
  have hntcB : e.loc (NGen.cNTwoCyc n) = 0 ∨ e.loc (NGen.cNTwoCyc n) = 1 := by
    rcases htc with h | h <;> rw [hntc, h] <;> norm_num
  have hcarry : e.loc (NGen.cCarryV4 n which)
      = e.loc (NGen.cCarryV3 n which) * e.loc (NGen.cNTwoCyc n) := by
    have hmem : prodPin (NGen.cCarryV4 n which) (NGen.cCarryV3 n which) (NGen.cNTwoCyc n)
        ∈ (automataflResolveDescN n).constraints := by
      refine cv4Lift ?_
      rw [NGen.carryV4Constraints]
      interval_cases which
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    exact prodN_of_sat hsat hc i hi (NGen.cCarryV4 n which) (NGen.cCarryV3 n which) (NGen.cNTwoCyc n)
      hmem hcv3 hntcB
  refine ⟨?_, ?_⟩
  · rcases hcv3 with a | a <;> rcases hntcB with b | b <;> rw [hcarry, a, b] <;> norm_num
  · rw [hcarry, hntc]
    rcases hcv3 with a | a <;> rcases htc with b | b <;> rw [a, b] <;> norm_num

/-- **`midV4CellN_of_sat`.** The FINAL corrected-board cell gate `cMidV4[c] = cResolvableV2 ·
cWBoardV4[c] + (1 − cResolvableV2) · old[c]`, rearranged (stated mod `p`) — the twin of §12. -/
theorem midV4CellN_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) (c : Nat) (hcK : c < NGen.KK n) :
    (envAt t i).loc (NGen.cMidV4 n c)
      ≡ (envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.cWBoardV4 n c)
        + (envAt t i).loc (NGen.old n c)
        - (envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.old n c)
      [ZMOD 2013265921] := by
  have hmem : cgH (NGen.midV4CellHead n c) ∈ (automataflResolveDescN n).constraints := by
    apply mem_resolve_of_mem_midV4
    rw [NGen.midV4Constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hcK, rfl⟩)
  have hg := rgateHN hsat i hi hmem
  have hE : (headToExpr (NGen.midV4CellHead n c)).eval (envAt t i).loc
      = (envAt t i).loc (NGen.cMidV4 n c)
        + (-1) * ((envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.cWBoardV4 n c))
        + (-1) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.cResolvableV2 n) * (envAt t i).loc (NGen.old n c) := rfl
  rw [hE] at hg
  exact (gate_modEq_iff (by ring)).mp hg

/-- **`writeCellV4N_of_sat`.** The emitted FINAL corrected `cWBoardV4` cell gate, rearranged — the twin
of §13, with `carryV3Col` replaced by the 2-cycle-gated `carryV4Col` (the `wDstV2` landing one-hots
are unchanged). Same degree-7 shape. Stated mod `p`; `x`/`y` = column/row. -/
theorem writeCellV4N_of_sat (hsat : Satisfied2 hash (automataflResolveDescN n) minit mfin maddrs t)
    (i : Nat) (hi : i + 1 < t.rows.length) (c y x : Nat) (hy : y = c / n) (hx : x = c % n)
    (hcK : c < NGen.KK n) :
    (envAt t i).loc (NGen.cWBoardV4 n c)
      ≡ (1 - (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wSrcRow n 0 y)
                * (envAt t i).loc (NGen.wSrcCol n 0 x))
           - (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wDstV2Row n 0 y)
                * (envAt t i).loc (NGen.wDstV2Col n 0 x))
           - (envAt t i).loc (NGen.carryV4Col n 1) * ((envAt t i).loc (NGen.wSrcRow n 1 y)
                * (envAt t i).loc (NGen.wSrcCol n 1 x))
           - (envAt t i).loc (NGen.carryV4Col n 1) * ((envAt t i).loc (NGen.wDstV2Row n 1 y)
                * (envAt t i).loc (NGen.wDstV2Col n 1 x))
           + (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wSrcRow n 0 y)
                * (envAt t i).loc (NGen.wSrcCol n 0 x)) * ((envAt t i).loc (NGen.carryV4Col n 1)
                * ((envAt t i).loc (NGen.wDstV2Row n 1 y) * (envAt t i).loc (NGen.wDstV2Col n 1 x)))
           + (envAt t i).loc (NGen.carryV4Col n 1) * ((envAt t i).loc (NGen.wSrcRow n 1 y)
                * (envAt t i).loc (NGen.wSrcCol n 1 x)) * ((envAt t i).loc (NGen.carryV4Col n 0)
                * ((envAt t i).loc (NGen.wDstV2Row n 0 y) * (envAt t i).loc (NGen.wDstV2Col n 0 x)))
           + (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wSrcRow n 0 y)
                * (envAt t i).loc (NGen.wSrcCol n 0 x)) * ((envAt t i).loc (NGen.carryV4Col n 1)
                * ((envAt t i).loc (NGen.wSrcRow n 1 y) * (envAt t i).loc (NGen.wSrcCol n 1 x)))
           + (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wDstV2Row n 0 y)
                * (envAt t i).loc (NGen.wDstV2Col n 0 x)) * ((envAt t i).loc (NGen.carryV4Col n 1)
                * ((envAt t i).loc (NGen.wDstV2Row n 1 y) * (envAt t i).loc (NGen.wDstV2Col n 1 x))))
          * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wDstV2Row n 0 y)
            * (envAt t i).loc (NGen.wDstV2Col n 0 x)) * (envAt t i).loc (NGen.particleCol n 0)
        + (envAt t i).loc (NGen.carryV4Col n 1) * ((envAt t i).loc (NGen.wDstV2Row n 1 y)
            * (envAt t i).loc (NGen.wDstV2Col n 1 x)) * (envAt t i).loc (NGen.particleCol n 1)
        - (envAt t i).loc (NGen.carryV4Col n 0) * ((envAt t i).loc (NGen.wDstV2Row n 0 y)
            * (envAt t i).loc (NGen.wDstV2Col n 0 x)) * ((envAt t i).loc (NGen.carryV4Col n 1)
            * ((envAt t i).loc (NGen.wDstV2Row n 1 y) * (envAt t i).loc (NGen.wDstV2Col n 1 x)))
            * (envAt t i).loc (NGen.particleCol n 1)
        [ZMOD 2013265921] := by
  subst hy; subst hx
  have hmem : cgH (NGen.writeCellV4Head n c) ∈ (automataflResolveDescN n).constraints := by
    apply mem_resolve_of_mem_midV4
    rw [NGen.midV4Constraints]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hcK, rfl⟩)
  have hg := rgateHN hsat i hi hmem
  have hshape : (headToExpr (NGen.writeCellV4Head n c)).eval (envAt t i).loc
      = (envAt t i).loc (NGen.cWBoardV4 n c) + (-1) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wSrcRow n 0 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 0 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (-1) * ((envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n)) * (envAt t i).loc (NGen.particleCol n 0))
        + (envAt t i).loc (NGen.carryV4Col n 1) * (envAt t i).loc (NGen.wSrcRow n 1 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 1 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (envAt t i).loc (NGen.carryV4Col n 1) * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n)) * (envAt t i).loc (NGen.old n c)
        + (-1) * ((envAt t i).loc (NGen.carryV4Col n 1) * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n)) * (envAt t i).loc (NGen.particleCol n 1))
        + (-1) * ((envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wSrcRow n 0 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 0 (c % n)) * (envAt t i).loc (NGen.carryV4Col n 1)
            * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n)) * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (-1) * ((envAt t i).loc (NGen.carryV4Col n 1) * (envAt t i).loc (NGen.wSrcRow n 1 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 1 (c % n)) * (envAt t i).loc (NGen.carryV4Col n 0)
            * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n)) * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (-1) * ((envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wSrcRow n 0 (c / n))
            * (envAt t i).loc (NGen.wSrcCol n 0 (c % n)) * (envAt t i).loc (NGen.carryV4Col n 1)
            * (envAt t i).loc (NGen.wSrcRow n 1 (c / n)) * (envAt t i).loc (NGen.wSrcCol n 1 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (-1) * ((envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n)) * (envAt t i).loc (NGen.carryV4Col n 1)
            * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n)) * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n))
            * (envAt t i).loc (NGen.old n c))
        + (envAt t i).loc (NGen.carryV4Col n 0) * (envAt t i).loc (NGen.wDstV2Row n 0 (c / n))
            * (envAt t i).loc (NGen.wDstV2Col n 0 (c % n)) * (envAt t i).loc (NGen.carryV4Col n 1)
            * (envAt t i).loc (NGen.wDstV2Row n 1 (c / n)) * (envAt t i).loc (NGen.wDstV2Col n 1 (c % n))
            * (envAt t i).loc (NGen.particleCol n 1) := rfl
  rw [hshape] at hg
  exact (gate_modEq_iff (by ring)).mp hg

end V4Extract

/-! ## §8 — Axiom hygiene. Every exported theorem, kernel-clean. -/

#assert_axioms movesWindow_three
#assert_axioms blockedV2N_of_sat
#assert_axioms carryV2ArithN_of_sat
#assert_axioms nonLeaveGateN_of_sat
#assert_axioms midV2CellN_of_sat
#assert_axioms writeCellV2N_of_sat
#assert_axioms flowThroughOcclusionGap_witness_n3
-- CHUNK-5 corrected-surface (V3) extraction, off `Satisfied2 (automataflResolveDescN n)`:
#assert_axioms ftV2AN_of_sat
#assert_axioms ftV2BN_of_sat
#assert_axioms nonLeaveV2GateN_of_sat
#assert_axioms cv2ValN_of_sat
#assert_axioms carryV3ArithN_of_sat
#assert_axioms midV3CellN_of_sat
#assert_axioms writeCellV3N_of_sat
#assert_axioms resolvableV2ArithN_of_sat
#assert_axioms dstIndV2N_of_sat
#assert_axioms ftV2A_inclBlocked_kills_flowThrough
-- CHUNK-5 corrected-landing occupancy read (the connective the landing correspondence consumes):
#assert_axioms gridProdInd_collapse
#assert_axioms landOldV2N_of_sat
#assert_axioms landNzV2N_of_sat
-- THE THIRD WOUND (2-cycle STAY): the spec-side falsifier the V3 surface does not close.
#assert_axioms twoCycleStay_witness_n3
-- CHUNK-6 FINAL corrected-surface (V4) extraction, off `Satisfied2 (automataflResolveDescN n)`:
#assert_axioms twoCycN_of_sat
#assert_axioms carryV4ArithN_of_sat
#assert_axioms midV4CellN_of_sat
#assert_axioms writeCellV4N_of_sat

end Dregg2.Circuit.Emit.AutomataflResolveMovesCapstone
