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

end Dregg2.Circuit.Emit.AutomataflResolveMovesCapstone
