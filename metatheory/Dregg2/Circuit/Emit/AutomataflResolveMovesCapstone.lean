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

/-! ## §8 — Axiom hygiene. Every exported theorem, kernel-clean. -/

#assert_axioms movesWindow_three
#assert_axioms blockedV2N_of_sat
#assert_axioms carryV2ArithN_of_sat
#assert_axioms nonLeaveGateN_of_sat
#assert_axioms midV2CellN_of_sat
#assert_axioms writeCellV2N_of_sat
#assert_axioms flowThroughOcclusionGap_witness_n3

end Dregg2.Circuit.Emit.AutomataflResolveMovesCapstone
