/-
Word54Cone — MEASURE the transitive input cone of packed step-statement word 54 (Mina's wrap
public-input slot 12) before anything is asserted about it.

    cd metatheory
    lake env lean --run wip/Word54Cone.lean
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture
import Dregg2.Circuit.Emit.KimchiStepWrapChainFixture
import Dregg2.Circuit.Emit.MinaWrapOwnVerifierKey

open Dregg2.Circuit.Emit KimchiStepMain
open Dregg2.Circuit.Emit.PastaField (pN)

def SPI : List Nat := Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC_IN
def PREVCOMM : List Nat := Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PREVCOMM_XY
def IDXW : List Nat := Dregg2.Circuit.Emit.MinaWrapOwnVerifierKey.INDEX_WORDS

def main : IO Unit := do
  let t := tStep
  let s := shapeStep
  let cone : List Nat := t.specD.ws.map (·.2)
  IO.println s!"cone length            = {cone.length}"
  IO.println s!"N_IDX_WORDS+N_HM_APP+2+bRounds = {N_IDX_WORDS + N_HM_APP + 2 + s.bRounds}"
  IO.println s!"word54 (segD squeeze)  = {(t.segD.states.getLastD []).getD 0 0}"
  IO.println s!"hmOutDigestOf          = {hmOutDigestOf s t.sp t.gXY}"
  IO.println s!"STEP_PUBLIC_IN.len     = {SPI.length}"
  IO.println s!"STEP_PUBLIC_IN[64]     = {SPI.getD 64 0}"
  IO.println s!"STEP_PUBLIC_IN[65]     = {SPI.getD 65 0}"
  IO.println s!"STEP_PUBLIC_IN[66]     = {SPI.getD 66 0}"
  -- family 1: the 56 index words
  let f1 := (List.range N_IDX_WORDS).all (fun i => cone.getD i 0 == IDXW.getD i 0)
  IO.println s!"[F1] first 56 == MinaWrapOwnVerifierKey.INDEX_WORDS : {f1}"
  -- family 2: the app state
  let f2 := (List.range N_HM_APP).all (fun i => cone.getD (N_IDX_WORDS + i) 0 == hmOVal i)
  IO.println s!"[F2] next {N_HM_APP} == hmOVal : {f2}"
  -- family 3: G
  let f3 := cone.getD (N_IDX_WORDS + N_HM_APP) 0 == t.gXY.1
             && cone.getD (N_IDX_WORDS + N_HM_APP + 1) 0 == t.gXY.2
  IO.println s!"[F3] next 2 == tStep.gXY : {f3}   G = {t.gXY}"
  -- family 4: the sixteen lifts
  let f4 := (List.range s.bRounds).all (fun k =>
      cone.getD (N_IDX_WORDS + N_HM_APP + 2 + k) 0 == liftOf s t.sp (s.uChal k))
  IO.println s!"[F4] last {s.bRounds} == liftOf (uChal k) : {f4}"
  -- ⚑ the raw 128-bit prechallenges whose lifts those are
  IO.println s!"prechals = {(List.range s.bRounds).map (fun k => chalOf s t.sp (s.uChal k))}"
  IO.println s!"lifts    = {(List.range s.bRounds).map (fun k => liftOf s t.sp (s.uChal k))}"
  -- (4) does any published statement entry appear in the cone?
  let hit := cone.filter (fun v => SPI.contains v)
  IO.println s!"[C4] cone ∩ STEP_PUBLIC_IN = {hit.length} : {hit}"
  -- which entries, by index
  let hitIx := (List.range SPI.length).filter (fun i => cone.contains (SPI.getD i 0))
  IO.println s!"[C4] hit entry indices = {hitIx}"
  -- (5) the marshaller's chosen accumulator and words 55/56
  IO.println s!"[C5] cone ∩ STEP_PREVCOMM_XY = {PREVCOMM.filter (fun v => cone.contains v)}"
  IO.println s!"[C5] cone contains entry 65 = {cone.contains (SPI.getD 65 0)}"
  IO.println s!"[C5] cone contains entry 66 = {cone.contains (SPI.getD 66 0)}"
  IO.println s!"[C5] cone contains entry 64 = {cone.contains (SPI.getD 64 0)}"
  -- (6) anti-vacuity: bend each family and watch word 54 move
  IO.println s!"[AV] bend Gx  moves : {hmOutDigestOf s t.sp (Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fAdd t.gXY.1 1, t.gXY.2) != hmOutDigestOf s t.sp t.gXY}"
  IO.println s!"[AV] bend Gy  moves : {hmOutDigestOf s t.sp (t.gXY.1, Dregg2.Circuit.Emit.KimchiRenderVarBaseMul.fAdd t.gXY.2 1) != hmOutDigestOf s t.sp t.gXY}"
  IO.println s!"cone nonzero count = {(cone.filter (fun v => v != 0)).length}"
