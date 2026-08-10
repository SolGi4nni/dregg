/- Scratch generator for `MinaWrapOpeningSched`'s literal manifest.
   Run: `lake env lean --run scripts/gen_opening_manifest.lean`
   Output: the 35 addend triples as Lean literals + the terminal sanity line.
   The literals are SPLICED, never hand-typed (the finalize `hiTable` lesson). -/
import Dregg2.Circuit.Emit.MinaWrapOpeningGate

open Dregg2.Circuit.Emit.MinaWrapOpeningGate
open Dregg2.Circuit.Emit.MinaWrapGroupGate (smul padd pneg)
open Dregg2.Circuit.Emit.PastaCurveComplete (Oproj)
open Dregg2.Circuit.Emit.PastaField (pN qN)

abbrev Pt := Dregg2.Circuit.Emit.MinaWrapGroupGate.Pt

def redPt (P : Pt) : Pt := (P.1 % pN, P.2.1 % pN, P.2.2 % pN)

def sgTerm : Nat × Pt := ((qN - Z1 % qN) % qN, SG)

def nonSgTerms : List (Nat × Pt) :=
  lrTerms C CHAL CHAL_INV
    ++ [ (C % qN, Dregg2.Circuit.Emit.MinaWrapAggregationGate.COMBINED_GOLD)
       , ((C * CIP_N % qN + qN - Z1 * B0 % qN) % qN, U_BASE)
       , ((qN - Z2 % qN) % qN, SRS_H) ]

def addends : List Pt :=
  (sgTerm :: nonSgTerms).map (fun t => redPt (smul t.1 t.2)) ++ [redPt DELTA]

def chainFold (As : List Pt) : Pt := As.foldl padd Oproj

def main : IO Unit := do
  IO.println s!"-- {addends.length} addends, spliced from scripts/gen_opening_manifest.lean"
  IO.println "def openingAddends : List Pt :="
  let mut first := true
  for a in addends do
    let sep := if first then "  [ " else "  , "
    first := false
    IO.println s!"{sep}({a.1},"
    IO.println s!"     {a.2.1},"
    IO.println s!"     {a.2.2})"
  IO.println "  ]"
  let t := chainFold addends
  IO.println s!"-- terminal X%p = {t.1 % pN}  Z%p = {t.2.2 % pN}  (both MUST be 0)"
  IO.println s!"-- isInfM = {Dregg2.Circuit.Emit.PastaCurveComplete.isInfM pN t}"
  -- prefix sanity: no proper non-empty prefix closes
  let pref := (List.range 34).all (fun k =>
    !(Dregg2.Circuit.Emit.PastaCurveComplete.isInfM pN (chainFold (addends.take (k + 1)))))
  IO.println s!"-- no accepting proper prefix = {pref}"
  -- the forged pair: cc slot (global index 31) re-scaled to FT_COMM_GOLD, sg slot solved
  let ccForged := redPt (smul (C % qN) Dregg2.Circuit.Emit.MinaWrapGroupGate.FT_COMM_GOLD)
  let forgedTail := (addends.drop 1).set 30 ccForged
  let solved := redPt (pneg (chainFold forgedTail))
  IO.println s!"-- ccForged = ({ccForged.1}, {ccForged.2.1}, {ccForged.2.2})"
  IO.println s!"-- solvedAddend = ({solved.1}, {solved.2.1}, {solved.2.2})"
  IO.println s!"-- forged chain closes = {Dregg2.Circuit.Emit.PastaCurveComplete.isInfM pN (chainFold (solved :: forgedTail))}"
  IO.println s!"-- solved != pinned sg addend = {solved != addends.getD 0 Oproj}"
  IO.println s!"-- moved-cc-alone does not close = {!(Dregg2.Circuit.Emit.PastaCurveComplete.isInfM pN (chainFold (addends.set 31 ccForged)))}"
  IO.println s!"-- terminal Y%p = {t.2.1 % pN}"
