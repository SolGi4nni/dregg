/-
WrapFloorProbe — re-measures the instrument `KimchiWrapProverChoice`'s header carries, AFTER the
`rungOwn`/`rungsUpto` rewrite.

    cd metatheory && LEAN_PATH=$(lake env printenv LEAN_PATH) lean --run wip/WrapFloorProbe.lean

⚑ THE HEADER'S OWN NUMBERS, measured 2026-08-03 BEFORE the rewrite, cold `lean --run` at `shapeWrap`:
    mkWrap shapeWrap                 75 ms
    circuitEnvAt tWrap .key          65 ms
    rungRows tWrap .key true  1 014 740 ms   ← 16 min 55 s, for 1 977 rows
…while the five families the `.key` branch returns cost 115 ms between them. The other 99.99% was
`xhatRows` + `splitRows`, bound by a `let` ABOVE the `match` and discarded.

⚑ `rowsWrapKey` is a NULLARY `def` named by THREE separate commands in that module, and
`wip/NullaryShareProbe.lean` measured that a nullary is recomputed **once per command** (582 / 583 /
580 ms for the same `def`, against 580 ms for a distinct control). So the multiplier in the header's
retracted "~51 minutes" sentence is REAL — the mechanism half of that sentence was right.
-/
import Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiWrapMain

set_option maxRecDepth 100000

def force (n : Nat) (what : String) : IO Nat := do
  if n == 0 then throw (IO.userError s!"probe: '{what}' produced nothing")
  pure n

def timed (what : String) (f : Unit → Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let v ← force (f ()) what
  let t1 ← IO.monoMsNow
  IO.println s!"{t1 - t0} ms\tval={v}\t{what}"

def main : IO Unit := do
  let s := shapeWrap
  timed "mkWrap shapeWrap (FRESH, forced inside the window)" (fun _ =>
    (mkWrap s).sp.evs.length + 1)
  let t := mkWrap s
  timed "circuitEnvAt tWrap .key" (fun _ => (circuitEnvAt t .key).length)
  IO.println "-- the row families the .key branch RETURNS --"
  timed "rungOwn t true .transcript" (fun _ => (rungOwn t true .transcript).length)
  timed "rungOwn t true .challenges" (fun _ => (rungOwn t true .challenges).length)
  timed "rungOwn t true .branch" (fun _ => (rungOwn t true .branch).length)
  timed "rungOwn t true .bind" (fun _ => (rungOwn t true .bind).length)
  timed "rungOwn t true .key" (fun _ => (rungOwn t true .key).length)
  IO.println "-- the families the .key branch DOES NOT return (the old defect's 99.99%) --"
  timed "rungOwn t true .xhat  [xhatRows]" (fun _ => (rungOwn t true .xhat).length)
  timed "rungOwn t true .split [splitRows]" (fun _ => (rungOwn t true .split).length)
  IO.println "-- ⚑ THE HEADER'S ROW: 1 014 740 ms before the rewrite --"
  timed "rungRows tWrap .key true   (rowsWrapKey)" (fun _ => (rungRows t .key true).length)
  timed "rungRows tWrap .ftcomm true (the top rung, ALL eight)" (fun _ =>
    (rungRows t .ftcomm true).length)
