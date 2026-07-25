/-
# EmitDungeonProgram — the descent cell-program emit executable.

Prints the checked-in JSON artifact for the DEPLOYED descent teeth
(`Dregg2.Games.Dungeon.Prog.dungeonProgram`), the Lean-sourced object
`dungeon-on-dregg/src/descent.rs::Deployment::program()` loads. The bytes are the
byte-exact output of this verified emit; the checked-in
`dungeon-on-dregg/program/dungeon_program.json` is a CACHE of this emission (Lean is the
source of truth), regenerate-and-diff gated by `dungeon-on-dregg/program/regen.sh`.

⚑ THE DESCENT IS A DAILY. The map is drawn from the committed day-seed
(`Dregg2.Games.Dungeon.drawFamily`), so the artifact carries the WHOLE family: one fully
emitted 13-case program per day, authored in Lean for exactly that day's minted homes and
guardian vitalities. The loader picks the day's index and resolves the symbolic names to
slots; it never assembles a constraint.

Run:  lake env lean --run EmitDungeonProgram.lean
-/
import Dregg2.Games.DungeonProgram

open Dregg2.Games.Dungeon.Prog (emitFamilyJson)

def main : IO Unit :=
  IO.print emitFamilyJson
