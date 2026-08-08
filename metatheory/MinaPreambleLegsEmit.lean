/-
# `MinaPreambleLegsEmit` — the ONE witness row of `dregg-mina-preamble-legs::v1`.

`Dregg2.Circuit.Emit.MinaPreambleLegsAir` authors the AIR and proves both polarities on its
`PreambleRowOk` predicate; this driver renders the row Lean already committed to
(`MinaPreambleLegsAir.realRow` — the real devnet block 539508's preamble tuple as
`bridge/src/mina_pickles.rs` measures it on the wire) so the deployed prover is handed the SAME
object rather than a Rust re-derivation of it.

    cd metatheory
    lake env lean --run MinaPreambleLegsEmit.lean ../circuit/tests/fixtures

writes `mina-preamble-legs-row.txt` — ONE line, 30 space-separated decimals, columns in
descriptor order. The PI vector is the first 8 entries (slot `s` IS column `s`), so nothing else
needs emitting.
-/
import Dregg2.Circuit.Emit.MinaPreambleLegsAir

open Dregg2.Circuit.Emit.MinaPreambleLegsAir

def main (args : List String) : IO Unit := do
  let dir := args.getD 0 "../circuit/tests/fixtures"
  let cells := (List.range PREAMBLE_WIDTH).map (fun c => toString (realRow c))
  let line := String.intercalate " " cells
  let path := System.FilePath.mk dir / "mina-preamble-legs-row.txt"
  IO.FS.writeFile path (line ++ "\n")
  IO.println s!"wrote {path} — {PREAMBLE_WIDTH} cells ({PREAMBLE_PI_COUNT} published)"
