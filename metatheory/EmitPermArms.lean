/-
# `EmitPermArms` — the byte source for the two STANDALONE permutation-arm table AIRs.

Prints one `<filename>\t<emitTableAirJson t>` line per arm, the same `<file>\t<json>` shape
`EmitTableAirs.lean` uses.

    lake env lean --run EmitPermArms.lean

⚠ **These are NOT deployed artifacts.** They are the measurement/fidelity fixtures under
`circuit/tests/fixtures/perm-arms/`, deliberately kept out of `EmitTableAirs.lean`'s routing table
so the descriptor-provenance pipeline and the eleven checked-in `circuit/descriptors/table-airs/`
files are untouched. The deployed chip still carries the WIDE arm; see
`Dregg2/Circuit/Emit/Poseidon2RoundGates.lean` §8g for the cutover list.

Law #1: the constraints are authored in `Dregg2/Circuit/Emit/Poseidon2RoundGates.lean` §5b/§8 and
proved there; `PermArmTableEmit.lean` only gives them a width and a name, and this file only
serializes them.
-/
import Dregg2.Circuit.Emit.PermArmTableEmit

def main : IO Unit := do
  for line in Dregg2.Circuit.Emit.PermArmTableEmit.emitPermArmLines do
    IO.println line
