/-
SCRATCH executable: emit the SCHEDULED (allocated, one-op-per-row) Pasta RCB complete-add
descriptors as IR-v2 JSON, so the COMMITTED width can be measured on the emitted bytes in Rust
rather than only on the Lean source.

  lake env lean --run EmitPastaCurveScheduled.lean pallas \
    > ../circuit/tests/fixtures/pasta-pallas-complete-add-scheduled.json
  lake env lean --run EmitPastaCurveScheduled.lean vesta \
    > ../circuit/tests/fixtures/pasta-vesta-complete-add-scheduled.json

⚑ **These go to `tests/fixtures/`, NOT to `descriptors/by-name/`.** The scheduled row is not routed
by name, no VK is rotated for it, and `PROVENANCE.json` is not stamped — it is a MEASUREMENT
artifact. Routing it would be a separate, deliberate act with its own `byNameDescriptors_length`
bump.

The descriptors are `Dregg2.Circuit.Emit.PastaCurveScheduled.{pallas,vesta}ScheduledDesc`, each
`EffectLower.lowerTiedAir` of the allocated source `EffectAir` whose every column index is computed
by `AirColumnAlloc.allocate`. This file only RENDERS; it authors nothing.
-/
import Dregg2.Circuit.Emit.PastaCurveScheduled

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.PastaCurveScheduled

def main (args : List String) : IO Unit :=
  match args with
  | ["pallas"] => IO.println (emitVmJson2 pallasScheduledDesc)
  | ["vesta"]  => IO.println (emitVmJson2 vestaScheduledDesc)
  | _ => IO.eprintln "usage: EmitPastaCurveScheduled.lean (pallas|vesta)"
