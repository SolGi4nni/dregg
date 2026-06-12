/-
# EmitRotationV3 — the staged ROTATION wire-artifact emit executable (sibling of
`EmitAllJsonV2.lean`).

Prints two TSV lines from the verified rotation emission
(`Dregg2/Circuit/Emit/EffectVmEmitRotation.lean`):

  `rotationLayoutManifest\t<manifest json>`
  `rotationProbeVmDescriptor2\t<descriptor.name>\t<emitVmJson2 descriptor>`

so the staged Rust artifacts (`circuit/descriptors/rotation-layout-v3-staged.json`,
`circuit/descriptors/dregg-effectvm-rotation-state-v3-staged.json`) can be regenerated
byte-for-byte from the verified Lean emit. STAGED: nothing rides the live v1 wire — the Rust
consumers are the recursion-gated IR-v2 path + the drift guards
(`effect_vm_descriptors.rs::rotation_layout_matches_lean` / `v3_staged_*`). SCRATCH
executable: run with `lake env lean --run EmitRotationV3.lean`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotation

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.EffectVmEmitRotation

def main : IO Unit := do
  IO.println s!"rotationLayoutManifest\t{rotationLayoutManifest}"
  IO.println
    s!"rotationProbeVmDescriptor2\t{rotationProbeVmDescriptor2.name}\t{emitVmJson2 rotationProbeVmDescriptor2}"
