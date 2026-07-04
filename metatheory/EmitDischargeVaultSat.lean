/-
# EmitDischargeVaultSat — SCRATCH emit runner for the G5 tag-18/19 staged satisfaction descriptors
(the pre-regen exercise fixtures; the registry rows themselves ride the BIG-BANG regen).

Prints two TSV-shaped lines from the verified emit:

  `dischargeSatVmDescriptor2R24\t<name>\t<emitVmJson2 (dischargeSatVmDescriptor2R24 0 1 2)>`
  `vaultSatVmDescriptor2R24\t<name>\t<emitVmJson2 (vaultSatVmDescriptor2R24 0 1)>`

so the prove exercise (`circuit/tests/gentian_discharge_vault_prove.rs`) can parse the Lean-emitted
descriptors directly (`parse_vm_descriptor2` on the JSON), byte-faithful to what the big-bang
registry regen will land. Slots: discharge cur/tot/due = fields 0/1/2; vault asset/share = 0/1.

Run: `lake env lean --run EmitDischargeVaultSat.lean`
-/
import Dregg2.Deos.DischargeSatDescriptor
import Dregg2.Deos.VaultSatDescriptor

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)

def main : IO Unit := do
  let d := Dregg2.Deos.DischargeSatDescriptor.dischargeSatVmDescriptor2R24 0 1 2
  IO.println s!"dischargeSatVmDescriptor2R24\t{d.name}\t{emitVmJson2 d}"
  let v := Dregg2.Deos.VaultSatDescriptor.vaultSatVmDescriptor2R24 0 1
  IO.println s!"vaultSatVmDescriptor2R24\t{v.name}\t{emitVmJson2 v}"
