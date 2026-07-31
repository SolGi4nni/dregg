/-
# EmitWideTransferProbe — ADDITIVE wide-transfer descriptor emit (STAGED slice).

Prints ONE TSV line:

  `transferVmDescriptor2R24Wide\t<name>\t<emitVmJson2 (wide transfer)>`

from the verified wide registry `v3RegistryWide` (the transfer member at index 0 =
`wideAppend transferV3 bb (bb + B_SPAN)`, host + the 992-column wide appendix). This is the byte source of the
ADDITIVE Rust artifact `circuit/descriptors/rotation-wide-transfer-staged.tsv` the wide-roundtrip
slice consumes — NOTHING on the live 1-felt wire path changes (`v3RegistryCapOpen` / the live TSV
are UNTOUCHED). SCRATCH executable: `lake env lean --run EmitWideTransferProbe.lean`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationWide
-- THE S2 DELETION (Epoch 1): the probe line is compacted exactly like the registry row
-- (bb = the bare transfer face width, checked by `compactOk`).
import Dregg2.Circuit.Emit.WideCompactTable
import Dregg2.Circuit.Emit.FieldsCanonicity9Emit

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide (v3RegistryWide)

def main : IO Unit := do
  -- transfer is index 0 of the wide cohort (member-for-member with the live registry).
  match v3RegistryWide with
  | (_, d0) :: _ =>
      let d := Dregg2.Circuit.Emit.FieldsCanonicity9Emit.fieldsCanonical9Wire d0
      let bb := Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor.traceWidth
      match Dregg2.Circuit.Emit.RotWideCompactS2.s2LaneBaseOf d bb with
      | none => throw (IO.userError "wide transfer probe: no recognizable S2 stratum")
      | some lb =>
        if Dregg2.Circuit.Emit.RotWideCompactS2.compactOk d bb lb then
          let cm := Dregg2.Circuit.Emit.RotWideCompactS2.compactS2 d bb lb
          IO.println s!"transferVmDescriptor2R24Wide\t{cm.name}\t{emitVmJson2 cm}"
        else
          throw (IO.userError
            "wide transfer probe: compactOk REFUSED — the S2 stratum is not the expected dead chains")
  | [] => IO.eprintln "v3RegistryWide is empty"
