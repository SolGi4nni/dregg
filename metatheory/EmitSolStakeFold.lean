/-
# EmitSolStakeFold — the byte source for `dregg-solana-stake-table-fold::v1`.

Prints `<filename>\t<emitVmJson2 descriptor>` for the MULTI-ROW Solana stake-table fold descriptor.
Same mechanism as `EmitMinaLink.lean`: run it, byte-pin the output as the descriptor JSON.

    lake env lean --run EmitSolStakeFold.lean

Law #1: the constraints are AUTHORED in `Dregg2/Circuit/Emit/LightClientSolStakeFoldAir.lean` — and
there they are the COMPILER's output (`EffectLower.lowerAir` of `solStakeFoldAir`), not
hand-written. This file only SERIALIZES. Rust interprets; Rust authors nothing.
-/
import Dregg2.Circuit.Emit.LightClientSolStakeFoldAir

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.LightClientSolStakeFoldAir (solStakeFoldDesc)

def main : IO Unit :=
  IO.println s!"dregg-solana-stake-table-fold-v1.json\t{emitVmJson2 solStakeFoldDesc}"
