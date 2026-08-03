/-
# EmitMinaLink — the byte source for `dregg-mina-lightclient-link::v1`.

Prints `<filename>\t<emitVmJson2 descriptor>` for the MULTI-ROW Mina exhibited-segment descriptor.
Same mechanism as `EmitTurnChain.lean`: run it, byte-pin the output as the descriptor JSON.

    lake env lean --run EmitMinaLink.lean

Law #1: the constraints are AUTHORED in `Dregg2/Circuit/Emit/LightClientMinaLinkAir.lean` — and
there they are the COMPILER's output (`EffectLower.lowerAir` of `minaLinkAir`), not hand-written.
This file only SERIALIZES. Rust interprets; Rust authors nothing.
-/
import Dregg2.Circuit.Emit.LightClientMinaLinkAir

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.LightClientMinaLinkAir (minaLinkDesc)

def main : IO Unit :=
  IO.println s!"dregg-mina-lightclient-link-v1.json\t{emitVmJson2 minaLinkDesc}"
