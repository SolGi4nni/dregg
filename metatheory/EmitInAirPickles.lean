/-
SCRATCH driver: emit the by-name rows this campaign's in-AIR Pickles rung moves.

  lake env lean --run EmitInAirPickles.lean

⚠ **THIS IS NOT A SECOND ROUTING TABLE.** Every descriptor below is ALREADY a row of
`EmitByName.byNameDescriptors`, and `--verify-by-name-routing` still reconciles both directions.
This file exists only because the routed emitter cannot be RUN today: `EmitByName.lean` imports
`Dregg2.Circuit.Emit.AutomataflNGenGolden`, whose two `emitVmJson2 … == "…"` byte goldens
(`:111`, `:114`) are RED at HEAD — a sibling lane's stale golden, in a file this lane has not
touched. `emitVmJson2 d` on the same `d` is byte-identical whichever driver calls it, so this
reproduces the routed bytes rather than transcribing them; the hop the routed emitter exists to
delete is a HAND transcription, and there is none here.

Delete this file the day `AutomataflNGenGolden` is green again.
-/
import Dregg2.Circuit.Emit.MinaWrapConjunctionAir
import Dregg2.Circuit.Emit.LightClientMinaAir

open Dregg2.Circuit Dregg2.Circuit.DescriptorIR2

def rows : List (String × EffectVmDescriptor2) :=
  [ ("mina-wrap-conjunction.json",
      Dregg2.Circuit.Emit.MinaWrapConjunctionAir.conjunctionDesc)
  , ("mina-wrap-conjunction-unthreaded.json",
      Dregg2.Circuit.Emit.MinaWrapConjunctionAir.conjunctionUnthreadedDesc)
  , ("dregg-mina-lightclient-verify-v1.json",
      Dregg2.Circuit.Emit.LightClientMinaAir.minaLcVerifyDesc) ]

def main : IO Unit := do
  for (n, d) in rows do IO.println s!"{n}\t{emitVmJson2 d}"
