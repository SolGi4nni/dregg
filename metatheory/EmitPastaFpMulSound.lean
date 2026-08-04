/-
SCRATCH executable: emit the FELT-SOUND Pasta multiply descriptors as IR-v2 JSON.

  lake env lean --run EmitPastaFpMulSound.lean fp > ../circuit/descriptors/by-name/pasta-fpmul-sound.json
  lake env lean --run EmitPastaFpMulSound.lean fq > ../circuit/descriptors/by-name/pasta-fqmul-sound.json
  lake env lean --run EmitPastaFpMulSound.lean trace > ../circuit/tests/fixtures/pasta-fpmul-sound-trace.txt

The descriptors are `Dregg2.Circuit.Emit.PastaFieldSound.{fpMulSoundDesc, fqMulSoundDesc}`, each
`EffectLower.lowerAir` of the source `EffectAir` `soundMulAir` — House Law #1's endpoint form: there
is no hand-written `VmConstraint2` list for a re-emission to drift from. This file only RENDERS;
it authors nothing.

The trace is `honestRow` of the Lean-generated witness `mulAsg`, repeated to a power-of-two height.
Every declared range lookup constrains its wire on EVERY row (`LookupSpec` carries no guard), so the
padding rows are copies rather than zeros.
-/
import Dregg2.Circuit.Emit.PastaFieldSound

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.PastaFieldSound

/-- Repeat the honest row to a power-of-two height. -/
def traceText : String :=
  let line := String.intercalate " " (fpHonestRow.map toString)
  String.intercalate "\n" (List.replicate 8 line) ++ "\n"

def main (args : List String) : IO Unit :=
  match args with
  | ["fp"]    => IO.println (emitVmJson2 fpMulSoundDesc)
  | ["fq"]    => IO.println (emitVmJson2 fqMulSoundDesc)
  | ["trace"] => IO.print traceText
  | _         => IO.eprintln "usage: EmitPastaFpMulSound.lean (fp|fq|trace)"
