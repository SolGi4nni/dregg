/-
SCRATCH executable: emit the FELT-SOUND Pasta ADD/SUB descriptors as IR-v2 JSON.

  lake env lean --run EmitPastaAddSubSound.lean fpadd > ../circuit/descriptors/by-name/pasta-fpadd-sound.json
  lake env lean --run EmitPastaAddSubSound.lean fpsub > ../circuit/descriptors/by-name/pasta-fpsub-sound.json
  lake env lean --run EmitPastaAddSubSound.lean fqadd > ../circuit/descriptors/by-name/pasta-fqadd-sound.json
  lake env lean --run EmitPastaAddSubSound.lean fqsub > ../circuit/descriptors/by-name/pasta-fqsub-sound.json
  lake env lean --run EmitPastaAddSubSound.lean addtrace > ../circuit/tests/fixtures/pasta-fpadd-sound-trace.txt
  lake env lean --run EmitPastaAddSubSound.lean subtrace > ../circuit/tests/fixtures/pasta-fpsub-sound-trace.txt

The descriptors are `Dregg2.Circuit.Emit.PastaAddSubSound.{fp,fq}{Add,Sub}SoundDesc`, each
`EffectLower.lowerAir` of the source `EffectAir` `soundAddSubAir` — House Law #1's endpoint form:
there is no hand-written `VmConstraint2` list for a re-emission to drift from. This file only
RENDERS; it authors nothing.

The traces are `fp{Add,Sub}HonestRow` of the Lean-generated witness `adAsg`, repeated to a
power-of-two height. Every declared range lookup constrains its wire on EVERY row (`LookupSpec`
carries no guard), so the padding rows are copies rather than zeros.
-/
import Dregg2.Circuit.Emit.PastaAddSubSound

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.PastaAddSubSound

/-- Repeat one honest row to a power-of-two height. -/
def traceText (row : List ℤ) : String :=
  let line := String.intercalate " " (row.map toString)
  String.intercalate "\n" (List.replicate 8 line) ++ "\n"

def main (args : List String) : IO Unit :=
  match args with
  | ["fpadd"]    => IO.println (emitVmJson2 fpAddSoundDesc)
  | ["fpsub"]    => IO.println (emitVmJson2 fpSubSoundDesc)
  | ["fqadd"]    => IO.println (emitVmJson2 fqAddSoundDesc)
  | ["fqsub"]    => IO.println (emitVmJson2 fqSubSoundDesc)
  | ["addtrace"] => IO.print (traceText fpAddHonestRow)
  | ["subtrace"] => IO.print (traceText fpSubHonestRow)
  | _            => IO.eprintln "usage: EmitPastaAddSubSound.lean (fpadd|fpsub|fqadd|fqsub|addtrace|subtrace)"
