/-
SCRATCH executable: emit the FELT-SOUND Pasta RCB complete-add descriptors as IR-v2 JSON, and the
honest Lean-generated trace rows.

  lake env lean --run EmitPastaCurveSound.lean pallas > ../circuit/descriptors/by-name/pasta-pallas-complete-add-sound.json
  lake env lean --run EmitPastaCurveSound.lean vesta  > ../circuit/descriptors/by-name/pasta-vesta-complete-add-sound.json
  lake env lean --run EmitPastaCurveSound.lean pallassz > ../circuit/descriptors/by-name/pasta-pallas-complete-add-sz.json
  lake env lean --run EmitPastaCurveSound.lean vestasz  > ../circuit/descriptors/by-name/pasta-vesta-complete-add-sz.json
  lake env lean --run EmitPastaCurveSound.lean pallastrace > ../circuit/tests/fixtures/pasta-pallas-complete-add-sound-trace.txt
  lake env lean --run EmitPastaCurveSound.lean vestatrace  > ../circuit/tests/fixtures/pasta-vesta-complete-add-sound-trace.txt

The descriptors are `Dregg2.Circuit.Emit.PastaCurveSound.{pallas,vesta}CompleteAddSoundDesc`, each
`EffectLower.lowerAir` of the composed source `EffectAir` — House Law #1's endpoint form. This file
only RENDERS; it authors nothing, and there is no hand-written `VmConstraint2` list anywhere in the
cone for a re-emission to drift from.

The trace is `rcbSoundRow` — the honest witness for `G + G` (the DOUBLING case, so RCB's strong
unification is what the row exercises), generated in Lean from `PastaCurveComplete.rcbTraceM` and
repeated to a power-of-two height. Every declared range lookup constrains its wire on EVERY row
(`LookupSpec` carries no guard), so the padding rows are copies rather than zeros.
-/
import Dregg2.Circuit.Emit.PastaCurveSound

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.PastaCurveSound

/-- Repeat an honest row to a power-of-two height. -/
def traceText (row : List ℤ) : String :=
  let line := String.intercalate " " (row.map toString)
  String.intercalate "\n" (List.replicate 8 line) ++ "\n"

def main (args : List String) : IO Unit :=
  match args with
  | ["pallas"]      => IO.println (emitVmJson2 pallasCompleteAddSoundDesc)
  | ["vesta"]       => IO.println (emitVmJson2 vestaCompleteAddSoundDesc)
  -- ⚑ The SZ rows. Same width, same lookups, same honest trace — only the twelve multiplies'
  -- algebra differs, so `pallastrace`/`vestatrace` serve both artifacts.
  | ["pallassz"]    => IO.println (emitVmJson2 pallasCompleteAddSzDesc)
  | ["vestasz"]     => IO.println (emitVmJson2 vestaCompleteAddSzDesc)
  | ["pallastrace"] => IO.print (traceText pallasHonestRow)
  | ["vestatrace"]  => IO.print (traceText vestaHonestRow)
  | _ => IO.eprintln "usage: EmitPastaCurveSound.lean (pallas|vesta|pallassz|vestasz|pallastrace|vestatrace)"
