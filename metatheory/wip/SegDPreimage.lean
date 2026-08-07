import Dregg2.Circuit.Emit.KimchiStepMainFixture
open Dregg2.Circuit.Emit KimchiStepMain

def main : IO Unit := do
  let spec : SegSpec := tStep.specD
  IO.println s!"ws.length = {spec.ws.length}  masked={spec.masked}  copyFrom.isSome={spec.copyFrom.isSome}"
  for (w, i) in spec.ws.zipIdx do
    IO.println s!"{i} {w.2}"
