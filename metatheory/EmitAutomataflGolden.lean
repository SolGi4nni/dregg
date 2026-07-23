import Dregg2.Circuit.Emit.AutomataflStepEmit
import Dregg2.Circuit.Emit.AutomataflNGenGolden

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)

def main : IO Unit := do
  IO.println s!"n2\t{emitVmJson2 Dregg2.Circuit.Emit.AutomataflStepEmit.automataflStepDesc}"
  IO.println s!"n11\t{emitVmJson2 Dregg2.Circuit.Emit.AutomataflNGenGolden.automataflStepDescN11}"
