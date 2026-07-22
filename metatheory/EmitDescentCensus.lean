import Dregg2.Games.DescentCensusDescriptor

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)

def main : IO Unit :=
  IO.print (emitVmJson2 Dregg2.Games.DescentCensusDescriptor.descentCensusDescriptor)
