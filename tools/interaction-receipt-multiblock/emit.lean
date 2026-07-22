import Dregg2.Calculus.IntensionalCCCInteractionMultiBlockDescriptorIR2

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Calculus.IntensionalCCCInteractionMultiBlockDescriptorIR2

#eval IO.println (emitVmJson2 (descriptorAtDepth 25))
