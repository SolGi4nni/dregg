import Dregg2.Circuit.Emit.LightClientEthAir
import Dregg2.Circuit.Emit.LightClientTendermintAir
import Dregg2.Circuit.Emit.LightClientSolanaAir
import Dregg2.Circuit.Emit.LightClientMidnightAir
import Dregg2.Circuit.Emit.LightClientMinaAir
import Dregg2.Circuit.Emit.LightClientMinaLinkAir
open Dregg2.Circuit Dregg2.Circuit.DescriptorIR2
def lcs : List (String × EffectVmDescriptor2) :=
  [ ("eth",       Dregg2.Circuit.Emit.LightClientEthAir.ethLcVerifyDesc)
  , ("tm",        Dregg2.Circuit.Emit.LightClientTendermintAir.tmLcVerifyDesc)
  , ("solana",    Dregg2.Circuit.Emit.LightClientSolanaAir.solLcVerifyDesc)
  , ("midnight",  Dregg2.Circuit.Emit.LightClientMidnightAir.midLcVerifyDesc)
  , ("mina",      Dregg2.Circuit.Emit.LightClientMinaAir.minaLcVerifyDesc)
  , ("mina-link", Dregg2.Circuit.Emit.LightClientMinaLinkAir.minaLinkDesc) ]
def main : IO Unit := do
  for (n, d) in lcs do IO.println s!"{n}\t{emitVmJson2 d}"
