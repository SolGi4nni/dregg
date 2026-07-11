/-
# Crypto linking-chain gauntlet aggregator

Building THIS module builds the entire from-scratch PQ-spec linking chain as one — the CI-reproducible
form of the whole-tree gauntlet (`lake build Dregg2.Crypto.CryptoVerifyAll`). It imports every top-level
linking result so a single target confirms they all compose (they are otherwise outside the default
`Dregg2.lean` aggregator, deliberately: they pull the heavy KAT `native_decide` chain, which would bloat
every default build).

What this transitively verifies:
- Both NTT-correctness proofs from scratch (Mathlib ships neither): `NttFaithful` (ML-DSA complete NTT),
  `MlKemNttFaithful` (ML-KEM incomplete Kyber NTT).
- All four `=spec` directions: `VerifyCoreEqSpec` (verify, full biconditional), `SignCoreSpec` (sign),
  `DecapsCoreSpec` (decaps byte-level), `EncapsCoreSpec` (encaps byte-level).
- Seam 2 floor unification: `FloorBridge`, and the quantitative reductions `ProbCrypto`, `UcSignatureQuant`,
  `HybridThresholdQuant`, `ProtocolSoundnessQuant`.
- Seam 3 model bridge: `ModelBridge`.
- Seam 4 δ analysis: `MlKemDelta`.

See `docs/LINKING-SEAMS-PROGRESS.md` for the seam-by-seam status and the named residuals.
-/
import Dregg2.Crypto.VerifyCoreEqSpec
import Dregg2.Crypto.VerifyCoreEqSpecW
import Dregg2.Crypto.CodecRoundTrip
import Dregg2.Crypto.SignCoreSpec
import Dregg2.Crypto.DecapsCoreSpec
import Dregg2.Crypto.EncapsCoreSpec
import Dregg2.Crypto.MlKemCodecSpec
import Dregg2.Crypto.FloorBridge
import Dregg2.Crypto.MlKemDelta
import Dregg2.Crypto.ModelBridge
import Dregg2.Crypto.UcSignatureQuant
import Dregg2.Crypto.HybridThresholdQuant
import Dregg2.Crypto.ProtocolSoundnessQuant
