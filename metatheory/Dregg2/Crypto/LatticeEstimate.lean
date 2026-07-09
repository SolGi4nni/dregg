/-
# `Dregg2.Crypto.LatticeEstimate` — the deployed parameters, the lattice-hardness interface, and the
LOOSE (forking/semiclassical) CONTRAST bit-counts (LEAF).

This file carries the ONE non-proof input of the whole crypto tree — the `LatticeEstimate` bag of NUMBERS
(MSIS/MLWE bit-security at the deployed ML-DSA-65 / ML-KEM-768 parameters) — plus the deployed and degraded
instances and the LOOSE contrast bit-counts `sigBitsR` / `o2hBitsR` (the forking / semiclassical floors the
tight reductions REPLACE, kept as the documented record of the campaign's gain).

It is a **leaf** (it imports only the `advOf` calculus): so BOTH the tight reduction files
(`LossyIdentification` needs `sigBitsR` + `deployedEstimate` for `tight_beats_forking`; `DoubleSidedO2H`
needs `o2hBitsR` + `deployedEstimate` + `degradedEstimate` for `deployed_tightness_gain`) AND the
system-bound file (`ParameterSecurity`) can depend on it without a cycle. Declarations keep the namespace
`Dregg2.Crypto.ParameterSecurity`, so every existing `LatticeEstimate` / `deployedEstimate` / `sigBitsR`
reference resolves unchanged.

**No named-carrier laundering.** `LatticeEstimate` is a `structure` of `ℕ`s — NOT a `def …Hard`, NOT a
`Prop`, never used as a hardness hypothesis. It is read ONLY by the downstream arithmetic. This is the single
place the tree touches the empirical world.
-/
import Dregg2.Crypto.AdvCalculus

namespace Dregg2.Crypto.ParameterSecurity

/-! ## THE DEPLOYED PARAMETERS. -/

/-- ML-DSA parameter record (for citation of the deployed instance). -/
structure MlDsaParams where
  k : ℕ
  l : ℕ
  eta : ℕ
  q : ℕ
  n : ℕ
deriving Repr, DecidableEq

/-- ML-KEM parameter record (for citation of the deployed instance). -/
structure MlKemParams where
  k : ℕ
  eta1 : ℕ
  eta2 : ℕ
  q : ℕ
  n : ℕ
deriving Repr, DecidableEq

/-- **ML-DSA-65** (FIPS 204, NIST security category 3): `(k,l,η,q,n) = (6,5,4,8380417,256)`. -/
def mlDsa65 : MlDsaParams := ⟨6, 5, 4, 8380417, 256⟩

/-- **ML-KEM-768** (FIPS 203, NIST security category 3): `(k,η₁,η₂,q,n) = (3,2,2,3329,256)`. -/
def mlKem768 : MlKemParams := ⟨3, 2, 2, 3329, 256⟩

/-- **`LatticeEstimate` — THE ONLY NON-PROOF INPUT IN THE ENTIRE TREE.**

The parameter-level theorem bottoms out at the concrete hardness of MSIS/MLWE at the deployed lattice
parameters. That hardness is NOT provable in Lean (it is the lattice FLOOR); its bit-security is an
EMPIRICAL number from the Lattice Estimator [Albrecht–Player–Scott] and the NIST parameter rationale
[FIPS 203/204]. This structure carries those numbers — and ONLY numbers.

It is deliberately a bag of `ℕ`s, **NOT** a `def …Hard`, **NOT** a `Prop`, **NOT** used as a hardness
hypothesis anywhere below: the fields are read ONLY by arithmetic (`sysSecurityBits`). This is the single
place the tree touches the empirical world; everything downstream is proof. -/
structure LatticeEstimate where
  /-- **EMPIRICAL (Lattice Estimator / NIST).** Bit-security of Module-SIS at the ML-DSA-65 parameters — the
  quantum core-SVP cost of finding a short vector, i.e. `−log₂(Adv^MSIS)`. A NUMBER, not a hypothesis. Feeds
  the CONTRAST forking bound `sigBitsR`; the tight lossy-ID reduction uses `mlweBits` instead. -/
  msisBits : ℕ
  /-- **EMPIRICAL (Lattice Estimator / NIST).** Bit-security of Module-LWE at the ML-KEM-768 parameters —
  `−log₂(Adv^MLWE)`. A NUMBER, not a hypothesis. With the lossy-ID reduction this is the binding lattice
  floor for BOTH the KEM and the signature (decision-MLWE). -/
  mlweBits : ℕ
  /-- Message / seed min-entropy `H∞(m*)` feeding the (CONTRAST) O2H guessing term. Also the lossy-soundness
  parameter `α` of the tight signature (the response-entropy gap, statistical, `≫ mlweBits`). A SPEC
  constant (ML-KEM encapsulates a 256-bit seed), not a lattice estimate. -/
  msgEntropyBits : ℕ
  /-- FO correctness margin: `−log₂(δ)` for the decryption-failure rate `δ` (the `(q+1)·δ` term of the tight
  HHM22 FO bound). A SPEC constant computed from the noise distribution. -/
  foCorrectnessBits : ℕ
  /-- The deployed ML-DSA parameters these `msisBits` were estimated at (for citation). -/
  mldsa : MlDsaParams
  /-- The deployed ML-KEM parameters these `mlweBits` were estimated at (for citation). -/
  mlkem : MlKemParams

/-- **THE DEPLOYED ESTIMATE.** ML-DSA-65 / ML-KEM-768, NIST security category 3. The empirical inputs:
`msisBits = 192` (category-3 MSIS; only feeds the CONTRAST forking bound), `mlweBits = 181` (Kyber768 MLWE —
the binding lattice floor for the tight signature AND KEM), `msgEntropyBits = 256` (encapsulated seed /
lossy-soundness α), `foCorrectnessBits = 174` (ML-KEM-768 `δ ≈ 2^(−174)`). -/
def deployedEstimate : LatticeEstimate where
  msisBits := 192
  mlweBits := 181
  msgEntropyBits := 256
  foCorrectnessBits := 174
  mldsa := mlDsa65
  mlkem := mlKem768

/-- **A DEGRADED ESTIMATE — the tooth.** Halve the lattice-hardness bits (`msisBits 192→96`,
`mlweBits 181→90`), everything else identical. Models the Lattice Estimator delivering a WEAKER hardness
number (better cryptanalysis). Since the TIGHT bounds track `mlweBits`, halving it moves λ. -/
def degradedEstimate : LatticeEstimate :=
  { deployedEstimate with msisBits := 96, mlweBits := 90 }

/-! ## THE LOOSE (forking/semiclassical) CONTRAST bit-counts.

Kept as the documented record of what the tight reductions bought. The system bound composes the TIGHT
floors; these are the loose ones the campaign REPLACED. Pure arithmetic in the estimate's numbers. -/

/-- **(CONTRAST)** The loose signature bits (post-forking): `(msisBits − log₂q)/2`. -/
noncomputable def sigBitsR (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  ((E.msisBits : ℝ) - (log2q : ℝ)) / 2

/-- **(CONTRAST)** The loose O2H reprogramming term's bits: `msgEntropyBits/2 − log₂q − 1`. -/
noncomputable def o2hBitsR (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  (E.msgEntropyBits : ℝ) / 2 - (log2q : ℝ) - 1

end Dregg2.Crypto.ParameterSecurity
