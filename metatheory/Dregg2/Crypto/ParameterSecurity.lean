/-
# `Dregg2.Crypto.ParameterSecurity` — THE PARAMETER-LEVEL SECURITY THEOREM.

The rest of the crypto tree proves the QUALITATIVE reduction tree: the hybrid signature is unforgeable if
`DL ∨ MSIS` holds (`HybridCombiner`), the KEM is IND-CCA in the QROM up to the FO + O2H terms (`FoQrom`,
`FoBookkeeping`), multi-session UC costs a session-count union bound (`UcSignature`), adaptive corruption
costs ZERO (`AdaptiveTSUF`), and the combiner is TIGHT (`HybridCombiner.hybrid_euf_cma_if_either`). Each is
a `Prop`-level statement or a symbolic advantage term. This module turns that qualitative tree into a
DEPLOYABLE NUMBER: at the deployed ML-DSA-65 / ML-KEM-768 parameters, against any `q`-query quantum
adversary, the whole system's advantage is `≤ 2^(−λ)` for a λ we COMPUTE.

## THE MODULE DAG — λ is a CONSEQUENCE of the tight proofs, not hand-matched arithmetic.

The `advOf` calculus and the `LatticeEstimate` interface were LEAVES-out so that the DAG can be INVERTED:

  * **`Dregg2.Crypto.AdvCalculus`** (leaf) — the `advOf b = 2^(−b)` advantage-in-bits calculus and ALL its
    laws (`advOf_sqrt`, `advOf_add_le`, `advOf_add3_le`, `advOf_antitone`, `natpow_mul_advOf`, …).
  * **`Dregg2.Crypto.LatticeEstimate`** (leaf) — the `LatticeEstimate` bag of numbers, the deployed/degraded
    instances, and the LOOSE contrast bit-counts `sigBitsR` / `o2hBitsR`.
  * **`Dregg2.Crypto.LossyIdentification`** (KLS18/AFLT12 lossy-identification EUF-CMA) and
    **`Dregg2.Crypto.DoubleSidedO2H`** (BHHHP19 double-sided O2H + HHM22 FO) — the TIGHT reductions. They now
    import the two LEAVES above (NOT this file), so THIS file can import THEM.

Because this file **imports** `LossyIdentification` and `DoubleSidedO2H`, the system bound below is not a
re-declared numeric shape that merely *matches* the tight theorems — it **cites them directly**: the
signature leg is `LossyIdentification.sigTightAdv_le` and the KEM leg is `DoubleSidedO2H.kemTightAdv_le`, and
the computed λ is built from `LossyIdentification.sigBitsTightN` / `DoubleSidedO2H.kemBitsTightN`. λ = 149 is
a consequence, through Lean's import graph, of the theorems those two files prove.

  * **`sigBitsTight = min mlweBits (min (α − log₂q) simBits) − 2`** (`≈ mlweBits − O(1)`, decision-MLWE at
    coefficient 1), replacing the loose `sigBitsR = (msisBits − log₂q)/2`. At the deployed estimate: **179**
    vs the forking **86** (`LossyIdentification.tight_beats_forking`).
  * **`kemBitsTight = min mlweBits (foCorrectnessBits − log₂q) − 2`**, replacing the loose
    `o2hBitsR = msgEntropyBits/2 − log₂q − 1`. At the deployed estimate: **152** vs the semiclassical **107**
    (`DoubleSidedO2H.deployed_tightness_gain`).

The OLD `sigBitsR` / `o2hBitsR` / `kem3R` / `sigForkAdv` / `kemQromAdv` are KEPT below as the documented
CONTRAST (the record of what the tight reductions bought) — but the SYSTEM bound composes the tight ones.

## The accounting (§-by-§)

  **§1 — `advOf` — the advantage-in-bits calculus.** Now in the `AdvCalculus` leaf; `advOf b = 2^(−b)`. The
  whole composition is arithmetic in this one function.

  **§2 — THE ADVANTAGE TWINS.** §2a: the loose (forking/semiclassical) twins `sigForkAdv`/`kemQromAdv`
  (CONTRAST). §2b: the TIGHT twins, SPECIALISED here from the CITED `LossyIdentification`/`DoubleSidedO2H`
  theorems (no re-declaration — `sigTightAdv_le`/`kemTightAdv_le` are `:= LossyIdentification.sigTightAdv_le
  …` / `:= DoubleSidedO2H.kemTightAdv_le …`).

  **§3 — THE COMPOSITION.** `sysAdvExpr E q log2q sessions consensus` composes the TIGHT twins by the actual
  reduction structure, and `system_advantage_bound` proves it `≤ advOf (lambdaR …)` — every step an `advOf`
  law, no new assumption.

  **§4 — THE LATTICE-HARDNESS INTERFACE.** In the `LatticeEstimate` leaf. The bit-security of MSIS/MLWE at
  the deployed parameters as LABELED NUMERIC INPUTS. **This is the ONLY non-proof input in the entire tree.**

  **§5 — THE THEOREM.** `system_security_bits`: given a `LatticeEstimate` in the deployable regime, for any
  `q ≤ 2^log2q` quantum adversary, `sysAdvExpr ≤ advOf (sysSecurityBits …)` — i.e. `≤ 2^(−λ)` for the
  COMPUTED λ. `#guard` computes λ at the deployed regime; `system_security_at_least_120` HOLDS the bar.

## No named-carrier laundering.

No `def …Hard` is introduced. The `LatticeEstimate` is a bag of NUMBERS, never a `Prop`, never assumed.
Every bound is `advOf` arithmetic proved from Mathlib's `rpow`/`sqrt` API — theorems, never `axiom`s. The
tight reductions are not cited-by-shape but cited-by-import. The only residual is the lattice floor
(`MLWESearchHard` and its decisional twin `DecisionMLWEHard`, plus `MSISHard`), quantified by the ONE labeled
estimate, exactly as the discipline permits.
-/
import Dregg2.Crypto.AdvCalculus
import Dregg2.Crypto.LatticeEstimate
import Dregg2.Crypto.LossyIdentification
import Dregg2.Crypto.DoubleSidedO2H
import Dregg2.Crypto.ConcreteSecurity
import Dregg2.Crypto.Lattice
import Dregg2.Crypto.HermineTSUF
import Dregg2.Crypto.FoQrom
import Dregg2.Crypto.FoBookkeeping
import Dregg2.Crypto.HybridCombiner
import Dregg2.Crypto.UcSignature
import Dregg2.Crypto.AdaptiveTSUF
import Dregg2.Tactics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open Dregg2.Crypto.ConcreteSecurity

namespace Dregg2.Crypto.ParameterSecurity

/-! ## §1 — `advOf` — the advantage-in-bits calculus.

Lives in the `Dregg2.Crypto.AdvCalculus` leaf (namespace `Dregg2.Crypto.ParameterSecurity`, so `advOf`,
`advOf_add3_le`, … resolve unqualified). §4 — the deployed parameters and the `LatticeEstimate` interface —
lives in the `Dregg2.Crypto.LatticeEstimate` leaf. Both are imported above. -/

/-! ## §2 — THE ADVANTAGE TWINS. §2a: the LOOSE (forking/semiclassical) twins, KEPT as CONTRAST.

(`sigBitsR` / `o2hBitsR`, the loose bit-counts, live in the `LatticeEstimate` leaf so the tight files can
cite them in their `tight_beats_forking` / `deployed_tightness_gain` contrasts.) -/

/-- **(CONTRAST) `sigForkAdv E q` — the loose forking forgery advantage.** `√(q · advOf msisBits)`: the
FORKING inversion of `HermineTSUF.forking_probability_bound`. The tight `sigTightAdv` (§2b) REPLACES this in
the system bound; this is retained as the record of the forking square-root the campaign removed. -/
noncomputable def sigForkAdv (E : LatticeEstimate) (q : ℕ) : ℝ :=
  Real.sqrt ((q : ℝ) * advOf E.msisBits)

/-- **(CONTRAST) `kemQromAdv E q` — the loose semiclassical-O2H IND-CCA advantage.**
`2·√(q·(q·b)) + advOf mlweBits + advOf foCorrectnessBits`. The tight `kemTightAdv` (§2b) REPLACES this. -/
noncomputable def kemQromAdv (E : LatticeEstimate) (q : ℕ) : ℝ :=
  2 * Real.sqrt ((q : ℝ) * ((q : ℝ) * advOf E.msgEntropyBits))
    + advOf E.mlweBits + advOf E.foCorrectnessBits

/-- **(CONTRAST)** The loose KEM bits: the MIN of the O2H term, the MLWE (CPA) term, and the correctness. -/
noncomputable def kem3R (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  min (o2hBitsR E log2q) (min (E.mlweBits : ℝ) (E.foCorrectnessBits : ℝ))

/-- **(CONTRAST) `sigForkAdv` bit bound.** A `q ≤ 2^log2q` adversary's forging advantage is
`≤ advOf (sigBitsR)` — the forking square-root loss made numeric. -/
theorem sigForkAdv_le (E : LatticeEstimate) {q log2q : ℕ} (hq : q ≤ 2 ^ log2q) :
    sigForkAdv E q ≤ advOf (sigBitsR E log2q) := by
  unfold sigForkAdv sigBitsR
  have hqr : (q : ℝ) ≤ (2:ℝ) ^ log2q := by exact_mod_cast hq
  have h1 : (q : ℝ) * advOf E.msisBits ≤ (2:ℝ) ^ log2q * advOf E.msisBits :=
    mul_le_mul_of_nonneg_right hqr (le_of_lt (advOf_pos _))
  calc Real.sqrt ((q : ℝ) * advOf E.msisBits)
      ≤ Real.sqrt ((2:ℝ) ^ log2q * advOf E.msisBits) := Real.sqrt_le_sqrt h1
    _ = advOf (((E.msisBits : ℝ) - (log2q : ℝ)) / 2) := by rw [natpow_mul_advOf, advOf_sqrt]

/-- **(CONTRAST)** The O2H term at the query budget. -/
theorem o2hTerm_bound (E : LatticeEstimate) (log2q : ℕ) :
    2 * Real.sqrt ((2:ℝ) ^ log2q * ((2:ℝ) ^ log2q * advOf E.msgEntropyBits))
      = advOf (o2hBitsR E log2q) := by
  unfold o2hBitsR
  rw [natpow_mul_advOf, natpow_mul_advOf, advOf_sqrt, two_mul_advOf]
  congr 1; ring

/-- **(CONTRAST) `kemQromAdv` bit bound.** A `q ≤ 2^log2q` quantum adversary's IND-CCA advantage is
`≤ advOf (kem3R − 2)`. -/
theorem kemQromAdv_le (E : LatticeEstimate) {q log2q : ℕ} (hq : q ≤ 2 ^ log2q) :
    kemQromAdv E q ≤ advOf (kem3R E log2q - 2) := by
  unfold kemQromAdv kem3R
  have hqr : (q : ℝ) ≤ (2:ℝ) ^ log2q := by exact_mod_cast hq
  have hpos : (0:ℝ) ≤ advOf E.msgEntropyBits := le_of_lt (advOf_pos _)
  have hle : (q : ℝ) * ((q : ℝ) * advOf E.msgEntropyBits)
      ≤ (2:ℝ) ^ log2q * ((2:ℝ) ^ log2q * advOf E.msgEntropyBits) := by
    have hinner : (q : ℝ) * advOf E.msgEntropyBits ≤ (2:ℝ) ^ log2q * advOf E.msgEntropyBits :=
      mul_le_mul_of_nonneg_right hqr hpos
    exact mul_le_mul hqr hinner (by positivity) (by positivity)
  have ho2h : 2 * Real.sqrt ((q : ℝ) * ((q : ℝ) * advOf E.msgEntropyBits))
      ≤ advOf (o2hBitsR E log2q) := by
    calc 2 * Real.sqrt ((q : ℝ) * ((q : ℝ) * advOf E.msgEntropyBits))
        ≤ 2 * Real.sqrt ((2:ℝ) ^ log2q * ((2:ℝ) ^ log2q * advOf E.msgEntropyBits)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (by norm_num)
      _ = advOf (o2hBitsR E log2q) := o2hTerm_bound E log2q
  have h3 := advOf_add3_le (o2hBitsR E log2q) (E.mlweBits : ℝ) (E.foCorrectnessBits : ℝ)
  calc 2 * Real.sqrt ((q : ℝ) * ((q : ℝ) * advOf E.msgEntropyBits))
          + advOf E.mlweBits + advOf E.foCorrectnessBits
      ≤ advOf (o2hBitsR E log2q) + advOf E.mlweBits + advOf E.foCorrectnessBits := by linarith
    _ ≤ advOf (min (o2hBitsR E log2q) (min (E.mlweBits : ℝ) (E.foCorrectnessBits : ℝ)) - 2) := h3

/-! ## §2b — THE TIGHT ADVANTAGE TWINS — CITED from the LANDED reductions, not re-declared.

The tight signature terms are `LossyIdentification.sigTightAdv/sigBitsTight` specialised at the
`LatticeEstimate` (α = `msgEntropyBits`, simBits = `mlweBits`); the tight KEM terms are
`DoubleSidedO2H.kemTightAdv/kemBitsTight` (already over a `LatticeEstimate`). The `_le` lemmas below are
PROOF-TERM citations of the downstream theorems — `sigTightAdv_le := LossyIdentification.sigTightAdv_le …`,
`kemTightAdv_le := DoubleSidedO2H.kemTightAdv_le …` — so the system bound depends on those proofs through the
import graph, not on hand-matched arithmetic. -/

/-- **`sigTightAdv E log2q`** — the TIGHT EUF-CMA advantage, `LossyIdentification.sigTightAdv` specialised at
the estimate (α = `msgEntropyBits`, simBits = `mlweBits`): `advOf mlweBits + advOf (msgEntropyBits − log₂q) +
advOf mlweBits`. REPLACES the forking `sigForkAdv`. -/
noncomputable def sigTightAdv (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  LossyIdentification.sigTightAdv E.mlweBits E.msgEntropyBits E.mlweBits log2q

/-- **`sigBitsTight E log2q`** — the TIGHT signature bits, `LossyIdentification.sigBitsTight` at the estimate:
`min mlweBits (min (msgEntropyBits − log₂q) mlweBits) − 2 ≈ mlweBits − O(1)`. REPLACES `sigBitsR`. -/
noncomputable def sigBitsTight (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  LossyIdentification.sigBitsTight E.mlweBits E.msgEntropyBits E.mlweBits log2q

/-- **`sigTightAdv ≤ advOf sigBitsTight`** — a PROOF-TERM CITATION of `LossyIdentification.sigTightAdv_le`
(the lossy-ID EUF-CMA tight bound), specialised at the estimate. -/
theorem sigTightAdv_le (E : LatticeEstimate) (log2q : ℕ) :
    sigTightAdv E log2q ≤ advOf (sigBitsTight E log2q) :=
  LossyIdentification.sigTightAdv_le E.mlweBits E.msgEntropyBits E.mlweBits log2q

/-- **`kemTightAdv E q`** — the TIGHT ML-KEM IND-CCA advantage, `DoubleSidedO2H.kemTightAdv` at the estimate:
`2·advOf mlweBits + (q+1)·advOf foCorrectnessBits`. REPLACES the semiclassical `kemQromAdv`. -/
noncomputable def kemTightAdv (E : LatticeEstimate) (q : ℕ) : ℝ :=
  DoubleSidedO2H.kemTightAdv E q

/-- **`kemBitsTight E log2q`** — the TIGHT KEM bits, `DoubleSidedO2H.kemBitsTight` at the estimate:
`min mlweBits (foCorrectnessBits − log₂q) − 2`. REPLACES `o2hBitsR` / `kem3R`. -/
noncomputable def kemBitsTight (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  DoubleSidedO2H.kemBitsTight E log2q

/-- **`kemTightAdv_le` — the tight KEM bit bound** — a PROOF-TERM CITATION of
`DoubleSidedO2H.kemTightAdv_le` (the double-sided-O2H FO-KEM tight bound). -/
theorem kemTightAdv_le (E : LatticeEstimate) {q log2q : ℕ} (hq : q ≤ 2 ^ log2q) :
    kemTightAdv E q ≤ advOf (kemBitsTight E log2q) :=
  DoubleSidedO2H.kemTightAdv_le E hq

/-! ## §3 — THE COMPOSITION (over the TIGHT twins). -/

/-- **`sysAdvExpr E q log2q sessions consensus` — THE END-TO-END SYSTEM ADVANTAGE.** A `2^consensus`-turn
consensus run, each turn union-bounding the `2^sessions`-session UC hybrid signature
(`UcSignature.multiUcAdv_le_sum`) and the KEM — now over the TIGHT twins `sigTightAdv`/`kemTightAdv`. -/
noncomputable def sysAdvExpr (E : LatticeEstimate) (q log2q sessions consensus : ℕ) : ℝ :=
  (2:ℝ) ^ consensus * ((2:ℝ) ^ sessions * sigTightAdv E log2q + kemTightAdv E q)

/-- **`lambdaR` — the derived security bits (real).** `min (sigBitsTight − sessions) kemBitsTight − 1 −
consensus`: the smaller of the TIGHT signature and KEM floors, minus the session, union, and consensus
bit-costs. -/
noncomputable def lambdaR (E : LatticeEstimate) (log2q sessions consensus : ℕ) : ℝ :=
  min (sigBitsTight E log2q - (sessions : ℝ)) (kemBitsTight E log2q) - 1 - (consensus : ℝ)

/-- **THE END-TO-END ADVANTAGE BOUND.** For any `q ≤ 2^log2q` quantum adversary,
`sysAdvExpr E q log2q sessions consensus ≤ advOf (lambdaR E log2q sessions consensus)`. Every step is an
`advOf` law composing the TIGHT twins (whose `_le` lemmas cite `LossyIdentification`/`DoubleSidedO2H`) —
lossy-ID decision-MLWE (coefficient 1), double-sided O2H (no `√`), session/consensus union — NO new
assumption. -/
theorem system_advantage_bound (E : LatticeEstimate) {q log2q : ℕ} (hq : q ≤ 2 ^ log2q)
    (sessions consensus : ℕ) :
    sysAdvExpr E q log2q sessions consensus ≤ advOf (lambdaR E log2q sessions consensus) := by
  unfold sysAdvExpr lambdaR
  have hsig : (2:ℝ) ^ sessions * sigTightAdv E log2q ≤ advOf (sigBitsTight E log2q - (sessions : ℝ)) := by
    calc (2:ℝ) ^ sessions * sigTightAdv E log2q
        ≤ (2:ℝ) ^ sessions * advOf (sigBitsTight E log2q) :=
          mul_le_mul_of_nonneg_left (sigTightAdv_le E log2q) (by positivity)
      _ = advOf (sigBitsTight E log2q - (sessions : ℝ)) := natpow_mul_advOf _ _
  have hkem := kemTightAdv_le E (log2q := log2q) hq
  have hsum : (2:ℝ) ^ sessions * sigTightAdv E log2q + kemTightAdv E q
      ≤ advOf (min (sigBitsTight E log2q - (sessions : ℝ)) (kemBitsTight E log2q) - 1) := by
    calc (2:ℝ) ^ sessions * sigTightAdv E log2q + kemTightAdv E q
        ≤ advOf (sigBitsTight E log2q - (sessions : ℝ)) + advOf (kemBitsTight E log2q) := by linarith
      _ ≤ advOf (min (sigBitsTight E log2q - (sessions : ℝ)) (kemBitsTight E log2q) - 1) := advOf_add_le _ _
  calc (2:ℝ) ^ consensus * ((2:ℝ) ^ sessions * sigTightAdv E log2q + kemTightAdv E q)
      ≤ (2:ℝ) ^ consensus * advOf (min (sigBitsTight E log2q - (sessions : ℝ)) (kemBitsTight E log2q) - 1) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = advOf (min (sigBitsTight E log2q - (sessions : ℝ)) (kemBitsTight E log2q) - 1 - (consensus : ℝ)) := by
        rw [natpow_mul_advOf]

/-! ## §5 — THE THEOREM. The computed λ and the deployable-regime restatement. -/

/-- **`sigBitsTightN`** — ℕ mirror, `LossyIdentification.sigBitsTightN` at the estimate (α = msgEntropy,
simBits = mlwe). No division ⟹ exact under the deployable regime. -/
def sigBitsTightN (E : LatticeEstimate) (log2q : ℕ) : ℕ :=
  LossyIdentification.sigBitsTightN E.mlweBits E.msgEntropyBits E.mlweBits log2q

/-- **`kemBitsTightN`** — ℕ mirror, `DoubleSidedO2H.kemBitsTightN` at the estimate. -/
def kemBitsTightN (E : LatticeEstimate) (log2q : ℕ) : ℕ :=
  DoubleSidedO2H.kemBitsTightN E log2q

/-- **`sysSecurityBits E log2q sessions consensus` — THE COMPUTED SECURITY PARAMETER λ (in bits).**
`min (sigBitsTightN − sessions) kemBitsTightN − 1 − consensus`, all `ℕ`. Instantiating a `LatticeEstimate`
and the adversary budget makes this a concrete number — the deployable security claim. -/
def sysSecurityBits (E : LatticeEstimate) (log2q sessions consensus : ℕ) : ℕ :=
  min (sigBitsTightN E log2q - sessions) (kemBitsTightN E log2q) - 1 - consensus

/-- **`sysSecurityBitsLoose` — THE OLD (loose, forking/semiclassical) λ, KEPT as the CONTRAST.** The forking
`(msisBits − log₂q)/2` signature floor and the semiclassical `msgEntropyBits/2` O2H floor. At the deployed
regime this is **79**; `lambda_tight_gt_loose` proves the tight λ strictly exceeds it. -/
def sysSecurityBitsLoose (E : LatticeEstimate) (log2q sessions consensus : ℕ) : ℕ :=
  min ((E.msisBits - log2q) / 2 - sessions)
      (min (E.msgEntropyBits / 2 - log2q - 1) (min E.mlweBits E.foCorrectnessBits) - 2)
    - 1 - consensus

/-- **`Deployable` — the meaningful-parameter regime.** The estimate bits exceed the composition losses at
every stage (no bit-count underflows). Decidable, so `by decide` discharges it at any concrete instance.
Outside this regime the bound is vacuous (the advantage can exceed `1`); inside it, it is the deployable
claim. -/
def Deployable (E : LatticeEstimate) (log2q sessions consensus : ℕ) : Prop :=
  log2q ≤ E.msgEntropyBits ∧
  log2q ≤ E.foCorrectnessBits ∧
  2 ≤ min E.mlweBits (min (E.msgEntropyBits - log2q) E.mlweBits) ∧
  2 ≤ min E.mlweBits (E.foCorrectnessBits - log2q) ∧
  sessions ≤ sigBitsTightN E log2q ∧
  1 + consensus ≤ min (sigBitsTightN E log2q - sessions) (kemBitsTightN E log2q)

instance (E : LatticeEstimate) (log2q sessions consensus : ℕ) :
    Decidable (Deployable E log2q sessions consensus) := by unfold Deployable; infer_instance

/-- The computed `ℕ` λ equals the real derived bits under the deployable regime (the tight bounds carry no
division, so the `ℕ` mirror casts EXACTLY), hence `↑sysSecurityBits ≤ lambdaR`. -/
theorem sysSecurityBits_le_lambdaR (E : LatticeEstimate) {log2q sessions consensus : ℕ}
    (hdep : Deployable E log2q sessions consensus) :
    (sysSecurityBits E log2q sessions consensus : ℝ) ≤ lambdaR E log2q sessions consensus := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hdep
  have hsigN : (sigBitsTightN E log2q : ℝ) = sigBitsTight E log2q := by
    unfold sigBitsTightN sigBitsTight LossyIdentification.sigBitsTightN LossyIdentification.sigBitsTight
    rw [Nat.cast_sub h3, Nat.cast_min, Nat.cast_min, Nat.cast_sub h1]
    norm_num
  have hkemN : (kemBitsTightN E log2q : ℝ) = kemBitsTight E log2q := by
    unfold kemBitsTightN kemBitsTight DoubleSidedO2H.kemBitsTightN DoubleSidedO2H.kemBitsTight
    rw [Nat.cast_sub h4, Nat.cast_min, Nat.cast_sub h2]
    norm_num
  have hmm : ((min (sigBitsTightN E log2q - sessions) (kemBitsTightN E log2q) : ℕ) : ℝ)
      = min (sigBitsTight E log2q - (sessions : ℝ)) (kemBitsTight E log2q) := by
    rw [Nat.cast_min, Nat.cast_sub h5, hsigN, hkemN]
  have hEq : (sysSecurityBits E log2q sessions consensus : ℝ) = lambdaR E log2q sessions consensus := by
    unfold sysSecurityBits lambdaR
    rw [Nat.cast_sub (show consensus ≤ min (sigBitsTightN E log2q - sessions) (kemBitsTightN E log2q) - 1
          by omega),
        Nat.cast_sub (show 1 ≤ min (sigBitsTightN E log2q - sessions) (kemBitsTightN E log2q) by omega),
        Nat.cast_one, hmm]
  exact le_of_eq hEq

/-- **`system_security_bits` — THE PARAMETER-LEVEL SECURITY THEOREM.**

Given a `LatticeEstimate` in the deployable regime, for ANY `q`-query quantum adversary (`q ≤ 2^log2q`),
the entire system's advantage is bounded:

  `sysAdvExpr E q log2q sessions consensus ≤ 2^(−λ)`,  where λ = `sysSecurityBits E log2q sessions consensus`.

Instantiating the estimate and the budget yields a CONCRETE λ (see the `#guard`s below). Every reduction is
cited (`LossyIdentification.sigTightAdv_le`, `DoubleSidedO2H.kemTightAdv_le` — through the import graph) and
proved; the ONLY empirical input is the `LatticeEstimate`'s `mlweBits`/`foCorrectnessBits`. -/
theorem system_security_bits (E : LatticeEstimate) {q log2q : ℕ} (hq : q ≤ 2 ^ log2q)
    (sessions consensus : ℕ) (hdep : Deployable E log2q sessions consensus) :
    sysAdvExpr E q log2q sessions consensus ≤ advOf ((sysSecurityBits E log2q sessions consensus : ℕ) : ℝ) := by
  refine (system_advantage_bound E hq sessions consensus).trans ?_
  exact advOf_antitone (sysSecurityBits_le_lambdaR E hdep)

/-! ## §6 — INSTANTIATION AT THE NIST-CLAIMED ESTIMATES + THE LOAD-BEARING TEETH.

(`deployedEstimate` / `degradedEstimate` live in the `LatticeEstimate` leaf, imported above.) -/

/-- **λ = 149.** At the DEPLOYED estimate a `2^20`-query, `2^4`-session, `2^2`-turn quantum adversary faces
**149 bits** of security. The composition: `sigBitsTight = min 181 (min 236 181) − 2 = 179`, minus
`sessions = 4` ⟹ `175`; `kemBitsTight = min 181 (174−20) − 2 = 152`; `min(175, 152) = 152`; minus the
`1`-bit sig/KEM union and `consensus = 2` ⟹ `152 − 1 − 2 = 149`. The binding term is the tight KEM floor
`kemBitsTight = 152` (the correctness margin `174 − log₂q = 154` under the MLWE floor `181`). -/
example : sysSecurityBits deployedEstimate 20 4 2 = 149 := by decide

#eval sysSecurityBits deployedEstimate 20 4 2   -- 149
#guard sysSecurityBits deployedEstimate 20 4 2 = 149

/-- The deployed estimate is in the deployable regime at these parameters, so `system_security_bits` fires:
the system advantage is `≤ 2^(−149)`. -/
example : Deployable deployedEstimate 20 4 2 := by decide

/-- **HOLD THE BAR — λ ≥ 120.** `120 ≤ sysSecurityBits deployedEstimate 20 4 2 = 149`, discharged by
`decide`. The tight reductions clear ember's `λ ≥ 120` bar with 29 bits of margin. -/
theorem system_security_at_least_120 : 120 ≤ sysSecurityBits deployedEstimate 20 4 2 := by decide

-- λ at a stress budget (`2^40` queries, `2^20` sessions, `2^10` turns): still **121 bits** — even here the
-- tight composition CLEARS the 120-bit bar (the loose forking bound gave only 45 at this budget).
#eval sysSecurityBits deployedEstimate 40 20 10   -- 121
#guard sysSecurityBits deployedEstimate 40 20 10 = 121
example : Deployable deployedEstimate 40 20 10 := by decide
example : 120 ≤ sysSecurityBits deployedEstimate 40 20 10 := by decide

-- **THE LOAD-BEARING TOOTH.** Halving the lattice-hardness bits STRICTLY drops the security parameter
-- (149 → 81 at the same budget). The `LatticeEstimate` is load-bearing — the whole claim moves with it, and
-- because the TIGHT signature/KEM floors track `mlweBits`, halving `mlweBits` (181→90) directly lowers λ.
#eval sysSecurityBits degradedEstimate 20 4 2   -- 81
#guard sysSecurityBits degradedEstimate 20 4 2 = 81

example : sysSecurityBits degradedEstimate 20 4 2 < sysSecurityBits deployedEstimate 20 4 2 := by decide

/-- **THE CAMPAIGN'S GAIN — a theorem.** The TIGHT λ strictly exceeds the OLD (loose, forking/semiclassical)
λ at the deployed regime: `sysSecurityBitsLoose = 79 < 149 = sysSecurityBits` — a **70-bit** end-to-end gain,
the composed effect of the lossy-ID (86→179 sig) and double-sided-O2H (107→152 KEM) tight reductions. -/
theorem lambda_tight_gt_loose :
    sysSecurityBitsLoose deployedEstimate 20 4 2 < sysSecurityBits deployedEstimate 20 4 2 := by decide

#guard sysSecurityBitsLoose deployedEstimate 20 4 2 = 79

/-- **THE VIOLATING (out-of-regime) INSTANCE.** If the query budget MEETS the correctness-margin bits
(`log2q = foCorrectnessBits = 174`), the KEM floor collapses: `foCorrectnessBits − log2q = 0`, so
`kemBitsTight = min 181 0 − 2 = 0`, λ bottoms out at `0` and `advOf 0 = 1` — a vacuous bound. So `Deployable`
is genuinely restrictive, and the estimate must EXCEED the losses for a real claim. -/
example : sysSecurityBits deployedEstimate 174 4 2 = 0 := by decide
example : ¬ Deployable deployedEstimate 174 4 2 := by decide

/-- The λ arithmetic is exactly `2^(−λ)`: at the deployed estimate the bound reads
`sysAdvExpr ≤ 1 / 2^149`. -/
example : advOf ((sysSecurityBits deployedEstimate 20 4 2 : ℕ) : ℝ) = 1 / (2:ℝ) ^ 149 := by
  rw [show sysSecurityBits deployedEstimate 20 4 2 = 149 from by decide, advOf_natCast]

#assert_all_clean [
  advOf_pos,
  advOf_mul,
  advOf_sqrt,
  advOf_antitone,
  advOf_add_le,
  advOf_add3_le,
  negl_advOf,
  sigForkAdv_le,
  o2hTerm_bound,
  kemQromAdv_le,
  sigTightAdv_le,
  kemTightAdv_le,
  system_advantage_bound,
  sysSecurityBits_le_lambdaR,
  system_security_bits,
  system_security_at_least_120,
  lambda_tight_gt_loose
]

end Dregg2.Crypto.ParameterSecurity
