/-
# `Dregg2.Crypto.ParameterSecurity` — THE PARAMETER-LEVEL SECURITY THEOREM.

The rest of the crypto tree proves the QUALITATIVE reduction tree: the hybrid signature is unforgeable if
`DL ∨ MSIS` holds (`HybridCombiner`), the KEM is IND-CCA in the QROM up to the FO + O2H terms (`FoQrom`,
`FoBookkeeping`), multi-session UC costs a session-count union bound (`UcSignature`), adaptive corruption
costs ZERO (`AdaptiveTSUF`), and the combiner is TIGHT (`HybridCombiner.hybrid_euf_cma_if_either`). Each is
a `Prop`-level statement or a symbolic advantage term. This module turns that qualitative tree into a
DEPLOYABLE NUMBER: at the deployed ML-DSA-65 / ML-KEM-768 parameters, against any `q`-query quantum
adversary, the whole system's advantage is `≤ 2^(−λ)` for a λ we COMPUTE.

## TIGHT reductions (the campaign's last unit).

The end-to-end composition now feeds the **TIGHT** twins, whose formalizations landed in two DOWNSTREAM
files (they `import` this one, so — by the module DAG — this file cannot import them back; the tight terms
below are the numeric SHAPES of those cited theorems, proved here by the SAME `advOf` laws):

  * **`Dregg2.Crypto.LossyIdentification`** (KLS18/AFLT12 lossy-identification EUF-CMA) — kills the forking
    square-root. The signature floor is now `sigBitsTight = min mlweBits (min (α − log₂q) simBits) − 2`
    (`≈ mlweBits − O(1)`, decision-MLWE at coefficient 1), replacing the loose `sigBitsR = (msisBits −
    log₂q)/2`. At the deployed estimate: **179** vs the forking **86** (`LossyIdentification.tight_beats_forking`).
  * **`Dregg2.Crypto.DoubleSidedO2H`** (BHHHP19 double-sided O2H + HHM22 FO) — kills the O2H square-root. The
    KEM floor is now `kemBitsTight = min mlweBits (foCorrectnessBits − log₂q) − 2`, replacing the loose
    `o2hBitsR = msgEntropyBits/2 − log₂q − 1`. At the deployed estimate: **152** vs the semiclassical **107**
    (`DoubleSidedO2H.deployed_tightness_gain`).

The OLD `sigBitsR` / `o2hBitsR` / `kem3R` / `sigForkAdv` / `kemQromAdv` are KEPT below as the documented
CONTRAST (the record of what the tight reductions bought) — but the SYSTEM bound composes the tight ones.

## The accounting (§-by-§)

  **§1 — `advOf` — the advantage-in-bits calculus.** `advOf b = 2^(−b)` (an advantage of `b` bits). The
  whole composition is arithmetic in this one function: `advOf a · advOf b = advOf (a+b)` (union/product),
  `√(advOf b) = advOf (b/2)` (the forking / O2H square-root loss, only in the CONTRAST terms now), `advOf`
  is ANTITONE, and finite sums fold with a `−log₂(#terms)` bit cost.

  **§2 — THE ADVANTAGE TWINS.** The loose (forking/semiclassical) twins `sigForkAdv`/`kemQromAdv` (CONTRAST),
  and §2b the TIGHT twins `sigTightAdv`/`kemTightAdv` (the LANDED reductions) that the system bound uses.

  **§3 — THE COMPOSITION.** `sysAdvExpr E q log2q sessions consensus` composes the TIGHT twins by the actual
  reduction structure, and `system_advantage_bound` proves it `≤ advOf (lambdaR …)` — every step an `advOf`
  law, no new assumption.

  **§4 — THE LATTICE-HARDNESS INTERFACE.** `LatticeEstimate` carries the bit-security of MSIS/MLWE at the
  deployed parameters as LABELED NUMERIC INPUTS. **This is the ONLY non-proof input in the entire tree.**
  With the lossy-ID reduction the signature floor is decision-MLWE (the decisional twin of the same lattice
  floor), so the binding lattice number for BOTH primitives is `mlweBits`.

  **§5 — THE THEOREM.** `system_security_bits`: given a `LatticeEstimate` in the deployable regime, for any
  `q ≤ 2^log2q` quantum adversary, `sysAdvExpr ≤ advOf (sysSecurityBits …)` — i.e. `≤ 2^(−λ)` for the
  COMPUTED λ. `#guard` computes λ at the deployed regime; `system_security_at_least_120` HOLDS the bar.

## No named-carrier laundering.

No `def …Hard` is introduced. The `LatticeEstimate` is a bag of NUMBERS, never a `Prop`, never assumed.
Every bound is `advOf` arithmetic proved from Mathlib's `rpow`/`sqrt` API — theorems, never `axiom`s. The
qualitative reductions are CITED (their shapes are these terms); the numeric composition is self-contained.
The only residual is the lattice floor (`MLWESearchHard` and its decisional twin `DecisionMLWEHard`, plus
`MSISHard`), quantified by the ONE labeled estimate, exactly as the discipline permits.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Dregg2.Tactics
import Dregg2.Crypto.ConcreteSecurity
import Dregg2.Crypto.Lattice
import Dregg2.Crypto.HermineTSUF
import Dregg2.Crypto.FoQrom
import Dregg2.Crypto.FoBookkeeping
import Dregg2.Crypto.HybridCombiner
import Dregg2.Crypto.UcSignature
import Dregg2.Crypto.AdaptiveTSUF

open Dregg2.Crypto.ConcreteSecurity

namespace Dregg2.Crypto.ParameterSecurity

/-! ## §1 — `advOf` — the advantage-in-bits calculus. -/

/-- **`advOf b = 2^(−b)`** — an advantage of `b` BITS of security. The single object the whole
parameter-level composition is arithmetic in. -/
noncomputable def advOf (b : ℝ) : ℝ := (2 : ℝ) ^ (-b)

theorem advOf_pos (b : ℝ) : 0 < advOf b := Real.rpow_pos_of_pos (by norm_num) _

/-- `advOf a · advOf b = advOf (a+b)` — the UNION / product law: multiplying advantages ADDS bit-losses. -/
theorem advOf_mul (a b : ℝ) : advOf a * advOf b = advOf (a + b) := by
  unfold advOf
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1; ring

/-- `advOf (-(n)) = 2^n` — a NEGATIVE bit-count is a power blow-up (the `2^sessions` / `2^consensus` /
`2^log2q` factors). -/
theorem advOf_negNat (n : ℕ) : advOf (-(n:ℝ)) = (2:ℝ) ^ n := by
  unfold advOf; rw [neg_neg, Real.rpow_natCast]

/-- `advOf (-1) = 2`. -/
theorem advOf_negOne : advOf (-1) = 2 := by
  unfold advOf; rw [neg_neg, Real.rpow_one]

/-- `2^k · advOf x = advOf (x − k)` — a `k`-bit blow-up EATS `k` bits of an advantage. -/
theorem natpow_mul_advOf (k : ℕ) (x : ℝ) : (2:ℝ) ^ k * advOf x = advOf (x - (k:ℝ)) := by
  rw [← advOf_negNat, advOf_mul]; congr 1; ring

/-- `√(advOf b) = advOf (b/2)` — THE SQUARE-ROOT LOSS: the forking-lemma / O2H reduction HALVES the bits. -/
theorem advOf_sqrt (b : ℝ) : Real.sqrt (advOf b) = advOf (b / 2) := by
  rw [Real.sqrt_eq_rpow]
  unfold advOf
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1; ring

/-- `advOf` is ANTITONE: more bits ⟹ smaller advantage. -/
theorem advOf_antitone {a b : ℝ} (h : a ≤ b) : advOf b ≤ advOf a := by
  unfold advOf
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith)

/-- `2 · advOf b = advOf (b − 1)`. -/
theorem two_mul_advOf (b : ℝ) : 2 * advOf b = advOf (b - 1) := by
  rw [← advOf_negOne, advOf_mul]; congr 1; ring

/-- **TWO-TERM UNION.** `advOf a + advOf b ≤ advOf (min a b − 1)` — summing two advantages costs one bit. -/
theorem advOf_add_le (a b : ℝ) : advOf a + advOf b ≤ advOf (min a b - 1) := by
  have h1 : advOf a ≤ advOf (min a b) := advOf_antitone (min_le_left a b)
  have h2 : advOf b ≤ advOf (min a b) := advOf_antitone (min_le_right a b)
  calc advOf a + advOf b ≤ 2 * advOf (min a b) := by linarith
    _ = advOf (min a b - 1) := two_mul_advOf _

/-- **THREE-TERM UNION.** `advOf a + advOf b + advOf c ≤ advOf (min a (min b c) − 2)` — summing three
advantages costs two bits (`3 ≤ 4 = 2²`). The FO chain's O2H + CPA + correctness fold. -/
theorem advOf_add3_le (a b c : ℝ) :
    advOf a + advOf b + advOf c ≤ advOf (min a (min b c) - 2) := by
  set m := min a (min b c) with hm
  have ha : advOf a ≤ advOf m := advOf_antitone (min_le_left _ _)
  have hb : advOf b ≤ advOf m := advOf_antitone (le_trans (min_le_right a (min b c)) (min_le_left b c))
  have hc : advOf c ≤ advOf m := advOf_antitone (le_trans (min_le_right a (min b c)) (min_le_right b c))
  have hpos := advOf_pos m
  have e4 : (4:ℝ) * advOf m = advOf (m - 2) := by
    have : (4:ℝ) * advOf m = 2 * (2 * advOf m) := by ring
    rw [this, two_mul_advOf, two_mul_advOf]; congr 1; ring
  calc advOf a + advOf b + advOf c ≤ 4 * advOf m := by linarith
    _ = advOf (m - 2) := e4

/-- `advOf (n : ℝ) = 1/2^n` — the bridge to `ConcreteSecurity.Negl`. -/
theorem advOf_natCast (n : ℕ) : advOf (n : ℝ) = 1 / (2:ℝ) ^ n := by
  unfold advOf
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]

/-- **(TOOTH — ties `advOf` into the concrete-security substrate.)** The ensemble `λ ↦ advOf λ = 2^(−λ)` is
NEGLIGIBLE — the parameter-level advantage, taken as a family in the security parameter, lands in the
`ConcreteSecurity.Negl` algebra. -/
theorem negl_advOf : Negl (fun n : ℕ => advOf (n : ℝ)) := by
  have h : (fun n : ℕ => advOf (n:ℝ)) = (fun n : ℕ => 1 / (2:ℝ) ^ n) := by
    funext n; exact advOf_natCast n
  rw [h]; exact negl_two_pow

/-! ## §4 (stated early) — THE DEPLOYED PARAMETERS + THE LATTICE-HARDNESS INTERFACE. -/

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

/-! ## §2 — THE ADVANTAGE TWINS. §2a: the LOOSE (forking/semiclassical) twins, KEPT as CONTRAST. -/

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

/-- **(CONTRAST)** The loose signature bits (post-forking): `(msisBits − log₂q)/2`. -/
noncomputable def sigBitsR (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  ((E.msisBits : ℝ) - (log2q : ℝ)) / 2

/-- **(CONTRAST)** The loose O2H reprogramming term's bits: `msgEntropyBits/2 − log₂q − 1`. -/
noncomputable def o2hBitsR (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  (E.msgEntropyBits : ℝ) / 2 - (log2q : ℝ) - 1

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

/-! ## §2b — THE TIGHT ADVANTAGE TWINS (the LANDED reductions the system bound uses).

The numeric shapes of `LossyIdentification.sigTightAdv/sigBitsTight` (lossy-ID EUF-CMA, α = `msgEntropyBits`,
simBits = `mlweBits`) and `DoubleSidedO2H.kemTightAdv/kemBitsTight` (double-sided O2H FO-KEM), specialised to
a `LatticeEstimate`. Proved by the SAME `advOf` laws (`advOf_add3_le`, `advOf_add_le`, `natpow_mul_advOf`);
no `√`, no new assumption — the only residual is `mlweBits`/`foCorrectnessBits` (the lattice/correctness
floor), read as numbers. -/

/-- **`sigTightAdv E log2q` — the TIGHT EUF-CMA advantage (lossy-ID; `LossyIdentification.sigTightAdv`).**
`advOf mlweBits + advOf (msgEntropyBits − log₂q) + advOf mlweBits`: the decision-MLWE term at COEFFICIENT 1
(no `√`, no `ε²`, no `q_H`), the lossy-soundness term `q_H·ε_ls = advOf (α − log₂q)`, the HVZK-simulation
term `advOf simBits` (simBits = mlweBits). REPLACES the forking `sigForkAdv`. -/
noncomputable def sigTightAdv (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  advOf (E.mlweBits : ℝ) + advOf ((E.msgEntropyBits : ℝ) - (log2q : ℝ)) + advOf (E.mlweBits : ℝ)

/-- **`sigBitsTight E log2q` — the TIGHT signature bits: `min mlweBits (min (msgEntropyBits − log₂q) mlweBits)
− 2 ≈ mlweBits − O(1)`.** No halving, no `log₂q` under a `/2`. REPLACES `sigBitsR = (msisBits − log₂q)/2`. -/
noncomputable def sigBitsTight (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  min (E.mlweBits : ℝ) (min ((E.msgEntropyBits : ℝ) - (log2q : ℝ)) (E.mlweBits : ℝ)) - 2

/-- **`sigTightAdv ≤ advOf sigBitsTight`** — directly `advOf_add3_le` (three-term union costs 2 bits), no
`√`, no new assumption. -/
theorem sigTightAdv_le (E : LatticeEstimate) (log2q : ℕ) :
    sigTightAdv E log2q ≤ advOf (sigBitsTight E log2q) := by
  unfold sigTightAdv sigBitsTight
  exact advOf_add3_le (E.mlweBits : ℝ) ((E.msgEntropyBits : ℝ) - (log2q : ℝ)) (E.mlweBits : ℝ)

/-- **`kemTightAdv E q` — the TIGHT ML-KEM IND-CCA advantage (HHM22; `DoubleSidedO2H.kemTightAdv`).**
`2·advOf mlweBits + (q+1)·advOf foCorrectnessBits`: the IND-CPA/MLWE term LINEAR at full strength (the
double-sided O2H removed the `√`), the query budget confined to the `(q+1)·δ` correctness term. REPLACES the
semiclassical `kemQromAdv`. -/
noncomputable def kemTightAdv (E : LatticeEstimate) (q : ℕ) : ℝ :=
  2 * advOf (E.mlweBits : ℝ) + ((q : ℝ) + 1) * advOf (E.foCorrectnessBits : ℝ)

/-- **`kemBitsTight E log2q` — the TIGHT KEM bits: `min mlweBits (foCorrectnessBits − log₂q) − 2`.** Governed
by the LATTICE floor `mlweBits`, not the (halved) message entropy. REPLACES `o2hBitsR` / `kem3R`. -/
noncomputable def kemBitsTight (E : LatticeEstimate) (log2q : ℕ) : ℝ :=
  min (E.mlweBits : ℝ) ((E.foCorrectnessBits : ℝ) - (log2q : ℝ)) - 2

/-- **`kemTightAdv_le` — the tight KEM bit bound** (`DoubleSidedO2H.kemTightAdv_le`, re-proved here on the
`LatticeEstimate` specialisation). `2·advOf mlweBits = advOf (mlweBits−1)`; `(q+1)·advOf foCorrectnessBits ≤
2^(log2q+1)·advOf foCorrectnessBits = advOf (foCorrectnessBits−log2q−1)`; the two-term union costs one more
bit — folding to `min mlweBits (foCorrectnessBits−log2q) − 2`. -/
theorem kemTightAdv_le (E : LatticeEstimate) {q log2q : ℕ} (hq : q ≤ 2 ^ log2q) :
    kemTightAdv E q ≤ advOf (kemBitsTight E log2q) := by
  unfold kemTightAdv kemBitsTight
  have h2mlwe : 2 * advOf (E.mlweBits : ℝ) = advOf ((E.mlweBits : ℝ) - 1) := two_mul_advOf _
  have hq1n : q + 1 ≤ 2 ^ (log2q + 1) := by
    have hp : 2 ^ (log2q + 1) = 2 * 2 ^ log2q := by rw [pow_succ]; ring
    have h1 : 1 ≤ 2 ^ log2q := Nat.one_le_pow log2q 2 (by norm_num)
    omega
  have hq1 : ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (log2q + 1) := by exact_mod_cast hq1n
  have hcorr : ((q : ℝ) + 1) * advOf (E.foCorrectnessBits : ℝ)
      ≤ advOf ((E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1)) := by
    calc ((q : ℝ) + 1) * advOf (E.foCorrectnessBits : ℝ)
        ≤ (2 : ℝ) ^ (log2q + 1) * advOf (E.foCorrectnessBits : ℝ) :=
          mul_le_mul_of_nonneg_right hq1 (le_of_lt (advOf_pos _))
      _ = advOf ((E.foCorrectnessBits : ℝ) - ((log2q + 1 : ℕ) : ℝ)) := natpow_mul_advOf _ _
      _ = advOf ((E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1)) := by rw [Nat.cast_add, Nat.cast_one]
  have hsum : 2 * advOf (E.mlweBits : ℝ) + ((q : ℝ) + 1) * advOf (E.foCorrectnessBits : ℝ)
      ≤ advOf (min ((E.mlweBits : ℝ) - 1) ((E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1)) - 1) := by
    rw [h2mlwe]
    calc advOf ((E.mlweBits : ℝ) - 1) + ((q : ℝ) + 1) * advOf (E.foCorrectnessBits : ℝ)
        ≤ advOf ((E.mlweBits : ℝ) - 1) + advOf ((E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1)) := by
          linarith [hcorr]
      _ ≤ advOf (min ((E.mlweBits : ℝ) - 1) ((E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1)) - 1) :=
          advOf_add_le _ _
  refine hsum.trans (advOf_antitone ?_)
  rcases le_total (E.mlweBits : ℝ) ((E.foCorrectnessBits : ℝ) - (log2q : ℝ)) with hle | hle
  · rw [min_eq_left hle,
        min_eq_left (by linarith : (E.mlweBits : ℝ) - 1 ≤ (E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1))]
    linarith
  · rw [min_eq_right hle,
        min_eq_right (by linarith : (E.foCorrectnessBits : ℝ) - ((log2q : ℝ) + 1) ≤ (E.mlweBits : ℝ) - 1)]
    linarith

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
`advOf` law composing the TIGHT twins — lossy-ID decision-MLWE (coefficient 1), double-sided O2H (no `√`),
session/consensus union — with NO new assumption. -/
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

/-- **`sigBitsTightN`** — ℕ mirror of `sigBitsTight` (`LossyIdentification.sigBitsTightN` at α = msgEntropy,
simBits = mlwe). No division ⟹ exact under the deployable regime. -/
def sigBitsTightN (E : LatticeEstimate) (log2q : ℕ) : ℕ :=
  min E.mlweBits (min (E.msgEntropyBits - log2q) E.mlweBits) - 2

/-- **`kemBitsTightN`** — ℕ mirror of `kemBitsTight` (`DoubleSidedO2H.kemBitsTightN`). -/
def kemBitsTightN (E : LatticeEstimate) (log2q : ℕ) : ℕ :=
  min E.mlweBits (E.foCorrectnessBits - log2q) - 2

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
    unfold sigBitsTightN sigBitsTight
    rw [Nat.cast_sub h3, Nat.cast_min, Nat.cast_min, Nat.cast_sub h1]
    norm_num
  have hkemN : (kemBitsTightN E log2q : ℝ) = kemBitsTight E log2q := by
    unfold kemBitsTightN kemBitsTight
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
cited and proved; the ONLY empirical input is the `LatticeEstimate`'s `mlweBits`/`foCorrectnessBits`. -/
theorem system_security_bits (E : LatticeEstimate) {q log2q : ℕ} (hq : q ≤ 2 ^ log2q)
    (sessions consensus : ℕ) (hdep : Deployable E log2q sessions consensus) :
    sysAdvExpr E q log2q sessions consensus ≤ advOf ((sysSecurityBits E log2q sessions consensus : ℕ) : ℝ) := by
  refine (system_advantage_bound E hq sessions consensus).trans ?_
  exact advOf_antitone (sysSecurityBits_le_lambdaR E hdep)

/-! ## §6 — INSTANTIATION AT THE NIST-CLAIMED ESTIMATES + THE LOAD-BEARING TEETH. -/

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
