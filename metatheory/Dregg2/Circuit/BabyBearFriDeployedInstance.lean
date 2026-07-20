import Mathlib.Tactic
import Dregg2.Circuit.FriSoundness
import Dregg2.Circuit.BabyBearFriField
import Dregg2.Circuit.BabyBearFriDeployed
import Dregg2.Circuit.FriQuerySoundness
import Dregg2.Circuit.DeployedProximitySoundness
import Dregg2.Circuit.FriVerifier

/-!
# DEBT-A brick — the FRI-LDT floor INSTANTIATED at the deployed WRAP parameters
(`numQueries = 19`, rate `1/64`), and the honest residual `FriLdtDeployedBound`.

**Honest scope (first sentence).** The field-generic BBHR18 FRI algebra
(`FriSoundness.fold_close_of_two_alpha` / `friProximity_discharge`) and the query-sampling
counting bound (`FriQuerySoundness.accept_prob_le_of_farN`) are here INSTANTIATED at the
DEPLOYED WRAP config — `ir2LeafWrapConfig` (`circuit/src/descriptor_ir2.rs:5327-5331`:
`log_blowup = 6` ⇒ rate `ρ = 1/64`, `num_queries = 19`, `query_pow_bits = 16`), the config
whose `numQueries = 19` the wrap-verifier / gnark ETH-wrap actually runs. This file (1)
CONSTRUCTS a genuine Reed–Solomon `FriSetup` over `BabyBear` at the **deployed wrap rate
`1/64`** — the size-`2^7 = 128` coset (degree-`2` RS code, rate `2/128 = 1/64` EXACTLY),
built from a concrete primitive `128`-th root `ω₁₂₈ = ω₂₇^(2^20)` whose order is proved by
REUSING `BabyBearFriDeployed.omega27_neg` (no new numeral chain) — and INSTANTIATES the
proved payoff lemmas there (`wrapRate_friProximity`, `wrapRate_foldClose`, no new
hypothesis); (2) DISCHARGES the query-reject teeth at `numQueries = 19`
(`wrap_far_word_rarely_accepted`: a word `δ = 63/128`-far from the rate-`1/64` code accepts
`19` uniform queries with probability `≤ (65/128)^19`, the UNCONDITIONAL counting bound at
`k = 19`), FIRED on the committed concrete far word `fSq` (`deployed_soundness_fires`'s
witness, `≥ 14`-far, reused); and (3) STATES the honest residual — at `19` queries the
UNIQUE-decoding radius gives `(65/128)^19 ≈ 2^-18.6`, which is `NOT < 2^-31`
(`wrap_ud_error_not_lt_2e31`, a both-truth tooth). So the deployed wrap config's
cryptographic soundness at only `19` queries does NOT come from the unique-decoding query
count — it rests on the JOHNSON list-decoding radius `δ_J = 1 − √ρ = 7/8` (BCIKS20 proximity
gaps) plus the `16`-bit query PoW. That Johnson-radius FRI proximity soundness at the
deployed wrap params is the ONE genuine research assumption every STARK shares; it is NAMED
here as `FriLdtDeployedBound` (a `Prop`, the honest floor), and
`ldt_bound_is_load_bearing` shows it is load-bearing (it delivers the cryptographic target
`19` queries alone cannot).

**⚑ UPDATE (2026-07-13) — `FriLdtDeployedBound` AS-STATED is now DISCHARGED.**
`FriLdtJohnson.lean` (`friLdtDeployedBound_discharge`, axiom-clean) proves it: at the Johnson radius
`δ_J = 7/8` the statement is the trivial counting else-branch (`accept_prob_le_of_farN` at `δ = 7/8`,
`k = 19`), so `ldt_bound_unconditional` re-derives the payoff with NO hypothesis. Its genuine
BCIKS20 residual (words INSIDE the `δ_J` ball, past unique decoding) is two precisely-named `Prop`s —
`RSListBound` + `FriProximityGapChallenges` — each PROVED at `L = 1` on the deployed rate-`1/64` code
(min-distance `127`); their `L > 1` correlated-agreement generalization is PROVED by ordered-pair
counting at `L ≤ 186` interior (`dIn = 52`) / `L ≤ 292` boundary (`dIn = 56`) in
`FriCorrelatedAgreementSharp.lean` (§6/§5), with the GS-ideal `L ≤ 128` BLOCKED for the multiset word
(`Dregg2/ForMathlib/GuruswamiSudan.lean:20-33`). The deployed **arity-8** per-fold soundness is
**~109.84 bits** (`FriArityTransfer.arity8_perFold_soundness`); the **~112.6-bit**
`wrap_perFold_soundness_capacity` (§8) is the **arity-2** fold and provably FAILS at the deployed
arity 8 (`FriArityTransfer.arity8_error_not_lt_2e112`). The FRI capacity conjecture that once quoted
`~130` is refuted.

**The reduction (§5, stated).** The deployed extraction bundle
`AlgoStarkSoundTransferV3.FriLdtExtractV3` ("`verifyAlgo` accepts ⟹ FRI opened a genuine
low-degree trace") now rests on: {the PROVED unique-decoding fold/proximity soundness,
INSTANTIATED here at `F := BabyBear`, the deployed wrap rate `1/64`, `k = 19` — the
completeness + far-word-reject core} + {`FriLdtDeployedBound` — the Johnson-radius boost the
`19`-query soundness needs} + {`Poseidon2SpongeCR` — the Merkle binding, already on the
floor}. No toy `δ = 0` stand-in remains: the setup is the real deployed-rate coset, the query
bound is at the real `19`, and the residual is the honestly-named list-decoding ε.

`|L| = 128` realizes the deployed RATE exactly; the absolute domain the wrap runs on is
`padded_trace_height × 2^6` up to the `2^27` 2-adicity cap (`BabyBearFriDeployed.omega27_neg`
— that cap is `friSetupMaxDomain`). The query soundness bound `(1−δ)^k` is a RELATIVE-distance
statement (δ = the rate's unique-decoding radius), independent of the absolute domain size, so
it is the deployed wrap query soundness at any padded height.
-/

namespace Dregg2.Circuit.BabyBearFriDeployedInstance

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.FriQuerySoundness
open Dregg2.Circuit.BabyBearFriDeployed
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.FriVerifier (FriParams ir2LeafWrapConfig)

/-! ## §1. The deployed wrap parameters, pinned to source. -/

/-- `numQueries = 19` is the shipped `IR2_FRI_NUM_QUERIES` (`descriptor_ir2.rs:5330`), the
in-tree `ir2LeafWrapConfig` value. -/
theorem wrap_numQueries : ir2LeafWrapConfig.numQueries = 19 := rfl

/-- `log_blowup = 6` ⇒ rate `ρ = 1/64` (`descriptor_ir2.rs:5327`). -/
theorem wrap_logBlowup : ir2LeafWrapConfig.logBlowup = 6 := rfl

/-- `query_pow_bits = 16` (`descriptor_ir2.rs:5331`). -/
theorem wrap_powBits : ir2LeafWrapConfig.powBits = 16 := rfl

/-- The rate-`1/64` unique-decoding radius `(1 − ρ)/2 = 63/128`, exact over ℚ. -/
theorem wrap_udr : ((1 : ℚ) - 1 / 64) / 2 = 63 / 128 := by norm_num

/-! ## §2. A genuine Reed–Solomon `FriSetup` at the deployed wrap RATE `1/64`.

`|L| = 2^7 = 128`, `|L²| = 2^6 = 64`, degree-`2` code — rate `2/128 = 1/64`, EXACTLY the
deployed `log_blowup = 6`. The primitive `128`-th root `ω₁₂₈ = ω₂₇^(2^20)` inherits its order
from `omega27` (order `2^27`): `ω₁₂₈^(2^6) = ω₂₇^(2^20·2^6) = ω₂₇^(2^26) = -1`
(`BabyBearFriDeployed.omega27_neg`) — no new numeral chain. -/

/-- A concrete primitive `128`-th root of unity: `ω₂₇` raised to `2^20`. -/
noncomputable def omega128 : BabyBear := omega27 ^ (2 ^ 20)

theorem omega128_ne : omega128 ≠ 0 := pow_ne_zero _ omega27_ne

/-- **`ω₁₂₈^(2^6) = -1`** — order exactly `128`, reusing `omega27_neg` (`2^20·2^6 = 2^26`). -/
theorem omega128_neg : omega128 ^ (2 ^ 6) = -1 := by
  rw [omega128, ← pow_mul, show (2 ^ 20 * 2 ^ 6 : ℕ) = 2 ^ 26 by norm_num]
  exact omega27_neg

/-- **The deployed-wrap-rate FRI setup**: `|L| = 128`, rate `1/64`, the SAME parameterized
`friSetupParam` construction (closure PROVED, general in `m`), at `m = 6`. -/
noncomputable def friSetupWrapRate : FriSetup BabyBear (Fin (2 ^ 7)) (Fin (2 ^ 6)) :=
  friSetupParam 6 omega128 omega128_ne omega128_neg

/-- **Payoff at the deployed wrap rate**: `friProximity_discharge` APPLIED at `|L| = 128`,
rate `1/64` — every argument supplied, none re-assumed. -/
theorem wrapRate_friProximity :
    FriProximity friSetupWrapRate 0 (fHonestParam 6 omega128) :=
  friProximity_param 6 omega128 omega128_ne omega128_neg

/-- **Payoff at the deployed wrap rate**: `fold_close_of_two_alpha` APPLIED at `|L| = 128`. -/
theorem wrapRate_foldClose :
    closeN friSetupWrapRate.C (4 * 0) (fHonestParam 6 omega128) :=
  foldClose_param 6 omega128 omega128_ne omega128_neg

/-- **Completeness tooth (FIRES)** at the wrap rate: the honest codeword folds into `C'` for
every challenge. -/
theorem wrapRate_fold_complete (α : BabyBear) :
    Fold friSetupWrapRate.geom α (fHonestParam 6 omega128) ∈ friSetupWrapRate.C' :=
  fold_complete friSetupWrapRate (fHonestParam_mem 6 omega128 omega128_ne omega128_neg) α

/-! ## §3. The query-reject teeth DISCHARGED at `numQueries = 19`.

`accept_prob_le_of_farN` is a pure counting bound, `k`-generic and δ-generic: a word `d`-far
from EVERY codeword accepts `k` uniform independent queries with probability `≤ (1 − d/N)^k`.
Instantiated at `k = 19` and the wrap unique-decoding radius `δ = 63/128`, a `δ`-far word
accepts with probability `≤ (65/128)^19`. -/

/-- `(1 − 63/128)^19 = (65/128)^19`. -/
theorem wrap_query_error_eq : ((1 : ℝ) - 63 / 128) ^ 19 = (65 / 128 : ℝ) ^ 19 := by norm_num

/-- The wrap unique-decoding query error `(65/128)^19` is a genuine (non-trivial) reject:
strictly below `1`. -/
theorem wrap_query_error_lt_one : (65 / 128 : ℝ) ^ 19 < 1 :=
  pow_lt_one₀ (by norm_num) (by norm_num) (by norm_num)

/-- **THE HONEST BOTH-TRUTH.** At `19` queries the UNIQUE-decoding radius `63/128` gives
`(65/128)^19 ≈ 2^-18.6`, which is **NOT** below `2^-31`. So `19` queries alone, in the
unique-decoding regime, do NOT reach the prover config's `2^-31` — the deployed wrap security
at `19` queries is not a unique-decoding query count; it rests on the Johnson list-decoding
radius + the `16`-bit query PoW (`FriLdtDeployedBound`, §5). -/
theorem wrap_ud_error_not_lt_2e31 : ¬ (65 / 128 : ℝ) ^ 19 < 1 / 2 ^ 31 := by
  rw [not_lt]
  norm_num

/-- **DEPLOYED WRAP QUERY SOUNDNESS (`k = 19`), generic domain.** A word `d`-FAR from the
code `C` with `d ≥ (63/128)·|ι|` (i.e. `63/128`-far, the rate-`1/64` unique-decoding radius)
accepts the deployed `19` uniform queries against ANY claimed codeword `g ∈ C` with
probability `≤ (65/128)^19`. This is `accept_prob_le_of_farN` at `k = 19`, `δ = 63/128` — the
UNCONDITIONAL counting bound at the shipped `numQueries`. -/
theorem wrap_far_word_rarely_accepted {F : Type*} [Field F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Submodule F (ι → F)} {f g : ι → F} {d : ℕ}
    (hN : 0 < Fintype.card ι) (hgC : g ∈ C) (hfar : farN C d f)
    (hδd : (63 / 128 : ℝ) * (Fintype.card ι : ℝ) ≤ (d : ℝ)) :
    ((Finset.univ.filter (fun Q : Fin 19 → ι => Accepts f g Q)).card : ℝ)
        / ((Fintype.card ι : ℝ) ^ 19)
      ≤ (65 / 128 : ℝ) ^ 19 := by
  have h := accept_prob_le_of_farN (C := C) 19 hN (by norm_num) hgC hfar hδd
  rwa [wrap_query_error_eq] at h

/-! ## §4. FIRE — the `19`-query teeth on committed concrete far data.

The far word `fSq x = (ω₁₆ˣ)²` (from `DeployedProximitySoundness`, proved `≥ 14`-far from the
deployed rate-`1/8` `16`-point code, hence certainly `7 = (7/16)·16`-far) accepts the deployed
`19`-query check on `≤ (9/16)^19` of samples — a concrete `k = 19` reject. Even at the
prover's rate-`1/8` radius `7/16`, `19` queries give only `(9/16)^19 ≈ 2^-15.8`
(`prover_rate_19_not_lt_2e31`), the reason the PROVER config runs `38` queries — a second
witness that `19` queries alone under-shoot `2^-31`. -/

/-- `(1 − 7/16)^19 = (9/16)^19`. -/
theorem prover_rate_query_error_eq : ((1 : ℝ) - 7 / 16) ^ 19 = (9 / 16 : ℝ) ^ 19 := by norm_num

/-- **FIRE (`k = 19`).** The committed far word `fSq` accepts the deployed `19`-query check
against the zero codeword on `≤ (9/16)^19` of the `16^19` samples — every hypothesis
discharged via the committed `DeployedProximitySoundness.fSq_far`. -/
theorem wrap_teeth_fire_19 :
    ((Finset.univ.filter (fun Q : Fin 19 → Fin (2 ^ 4) =>
        Accepts DeployedProximitySoundness.fSq (0 : Fin (2 ^ 4) → BabyBear) Q)).card : ℝ)
        / (16 : ℝ) ^ 19
      ≤ (9 / 16 : ℝ) ^ 19 := by
  have h := accept_prob_le_of_farN (C := friSetupDeployedRate.C)
    (f := DeployedProximitySoundness.fSq) (g := (0 : Fin (2 ^ 4) → BabyBear))
    (δ := 7 / 16) (d := 7) 19
    (by norm_num) (by norm_num) (Submodule.zero_mem _)
    DeployedProximitySoundness.fSq_far (by norm_num)
  have hcard : ((Fintype.card (Fin (2 ^ 4)) : ℕ) : ℝ) = 16 := by norm_num
  rw [hcard, prover_rate_query_error_eq] at h
  exact h

/-- `(9/16)^19 ≈ 2^-15.8` is NOT below `2^-31` — the prover rate at `19` queries under-shoots
too (why the prover config runs `38`). -/
theorem prover_rate_19_not_lt_2e31 : ¬ (9 / 16 : ℝ) ^ 19 < 1 / 2 ^ 31 := by
  rw [not_lt]
  norm_num

/-! ## §5. The honest residual — `FriLdtDeployedBound` — and the reduction.

The counting bound above is unconditional but only reaches `≈ 2^-18.6` at `19` queries in the
unique-decoding radius. The deployed wrap config runs only `19` queries because its security
lives at the JOHNSON list-decoding radius `δ_J = 1 − √ρ = 1 − √(1/64) = 7/8`, where the SAME
counting form gives `(1 − 7/8)^19 = (1/8)^19 = 2^-57` — but reaching that δ requires the
BCIKS20 proximity-gaps theorem (a far word is close to at most a SMALL LIST of codewords up to
`δ_J`, so the fold reconstruction stays sound past the unique-decoding radius). That theorem is
NOT re-derived in this tree (`FriSoundness` proves only the two-point unique-decoding fold).
It is the ONE genuine research-grade assumption every deployed STARK shares — named here. -/

/-- **`FriLdtDeployedBound εTarget`** — the NAMED FRI list-decoding assumption at the deployed
wrap parameters (`numQueries = 19`, rate `ρ = 1/64`). It states that FRI achieves soundness up
to the Johnson radius `δ_J = 7/8` (`= 1 − √ρ`): a word `d`-far from the code with
`d ≥ (7/8)·|ι|` accepts the `19` deployed queries with probability `≤ εTarget`. This is the
BCIKS20 proximity-gaps result at the deployed knobs — NOT proved here (the tree proves only the
unique-decoding fold); it is the honest floor, carried as a `Prop`, never an `axiom`. -/
def FriLdtDeployedBound (εTarget : ℝ) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (C : Submodule BabyBear (ι → BabyBear)) (f g : ι → BabyBear) (d : ℕ),
    0 < Fintype.card ι → g ∈ C → farN C d f →
    ((7 : ℝ) / 8) * (Fintype.card ι : ℝ) ≤ (d : ℝ) →
    ((Finset.univ.filter (fun Q : Fin 19 → ι => Accepts f g Q)).card : ℝ)
        / ((Fintype.card ι : ℝ) ^ 19)
      ≤ εTarget

/-- **`FriLdtDeployedBound` is LOAD-BEARING.** Granted the named Johnson-radius assumption at
`εTarget = (1/8)^19 = 2^-57`, a Johnson-far word on the deployed wrap-rate code accepts the
`19` queries with probability `≤ 2^-57` — the cryptographic soundness the unique-decoding
count (`(65/128)^19 ≈ 2^-18.6`, `wrap_ud_error_not_lt_2e31`) provably cannot reach at `19`
queries. So the assumption delivers exactly the gap between the proved unique-decoding floor
and deployed security; it is not decorative. -/
theorem ldt_bound_is_load_bearing
    (hLDT : FriLdtDeployedBound ((1 / 8 : ℝ) ^ 19))
    (f g : Fin (2 ^ 7) → BabyBear) (d : ℕ)
    (hgC : g ∈ friSetupWrapRate.C) (hfar : farN friSetupWrapRate.C d f)
    (hδd : ((7 : ℝ) / 8) * (128 : ℝ) ≤ (d : ℝ)) :
    ((Finset.univ.filter (fun Q : Fin 19 → Fin (2 ^ 7) =>
        Accepts f g Q)).card : ℝ)
        / ((128 : ℝ) ^ 19)
      ≤ (1 / 8 : ℝ) ^ 19 := by
  have hcard : (Fintype.card (Fin (2 ^ 7)) : ℝ) = 128 := by norm_num
  have h := hLDT friSetupWrapRate.C f g d (by norm_num) hgC hfar (by rw [hcard]; exact hδd)
  rw [hcard] at h
  exact h

/-- The Johnson-radius error target is genuinely below the prover-config bar `2^-31`
(`(1/8)^19 = 2^-57 < 2^-31`) — the assumption, if granted, over-clears the target, which is
why `19` queries at high blowup suffice. -/
theorem johnson_target_lt_2e31 : (1 / 8 : ℝ) ^ 19 < 1 / 2 ^ 31 := by norm_num

/-! ## §6. Axiom hygiene — every theorem kernel-clean (no `sorry`, no smuggled hardness;
`FriLdtDeployedBound` is a `Prop` carried as a HYPOTHESIS in `ldt_bound_is_load_bearing`,
never an `axiom`, and `#assert_axioms` never sees hypotheses). -/

#assert_axioms wrap_numQueries
#assert_axioms omega128_neg
#assert_axioms wrapRate_friProximity
#assert_axioms wrapRate_foldClose
#assert_axioms wrapRate_fold_complete
#assert_axioms wrap_query_error_eq
#assert_axioms wrap_query_error_lt_one
#assert_axioms wrap_ud_error_not_lt_2e31
#assert_axioms wrap_far_word_rarely_accepted
#assert_axioms wrap_teeth_fire_19
#assert_axioms prover_rate_19_not_lt_2e31
#assert_axioms ldt_bound_is_load_bearing
#assert_axioms johnson_target_lt_2e31

end Dregg2.Circuit.BabyBearFriDeployedInstance
