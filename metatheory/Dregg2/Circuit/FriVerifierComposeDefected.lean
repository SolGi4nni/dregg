/-
# Dregg2.Circuit.FriVerifierComposeDefected — FRI ladder rung L1: `epsFri_compose` restated with the
DEFECTED query leg, in the `condProb` model, with the deployed leg DISCHARGED.

`FriVerifierCompose.epsFri_compose` union-bounds the four legs over ONE shared oracle, but its query
leg is `epsQuery cardF k δ = 1/|F| + (1 − δ)^k` — the UNIFORM-sampler value. The deployed sampler is
provably NOT uniform (`FriVerifierCompose.babybear_sampleBits_not_balanced`: `|F|` is odd, so the
`n % 2^logN` buckets cannot balance at any shipped `logN`), so the uniform leg is not a statement
about the deployed system. This module restates the composition with the leg the deployed sampler
actually earns:

    epsQueryDefected cardF m k δ  =  1/|F| + ((1 − δ) + m/|F|)^k

— the `m/N` modular-reduction defect of `FriCarrierEpsilon.friQueryForgeryBound_proven`, in place of
the uniform `(1 − δ)^k`. Everything here lives in the SAME `condProb` model as `epsFri_compose`
(fractions of a finite oracle set; no independence assumed anywhere), completing the condProb
unification: the deployed-sampler proximity theorem
(`DeployedProximitySoundnessSampler.far_word_rarely_accepted_deployed_sampler`) is re-read as a
`condProb` bound (`deployed_query_leg_condProb`) and plugged straight into the union bound
(`epsFri_compose_deployed_defected`) — the query leg arrives as a THEOREM at the deployed
parameters, not as a hypothesis.

## Non-vacuity: the defect is LOAD-BEARING, not cosmetic
`undefected_query_leg_refuted` shows the UN-defected leg value `(1 − δ)^k` is FALSE as a `condProb`
bound at the witness `N = 3, m = 2, k = 1, δ = 1/2` — and the refutation runs THROUGH the committed
falsifier `FriCarrierEpsilon.friQueryForgeryBound_false_without_defect`: the condProb bound at the
un-defected value would transfer to `FriQueryForgeryBound` at exactly the ε the falsifier refutes.
`defected_query_leg_holds_at_witness` shows the defected leg DOES hold at the same witness. So the
`m/N` addend is exactly what separates a false bound from a true one.

## Scope, stated so it cannot be read up
This is the union-bound composition and its query leg, over the squeeze space under the same ROM
idealisation as `FriQueryBiasSharp`/`DeployedProximitySoundness` (sponge squeeze uniform over `F`).
`δ = 7/16` is the unique-decoding radius — the ONLY radius the tree proves. Blocker (a) of
`FriVerifierCompose` §3 (`WordProofBridge` = `DeployedFriEmbedding`) is UNTOUCHED here: the deployed
leg is discharged for the abstract far word `f` against the code, not yet attached to a
`BatchProofData` extraction bundle. Blocker (b) — the sampling defect — is what this rung retires.
-/
import Mathlib.Tactic
import Dregg2.Circuit.FriVerifierCompose
import Dregg2.Circuit.FriCarrierEpsilon
import Dregg2.Circuit.DeployedProximitySoundnessSampler

set_option autoImplicit false

namespace Dregg2.Circuit.FriVerifierComposeDefected

open Dregg2.Crypto.RomCounting (condProb)
open Dregg2.Circuit.FriVerifierCompose
  (epsFS epsGrind epsMerkle epsQuery epsFri condProb_or4_le babybear_sampleBits_not_balanced)
open Dregg2.Circuit.FriCarrierEpsilon
  (FriQueryForgeryBound missSet witness_forgery_fraction friQueryForgeryBound_false_without_defect)
open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.FriQuerySoundness
open Dregg2.Circuit.BabyBearFriDeployed
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.DeployedProximitySoundnessSampler
  (sampledQuery far_word_rarely_accepted_deployed_sampler)

/-! ## §1 — the DEFECTED query leg, and the composition restated. -/

/-- **The query leg over the DEPLOYED (non-uniform) sampler.** Same shape as
`FriVerifierCompose.epsQuery` with the survival base carrying the `m/N` modular-reduction defect:
`1/|F| + ((1 − δ) + m/|F|)^k`. `m` is the query-domain size (`2^logN`); the addend `m/|F|` is the
worst-case per-index bucket overweight of `sampleBits` (`FriCarrierEpsilon` §2). -/
noncomputable def epsQueryDefected (cardF m k : ℕ) (δ : ℝ) : ℝ :=
  1 / (cardF : ℝ) + ((1 - δ) + (m : ℝ) / (cardF : ℝ)) ^ k

/-- **`εFri` with the defected query leg** — the composed error the DEPLOYED sampler earns:
`εFS + εGrind + εMerkle + epsQueryDefected`. -/
noncomputable def epsFriDefected (Q degBound cardF powBits cardA m k : ℕ) (δ : ℝ) : ℝ :=
  epsFS Q degBound cardF + epsGrind Q powBits + epsMerkle Q cardA + epsQueryDefected cardF m k δ

/-- The defected leg is a SOUND correction, not a tightening: it dominates the uniform leg, so
nothing proven against `epsQueryDefected` silently claims more than the uniform model did. -/
theorem epsQuery_le_epsQueryDefected (cardF m k : ℕ) (δ : ℝ) (hδ1 : δ ≤ 1) :
    epsQuery cardF k δ ≤ epsQueryDefected cardF m k δ := by
  unfold epsQuery epsQueryDefected
  have h0 : (0 : ℝ) ≤ 1 - δ := by linarith
  have hm : (0 : ℝ) ≤ (m : ℝ) / (cardF : ℝ) := by positivity
  have hpow : (1 - δ) ^ k ≤ ((1 - δ) + (m : ℝ) / (cardF : ℝ)) ^ k :=
    pow_le_pow_left₀ h0 (by linarith) k
  linarith

/-- **⚑ THE `εFri` COMPOSITION, DEFECTED LEG (rung L1).** `FriVerifierCompose.epsFri_compose`
restated with the query leg the deployed non-uniform `sampleBits` sampler actually admits: the
probability that ANY of the four legs fails on one adversary's single run against one shared oracle
is at most `epsFriDefected`. Same real union bound over the same shared conditioning — no
independence anywhere — only the query addend is now the honest `((1 − δ) + m/N)^k` form instead of
the uniform `(1 − δ)^k` that `babybear_sampleBits_not_balanced` shows the deployed sampler does not
have. -/
theorem epsFri_compose_defected {D R : Type} [Fintype D] [DecidableEq D] [Fintype R]
    [DecidableEq R]
    (C : Finset (D → R)) (wFS wGrind wMerkle wQuery : (D → R) → Bool)
    (Q degBound cardF powBits cardA m k : ℕ) (δ : ℝ)
    (hFS : condProb C wFS ≤ epsFS Q degBound cardF)
    (hGrind : condProb C wGrind ≤ epsGrind Q powBits)
    (hMerkle : condProb C wMerkle ≤ epsMerkle Q cardA)
    (hQuery : condProb C wQuery ≤ epsQueryDefected cardF m k δ) :
    condProb C (fun H => wFS H || wGrind H || wMerkle H || wQuery H)
      ≤ epsFriDefected Q degBound cardF powBits cardA m k δ := by
  refine le_trans (condProb_or4_le C wFS wGrind wMerkle wQuery) ?_
  unfold epsFriDefected
  linarith

/-! ## §2 — the condProb unification: the deployed query leg, DISCHARGED.

`far_word_rarely_accepted_deployed_sampler` is a fraction over the squeeze space
`Fin 38 → Fin |F|`. That fraction IS `condProb` at `C = univ` — so the leg plugs into the union
bound with no model seam. -/

/-- **⚑ THE DEPLOYED QUERY LEG AS A `condProb` BOUND.** For a `7/16`-far word `f`, the event "the
deployed 38-query check accepts `f`" — queries drawn by the ACTUAL `n % 16` field-squeeze
reduction, as an event over the uniform squeeze oracle `H : Fin 38 → Fin |F|` — has `condProb`
at most `epsQueryDefected |F| 16 38 (7/16)`. This is
`far_word_rarely_accepted_deployed_sampler`'s sharp bound `((1 − δ) + δ/|F|)^38` relaxed into the
`m/N`-defect leg (`δ ≤ 1 ≤ m` and the `1/|F|` addend are both give-aways), re-read in the
`condProb` model. The query leg of `epsFri_compose_defected` is hereby a THEOREM at the deployed
parameters, not a hypothesis. -/
theorem deployed_query_leg_condProb {f g : Fin (2 ^ 4) → BabyBear}
    (hgC : g ∈ friSetupDeployedRate.C) (hfar : farN friSetupDeployedRate.C 7 f) :
    condProb (Finset.univ : Finset (Fin 38 → Fin 2013265921))
        (fun H => decide (Accepts f g (fun i => sampledQuery (H i))))
      ≤ epsQueryDefected 2013265921 (2 ^ 4) 38 (7 / 16) := by
  classical
  have hbase := far_word_rarely_accepted_deployed_sampler hgC hfar
  have hcard : ((Finset.univ : Finset (Fin 38 → Fin 2013265921)).card : ℝ)
      = (2013265921 : ℝ) ^ 38 := by
    rw [Finset.card_univ, Fintype.card_fun]
    push_cast
    norm_num
  have hfil : Finset.univ.filter
        (fun H : Fin 38 → Fin 2013265921 =>
          (fun H => decide (Accepts f g (fun i => sampledQuery (H i)))) H = true)
      = Finset.univ.filter
        (fun Q : Fin 38 → Fin 2013265921 => Accepts f g (fun i => sampledQuery (Q i))) := by
    apply Finset.filter_congr
    intro H _
    simp
  have hcond : condProb (Finset.univ : Finset (Fin 38 → Fin 2013265921))
        (fun H => decide (Accepts f g (fun i => sampledQuery (H i))))
      = ((Finset.univ.filter (fun Q : Fin 38 → Fin 2013265921 =>
          Accepts f g (fun i => sampledQuery (Q i)))).card : ℝ)
        / ((2013265921 : ℝ) ^ 38) := by
    unfold Dregg2.Crypto.RomCounting.condProb
    rw [hfil, hcard]
  rw [hcond]
  refine le_trans hbase ?_
  unfold epsQueryDefected
  have hNpos : (0 : ℝ) < (2013265921 : ℝ) := by norm_num
  have hmono : ((1 - 7 / 16 : ℝ) + (7 / 16) / (2013265921 : ℝ)) ^ 38
      ≤ ((1 - (7 / 16 : ℝ)) + ((2 ^ 4 : ℕ) : ℝ) / (2013265921 : ℝ)) ^ 38 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 38
    have hdiv : (7 / 16 : ℝ) / (2013265921 : ℝ) ≤ ((2 ^ 4 : ℕ) : ℝ) / (2013265921 : ℝ) := by
      push_cast
      norm_num
    linarith
  have hpos : (0 : ℝ) ≤ 1 / ((2013265921 : ℕ) : ℝ) := by positivity
  push_cast at hmono ⊢
  linarith

/-- **⚑⚑ RUNG L1 LANDED: the deployed composition with the query leg DISCHARGED.** For ANY FS,
grinding, and Merkle events over the deployed squeeze oracle satisfying their Stage-2/3 bounds, and
the ACTUAL deployed far-word acceptance event as the fourth leg, the union of all four is bounded by
`epsFriDefected` at the deployed parameters `|F| = 2013265921, m = 16, k = 38, δ = 7/16`. The query
leg is supplied by `deployed_query_leg_condProb` — a theorem, not a hypothesis. Compare
`friLdtExtractV3_rom_of_legs`, whose `hQuery` "does not come home": over the honest defected leg, at
these parameters, it now does. -/
theorem epsFri_compose_deployed_defected
    (wFS wGrind wMerkle : (Fin 38 → Fin 2013265921) → Bool)
    {f g : Fin (2 ^ 4) → BabyBear}
    (hgC : g ∈ friSetupDeployedRate.C) (hfar : farN friSetupDeployedRate.C 7 f)
    (Q degBound powBits cardA : ℕ)
    (hFS : condProb Finset.univ wFS ≤ epsFS Q degBound 2013265921)
    (hGrind : condProb Finset.univ wGrind ≤ epsGrind Q powBits)
    (hMerkle : condProb Finset.univ wMerkle ≤ epsMerkle Q cardA) :
    condProb (Finset.univ : Finset (Fin 38 → Fin 2013265921))
        (fun H => wFS H || wGrind H || wMerkle H
          || decide (Accepts f g (fun i => sampledQuery (H i))))
      ≤ epsFriDefected Q degBound 2013265921 powBits cardA (2 ^ 4) 38 (7 / 16) :=
  epsFri_compose_defected Finset.univ wFS wGrind wMerkle _
    Q degBound 2013265921 powBits cardA (2 ^ 4) 38 (7 / 16)
    hFS hGrind hMerkle (deployed_query_leg_condProb hgC hfar)

/-! ## §3 — ⚑ NON-VACUITY: the falsifier refutes the UN-defected form.

If the defect addend were cosmetic, the uniform leg `(1 − δ)^k` would also be a sound `condProb`
bound. It is not: at `N = 3, m = 2, k = 1, δ = 1/2` the acceptance event has `condProb = 2/3 > 1/2`.
The refutation is routed THROUGH `friQueryForgeryBound_false_without_defect` — the committed
falsifier does the knocking-over, so the canary and the carrier refute the SAME wrong ε. -/

/-- The witness acceptance event in the `condProb` model: oracle `H : Fin 1 → Fin 3` (one squeeze,
three field values), event "the single reduced query `(H 0) % 2` lands in the far word's miss set
`{0}`". Identical to membership in `FriCarrierEpsilon.missSet 3 2 1 {0}`. -/
def wMissWitness : (Fin 1 → Fin 3) → Bool :=
  fun H => decide (∀ i : Fin 1, (H i).val % 2 ∈ ({0} : Finset ℕ))

/-- The witness event's exact probability: `2/3` — squeeze values `0` and `2` both reduce to the
heavy residue `0`. -/
theorem condProb_wMissWitness_eq :
    condProb (Finset.univ : Finset (Fin 1 → Fin 3)) wMissWitness = 2 / 3 := by
  unfold Dregg2.Crypto.RomCounting.condProb wMissWitness
  have h1 : (Finset.univ.filter (fun H : Fin 1 → Fin 3 =>
      (fun H : Fin 1 → Fin 3 =>
        decide (∀ i : Fin 1, (H i).val % 2 ∈ ({0} : Finset ℕ))) H = true)).card = 2 := by decide
  have h2 : (Finset.univ : Finset (Fin 1 → Fin 3)).card = 3 := by decide
  rw [h1, h2]
  norm_num

/-- **The transfer**: were the UN-defected uniform value `(1 − δ)^k` a sound `condProb` bound on the
witness event, it would validate `FriQueryForgeryBound` at exactly the ε the committed falsifier
refutes. (The `condProb` event and the carrier's `Q = 1`-attempt fraction are the same `2/3`:
`condProb_wMissWitness_eq` and `witness_forgery_fraction`.) -/
theorem undefected_leg_transfers
    (h : condProb (Finset.univ : Finset (Fin 1 → Fin 3)) wMissWitness
      ≤ (1 - (1 / 2 : ℝ)) ^ 1) :
    FriQueryForgeryBound 3 2 1 1 ({0} : Finset ℕ) ((1 : ℝ) * (1 - (1 / 2 : ℝ)) ^ 1) := by
  unfold FriQueryForgeryBound
  rw [witness_forgery_fraction]
  rw [condProb_wMissWitness_eq] at h
  norm_num at h

/-- **⚑⚑ THE CANARY: the un-defected query leg is REFUTED, by the committed falsifier.** The
uniform value `(1 − δ)^k` is NOT a `condProb` bound on the deployed-sampler acceptance event at the
witness — because if it were, `undefected_leg_transfers` would produce exactly the
`FriQueryForgeryBound` instance that `friQueryForgeryBound_false_without_defect` refutes. The `m/N`
defect in `epsQueryDefected` is load-bearing: remove it and the leg is FALSE. -/
theorem undefected_query_leg_refuted :
    ¬ (condProb (Finset.univ : Finset (Fin 1 → Fin 3)) wMissWitness
        ≤ (1 - (1 / 2 : ℝ)) ^ 1) :=
  fun h => friQueryForgeryBound_false_without_defect (undefected_leg_transfers h)

/-- And the DEFECTED leg holds at the same witness: `2/3 ≤ 1/3 + ((1 − 1/2) + 2/3)^1 = 3/2`. The
defect addend is the cost that restores truth — paid, not slack. -/
theorem defected_query_leg_holds_at_witness :
    condProb (Finset.univ : Finset (Fin 1 → Fin 3)) wMissWitness
      ≤ epsQueryDefected 3 2 1 (1 / 2) := by
  rw [condProb_wMissWitness_eq]
  unfold epsQueryDefected
  norm_num

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  epsQuery_le_epsQueryDefected,
  epsFri_compose_defected,
  deployed_query_leg_condProb,
  epsFri_compose_deployed_defected,
  condProb_wMissWitness_eq,
  undefected_leg_transfers,
  undefected_query_leg_refuted,
  defected_query_leg_holds_at_witness
]

end Dregg2.Circuit.FriVerifierComposeDefected
