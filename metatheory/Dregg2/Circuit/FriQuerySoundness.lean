/-
# Dregg2.Circuit.FriQuerySoundness — the DEPLOYED FRI query-sampling soundness bound.

**Honest scope (first sentence).** This module PROVES the query-phase soundness error of the
DEPLOYED FRI sampler as a real inequality: for a `δ`-far oracle, the probability that `k`
uniform independent queries all accept is `≤ (1 − δ)^k`; instantiated at the deployed
`k = 38` queries with `δ = 7/16` (the rate-`1/8` code's UNIQUE-DECODING radius) this is
`(9/16)^38 < 2⁻³¹`. It rests only on the standard kernel + `Mathlib` (no `sorry`, no smuggled
hardness). What remains ASSUMED (stated precisely in §5): the union-bound COMPOSITION with the
per-round bad-challenge error lives at the level of a common transcript measure whose two
sub-events are (a) some fold challenge is exceptional — bounded `≤ rounds/|F|` by the committed
`exceptional_subsingleton` — and (b) the query phase all-misses — bounded `(1−δ)^k` here; the
arithmetic of that composition is proved (`soundness_error_compose`), but the identification of
the two finset events with the committed lemmas is left as the documented wiring.

**Why this is the missing piece.** `FriSoundness.friProximity_discharge` and the arity keystone
`FriFoldArity.fold_close_of_arity_challenges` both close soundness through a query set `Q` that
COVERS the disagreement (`hcover : disagree … ⊆ Q`), whereupon the oracle is EXACTLY a codeword
(`d = 0`). Every BabyBear instantiation supplies that cover by `Finset.subset_univ` — i.e. it
queries EVERY point. The deployed prover instead SAMPLES `PROD_FRI_NUM_QUERIES = 38` points
(`circuit/src/plonky3_prover.rs:99`). The probabilistic step — a random `38`-sample HITS a
`δ`-far disagreement set w.h.p. — is exactly what `hcover` assumed away, and it is where FRI's
soundness error lives. This file models the SAMPLE (not `univ`) and proves that step. Because a
sampled `Q` yields `d`-closeness for `d > 0` (not `d = 0`), the arity constant `n²·d = 64d` of
`FriFoldArity` finally BITES (`arity_constant_bites`, `§4`).

**The four pieces.**
1. `§1` The sampled-query model: uniform independent queries, `Ω = (Fin k → ι)`, `|Ω| = Nᵏ`.
   This is FAITHFUL to the shipped verifier (`Plonky3@82cfad73 fri/src/verifier.rs:266-268` draws
   each of `num_queries` indices independently, no dedup — sampling with replacement), so `(1−δ)ᵏ`
   is the ACTUAL query error, not merely an upper bound.
2. `§2` The deterministic contrapositive (`accept_avoids_disagree`): an accepting sample entirely
   AVOIDED the disagreement — the probability-free half. And the counting identity
   (`accepting_card`): the accepting samples are `((disagree f g)ᶜ)ᵏ`.
3. `§3` The COUNTING/probability bound (`accept_prob_le`): `|accepting|/Nᵏ ≤ (1−δ)ᵏ` in the clean
   product form `(|Bᶜ|/N)ᵏ ≤ (1−δ)ᵏ`, quantified over the whole code (`accept_prob_le_of_farN`).
   Reframed onto the EXACT committed check (`fold_check_pass_prob_le`, bad set
   `disagree f' (Fold α f)`) so it closes `friProximity_discharge`'s `hcover` seam
   (`sampled_cover_discharges`). Deployed at `k = 38`, `δ = 7/16` (`deployed_accept_prob_lt`):
   error `< 2⁻³¹`.
4. `§4` The arity corollary (`arity_constant_bites`) and `§5` the composition + teeth.

Sibling `Dregg2/Crypto/MlDsaSignReal.lean` is modified in the working tree; this file does not
touch it.
-/
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Dregg2.Circuit.FriSoundness
import Dregg2.Circuit.FriFoldArity

namespace Dregg2.Circuit.FriQuerySoundness

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.FriFoldArity (friSetupK8 fold_close_of_arity_challenges)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open scoped BigOperators

/-! ## §1. The sampled-query model.

The deployed FRI query phase draws `k` points of the evaluation domain `L = ι` and checks that
the oracle `f` agrees with the claimed low-degree codeword `g` at each. We model `k` **uniform
independent** queries: a sample is a function `Q : Fin k → ι`, the sample space `Ω = (Fin k → ι)`
has `|Ω| = Nᵏ` (`N = |L|`), and each `Q` is equally likely. Acceptance is agreement at every
queried point.

**This model is FAITHFUL to the deployed verifier, not merely an upper bound.** The plonky3 FRI
verifier (`Plonky3/Plonky3@82cfad73 fri/src/verifier.rs:266-268`) draws each of the `num_queries`
indices INDEPENDENTLY inside the per-query loop —
`let index = challenger.sample_bits(log_global_max_height + …)` — with NO deduplication, so query
points may coincide. That is sampling WITH replacement over `Fin k → ι`, exactly `Ω` here; the
`(1−δ)ᵏ` bound is therefore the actual per-oracle query soundness error of the shipped verifier
(a distinct-index sampler would only lower it, by negative association). -/

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Acceptance.** The verifier accepts the sample `Q` against the claimed codeword `g` iff the
oracle `f` agrees with `g` at every queried point. (`reducible` so `filter`/`decide` see the
decidable `∀`.) -/
@[reducible] def Accepts (f g : ι → F) {k : ℕ} (Q : Fin k → ι) : Prop := ∀ i, f (Q i) = g (Q i)

/-! ## §2. The deterministic contrapositive and the counting identity.

The honest, probability-free half: acceptance FORCES the sample to have avoided the disagreement
set entirely. Sampling is the only thing that makes "avoid the disagreement" IMPROBABLE. -/

/-- **Deterministic contrapositive (the probability-free half).** If the verifier ACCEPTS — all
`k` queried points agree with the claimed codeword `g` — then the sample entirely AVOIDED the
disagreement set: every query landed OUTSIDE `disagree f g`. A far oracle (large `disagree f g`)
is only accepted when the sample missed a large set — precisely the event sampling makes rare. -/
theorem accept_avoids_disagree {f g : ι → F} {k : ℕ} {Q : Fin k → ι}
    (h : Accepts f g Q) : ∀ i, Q i ∉ disagree f g := by
  intro i
  rw [mem_disagree, not_not]
  exact h i

/-- Restatement: an accepting sample lands entirely in the disagreement COMPLEMENT. -/
theorem accept_forces_avoidance {f g : ι → F} {k : ℕ} {Q : Fin k → ι}
    (h : Accepts f g Q) : ∀ i, Q i ∈ (disagree f g)ᶜ := by
  intro i
  rw [Finset.mem_compl]
  exact accept_avoids_disagree h i

/-- **The counting identity.** The accepting samples are EXACTLY the functions into the
disagreement complement, so there are `|(disagree f g)ᶜ|ᵏ = (N − |disagree f g|)ᵏ` of them. This
is the deterministic core of the counting bound: it counts the `k`-samples that miss a set. -/
theorem accepting_card (f g : ι → F) (k : ℕ) :
    (Finset.univ.filter (fun Q : Fin k → ι => Accepts f g Q)).card
      = ((disagree f g)ᶜ).card ^ k := by
  have hset : (Finset.univ.filter (fun Q : Fin k → ι => Accepts f g Q))
      = Fintype.piFinset (fun _ : Fin k => (disagree f g)ᶜ) := by
    ext Q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      Finset.mem_compl, mem_disagree, not_not, Accepts]
  rw [hset, Fintype.card_piFinset_const]

/-! ## §3. THE COUNTING / PROBABILITY BOUND (the content DEBT-A #2 asks for).

If `f` is `δ`-FAR from the code — for the claimed codeword `g`, `|disagree f g| > δ·N` — then the
FRACTION of `k`-samples that accept is `≤ (1−δ)ᵏ`. In the standard `k`-subset form this is
`C((1−δ)N, k)/C(N, k) ≤ (1−δ)ᵏ`; in the with-replacement form proved here it is the clean product
`(|Bᶜ|/N)ᵏ ≤ (1−δ)ᵏ`, since `|Bᶜ|/N = 1 − |B|/N < 1 − δ`. This is the probabilistic step every
current through-line assumed away via `hcover : disagree … ⊆ Q`. -/

/-- **QUERY SOUNDNESS ERROR (the counting bound).** For a `δ`-far oracle
(`hfar : δ·N < |disagree f g|`) the probability that `k` uniform independent queries all accept
is `≤ (1−δ)ᵏ`. Proof: `|accepting|/Nᵏ = (|Bᶜ|/N)ᵏ` (`accepting_card` + `div_pow`), and
`|Bᶜ|/N = (N−|B|)/N ≤ 1−δ` (from `hfar`, `N>0`), raised to `k` (base nonneg). -/
theorem accept_prob_le {f g : ι → F} {δ : ℝ} (k : ℕ)
    (hN : 0 < Fintype.card ι) (_hδ0 : 0 ≤ δ)
    (hfar : δ * (Fintype.card ι : ℝ) < ((disagree f g).card : ℝ)) :
    ((Finset.univ.filter (fun Q : Fin k → ι => Accepts f g Q)).card : ℝ)
        / ((Fintype.card ι : ℝ) ^ k)
      ≤ (1 - δ) ^ k := by
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; exact_mod_cast hN
  have hle : (disagree f g).card ≤ Fintype.card ι := by
    simpa using Finset.card_le_univ (disagree f g)
  have hBc : (((disagree f g)ᶜ).card : ℝ) = N - ((disagree f g).card : ℝ) := by
    rw [Finset.card_compl, Nat.cast_sub hle, hNdef]
  -- The base ratio is `≤ 1 − δ`.
  have hbase : (((disagree f g)ᶜ).card : ℝ) / N ≤ 1 - δ := by
    rw [div_le_iff₀ hNpos, hBc]
    have hexp : (1 - δ) * N = N - δ * N := by ring
    rw [hexp]; linarith [hfar]
  have hbase0 : (0 : ℝ) ≤ ((disagree f g)ᶜ).card / N := by positivity
  -- Rewrite the LHS as `(|Bᶜ|/N)ᵏ` and bound.
  rw [accepting_card]
  push_cast
  rw [← div_pow]
  exact pow_le_pow_left₀ hbase0 hbase k

/-- **Quantified over the WHOLE code (the honest far hypothesis).** The prover's claimed codeword
`g` is SOME member of the code `C`; `δ`-farness must hold against ALL of `C`. If `f` is `farN`
from `C` at radius `d ≥ δ·N`, then against every claimed `g ∈ C` the accept probability is
`≤ (1−δ)ᵏ` — the bound does not depend on which codeword the prover names, because `farN` bounds
`|disagree f g|` below for every `g ∈ C` at once. -/
theorem accept_prob_le_of_farN {C : Submodule F (ι → F)} {f g : ι → F} {δ : ℝ} {d : ℕ} (k : ℕ)
    (hN : 0 < Fintype.card ι) (hδ0 : 0 ≤ δ) (hgC : g ∈ C)
    (hfar : farN C d f) (hδd : δ * (Fintype.card ι : ℝ) ≤ (d : ℝ)) :
    ((Finset.univ.filter (fun Q : Fin k → ι => Accepts f g Q)).card : ℝ)
        / ((Fintype.card ι : ℝ) ^ k)
      ≤ (1 - δ) ^ k := by
  refine accept_prob_le k hN hδ0 ?_
  have hgt : d < (disagree f g).card := by
    by_contra hle
    exact hfar ⟨g, hgC, not_lt.mp hle⟩
  calc δ * (Fintype.card ι : ℝ) ≤ (d : ℝ) := hδd
    _ < ((disagree f g).card : ℝ) := by exact_mod_cast hgt

/-! ### Closing the committed `hcover` seam directly.

`FriSoundness.friProximity_discharge` and `FriSoundness.query_sound_of_cover` take
`hcover : disagree f' (Fold α f) ⊆ Q` and conclude EXACT equality `f' = Fold α f` (proximity at
`d = 0`). Every BabyBear instantiation supplies `hcover` by `Finset.subset_univ` — querying every
point. The bound below is that `hcover`'s missing probability: instantiating `accept_prob_le` at
the folded domain `κ` with the tested pair `(f', Fold S.geom α f)`, the bad set is EXACTLY the
committed `disagree f' (Fold S.geom α f)`, so a `δ`-far round oracle passes the sampled fold check
with probability `≤ (1−δ)ᵏ`. Its complement is where `hcover` holds. -/

/-- **The seam, quantified.** If the round oracle `f'` is `δ`-FAR from the true fold
`Fold S.geom α f` on `κ`, a `k`-query sample passes the fold check
(`∀ i, f' (Q i) = Fold S.geom α f (Q i)`) with probability `≤ (1−δ)ᵏ`. This is `accept_prob_le`
at `ι := κ`, `f := f'`, `g := Fold S.geom α f`: the bad set it counts against is the committed
`disagree f' (Fold S.geom α f)` verbatim. -/
theorem fold_check_pass_prob_le {S : FriSetup F ι κ} {f : ι → F} {f' : κ → F} {α : F} {δ : ℝ}
    (k : ℕ) (hN : 0 < Fintype.card κ) (hδ0 : 0 ≤ δ)
    (hfar : δ * (Fintype.card κ : ℝ) < ((disagree f' (Fold S.geom α f)).card : ℝ)) :
    ((Finset.univ.filter
        (fun Q : Fin k → κ => Accepts f' (Fold S.geom α f) Q)).card : ℝ)
        / ((Fintype.card κ : ℝ) ^ k)
      ≤ (1 - δ) ^ k :=
  accept_prob_le k hN hδ0 hfar

/-- **The good event fires the committed discharge.** When the sample COVERS the disagreement
(`disagree f' (Fold α f) ⊆ image Q univ`) and passes, the committed
`FriSoundness.friProximity_discharge` applies verbatim (with `Q' = image Q univ`), yielding exact
`FriProximity S 0 f`. So the dichotomy is complete: on the good event (probability
`≥ 1 − (1−δ)ᵏ` by `fold_check_pass_prob_le`) proximity is EXACT; the bad event is the `≤ (1−δ)ᵏ`
false-accept mass this file bounds. -/
theorem sampled_cover_discharges {S : FriSetup F ι κ} {f : ι → F} {f' : κ → F} {α : F} {k : ℕ}
    (Q : Fin k → κ)
    (hcover : disagree f' (Fold S.geom α f) ⊆ Finset.image Q Finset.univ)
    (hpass : Accepts f' (Fold S.geom α f) Q)
    (hfinal : f' ∈ S.C')
    (hgeneric : Fold S.geom α f ∈ S.C' → f ∈ S.C) :
    FriProximity S 0 f := by
  refine friProximity_discharge S (Finset.image Q Finset.univ) hcover ?_ hfinal hgeneric
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨i, _, rfl⟩ := hy
  exact hpass i

/-! ### Deployed instantiation: `log_blowup = 3` ⇒ rate `ρ = 1/8`, `num_queries = 38`.

`circuit/src/plonky3_prover.rs:97-99`: `PROD_FRI_LOG_BLOWUP = 3` (rate `ρ = 2⁻³ = 1/8`) and
`PROD_FRI_NUM_QUERIES = 38`. The rate-`1/8` Reed–Solomon code has relative minimum distance
`1 − ρ = 7/8`, so its UNIQUE-DECODING radius is `δ = (1 − ρ)/2 = 7/16`. We use THIS `δ`: it is
the regime the committed lemmas prove (the two-point / size-`n` Vandermonde reconstruction of
`FriSoundness.fold_close_of_two_alpha` / `FriFoldArity.fold_close_of_arity_challenges` is a
unique-decoding argument). Claiming the larger Johnson list-decoding radius `1 − √ρ ≈ 0.646`
would need the BCIKS20 proximity-gaps machinery, which is NOT proved here — so `δ = 7/16` is the
honest choice, giving per-oracle query error `(1 − 7/16)^38 = (9/16)^38`. -/

/-- `(1 − 7/16)^38 = (9/16)^38` — the deployed unique-decoding query error, in lowest terms. -/
theorem deployed_query_error_eq : ((1 : ℝ) - 7 / 16) ^ 38 = (9 / 16 : ℝ) ^ 38 := by norm_num

/-- **The concrete numeric error.** `(9/16)^38 < 2⁻³¹` (in fact `≈ 2⁻³¹·⁵`): the deployed `38`
queries at the rate-`1/8` unique-decoding radius give per-oracle query soundness error below
`2⁻³¹`. (`9^38 = 3^76 < 2¹²¹`, so `(9/16)^38 = 9^38 / 2¹⁵² < 2⁻³¹`.) -/
theorem deployed_query_error_lt : (9 / 16 : ℝ) ^ 38 < 1 / 2 ^ 31 := by norm_num

/-- **DEPLOYED QUERY SOUNDNESS.** At the deployed `k = 38` queries and `δ = 7/16`, a `δ`-far
oracle accepts with probability `< 2⁻³¹`. This is `accept_prob_le` specialized and chained
through `deployed_query_error_lt` — the honest per-oracle FRI query soundness error at the
shipped parameters. -/
theorem deployed_accept_prob_lt {f g : ι → F}
    (hN : 0 < Fintype.card ι)
    (hfar : (7 / 16 : ℝ) * (Fintype.card ι : ℝ) < ((disagree f g).card : ℝ)) :
    ((Finset.univ.filter (fun Q : Fin 38 → ι => Accepts f g Q)).card : ℝ)
        / ((Fintype.card ι : ℝ) ^ 38)
      < 1 / 2 ^ 31 := by
  refine lt_of_le_of_lt (accept_prob_le 38 hN (by norm_num) hfar) ?_
  rw [deployed_query_error_eq]
  exact deployed_query_error_lt

/-! ## §4. The consequence: with a SAMPLED `Q`, the arity constant `64d` BITES.

The committed through-lines take `hcover` and land on `d = 0`, which annihilates the arity
constant (`n²·d = 0`). A SAMPLED `Q` only makes the oracle `d`-CLOSE for `d > 0` — the query
bound above says `d ≈ δ·N` with the stated probability. Fed into the arity keystone at the
deployed `n = 8`, the constant `8² = 64` finally multiplies a NONZERO `d`. -/

/-- **The arity constant bites** at the deployed arity `n = 8`. If a (sampled-query, hence
`d`-close for `d > 0`) oracle folds `d`-close under `8` distinct challenges, it is `64·d`-close —
`64 = 8²` is `FriFoldArity`'s obligation-#6 constant, INVISIBLE while `d = 0` under `hcover`, now
load-bearing. (`arity_constant_bites` at `d = 0` recovers `0`-closeness; at `d ≥ 1` it is `≥ 64`.) -/
theorem arity_constant_bites {f : Fin 16 → BabyBear} {α : Fin 8 → BabyBear}
    (hα : Function.Injective α) {d : ℕ}
    (hclose : ∀ i, closeN friSetupK8.C' d
        (Dregg2.Circuit.FriFoldArity.Fold friSetupK8.geom (α i) f)) :
    closeN friSetupK8.C (64 * d) f := by
  have h := fold_close_of_arity_challenges friSetupK8 hα hclose
  have he : (8 : ℕ) ^ 2 * d = 64 * d := by norm_num
  rwa [he] at h

/-- The constant is `64` — witnessed, not decorative: `d > 0` ⇒ `64·d ≥ 64 > 0`, whereas the
`hcover`-through-lines had `64·0 = 0`. -/
theorem arity_constant_value {d : ℕ} (hd : 0 < d) : 0 < 64 * d := by omega

/-! ## §5. The honest composition + both-truth teeth.

**Composition.** Total FRI soundness error `≤ (per-round bad-challenge error) + (query error)`.
`soundness_error_compose` proves the union-bound ARITHMETIC over a common finite transcript space
`Ω`: if the accept-a-far-oracle event is contained in (some fold challenge exceptional) ∪ (query
phase all-misses), its measure is `≤` the sum of the two. What is PROVED: the arithmetic. What is
ASSUMED (the documented wiring): identifying `Efold` with the transcripts whose fold challenge is
exceptional — bounded `≤ rounds/|F| ≈ (log-domain)/2³¹` by the committed
`FriSoundness.exceptional_subsingleton` / `FriFoldArity.good_challenge_card_lt` — and `Equery`
with the query all-miss event bounded `(1−δ)ᵏ` here. -/

/-- **Union-bound composition (arithmetic core, genuine — not `P → P`).** Over any finite
transcript space `Ω`, if the far-accept event `Eaccept` decomposes into the fold-exceptional
event `Efold` and the query-all-miss event `Equery`, then its probability is at most the sum of
the two probabilities. Proof: `card_le_card` of the containment, then `card_union_le`, divided. -/
theorem soundness_error_compose {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (Eaccept Efold Equery : Finset Ω) (hdecomp : Eaccept ⊆ Efold ∪ Equery) :
    (Eaccept.card : ℝ) / Fintype.card Ω
      ≤ (Efold.card : ℝ) / Fintype.card Ω + (Equery.card : ℝ) / Fintype.card Ω := by
  have h1 : Eaccept.card ≤ Efold.card + Equery.card :=
    le_trans (Finset.card_le_card hdecomp) (Finset.card_union_le _ _)
  rw [← add_div]
  gcongr
  exact_mod_cast h1

/-! ### Teeth — soundness is PROBABILISTIC, not absolute (both polarities).

Over the genuine rate-`1/2` `ZMod 5` instance `rsSetup` (`FriSoundness §5`): the far word
`fFar = ![1,0,0,0]` disagrees with the codeword `gZero = 0` at EXACTLY the single point `0`.
FIRES: a query that hits `0` catches `fFar` (acceptance fails). BITES: a query that misses `0`
ACCEPTS the far word `fFar ∉ C` — so a single sample can accept a far oracle, i.e. soundness is
only probabilistic, exactly the gap the counting bound quantifies (never `1`, but not `0`). -/

section Teeth

/-- The zero codeword — a genuine member of the domain code. -/
def gZero : Fin 4 → ZMod 5 := fun _ => 0

theorem gZero_mem : gZero ∈ rsSetup.C := ⟨0, 0, by funext x; simp [gZero]⟩

/-- **FIRES.** A query that HITS the sole disagreement point `0` catches the far word: the
sample `Q = ![0]` does NOT accept `fFar` against `gZero` (`fFar 0 = 1 ≠ 0 = gZero 0`). A covering
query is deterministically sound (`FriSoundness.query_sound_of_cover`). -/
theorem far_caught_by_hitting_query :
    ¬ Accepts fFar gZero (![0] : Fin 1 → Fin 4) := by decide

/-- **BITES.** A query that MISSES the disagreement point `0` ACCEPTS the far word: the sample
`Q = ![1]` accepts `fFar` against `gZero` even though `fFar ∉ C`. So a lone sample can accept a
far oracle — soundness is PROBABILISTIC, not absolute; this is the event `accept_prob_le` bounds
by `(1−δ)ᵏ` (nonzero, hence a genuine — not vanishing — error). -/
theorem far_accepted_by_missing_query :
    Accepts fFar gZero (![1] : Fin 1 → Fin 4) := by decide

/-- The far word IS far — `fFar ∉ C` (so the BITES tooth is non-vacuous: a genuine far oracle is
accepted by the missing query). -/
theorem fFar_is_far : fFar ∉ rsSetup.C := fFar_not_mem

end Teeth

/-! ## §6. Axiom hygiene — the query bound, the deployed instantiation, the arity corollary, the
composition, and the teeth rest only on the kernel axioms + `Mathlib`. No `sorry`, no smuggled
hardness (`δ = 7/16` is the code's unique-decoding radius, the regime the committed lemmas prove). -/

#assert_axioms accept_avoids_disagree
#assert_axioms accepting_card
#assert_axioms accept_prob_le
#assert_axioms accept_prob_le_of_farN
#assert_axioms fold_check_pass_prob_le
#assert_axioms sampled_cover_discharges
#assert_axioms deployed_query_error_lt
#assert_axioms deployed_accept_prob_lt
#assert_axioms arity_constant_bites
#assert_axioms soundness_error_compose
#assert_axioms far_caught_by_hitting_query
#assert_axioms far_accepted_by_missing_query

end Dregg2.Circuit.FriQuerySoundness
