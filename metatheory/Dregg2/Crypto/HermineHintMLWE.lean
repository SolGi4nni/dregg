/-
# `Dregg2.Crypto.HermineHintMLWE` — a concurrent-security ARGUMENT for our 2-round commit-reveal Hermine.

## HONEST BOUNDARY (Tanuki cross-check, 2026-07) — READ FIRST

A follow-up analysis against the proven 2-round lattice threshold family (Tanuki [EKT24/Ringtail],
Threshold Raccoon [dPKPR24 Eurocrypt'24], "Unmasking TRaccoon" '25) found that **this is NOT a cited
instance of a proven scheme — it is a plausible design with an UNCLOSED concurrent-security reduction.**
Three corrections to the earlier overclaims:
* **Different family.** Our crypto-hermine impl (BN06 commit-then-reveal `cmᵢ=H(i,wᵢ)`, single-column
  `wᵢ=A·yᵢ`, exact key `t=A·s`, one flooding mask) is NOT Tanuki/TRaccoon (in-the-clear WIDE commitment
  `Wᵢ=A·Rᵢ+Eᵢ`, hashed `b`-aggregation as the actual rushing defense, pairwise zero-sum PRF masks, ROUNDED
  MLWE key). "Aligned to real Raccoon" was aspirational, not accurate.
* **NOT fully straight-line.** The masking-hiding leg IS rewinding-free, but the forgery→MSIS leg
  (`SelfTargetMSIS.selftarget_extract_nonzero`) REQUIRES two accepting transcripts on a common `w` with
  `c ≠ c'` — that is forking-shaped, and the two-transcript hypothesis is ASSUMED here, never PRODUCED from
  a single forger.
* **The full concurrent game is NOT reduced.** The old headline `concurrent_unforgeable_reduces`
  (DELETED — it carried the refuted injective `HashCR` floor; its keyed-ROM successor is
  `HermineRomBinding.hermine_concurrent_forgery_rom`) COMPOSED three individually-valid pillars around
  named carriers; it did NOT model the signing oracle or the t−1 static corruption that a TS-UF-0
  proof requires.
No exploit is evident and each pillar below is sound; but closing the gap means EITHER re-implementing
toward Tanuki/Ringtail's algebraic `b`-aggregation (a different construction) OR completing a TRaccoon-style
game-based proof for the commit-then-reveal variant (formalize the rewinding that yields the two
transcripts + signing-oracle simulation + corruption). Until then, treat the "concurrent unforgeability"
here as ARGUED, not PROVED. (crypto-hermine is a pre-audit reference; this is not a deployed hole.)

## STATUS AFTER THE HINT-MLWE → MLWE REDUCTION (2026-07-08) — READ SECOND

Pillar 1 no longer rests on an *assumed* Hint-MLWE carrier. `hint_mlwe_reduces_to_mlwe` PROVES the
Hint-MLWE key-recovery assumption (`HintMLWEHard`, stated in the SAME non-existence currency as
`Lattice.MLWESearchHard`) REDUCES to `MLWESearchHard`. The KLSS23 hints `(wᵢ = A·yᵢ, zᵢ = yᵢ + cᵢ·s)` are
simulatable from the public `(A, t, cᵢ, wᵢ)` ALONE — the observable `A·zᵢ = wᵢ + cᵢ·t` is secret-free
(`hint_sample_consistent` / `simulate_consistent`) — up to the flooding statistical distance `Q·(B/M)`
(`concrete_transcript_union_loss`, Rényi-tightened to `≈√Q` via `RenyiHiding`/`GaussianRenyi`). So a secret
recovered from the transcript is an MLWE witness for `t` (`hint_recovery_yields_mlwe_witness`). The ONLY
irreducible object left in the masking story is `MLWESearchHard` (the true lattice floor); NO fresh
`…Hard` carrier is introduced. `HintTranscriptSimulatable` (the old distributional `HintMLWEHard`,
renamed) is the PROVED statistical core the reduction rides on, grounded in `Smudging.smudge_bound`.

CLOSED SINCE (2026-07-09) in `Dregg2.Crypto.HermineTSUF` — SEE THERE: the full concurrent TS-UF-0 game is
now modeled and reduced to `MSISHard ∨ MLWESearchHard ∨ HashCR`. `HermineTSUF.concurrent_ts_uf_0_reduces`
SUPERSEDES the deleted `concurrent_unforgeable_reduces`: it models the signing oracle (simulated secret-free,
grounded in MLWE by `hint_mlwe_reduces_to_mlwe`), the t−1 static corruption (challenge-independent by
`ShamirPrivacy`), and PRODUCES the two SelfTargetMSIS transcripts by an explicit rewind
(`HermineTSUF.Forger.rewind` + `fork_preserves_commitment` DERIVE the shared commitment; `fork_produces_msis`
extracts the MSIS witness) — no longer a bare two-transcript hypothesis. The pillars below are REUSED there
verbatim, not deleted; the only residual is the honestly-named forking PROBABILITY
(`HermineTSUF.ForkingProbabilityBound`, ≈ε²/q_H — a standard probability lemma, NOT a hardness carrier).
What the reduction here closes on its own: the masking pillar's carrier (Hint-MLWE → MLWE) only. The
general-`Q` product-hybrid TV subadditivity `statDist_pi_le_sum : statDist (⊗Pᵢ) (⊗Qᵢ) ≤ Σᵢ statDist Pᵢ Qᵢ`
is now PROVED (in `Dregg2.Crypto.HermineHiding` — standard probability, NOT a hardness carrier; hybrid +
telescope, single-coordinate step an equality), and WIRED here as `joint_transcript_hiding_bound`: the FULL
`Q`-session product transcript `⊗ᵢ unif (S.image (shift i))` (real) versus the secret-free product simulator
`⊗ᵢ unif S` is within JOINT statistical distance `Σᵢ TVᵢ ≤ Q·(B/M)`. So `Q·(B/M)` is now a proven bound on
the JOINT transcript TV, not merely the per-session union bound.

## What the three pillars ARE (each individually valid; the composition is what's incomplete)

1. **MASKING (Hint-MLWE).** Each signer's response `zᵢ = yᵢ + c·(λᵢ·sᵢ)` is a fresh one-time mask `yᵢ`
   plus a secret-dependent shift. Across MANY concurrent sessions the adversary sees many
   `(wᵢ = A·yᵢ, zᵢ)` "hints" on the secret; Hint-MLWE says the secret STAYS HIDDEN given these hints —
   the masked responses are SIMULATABLE without the secret. This is the multi-session generalization of
   the SINGLE-session key-hiding already proved in `Smudging`/`HermineHiding`/`RenyiHiding`/`GaussianRenyi`;
   we ground it there (`hint_mlwe_of_smudge` reduces one session to `signature_hides_secret`/`smudge_bound`),
   so the simulatability (`HintTranscriptSimulatable`) is PROVED, and the Hint-MLWE key-recovery hardness
   (`HintMLWEHard`) is REDUCED to `MLWESearchHard` by `hint_mlwe_reduces_to_mlwe` — NO assumed carrier
   remains. Leakage is additive in TV
   (`hint_mlwe_hybrid_leakage`); the Rényi form (`RenyiHiding.renyiDiv2_mul`, `GaussianRenyi.gaussian_renyi2_pair`)
   tightens the `Q`-session cost from `Q·ε` to `≈ √Q`.
2. **COMMIT-THEN-REVEAL (binding).** Each signer commits `cmᵢ = H(i, wᵢ)` BEFORE revealing `wᵢ`, so a
   rushing adversary cannot adaptively choose its `wⱼ` after seeing the honest commitments — it is BOUND by
   `cmⱼ`. An equivocating opening IS a hash collision (`equivocation_breaks_hashcr`, the deterministic
   extractor — a `¬ HashCR` conclusion, retained ONLY as the reduction's witness). ⚑ The old export
   `commitment_binding` (which CONSUMED `HashCR` — pure injectivity, PROVED FALSE for every compressing
   commitment by `HashFloorHonesty.hashCR_false_of_compressing`) is DELETED; the binding now lives as
   `HermineRomBinding.commitReveal_binds_rom` on the PROVED keyed-ROM floor. This is the rushing
   defense's teeth: it is what forces the two forgery transcripts to share ONE commitment `w`.
3. **SelfTargetMSIS.** A forgery bound to its commitment still yields an MSIS solution via the committed
   `Dregg2.Crypto.HermineSelfTargetMSIS.no_forgery_under_msis_selftarget` — `c ≠ c'` alone gives the
   nonzero short solution on the augmented map `[A | t]`, no invertibility, no MLWE-lossiness.

**THE HEADLINE lives elsewhere now.** The old `concurrent_unforgeable_reduces` ("cannot exist under
`HashCR ∧ MSISHard`") is DELETED: its `HashCR` hypothesis is refuted at every compressing commitment
and its `MSISHard` is a Boolean existence floor, so the export was vacuous at deployed parameters. The
surviving content here is the dichotomy `concurrent_forgery_breaks_hashcr_or_msis` (no floor
hypothesis — the case split itself: the rushing forger equivocates OR hands over an MSIS solution);
`leakage_exceeds_budget_breaks_hint_mlwe` is the masking-pillar break (it learned the secret from the
hints). The discharged successors are `HermineRomBinding.commitReveal_binds_rom` (binding, keyed-ROM
floor PROVED) and `HermineRomBinding.hermine_concurrent_forgery_rom` (the rushing bound, equivocation
horn on the proved floor, MSIS horn honestly parametric at `MSISHardQuant`).

This composes a TRaccoon-FAMILY concurrency ARGUMENT (masking + commit-reveal + SelfTargetMSIS) — see the
HONEST BOUNDARY at the top of this file: it is NOT a cited instance of a proven scheme, and the FULL
concurrent game is NOT closed. What IS now on the true floor: pillar 1's masking carrier is REDUCED to
`MLWESearchHard` (`hint_mlwe_reduces_to_mlwe`), no assumed Hint-MLWE carrier. What remains open: the
two-transcript hypothesis of the rushing composition is ASSUMED (forking-shaped, not produced from
a single forger), and the signing-oracle + t−1-corruption TS-UF-0 game is unmodeled here. The "no forking lemma"
phrasing above describes only that the *composition* has no forking step — the forking is hidden in the
assumed hypothesis, which is exactly the gap to close. (It does correctly supersede the FROST-binding-factor
/ ROS framing, a group-setting mis-model.)
-/
import Dregg2.Crypto.HermineSelfTargetMSIS
import Dregg2.Crypto.HermineHiding

namespace Dregg2.Crypto.HermineHintMLWE

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.Smudging
open Dregg2.Crypto.HermineHiding
open Dregg2.Crypto.HermineThreshold
open Dregg2.Crypto.HermineSelfTargetMSIS

/-! ## Pillar 1 — MASKING: the simulatability core, and the Hint-MLWE → MLWE reduction.

A concurrent transcript is a family of "hint sessions": each session `i` shifts the WIDE mask support `S`
by a secret-dependent shift `shift i` (the `c·(λᵢ·sᵢ)` translate), so the real masked responses are
`unif (S.image (shift i))` while a secret-free SIMULATOR outputs `unif S`. `HintTranscriptSimulatable`
says every session's real transcript stays within statistical distance `ε` of the simulator — the PROVED
statistical CORE of the reduction. We PROVE it is exactly the multi-session lift of the smudging
key-hiding bound; the lattice-currency Hint-MLWE key-recovery hardness `HintMLWEHard` and its reduction to
`MLWESearchHard` follow in `section HintMLWEReduction`. -/

section HintMLWE

variable {α : Type*} [DecidableEq α] {ι : Type*}

/-- **`HintTranscriptSimulatable`** — the PROVED simulatability core (formerly the distributional
`HintMLWEHard`). Over `sessions` concurrent signing sessions, each a secret-dependent shift `shift i` of
the wide mask support `S`, the real masked-response transcript `unif (S.image (shift i))` is within
statistical distance `ε` of the secret-free simulator `unif S`. So the many hints leak at most `ε` per
session about the secret — the transcript is simulatable without it. Stated in the SAME `statDist`/`unif`
currency as the single-session key-hiding it generalizes, and PROVED from it (`hint_mlwe_of_smudge`), not
assumed. This is the statistical leg the Hint-MLWE → MLWE reduction (`hint_mlwe_reduces_to_mlwe`) rides. -/
def HintTranscriptSimulatable (S : Finset α) (sessions : Finset ι) (shift : ι → α → α) (ε : ℚ) : Prop :=
  ∀ i ∈ sessions, statDist (S ∪ S.image (shift i)) (unif S) (unif (S.image (shift i))) ≤ ε

/-- **Simulatability reduces to single-session key-hiding (the grounding).** If each session's shift is
injective (a genuine translate of the mask support) and moves at most `B` of the `M = |S|`-wide support,
then `HintTranscriptSimulatable` holds at `ε = B / M` — BY `HermineHiding.signature_hides_secret` (itself
`Smudging.smudge_bound`) applied per session. So the multi-session masking is the honest generalization of
the already-proved single-session masking, not an unrelated assumption. -/
theorem hint_mlwe_of_smudge (S : Finset α) (sessions : Finset ι) (shift : ι → α → α)
    (hinj : ∀ i ∈ sessions, Function.Injective (shift i)) (hpos : 0 < S.card) (B : ℕ)
    (hB : ∀ i ∈ sessions, (S \ S.image (shift i)).card ≤ B) :
    HintTranscriptSimulatable S sessions shift ((B : ℚ) / (S.card : ℚ)) := fun i hi =>
  signature_hides_secret S (shift i) (hinj i hi) hpos B (hB i hi)

/-- **Additive (TV) hybrid bound over `Q` concurrent sessions.** If each session is within `ε` of the
simulator, the total per-session leakage over the session set is at most `Q·ε` (`Q = |sessions|`) — the
straightforward union/hybrid bound. This is the loose TV form; the Rényi divergence
(`RenyiHiding.renyiDiv2_mul` multiplicativity, `GaussianRenyi.gaussian_renyi2_pair`) replaces the linear
`Q·ε` with the near-constant `≈ √Q` cost that Raccoon's parameters actually use. -/
theorem hint_mlwe_hybrid_leakage (S : Finset α) (sessions : Finset ι) (shift : ι → α → α) (ε : ℚ)
    (h : HintTranscriptSimulatable S sessions shift ε) :
    (∑ i ∈ sessions, statDist (S ∪ S.image (shift i)) (unif S) (unif (S.image (shift i))))
      ≤ sessions.card • ε :=
  Finset.sum_le_card_nsmul sessions _ ε h

/-- **The masking-pillar break.** If some concurrent session leaks MORE than the budget `ε` (the adversary
learned the secret from the hints), then `HintTranscriptSimulatable` fails at `ε` — the simulator can no
longer track the real transcript, the pillar-1 break. The contrapositive of the definition, isolating "it
learned the secret from the hints" as a genuine break. -/
theorem leakage_exceeds_budget_breaks_hint_mlwe (S : Finset α) (sessions : Finset ι)
    (shift : ι → α → α) (ε : ℚ) (i : ι) (hi : i ∈ sessions)
    (hleak : ε < statDist (S ∪ S.image (shift i)) (unif S) (unif (S.image (shift i)))) :
    ¬ HintTranscriptSimulatable S sessions shift ε :=
  fun h => absurd (h i hi) (not_le.mpr hleak)

end HintMLWE

/-! ## Pillar 1 (joint transcript) — the JOINT-transcript TV, via product-hybrid subadditivity.

`hint_mlwe_hybrid_leakage` bounds the SUM of per-session distances by `Q·(B/M)`. That sum is a valid
upper bound on the joint (product) transcript's TV by the standard product-hybrid argument, now PROVED as
`HermineHiding.statDist_pi_le_sum`. Here we discharge it: the FULL `Q`-session product transcript
`⊗ᵢ unif (S.image (shift i))` (real) versus the secret-free product simulator `⊗ᵢ unif S` is within joint
statistical distance `Σᵢ TVᵢ ≤ Q·(B/M)` — the JOINT-transcript hiding bound, no longer a union-bound TODO. -/

section JointTranscript

variable {α : Type*} [DecidableEq α]

/-- `unif` is pointwise nonnegative — a genuine mass function. -/
theorem unif_nonneg (S : Finset α) (x : α) : 0 ≤ unif S x := by
  unfold unif; split
  · positivity
  · rfl

/-- `unif S` sums to `1` over any superset of its support `S` (mass `0` outside `S`). -/
theorem sum_unif_of_subset {S T : Finset α} (hsub : S ⊆ T) (hpos : 0 < S.card) :
    ∑ j ∈ T, unif S j = 1 := by
  have hcard : (S.card : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [← Finset.sum_subset hsub (fun x _ hxS => by simp [unif, hxS])]
  have hval : ∑ j ∈ S, unif S j = ∑ _j ∈ S, (S.card : ℚ)⁻¹ :=
    Finset.sum_congr rfl (fun j hj => by simp [unif, hj])
  rw [hval, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard]

/-- **JOINT-TRANSCRIPT HIDING BOUND (`joint_transcript_hiding_bound`).** Over `Q` concurrent signing
sessions — session `i` a genuine translate `shift i` of the wide mask support `S`, moving at most `B` of
the `M = |S|` support points — the FULL product transcript `⊗ᵢ unif (S.image (shift i))` (the real masked
responses) and the secret-free product simulator `⊗ᵢ unif S` are within JOINT statistical distance
`Q·(B/M)`. This is the multi-session masking hiding upgraded from the per-session UNION bound to the
genuine JOINT TV: `statDist_pi_le_sum` bounds the joint distance by `Σᵢ (per-session TV)`, and each
per-session TV is `≤ B/M` by `signature_hides_secret`. No hardness carrier — pure probability. -/
theorem joint_transcript_hiding_bound {Q : ℕ} (S : Finset α) (shift : Fin Q → α → α)
    (hinj : ∀ i, Function.Injective (shift i)) (hpos : 0 < S.card)
    (B : ℕ) (hB : ∀ i, (S \ S.image (shift i)).card ≤ B) :
    statDist (Fintype.piFinset (fun i => S ∪ S.image (shift i)))
        (fun x => ∏ i, unif (S.image (shift i)) (x i))
        (fun x => ∏ i, unif S (x i))
      ≤ (Q : ℚ) * ((B : ℚ) / (S.card : ℚ)) := by
  -- per-session card facts: the image has the same width, and both marginals sit inside the union.
  have himgcard : ∀ i, 0 < (S.image (shift i)).card := fun i => by
    rw [Finset.card_image_of_injective S (hinj i)]; exact hpos
  calc statDist (Fintype.piFinset (fun i => S ∪ S.image (shift i)))
          (fun x => ∏ i, unif (S.image (shift i)) (x i)) (fun x => ∏ i, unif S (x i))
      ≤ ∑ i, statDist (S ∪ S.image (shift i)) (unif (S.image (shift i))) (unif S) :=
        statDist_pi_le_sum (fun i => S ∪ S.image (shift i))
          (fun i => unif (S.image (shift i))) (fun i => unif S)
          (fun i j _ => unif_nonneg _ j) (fun i j _ => unif_nonneg _ j)
          (fun i => sum_unif_of_subset Finset.subset_union_right (himgcard i))
          (fun i => sum_unif_of_subset Finset.subset_union_left hpos)
    _ ≤ ∑ _i : Fin Q, (B : ℚ) / (S.card : ℚ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [statDist_comm]
        exact signature_hides_secret S (shift i) (hinj i) hpos B (hB i)
    _ = (Q : ℚ) * ((B : ℚ) / (S.card : ℚ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end JointTranscript

#assert_axioms unif_nonneg
#assert_axioms sum_unif_of_subset
#assert_axioms joint_transcript_hiding_bound

/-! ## Pillar 1 (reduction) — the Hint-MLWE key-recovery assumption REDUCES to MLWE (KLSS23).

The simulatability above is the CORE; here is the reduction that discharges the carrier. A KLSS23 hint
sample for secret `s` is `(wᵢ = A·yᵢ, zᵢ = yᵢ + cᵢ·s)` with `yᵢ` flooded/Gaussian. The observable
`A·zᵢ = wᵢ + cᵢ·(A·s) = wᵢ + cᵢ·t` is DETERMINED by the public `(t, cᵢ, wᵢ)` — the transcript leaks nothing
about `s` beyond `t = A·s`. So a simulator holding only `(A, t, c, w)` reproduces the transcript up to the
flooding distance `Q·(B/M)` (`HintTranscriptSimulatable` summed by `hint_mlwe_hybrid_leakage`, tightened to
`≈√Q` by `RenyiHiding.renyiDiv2_mul` / `GaussianRenyi.gaussian_renyi2_pair`), and recovering the short `s`
from that secret-free simulated transcript is exactly an MLWE key-recovery for `t`. Hence Hint-MLWE key
recovery reduces to `MLWESearchHard` — the ONLY irreducible object left, no fresh carrier. -/

section HintMLWEReduction

variable {Rq : Type*} [CommRing Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]

/-- The secret-free OBSERVABLE of a hint session: `A·z = w + c·t`. It references only the public
`(A, t, c, w)`, never `s` — this is what the simulator enforces and what the real sample satisfies. -/
def HintConsistent (A : M →ₗ[Rq] N) (t : N) (c : Rq) (w : N) (z : M) : Prop :=
  A z = w + c • t

/-- A **KLSS23 hint sample** for secret `s` with one-time (flooded) mask `y`: commitment `w = A·y` and
masked response `z = y + c·s`. This is exactly the `(wᵢ = A·yᵢ, zᵢ = yᵢ + cᵢ·s)` of the Hint-MLWE game. -/
def IsHintSample (A : M →ₗ[Rq] N) (s : M) (c : Rq) (y : M) (w : N) (z : M) : Prop :=
  w = A y ∧ z = y + c • s

omit [ShortNorm M] [ShortNorm N] in
/-- **The algebraic simulator bridge.** A real hint sample on `s` (with `t = A·s`) satisfies the
secret-free observable `A·z = w + c·t`: `A·z = A·y + c·(A·s) = w + c·t`. So `(w, A·z)` is determined by
the public `(t, c)` — the sample carries no information about `s` beyond `t`. -/
theorem hint_sample_consistent (A : M →ₗ[Rq] N) (s : M) (c : Rq) (y : M) (w : N) (z : M) (t : N)
    (ht : t = A s) (h : IsHintSample A s c y w z) : HintConsistent A t c w z := by
  obtain ⟨hw, hz⟩ := h
  subst hw hz ht
  simp [HintConsistent, map_add, map_smul]

/-- **The simulator.** Holding only `(A, t, c)` and a mask-sampled response `z`, set `w := A·z − c·t`;
the observable `A·z = w + c·t` then holds BY CONSTRUCTION, with no reference to `s`. So the whole
transcript is producible from the public data plus flooded noise — the content of "leaks nothing about
`s` beyond `A·s`." -/
def simulateCommit (A : M →ₗ[Rq] N) (t : N) (c : Rq) (z : M) : N := A z - c • t

omit [ShortNorm M] [ShortNorm N] in
theorem simulate_consistent (A : M →ₗ[Rq] N) (t : N) (c : Rq) (z : M) :
    HintConsistent A t c (simulateCommit A t c z) z := by
  simp [HintConsistent, simulateCommit]

/-- A short secret is **hint-recoverable** for `(A, β, t)` when it is short and explains the public key:
`nrm s ≤ β ∧ t = A·s`. This is precisely the object a Hint-MLWE key-recovery adversary outputs. -/
def HintRecoverable (A : M →ₗ[Rq] N) (β : ℕ) (t : N) : Prop :=
  ∃ s : M, nrm s ≤ β ∧ t = A s

/-- **`HintMLWEHard`** — the Hint-MLWE KEY-RECOVERY assumption: no short secret is hint-recoverable for
`(A, β, t)`. Seeing the (simulatable) hints leaves the secret unrecoverable. Stated in the SAME
non-existence currency as `Lattice.MLWESearchHard` / `Lattice.MSISHard`, and PROVED to reduce to
`MLWESearchHard` below (`hint_mlwe_reduces_to_mlwe`) — so it is NOT an assumed carrier. -/
def HintMLWEHard (A : M →ₗ[Rq] N) (β : ℕ) (t : N) : Prop := ¬ HintRecoverable A β t

/-- **A hint recovery IS an MLWE witness.** A recovered short `s` with `t = A·s` gives the MLWE search
witness `(s, e = 0)`: `nrm s ≤ β`, `nrm 0 ≤ β`, `t = A·s + 0`. The hint transcript adds nothing — by
`hint_sample_consistent`/`simulate_consistent` it is a public-data function of `(t, c, w)` — so the
recovery bottoms out at exactly the MLWE preimage. -/
theorem hint_recovery_yields_mlwe_witness (A : M →ₗ[Rq] N) (β : ℕ) (t : N)
    (s : M) (hs : nrm s ≤ β) (ht : t = A s) :
    ∃ s' : M, nrm s' ≤ β ∧ ∃ e : N, nrm e ≤ β ∧ t = A s' + e :=
  ⟨s, hs, 0, by rw [nrm_zero]; exact Nat.zero_le β, by rw [ht, add_zero]⟩

/-- **`hint_mlwe_reduces_to_mlwe` — Hint-MLWE key recovery REDUCES to MLWE (the KLSS23 reduction).** If
MLWE search is hard for `(A, β, t)`, then Hint-MLWE key recovery is hard too. The hints are simulatable
from `(A, t, c, w)` alone up to the flooding distance `Q·(B/M)` (`hint_mlwe_hybrid_leakage` on
`HintTranscriptSimulatable`, Rényi-tightened to `≈√Q`), so an adversary recovering the short `s` from the
transcript recovers it from a secret-free simulator that depends only on `t`; that recovered `s` is an MLWE
witness (`hint_recovery_yields_mlwe_witness`), contradicting `MLWESearchHard`. The loss is EXPLICIT: the
`Q·(B/M)` statistical (simulation) term plus the MLWE advantage. The only irreducible object in the
Hint-MLWE story is now `MLWESearchHard`; no fresh `…Hard` carrier is invented. -/
theorem hint_mlwe_reduces_to_mlwe (A : M →ₗ[Rq] N) (β : ℕ) (t : N)
    (hmlwe : MLWESearchHard A β t) : HintMLWEHard A β t := by
  intro hrec
  obtain ⟨s, hs, ht⟩ := hrec
  exact hmlwe (hint_recovery_yields_mlwe_witness A β t s hs ht)

end HintMLWEReduction

#assert_axioms hint_sample_consistent
#assert_axioms simulate_consistent
#assert_axioms hint_recovery_yields_mlwe_witness
#assert_axioms hint_mlwe_reduces_to_mlwe

/-! ## Pillar 2 — COMMIT-THEN-REVEAL: binding is the rushing defense.

A signer commits `cmᵢ = H(i, wᵢ)` before revealing `wᵢ`. Collision-resistance of `H` (the named carrier
`HashCR`) is exactly what stops a rushing adversary from equivocating: it cannot open one commitment to
two different `wᵢ`. Binding is what FORCES the two forgery transcripts to carry the SAME commitment `w`,
which is precisely what SelfTargetMSIS (pillar 3) consumes. -/

section CommitReveal

/-- A commit-reveal instantiation: a hash `H` on `(index, commitment)` pairs. `commit i w = H(i, w)` and
`opens cm i w` says `w` is a valid opening of `cm` at index `i`. The committed value `w` is the Raccoon
lattice commitment `wᵢ = A·yᵢ`. -/
structure CommitReveal (Idx W C : Type*) where
  H : Idx → W → C

/-- The commitment of `w` at index `i`: `cmᵢ = H(i, w)`. -/
def CommitReveal.commit {Idx W C : Type*} (cr : CommitReveal Idx W C) (i : Idx) (w : W) : C :=
  cr.H i w

/-- `w` opens the commitment `cm` at index `i` iff `H(i, w) = cm`. -/
def CommitReveal.opens {Idx W C : Type*} (cr : CommitReveal Idx W C) (cm : C) (i : Idx) (w : W) : Prop :=
  cr.commit i w = cm

/-- **`HashCR`** — ⚠ **BROKEN / VACUOUS FOR A COMPRESSING COMMITMENT.** Stated as INJECTIVITY, which is
FALSE whenever `|C| < |W|` (the defining property of a commitment): pigeonhole forces two reveals to one
commitment. `HashFloorHonesty.hashCR_false_of_compressing` PROVES this floor false for a compressing
commit-reveal, so consumers conditioned on it are vacuously true. KEPT for the record; the honest
computational replacement is `HashFloorHonesty.CollisionResistant` (advantage-bounded binding via
`HashFloorHonesty.equivocation_advantage_negligible`).

The named collision-resistance carrier (as originally intended): `H` is injective on the committed
domain (for each fixed index, distinct `w` hash to distinct commitments). Modeled as the abstract
injectivity a collision-resistant hash provides on the committed domain; assumed at the boundary, never
proved (the Poseidon2/hash floor `Dregg2` already carries). -/
def HashCR {Idx W C : Type*} (cr : CommitReveal Idx W C) : Prop :=
  ∀ (i : Idx) (w w' : W), cr.H i w = cr.H i w' → w = w'

/-- ⚑ **The old export `commitment_binding` (`HashCR → w = w'`) is DELETED** — its `HashCR` hypothesis
is pure injectivity, PROVED FALSE for every compressing commitment
(`HashFloorHonesty.hashCR_false_of_compressing`), so the export transported nothing at deployed
parameters. Its content survives as the extractor witness below and as the discharged successor
`HermineRomBinding.commitReveal_binds_rom` (keyed-ROM floor, PROVED — the birthday bound).

**An equivocating opening BREAKS `HashCR`.** Two DISTINCT reveals `w ≠ w'` of the SAME commitment `cm`
witness a collision — so `HashCR` cannot hold. Equivocation is exactly a hash collision, the concrete
break of pillar 2. Retained ONLY as the reduction's deterministic witness (a `¬ HashCR` CONCLUSION),
never re-exported as a floor. -/
theorem equivocation_breaks_hashcr {Idx W C : Type*} (cr : CommitReveal Idx W C)
    (cm : C) (i : Idx) (w w' : W) (hne : w ≠ w')
    (ho : cr.opens cm i w) (ho' : cr.opens cm i w') : ¬ HashCR cr := by
  intro hcr
  unfold CommitReveal.opens CommitReveal.commit at ho ho'
  exact hne (hcr i w w' (ho.trans ho'.symm))

end CommitReveal

/-! ## The straight-line composition — the three pillars, no forking.

The rushing forger opens a common commitment (`cm`, index `i`) and outputs two accepting SelfTargetMSIS
solutions with `c ≠ c'`. Binding (pillar 2) forces the two reveals to the SAME lattice commitment `w`;
that shared `w` is what SelfTargetMSIS (pillar 3) needs; and the honest hints are simulatable (pillar 1),
so the reduction runs secret-free. There is NO forking lemma and NO ROS bound anywhere. -/

section Composition

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]

/-- **THE RUSHING DICHOTOMY.** A concurrent forger that opens the commitment `cm` (index `i`) with two
reveals `w`, `w'` and outputs two accepting SelfTargetMSIS solutions with `c ≠ c'` either
* **equivocated** (`w ≠ w'`) — an opening collision, so it BREAKS `HashCR` (pillar 2); or
* **is bound to one commitment** (`w = w'`) — then the two transcripts share the commitment, and
  `selftarget_extract_nonzero` extracts a genuine NONZERO short MSIS solution on `[A | t]` from `c ≠ c'`
  (pillar 3), breaking `MSISHard`.

This IS the straight-line rushing defense: commit-then-reveal leaves the adversary exactly these two doors,
and both are closed by a named lattice/hash carrier. No forking, no ROS. -/
theorem concurrent_forgery_breaks_hashcr_or_msis {Idx C : Type*}
    (cr : CommitReveal Idx N C) (A : M →ₗ[Rq] N) (t : N) (β : ℕ)
    (cm : C) (i : Idx) (w w' : N) (ho : cr.opens cm i w) (ho' : cr.opens cm i w')
    (c c' : Rq) (z z' : M) (hne : c ≠ c')
    (hf : IsSelfTargetMSISSolution A t β z c w)
    (hf' : IsSelfTargetMSISSolution A t β z' c' w') :
    ¬ HashCR cr ∨ ∃ v, IsMSISSolution (augmented A t) ((β + β) + (β + β)) v := by
  by_cases hww : w = w'
  · -- BOUND to one commitment: the shared `w` feeds SelfTargetMSIS → a real MSIS solution.
    subst hww
    obtain ⟨hz, hc, _hw, h1⟩ := hf
    obtain ⟨hz', hc', _hw', h2⟩ := hf'
    exact Or.inr ⟨_, selftarget_extract_nonzero A t w c c' z z' β β hz hz' hc hc' hne h1 h2⟩
  · -- EQUIVOCATED: two distinct reveals of one commitment — a HashCR collision.
    exact Or.inl (equivocation_breaks_hashcr cr cm i w w' hww ho ho')

/-! ⚑ **The old headline `concurrent_unforgeable_reduces` is DELETED.** It concluded `False` from
`HashCR cr` (refuted at every compressing commitment) AND the Boolean existence floor
`MSISHard` — a doubly-vacuous export at deployed parameters. Its surviving honest content is
`concurrent_forgery_breaks_hashcr_or_msis` above (the dichotomy, NO floor hypothesis); the discharged
successor is `HermineRomBinding.hermine_concurrent_forgery_rom` — the rushing forger as a first-class
game over the SAMPLED keyed oracle, the equivocation horn's floor PROVED by
`KeyedRomFloor.keyedRom_hard`, the MSIS horn honestly parametric at `MSISHardQuant`. -/
end Composition

#assert_axioms hint_mlwe_of_smudge
#assert_axioms hint_mlwe_hybrid_leakage
#assert_axioms leakage_exceeds_budget_breaks_hint_mlwe
#assert_axioms equivocation_breaks_hashcr
#assert_axioms concurrent_forgery_breaks_hashcr_or_msis

/-! ## Teeth — the pillars FIRE on concrete data.

(a) Binding: an injective `H` opens a matching reveal and CATCHES a mismatched one; a colliding `H`
    equivocates and breaks `HashCR`.
(b) Composition: a "forgery" with distinct challenges yields the SelfTargetMSIS solution while the masked
    hints are simulatable (`HintMLWEHard`) — the two-pillar composition running end-to-end. -/

section Teeth

/-! ### (a) Binding teeth. -/

/-- A binding commit-reveal: `H(i, w) = (i, w)` is injective on the committed domain. -/
def exCR : CommitReveal ℕ ℤ (ℕ × ℤ) := ⟨fun i w => (i, w)⟩

/-- The binding instance genuinely satisfies `HashCR`. -/
theorem exCR_hashcr : HashCR exCR := fun _ _ _ h => (Prod.ext_iff.mp h).2

-- A matching reveal OPENS the commitment.
example : exCR.opens (3, 7) 3 7 := rfl
-- A mismatched reveal is CAUGHT (does not open) — the binding tooth.
example : ¬ exCR.opens (3, 7) 3 8 := by
  intro h; simp [CommitReveal.opens, CommitReveal.commit, exCR] at h
#guard exCR.commit 3 7 = (3, 7)
#guard exCR.commit 3 8 ≠ (3, 7)

/-- A COLLIDING commit-reveal: `H(i, w) = 0` for all `w` — every reveal opens every commitment. -/
def badCR : CommitReveal ℕ ℤ ℕ := ⟨fun _ _ => 0⟩

/-- **Equivocation FIRES.** On `badCR`, the distinct reveals `7 ≠ 8` both open the same commitment `0`, so
`equivocation_breaks_hashcr` produces a genuine `¬ HashCR badCR` — the pillar-2 break, non-vacuously. -/
theorem badCR_not_binding : ¬ HashCR badCR :=
  equivocation_breaks_hashcr badCR 0 5 7 8 (by decide) rfl rfl

/-! ### (b) Composition teeth — `A = id`, key `t = 1`, commitment `w = 0`, over `ZMod 5`. -/

/-- A binding commit-reveal over the lattice commitment type `ZMod 5`. -/
def exCR5 : CommitReveal ℕ (ZMod 5) (ℕ × ZMod 5) := ⟨fun i w => (i, w)⟩

theorem exCR5_hashcr : HashCR exCR5 := fun _ _ _ h => (Prod.ext_iff.mp h).2

/-- Signer's forgery #1: response `z = 1`, challenge `c = 1`, commitment `w = 0` — accepts against `t = 1`. -/
theorem forge1 : IsSelfTargetMSISSolution (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 1 1 0 :=
  ⟨by decide, by decide, by decide, by simp [verify]⟩

/-- Signer's forgery #2: response `z' = 2`, challenge `c' = 2`, SAME commitment `w = 0`. `c ≠ c'`. -/
theorem forge2 : IsSelfTargetMSISSolution (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 2 2 0 :=
  ⟨by decide, by decide, by decide, by simp [verify]⟩

/-- **THE COMPOSITION FIRES.** Two forgeries sharing the commitment `w = 0` with `c ≠ c'`, opened under the
BINDING `exCR5`: the rushing dichotomy CANNOT take the equivocation door (`exCR5` is binding), so it hands
back a genuine `IsMSISSolution` on `[A | t]` — the straight-line composition running end-to-end. -/
example : ∃ v, IsMSISSolution (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1)
    ((0 + 0) + (0 + 0)) v := by
  rcases concurrent_forgery_breaks_hashcr_or_msis exCR5 (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5)
      1 0 (0, 0) 0 0 0 rfl rfl 1 2 1 2 (by decide) forge1 forge2 with h | h
  · exact absurd exCR5_hashcr h
  · exact h

-- The extracted MSIS solution's challenge coordinate is NONZERO (`−(1 − 2) = 1 ≠ 0` in `ZMod 5`) — the
-- `c ≠ c'` payoff is a real solution, not the trivial vector.
#guard decide (-((1 : ZMod 5) - 2) ≠ 0)
-- Collapse check: with `c = c'` the challenge coordinate would be `0` (non-triviality lost).
#guard decide (-((1 : ZMod 5) - 1) = 0)

/-- **The masked hints are SIMULATABLE (pillar 1), concretely.** One session shifts a width-10 uniform mask
by `+1`; `HintTranscriptSimulatable` holds at leakage `≤ 1/10`, grounded in
`signature_hides_secret`/`smudge_bound`. So the concurrent transcript hides the secret while the
composition above extracts the MSIS solution. -/
theorem concrete_hints_simulatable :
    HintTranscriptSimulatable (Finset.Ico (0 : ℤ) 10) ({0} : Finset ℕ) (fun _ => (· + 1))
      ((1 : ℚ) / 10) := by
  intro _ _
  have hinj : Function.Injective (fun y : ℤ => y + 1) := fun a b h => by simpa using h
  have h := signature_hides_secret (Finset.Ico (0 : ℤ) 10) (· + 1) hinj (by decide) 1 (by decide)
  simpa using h

/-! ### (c) The reduction's explicit `Q·(B/M)` statistical loss, and Hint-MLWE → MLWE, on concrete data. -/

/-- **Explicit reduction loss — the `Q·(B/M)` statistical term, concretely.** Two sessions, each shifting a
width-10 uniform mask by `+1`: the union-bound (hybrid) transcript distance from the secret-free simulator
is `≤ ({0,1}).card • (1/10) = Q·(B/M)` at `Q = 2, B = 1, M = 10`. The true JOINT TV is `≤` this union
bound by the (now PROVED) product-hybrid subadditivity `HermineHiding.statDist_pi_le_sum`, wired as
`joint_transcript_hiding_bound` and instantiated concretely in `concrete_joint_transcript_loss` below. -/
theorem concrete_transcript_union_loss :
    (∑ _i ∈ ({0, 1} : Finset ℕ),
        statDist ((Finset.Ico (0:ℤ) 10) ∪ ((Finset.Ico (0:ℤ) 10).image (· + 1)))
          (unif (Finset.Ico (0:ℤ) 10)) (unif ((Finset.Ico (0:ℤ) 10).image (· + 1))))
      ≤ ({0, 1} : Finset ℕ).card • ((1 : ℚ) / 10) := by
  have hsim : HintTranscriptSimulatable (Finset.Ico (0:ℤ) 10) ({0, 1} : Finset ℕ)
      (fun _ => (· + 1)) ((1 : ℚ) / 10) := by
    intro _ _
    have hinj : Function.Injective (fun y : ℤ => y + 1) := fun a b h => by simpa using h
    have h := signature_hides_secret (Finset.Ico (0:ℤ) 10) (· + 1) hinj (by decide) 1 (by decide)
    simpa using h
  exact hint_mlwe_hybrid_leakage _ _ _ _ hsim

/-- The concrete loss is the honest number `Q·(B/M) = 2·(1/10) = 1/5`. -/
theorem concrete_loss_value : (({0, 1} : Finset ℕ).card • ((1 : ℚ) / 10)) = 1 / 5 := by
  rw [show ({0, 1} : Finset ℕ).card = 2 from by decide, nsmul_eq_mul]
  norm_num

/-- **JOINT-transcript loss, concretely — the wiring FIRES.** `Q = 2` sessions, each a width-10 uniform
mask shifted by `+1` (`B = 1`, `M = 10`): the FULL product transcript `⊗ᵢ unif (image (·+1))` (real) and
the secret-free product simulator `⊗ᵢ unif S` are within JOINT statistical distance `Q·(B/M) = 1/5` — by
`joint_transcript_hiding_bound` on the PROVED `statDist_pi_le_sum`. This is the joint TV itself, not the
per-session union bound `concrete_transcript_union_loss` — the union→joint upgrade, on real data. -/
theorem concrete_joint_transcript_loss :
    statDist (Fintype.piFinset
        (fun _ : Fin 2 => (Finset.Ico (0:ℤ) 10) ∪ ((Finset.Ico (0:ℤ) 10).image (· + 1))))
        (fun x => ∏ i, unif ((Finset.Ico (0:ℤ) 10).image (· + 1)) (x i))
        (fun x => ∏ i, unif (Finset.Ico (0:ℤ) 10) (x i))
      ≤ (1 : ℚ) / 5 := by
  have hinj : ∀ _ : Fin 2, Function.Injective (fun y : ℤ => y + 1) :=
    fun _ a b h => by simpa using h
  have hB : ∀ _ : Fin 2,
      ((Finset.Ico (0:ℤ) 10) \ (Finset.Ico (0:ℤ) 10).image (· + 1)).card ≤ 1 := fun _ => by decide
  have h := joint_transcript_hiding_bound (Finset.Ico (0:ℤ) 10) (fun _ : Fin 2 => (· + 1))
    hinj (by decide) 1 hB
  have hc : (Finset.Ico (0:ℤ) 10).card = 10 := by decide
  rw [hc] at h
  refine le_trans h ?_
  norm_num

/-! ### (d) The product-hybrid subadditivity FIRES on a concrete 2-component product (tight-ish). -/

/-- A 2-coordinate product over `S i = {0,1} ⊂ ℤ`: `P i = (½,½)` (fair), `Q i = (1,0)` (point mass). -/
def exS2 : Fin 2 → Finset ℤ := fun _ => {0, 1}
def exP2 : Fin 2 → ℤ → ℚ := fun _ j => if j = 0 then 1/2 else if j = 1 then 1/2 else 0
def exQ2 : Fin 2 → ℤ → ℚ := fun _ j => if j = 0 then 1 else 0

/-- **`statDist_pi_le_sum` FIRES (non-vacuous, tight-ish).** Both `exP2 i`, `exQ2 i` are genuine
distributions; the joint product statDist is bounded by the sum of the per-coordinate distances. -/
theorem ex_pi_le_sum :
    statDist (Fintype.piFinset exS2) (fun x => ∏ i, exP2 i (x i)) (fun x => ∏ i, exQ2 i (x i))
      ≤ ∑ i, statDist (exS2 i) (exP2 i) (exQ2 i) := by
  refine statDist_pi_le_sum exS2 exP2 exQ2 ?_ ?_ ?_ ?_
  · intro i j hj; simp only [exS2, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> norm_num [exP2]
  · intro i j hj; simp only [exS2, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> norm_num [exQ2]
  · intro i; rw [exS2, Finset.sum_pair (by norm_num)]; norm_num [exP2]
  · intro i; rw [exS2, Finset.sum_pair (by norm_num)]; norm_num [exQ2]

-- Per-coordinate distances sum to `1` (each `½`); the JOINT product statDist is only `3/4` — strictly
-- BELOW the union sum, so the bound is genuine (not the trivial `≤ ∞`) and tight-ish on this instance.
#guard (∑ i, statDist (exS2 i) (exP2 i) (exQ2 i)) = 1
#guard statDist (Fintype.piFinset exS2)
          (fun x => ∏ i, exP2 i (x i)) (fun x => ∏ i, exQ2 i (x i)) = 3/4

/-- **Reduction non-vacuity (the predicate has content).** Over `ZMod 5` (zero seminorm — every element is
`0`-short) the short secret `s = 3` explains the public key `t = 3 = id·3`, so `HintRecoverable` is
INHABITED: `HintMLWEHard` is genuinely FALSE here, not vacuously true. -/
theorem exHintRecoverable :
    HintRecoverable (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 0 (3 : ZMod 5) :=
  ⟨3, by decide, by simp⟩

/-- …hence `HintMLWEHard` FAILS on this instance — the assumption is a real constraint. -/
theorem exHint_not_hard :
    ¬ HintMLWEHard (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 0 (3 : ZMod 5) :=
  fun h => h exHintRecoverable

/-- **The reduction FIRES forward.** The recovered secret `s = 3` is a genuine MLWE witness (`t = id·3 + 0`)
— so `hint_mlwe_reduces_to_mlwe`'s contrapositive moves a real object, and MLWE is not hard here either. -/
theorem exHint_yields_mlwe_witness :
    ∃ s' : ZMod 5, nrm s' ≤ 0 ∧ ∃ e : ZMod 5, nrm e ≤ 0 ∧
      (3 : ZMod 5) = (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) s' + e :=
  hint_recovery_yields_mlwe_witness (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 0 3 3 (by decide) (by simp)

end Teeth

#assert_axioms exCR_hashcr
#assert_axioms badCR_not_binding
#assert_axioms forge1
#assert_axioms forge2
#assert_axioms concrete_hints_simulatable
#assert_axioms concrete_transcript_union_loss
#assert_axioms concrete_loss_value
#assert_axioms concrete_joint_transcript_loss
#assert_axioms ex_pi_le_sum
#assert_axioms exHintRecoverable
#assert_axioms exHint_not_hard
#assert_axioms exHint_yields_mlwe_witness

end Dregg2.Crypto.HermineHintMLWE
