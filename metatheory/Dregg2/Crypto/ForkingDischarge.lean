/-
# `Dregg2.Crypto.ForkingDischarge` — RETIRING the deterministic forking-extractor hypothesis.

The crypto tree's protocol layer rests on ONE keystone, `HybridCombiner.hybrid_secure_if_either_floor`,
and that keystone TAKES two un-discharged reduction hypotheses:

  * `dlFork  : Forgery Cl pkc Q → SchnorrCurveField.DLSolver C G`
  * `msisFork : Forgery Pq pkp Q → ∃ w c c' z z', c ≠ c' ∧ IsSelfTargetMSISSolution … ∧ …`

and so do `pq_euf_cma_grounded_in_msis`, `DreggPqRefinement.dregg_pq_is_eufcma_under_msis` (the DEPLOYED
refinement) and `TurnAuthSignature.ForkingExtractor` — passed straight through by every protocol consumer
(`CapabilityChain`, `DowngradeResistance`, `RevocationSoundness`, `TurnSoundness`, `BlocklaceSafety`,
`ConsensusSafety`, `LightClientSoundness`, `WireAke`, `DualSchemeAuthority`, `UcSignature`). The prose in
each cites "the PROVED forking machinery of `HermineTSUF`", but `#assert_axioms` never sees a hypothesis:
the citation was never wired.

## Why the deterministic shape cannot be discharged — proved, not asserted

`HybridCombiner.Forgery S pk Q = ∃ m σ, ¬ Q m ∧ S.verify pk m σ` is a BARE existential witness: ONE
message, ONE signature, no algorithm, nothing to rewind. Rewinding is intrinsically probabilistic, and
`no_forked_pair_of_hits_le_one` PROVES the obstruction in the tree's own counting model: an adversary with
at most ONE accepting challenge per prefix has `forkProb = 0` and admits NO two-transcript event, so no
extraction is available at any hardness floor. A deterministic `Forgery` is exactly that adversary. The
hypothesis `fork : Forgery S pk Q → …` is therefore not merely un-discharged; in the stated model it is
un-DISCHARGEABLE. Fabricating a deterministic extractor would be laundering.

## What this file does instead — the bridge, and the honest residual

**§1 THE BRIDGE.** `ProbGameForger S pk Q A t β Ω` is the missing object: a probabilistic EUF-CMA adversary
in the finite forking model — a prefix world `Ω` fixing the ML-DSA commitment `comm ω` BEFORE the
Fiat–Shamir challenge, a response `resp ω c`, an accept predicate `acc`, and TWO soundness fields tying it
to both worlds at once:

  * `acc_wins`  — an accepting outcome IS an EUF-CMA win (a genuine `HybridCombiner.Forgery`);  ← GAME side
  * `acc_sound` — an accepting outcome IS an `IsSelfTargetMSISSolution` on the shared `comm ω`. ← FORKING side

`toProbForger` is the map into `HermineTSUF.ProbForger` (it is exactly the `acc_sound` field), so the whole
PROVED forking apparatus applies verbatim.

**§2 THE FORKING, DISCHARGED.** `forkPair_of_advantage` DERIVES the `msisFork` hypothesis' EXACT conclusion —
`∃ w c c' z z', c ≠ c' ∧ IsSelfTargetMSISSolution A t β z c w ∧ IsSelfTargetMSISSolution A t β z' c' w` —
from an advantage exceeding the challenge-guessing floor `1/|Rq|`, through `forkProb_ge_advantage` (the
PROVED Cauchy–Schwarz counting inequality), `forkProb_pos_of_advantage` and
`exists_forked_pair_of_forkProb_pos`. No hypothesis. `pq_advantage_bounded_under_msis` is the keystone in
the honest, advantage-bounded form: under `MSISHard`, EVERY probabilistic game forger's advantage is at most
`1/|Rq|` — the guessing floor, nothing more.

**§3 THE ONE RESIDUAL — `ForgeryRealizable`.** To keep the ~18 consumers' DETERMINISTIC conclusion
(`EufCma := ¬ Forgery`) we still need to cross from the bare `∃`-witness to an adversary. That crossing is
`ForgeryRealizable`: *if a forgery exists, it is produced by a probabilistic forking adversary of noticeable
advantage.* This is a MODELLING statement (the abstract `∃` is realized by an algorithm) — it assumes
NOTHING cryptographic. Everything cryptographic — the rewind, the shared commitment, the distinct
challenges, the MSIS/DL extraction — is PROVED downstream of it. Compare what it replaces: `msisFork`
assumed the entire extraction outright. `fork_of_realizable` derives `msisFork` from `ForgeryRealizable` +
the proved bound, so every consumer that took `msisFork` can now be fed a PROOF TERM.

**§4 THE CLASSICAL LEG.** `ProbSchnorrForger` is the mirror over the scalar field. `SchnorrEufCma`'s
`SchnorrForgeryFamily` carries `accepts_rewind` as an ASSUMED FIELD — the second transcript, hypothesized.
Here it is DERIVED: `prob_schnorr_yields_dlog` obtains the fork from the advantage, so
`no_prob_schnorr_family_under_dl` needs no assumed rewind. The floor is `SchnorrEufCma.SchnorrDLHardF`, the
field-scalar discrete-log assumption already in the tree.

**§5 THE KEYSTONES, RESTATED.** `hybrid_secure_if_either_floor_discharged` — `EufCma (hybrid Cl Pq)` under
`SchnorrDLHardF ∨ MSISHard`, with NO `dlFork` and NO `msisFork`; and
`dregg_pq_is_eufcma_under_msis_discharged` — the DEPLOYED `dregg-pq` ML-DSA refinement on `MSISHard` alone.

**§6 THE QUANTITATIVE KEYSTONE.** `GameForkingFamily` welds the game predicate to
`ProbCrypto.ForkingFamily`, so `game_forger_negl_under_msis_quant` gives the ensemble-level statement the
quant track already proves: `MSISHardQuant` + a growing challenge space ⟹ the game forger's advantage
ENSEMBLE is negligible.

**§7 TEETH.** The obstruction is proved (`no_forked_pair_of_hits_le_one`); the derived fork FIRES on a
concrete `ZMod 5` adversary of advantage `2/5 > 1/5`; and `keystone_msis_floor_load_bearing` shows the
discharged keystone is NON-VACUOUS and its floor LOAD-BEARING — `brokenToy` verifies everything (so `EufCma`
is FALSE) and our realizability bridge HOLDS for it, hence the keystone FORCES `¬ MSISHard` on the toy
instance, which is indeed easy. The floor is exactly what carries the conclusion.

`#assert_all_clean` (⊆ `{propext, Classical.choice, Quot.sound}`).
-/
import Dregg2.Crypto.ProbCrypto
import Dregg2.Crypto.SchnorrEufCma
import Dregg2.Crypto.DreggPqRefinement
import Dregg2.Tactics

namespace Dregg2.Crypto.ForkingDischarge

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.HermineTSUF
open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.ProbCrypto
open Dregg2.Crypto.ConcreteSecurity

/-! ## §0 — The obstruction, PROVED: a single-transcript adversary cannot be forked.

Before building anything, we prove why the deterministic shape is the wrong one. In the tree's own finite
counting model, an adversary with at most ONE accepting challenge per prefix world admits NO
distinct-challenge accepting pair — so `forkProb = 0` and there is nothing to extract, at any floor. A
deterministic `Forgery` (one message, one signature) IS such an adversary. This is the formal content of
"rewinding is intrinsically probabilistic". -/

section Obstruction

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq] [Fintype Rq] [DecidableEq Rq]
variable {Ω : Type*} [Fintype Ω]

/-- **THE OBSTRUCTION.** If the adversary accepts on at most ONE challenge per prefix world, then NO
forking event exists: there is no prefix carrying two DISTINCT accepting challenges. A single deterministic
transcript is exactly `hits ≤ 1`, so a deterministic forgery yields no forked pair — and hence no MSIS/DL
extraction — no matter how hard the underlying problem is. The `fork` hypothesis cannot be discharged in
the deterministic shape; it must be RESTATED. -/
theorem no_forked_pair_of_hits_le_one (acc : Ω → Rq → Bool) (h : ∀ ω, hits acc ω ≤ 1) :
    ¬ ∃ (ω : Ω) (c c' : Rq), c ≠ c' ∧ acc ω c = true ∧ acc ω c' = true := by
  rintro ⟨ω, c, c', hne, ha, ha'⟩
  have hsub : ({c, c'} : Finset Rq) ⊆ acceptSet acc ω := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [acceptSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl
    · exact ha
    · exact ha'
  have hpair : ({c, c'} : Finset Rq).card = 2 := by
    rw [Finset.card_pair hne]
  have hcard : 2 ≤ (acceptSet acc ω).card := by
    have hle := Finset.card_le_card hsub
    rwa [hpair] at hle
  have := h ω
  unfold hits at this
  omega

/-- The probability-level form: a single-transcript adversary has fork probability EXACTLY zero — the
rewind never yields two distinct-challenge transcripts, so `prob_forger_forkProb_yields_msis` has nothing
to consume. -/
theorem forkProb_eq_zero_of_hits_le_one (acc : Ω → Rq → Bool) (h : ∀ ω, hits acc ω ≤ 1) :
    forkProb acc = 0 := by
  unfold forkProb
  have hz : ∀ ω : Ω, ((forkPairs acc ω).card : ℚ) = 0 := by
    intro ω
    rw [forkPairs_card]
    have := h ω
    interval_cases hh : hits acc ω <;> simp
  rw [Finset.sum_congr rfl (fun ω _ => hz ω)]
  simp

/-- A positive advantage PRODUCES an accepting outcome — the elementary counting step used to read a
`Forgery` back out of a probabilistic adversary. -/
theorem exists_acc_of_advantage_pos (acc : Ω → Rq → Bool) (h : 0 < advantage acc) :
    ∃ (ω : Ω) (c : Rq), acc ω c = true := by
  by_contra hcon
  push_neg at hcon
  have hz : ∀ ω : Ω, (hits acc ω : ℚ) = 0 := by
    intro ω
    have hempty : acceptSet acc ω = ∅ := by
      rw [acceptSet, Finset.filter_eq_empty_iff]
      intro c _
      exact hcon ω c
    simp [hits, hempty]
  have hsum : (∑ ω : Ω, (hits acc ω : ℚ)) = 0 := Finset.sum_eq_zero (fun ω _ => hz ω)
  unfold advantage at h
  rw [hsum] at h
  simp at h

end Obstruction

/-! ## §1 — THE BRIDGE: an EUF-CMA game adversary, in the forking model.

`ProbGameForger` is the object `HybridCombiner.Forgery` lacked. It lives in BOTH worlds at once: its
acceptance is an EUF-CMA win (`acc_wins`, so it produces genuine `Forgery` witnesses) AND an ML-DSA
verification equation (`acc_sound`, so it is a `HermineTSUF.ProbForger`). The map `toProbForger` is the
bridge — quite literally the `acc_sound` field — and it makes the PROVED forking bound apply to the GAME. -/

section PqBridge

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq] [Fintype Rq] [DecidableEq Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
variable {Ω : Type*} [Fintype Ω]
variable {SK PK Msg Sig : Type*}

/-- **THE GAME↔FORKING BRIDGE OBJECT.** A probabilistic EUF-CMA adversary against `S` at public key `pk`
with signing transcript `Q`, presented in the finite forking model of `HermineTSUF`:

* `Ω` — the prefix world: the adversary's coins ⊕ the random-oracle answers STRICTLY BELOW its fixed
  forgery-challenge index. This is what fixes the commitment before the challenge is drawn.
* `comm ω` — the ML-DSA commitment `w`, a function of the prefix ALONE (so the two rewound runs share it).
* `resp ω c` — the response `z`.
* `out ω c` — the candidate forgery `(m, σ)` the adversary submits to the game.
* `acc ω c` — the accept predicate: the forger's win event.

and the two soundness fields, which are what make it a bridge:

* `acc_wins` — **the GAME leg**: an accepting outcome IS an EUF-CMA win, a fresh message with a verifying
  signature. So the adversary genuinely produces `HybridCombiner.Forgery` witnesses.
* `acc_sound` — **the FORKING leg**: an accepting outcome IS a genuine `IsSelfTargetMSISSolution` on the
  prefix-fixed commitment `comm ω` with challenge `c` (the ML-DSA verification equation, exactly the shape
  `HermineSelfTargetMSIS.selftarget_extract_nonzero` consumes).

Nothing here is a hardness assumption: both fields are properties a CONCRETE scheme's verifier satisfies. -/
structure ProbGameForger (S : SigScheme SK PK Msg Sig) (pk : PK) (Q : Msg → Prop)
    (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (Ω : Type*) [Fintype Ω] where
  /-- The candidate forgery `(m, σ)` submitted to the EUF-CMA game. -/
  out : Ω → Rq → Msg × Sig
  /-- The ML-DSA commitment `w`, fixed by the prefix world BEFORE the fork challenge. -/
  comm : Ω → N
  /-- The response `z`, a function of prefix and challenge. -/
  resp : Ω → Rq → M
  /-- The forger's accept (win) predicate. -/
  acc : Ω → Rq → Bool
  /-- **GAME leg** — accepting means winning the EUF-CMA game: a fresh message with a verifying signature. -/
  acc_wins : ∀ ω c, acc ω c = true → ¬ Q (out ω c).1 ∧ S.verify pk (out ω c).1 (out ω c).2
  /-- **FORKING leg** — accepting means the output is a SelfTargetMSIS solution on the shared commitment. -/
  acc_sound : ∀ ω c, acc ω c = true → IsSelfTargetMSISSolution A t β (resp ω c) c (comm ω)

variable {S : SigScheme SK PK Msg Sig} {pk : PK} {Q : Msg → Prop}
variable {A : M →ₗ[Rq] N} {t : N} {β : ℕ}

/-- **THE BRIDGE.** A game adversary IS a `HermineTSUF.ProbForger` — the `acc_sound` field is precisely the
`ProbForger.acc_sound` obligation. Every proved forking theorem now applies to the GAME adversary. -/
def ProbGameForger.toProbForger (pf : ProbGameForger S pk Q A t β Ω) : ProbForger A t β Ω where
  comm := pf.comm
  resp := pf.resp
  acc := pf.acc
  acc_sound := pf.acc_sound

/-- The bridge preserves the accept predicate definitionally — the advantage of the game adversary IS the
advantage the forking bound is stated against. -/
@[simp] theorem ProbGameForger.toProbForger_acc (pf : ProbGameForger S pk Q A t β Ω) :
    pf.toProbForger.acc = pf.acc := rfl

/-- **THE GAME SIDE — an accepting outcome IS a `Forgery`.** The probabilistic adversary genuinely plays the
EUF-CMA game the ~18 consumers speak about; it is not a different object wearing the same name. -/
theorem ProbGameForger.forgery_of_acc (pf : ProbGameForger S pk Q A t β Ω) (ω : Ω) (c : Rq)
    (h : pf.acc ω c = true) : Forgery S pk Q :=
  ⟨(pf.out ω c).1, (pf.out ω c).2, (pf.acc_wins ω c h).1, (pf.acc_wins ω c h).2⟩

/-- A game adversary with POSITIVE advantage exhibits a `Forgery` — the game-level non-vacuity of the
bridge. -/
theorem ProbGameForger.forgery_of_advantage_pos (pf : ProbGameForger S pk Q A t β Ω)
    (h : 0 < advantage pf.acc) : Forgery S pk Q := by
  obtain ⟨ω, c, hc⟩ := exists_acc_of_advantage_pos pf.acc h
  exact pf.forgery_of_acc ω c hc

/-! ## §2 — THE FORKING, DISCHARGED.

`forkPair_of_advantage` produces, with NO hypothesis, exactly the conclusion the `msisFork` hypothesis used
to assume. The chain is entirely proved: advantage `> 1/|Rq|` ⟹ `forkProb > 0`
(`forkProb_pos_of_advantage`, from the Cauchy–Schwarz bound `forkProb_ge_advantage`) ⟹ two distinct-challenge
accepting outcomes on a SHARED prefix (`exists_forked_pair_of_forkProb_pos`) ⟹ two SelfTargetMSIS solutions
on the SHARED commitment (`acc_sound`). -/

/-- **THE `msisFork` HYPOTHESIS, PROVED.** A game adversary whose advantage exceeds the challenge-guessing
floor `1/|Rq|` YIELDS two SelfTargetMSIS solutions on a shared commitment with DISTINCT challenges — the
EXACT conclusion `HybridCombiner.pq_euf_cma_grounded_in_msis` took as its `fork` hypothesis. Nothing is
assumed: the two transcripts are derived from the probability being positive. -/
theorem forkPair_of_advantage (pf : ProbGameForger S pk Q A t β Ω)
    (hΩ : 0 < Fintype.card Ω) (hC : 0 < Fintype.card Rq)
    (hadv : 1 / (Fintype.card Rq : ℚ) < advantage pf.acc) :
    ∃ (w : N) (c c' : Rq) (z z' : M), c ≠ c' ∧
      IsSelfTargetMSISSolution A t β z c w ∧ IsSelfTargetMSISSolution A t β z' c' w := by
  obtain ⟨ω, c, c', hne, ha, ha'⟩ :=
    exists_forked_pair_of_forkProb_pos pf.acc (forkProb_pos_of_advantage pf.acc hΩ hC hadv)
  exact ⟨pf.comm ω, c, c', pf.resp ω c, pf.resp ω c', hne,
    pf.acc_sound ω c ha, pf.acc_sound ω c' ha'⟩

/-- **THE MSIS WITNESS.** The forked pair collapses to a genuine `IsMSISSolution` on `[A | t]` through the
PROVED `HermineTSUF.prob_forger_advantage_yields_msis` — the bridge routed straight into the extractor. -/
theorem probGameForger_yields_msis (pf : ProbGameForger S pk Q A t β Ω)
    (hΩ : 0 < Fintype.card Ω) (hC : 0 < Fintype.card Rq)
    (hadv : 1 / (Fintype.card Rq : ℚ) < advantage pf.acc) :
    ∃ v, IsMSISSolution (augmented A t) ((β + β) + (β + β)) v :=
  prob_forger_advantage_yields_msis pf.toProbForger hΩ hC hadv

/-- **THE PQ KEYSTONE, IN THE HONEST FORM — advantage-bounded, NO fork hypothesis.** Under the Module-SIS
floor, EVERY probabilistic game forger against the scheme has advantage at most `1/|Rq|`: it can do no
better than GUESS the Fiat–Shamir challenge. This is what "EUF-CMA reduces to MSIS" actually says; the
deterministic `¬ Forgery` phrasing was never derivable from a hardness floor. -/
theorem pq_advantage_bounded_under_msis (pf : ProbGameForger S pk Q A t β Ω)
    (hΩ : 0 < Fintype.card Ω) (hC : 0 < Fintype.card Rq)
    (hard : MSISHard (augmented A t) ((β + β) + (β + β))) :
    advantage pf.acc ≤ 1 / (Fintype.card Rq : ℚ) := by
  by_contra hgt
  push_neg at hgt
  exact hard (probGameForger_yields_msis pf hΩ hC hgt)

/-! ## §3 — THE ONE RESIDUAL: `ForgeryRealizable`, and the derived `fork`.

The consumers conclude `EufCma := ¬ Forgery`, a DETERMINISTIC proposition about a bare `∃`-witness. Crossing
from that witness to an adversary is the one thing the probabilistic machinery cannot do for free — and it is
the ONLY thing left. `ForgeryRealizable` names it precisely and assumes nothing cryptographic. -/

/-- **`ForgeryRealizable` — THE SINGLE RESIDUAL MODELLING BRIDGE.** If the abstract game admits a `Forgery`
at all, that forgery is REALIZED by a probabilistic forking adversary of noticeable advantage (better than
guessing the challenge).

This is a statement about the MODEL, not about cryptography: it says the game's bare `∃ m σ` witness comes
from an actual algorithm with a prefix world and a rewindable challenge — the thing an abstract existential
quietly drops. It assumes NO extraction, NO rewind success, NO hardness. Everything cryptographic is proved
below it: `fork_of_realizable` DERIVES the reduction that `msisFork` used to assume outright.

Contrast the retired hypothesis, `msisFork : Forgery S pk Q → ∃ w c c' z z', c ≠ c' ∧ STMSIS ∧ STMSIS` —
that assumed the entire forking extraction, the whole cryptographic content, by fiat. -/
def ForgeryRealizable (S : SigScheme SK PK Msg Sig) (pk : PK) (Q : Msg → Prop)
    (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (Ω : Type*) [Fintype Ω] : Prop :=
  Forgery S pk Q → ∃ pf : ProbGameForger S pk Q A t β Ω,
    1 / (Fintype.card Rq : ℚ) < advantage pf.acc

/-- **THE RETIRED `fork`/`msisFork` HYPOTHESIS, NOW A THEOREM.** Its exact type, DERIVED from the
realizability bridge plus the PROVED forking bound. Every consumer that took `msisFork` as a hypothesis can
be handed THIS proof term instead. -/
theorem fork_of_realizable (S : SigScheme SK PK Msg Sig) (pk : PK) (Q : Msg → Prop)
    (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (Ω : Type*) [Fintype Ω]
    (hΩ : 0 < Fintype.card Ω) (hC : 0 < Fintype.card Rq)
    (hreal : ForgeryRealizable S pk Q A t β Ω) :
    Forgery S pk Q → ∃ (w : N) (c c' : Rq) (z z' : M), c ≠ c' ∧
      IsSelfTargetMSISSolution A t β z c w ∧ IsSelfTargetMSISSolution A t β z' c' w := by
  intro hforge
  obtain ⟨pf, hadv⟩ := hreal hforge
  exact forkPair_of_advantage pf hΩ hC hadv

/-- **THE PQ KEYSTONE, DISCHARGED.** `HybridCombiner.pq_euf_cma_grounded_in_msis` with its `fork` hypothesis
REPLACED by a proof. The scheme is `EufCma` under the Module-SIS floor and the realizability bridge — the
forking extraction is no longer assumed anywhere on this path. -/
theorem pq_euf_cma_grounded_in_msis_discharged (S : SigScheme SK PK Msg Sig) (pk : PK) (Q : Msg → Prop)
    (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (Ω : Type*) [Fintype Ω]
    (hΩ : 0 < Fintype.card Ω) (hC : 0 < Fintype.card Rq)
    (hreal : ForgeryRealizable S pk Q A t β Ω)
    (hard : MSISHard (augmented A t) ((β + β) + (β + β))) :
    EufCma S pk Q :=
  pq_euf_cma_grounded_in_msis S pk Q A t β (fork_of_realizable S pk Q A t β Ω hΩ hC hreal) hard

end PqBridge

/-! ## §4 — THE CLASSICAL LEG: the rewind acceptance, DERIVED.

`SchnorrEufCma.SchnorrForgeryFamily` carries `accepts_rewind` — "the rewound run also accepts" — as an
ASSUMED STRUCTURE FIELD. That is the second transcript, hypothesized. Here the same forking machinery
DERIVES it: a probabilistic Schnorr forger whose advantage beats the challenge-guessing floor `1/|F|` has a
positive fork probability, hence a genuine two-transcript event on a shared nonce, hence the discrete log. -/

section ClassicalBridge

open Dregg2.Crypto.Frost
open Dregg2.Crypto.Schnorr
open Dregg2.Crypto.SchnorrEufCma

variable {F : Type*} [Field F] [ShortNorm F] [Fintype F] [DecidableEq F]
variable {G : Type*} [AddCommGroup G] [Module F G]
variable {Ω : Type*} [Fintype Ω]
variable {SK PK Msg Sig : Type*}

/-- **A PROBABILISTIC SCHNORR FORGER** — the classical mirror of `HermineTSUF.ProbForger`. The prefix world
`Ω` fixes the NONCE `comm ω` before the Fiat–Shamir challenge `c` is drawn (the forking precondition,
`SchnorrForger.commitment_preChallenge` in probabilistic clothing); acceptance IS an accepting Schnorr
transcript (`Frost.SchnorrVerifies g pk R c s`). -/
structure ProbSchnorrForger (g pk : G) (Ω : Type*) [Fintype Ω] where
  /-- The nonce `R`, fixed by the prefix world BEFORE the challenge. -/
  comm : Ω → G
  /-- The response `s`. -/
  resp : Ω → F → F
  /-- The accept predicate. -/
  acc : Ω → F → Bool
  /-- **Acceptance is soundness** — an accepting outcome IS an accepting Schnorr transcript on `comm ω`. -/
  acc_sound : ∀ ω c, acc ω c = true → SchnorrVerifies g pk (comm ω) c (resp ω c)

/-- **THE CLASSICAL FORKING, PROVED — the rewind acceptance DERIVED, not assumed.** A probabilistic Schnorr
forger whose advantage exceeds `1/|F|` yields the DISCRETE LOG of `pk`: the positive fork probability
PRODUCES two accepting transcripts on the shared nonce `comm ω` with `c ≠ c'`, and
`schnorr_forking_extracts_dl` reads off `pk = ((s − s')/(c − c'))·g`. This retires
`SchnorrForgeryFamily.accepts_rewind`. -/
theorem prob_schnorr_yields_dlog {g pk : G} (pf : ProbSchnorrForger (F := F) g pk Ω)
    (hΩ : 0 < Fintype.card Ω) (hF : 0 < Fintype.card F)
    (hadv : 1 / (Fintype.card F : ℚ) < advantage pf.acc) :
    ∃ x : F, x • g = pk := by
  obtain ⟨ω, c, c', hne, ha, ha'⟩ :=
    exists_forked_pair_of_forkProb_pos pf.acc (forkProb_pos_of_advantage pf.acc hΩ hF hadv)
  exact ⟨extractWitness c c' (pf.resp ω c) (pf.resp ω c'),
    (schnorr_forking_extracts_dl g pk (pf.comm ω) c c' (pf.resp ω c) (pf.resp ω c') hne
      (pf.acc_sound ω c ha) (pf.acc_sound ω c' ha')).symm⟩

/-- **A PROBABILISTIC SCHNORR FORGER FAMILY** — the faithful EUF-CMA adversary: keygen outputs `x·g` with
`x` ranging over the whole scalar field, so a scheme-level forger must win for EVERY honest public key. Each
per-key forger has NOTICEABLE advantage (better than guessing the challenge). The probabilistic upgrade of
`SchnorrEufCma.SchnorrForgeryFamily` — with the assumed `accepts_rewind` field REMOVED. -/
structure ProbSchnorrFamily (g : G) (Ω : Type*) [Fintype Ω] where
  /-- The forger the adversary runs against public key `P`. -/
  forger : ∀ P : G, ProbSchnorrForger (F := F) g P Ω
  /-- Its advantage beats the challenge-guessing floor `1/|F|`. -/
  noticeable : ∀ P : G, 1 / (Fintype.card F : ℚ) < advantage (forger P).acc

/-- **THE FAMILY IS A DISCRETE-LOG SOLVER.** Running the family on every point and applying the PROVED
forking extraction gives a discrete log for EVERY point — a `SchnorrEufCma.DLSolverF`. -/
theorem prob_schnorr_family_yields_dlsolver {g : G} (fam : ProbSchnorrFamily (F := F) g Ω)
    (hΩ : 0 < Fintype.card Ω) (hF : 0 < Fintype.card F) :
    DLSolverF (S := F) g := by
  have h : ∀ P : G, ∃ x : F, x • g = P := fun P =>
    prob_schnorr_yields_dlog (fam.forger P) hΩ hF (fam.noticeable P)
  choose dlog hdlog using h
  exact ⟨dlog, hdlog⟩

/-- **THE CLASSICAL KEYSTONE, IN THE HONEST FORM.** Under the discrete-log floor `SchnorrDLHardF`, NO
probabilistic Schnorr forger family of noticeable advantage exists. Every step of the reduction — the
rewind, the shared nonce, the distinct challenges, the extraction — is PROVED. -/
theorem no_prob_schnorr_family_under_dl {g : G}
    (hΩ : 0 < Fintype.card Ω) (hF : 0 < Fintype.card F)
    (hard : SchnorrDLHardF (S := F) g) : ProbSchnorrFamily (F := F) g Ω → False :=
  fun fam => hard (prob_schnorr_family_yields_dlsolver fam hΩ hF)

/-- **`ClassicalForgeryRealizable`** — the classical twin of `ForgeryRealizable`: a game forgery against the
classical component is REALIZED by a probabilistic Schnorr forger family of noticeable advantage. Again a
MODELLING statement; the forking is proved. It replaces
`dlFork : Forgery Cl pkc Q → DLSolver C G`, which assumed the DL extraction outright. -/
def ClassicalForgeryRealizable (Cl : SigScheme SK PK Msg Sig) (pkc : PK) (Q : Msg → Prop)
    (g : G) (Ω : Type*) [Fintype Ω] : Prop :=
  Forgery Cl pkc Q → Nonempty (ProbSchnorrFamily (F := F) g Ω)

/-- **THE CLASSICAL LEG, DISCHARGED.** `HybridCombiner.classical_euf_cma_grounded_in_dl` with its `fork`
hypothesis REPLACED by a proof: under `SchnorrDLHardF` and the realizability bridge, the classical component
is `EufCma`. No `dlFork`. -/
theorem classical_euf_cma_grounded_in_dl_discharged
    {Cl : SigScheme SK PK Msg Sig} {pkc : PK} {Q : Msg → Prop} {g : G}
    (hΩ : 0 < Fintype.card Ω) (hF : 0 < Fintype.card F)
    (hreal : ClassicalForgeryRealizable (F := F) Cl pkc Q g Ω)
    (hard : SchnorrDLHardF (S := F) g) : EufCma Cl pkc Q := by
  intro hforge
  obtain ⟨fam⟩ := hreal hforge
  exact no_prob_schnorr_family_under_dl hΩ hF hard fam

end ClassicalBridge

/-! ## §5 — THE KEYSTONES, RESTATED.

`hybrid_secure_if_either_floor` with BOTH forking hypotheses retired. The combiner itself
(`hybrid_euf_cma_if_either`) was always unconditional; only the two legs' anchors carried the un-discharged
`fork`s, and both are now proofs. -/

section Keystone

open Dregg2.Crypto.SchnorrEufCma
open Dregg2.Crypto.DreggPqRefinement

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq] [Fintype Rq] [DecidableEq Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
variable {F : Type*} [Field F] [ShortNorm F] [Fintype F] [DecidableEq F]
variable {G : Type*} [AddCommGroup G] [Module F G]

/-- **THE KEYSTONE, DISCHARGED — `hybrid_secure_if_either_floor` with NO forking hypotheses.**

The hybrid `ed25519 × ML-DSA` signature is EUF-CMA-unforgeable if EITHER the discrete-log floor
`SchnorrDLHardF` OR the Module-SIS floor `MSISHard` holds. Compare the original
(`HybridCombiner.hybrid_secure_if_either_floor`), which additionally TOOK `dlFork` and `msisFork` — the two
un-discharged forking reductions — and passed them through to every consumer.

Here both are gone. What remains is: the two floors (irreducible, as they must be), and the two
REALIZABILITY bridges — modelling statements saying the game's bare `∃`-forgery is produced by an actual
adversary. Every cryptographic step (rewind, shared commitment/nonce, distinct challenges, MSIS/DL
extraction) is PROVED. -/
theorem hybrid_secure_if_either_floor_discharged
    {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Q : Msg → Prop)
    (g : G) (A : M →ₗ[Rq] N) (t : N) (β : ℕ)
    (Ωc : Type*) [Fintype Ωc] (Ωp : Type*) [Fintype Ωp]
    (hΩc : 0 < Fintype.card Ωc) (hΩp : 0 < Fintype.card Ωp)
    (hF : 0 < Fintype.card F) (hC : 0 < Fintype.card Rq)
    (hrealCl : ClassicalForgeryRealizable (F := F) Cl pkc Q g Ωc)
    (hrealPq : ForgeryRealizable Pq pkp Q A t β Ωp)
    (hfloor : SchnorrDLHardF (S := F) g ∨ MSISHard (augmented A t) ((β + β) + (β + β))) :
    EufCma (hybrid Cl Pq) (pkc, pkp) Q := by
  refine hybrid_euf_cma_if_either Cl Pq pkc pkp Q ?_
  rcases hfloor with hdl | hmsis
  · exact Or.inl (classical_euf_cma_grounded_in_dl_discharged hΩc hF hrealCl hdl)
  · exact Or.inr (pq_euf_cma_grounded_in_msis_discharged Pq pkp Q A t β Ωp hΩp hC hrealPq hmsis)

/-- **THE DEPLOYED REFINEMENT, DISCHARGED.** `DreggPqRefinement.dregg_pq_is_eufcma_under_msis` — the theorem
that carries the SHIPPED `dregg-pq` ML-DSA API into the security games — with its `fork` hypothesis retired.
The deployed scheme is `EufCma` under Module-SIS hardness and the realizability bridge; the forking
extraction is proved, not assumed. -/
theorem dregg_pq_is_eufcma_under_msis_discharged
    {Seed PK Ctx Msg Sig : Type*}
    (api : DreggPqApi Seed PK Ctx Msg Sig) (pk : PK) (Q : (Ctx × Msg) → Prop)
    (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (Ω : Type*) [Fintype Ω]
    (hΩ : 0 < Fintype.card Ω) (hC : 0 < Fintype.card Rq)
    (hreal : ForgeryRealizable (dreggPqSigScheme api) pk Q A t β Ω)
    (hard : MSISHard (augmented A t) ((β + β) + (β + β))) :
    EufCma (dreggPqSigScheme api) pk Q :=
  pq_euf_cma_grounded_in_msis_discharged (dreggPqSigScheme api) pk Q A t β Ω hΩ hC hreal hard

end Keystone

/-! ## §6 — THE QUANTITATIVE KEYSTONE.

`ProbCrypto.ForkingFamily` already carries the honest λ-indexed forking bound end-to-end (its `bound` field
is the ℝ-cast of `forkProb_ge_advantage`). What it lacked was the GAME leg. `GameForkingFamily` welds them:
a forking family whose every accepting outcome is a genuine `HybridCombiner.Forgery`. The quantitative
keystone is then the ensemble statement the quant track proves — `MSISHardQuant` + a growing challenge space
⟹ the game forger's advantage ENSEMBLE is negligible. -/

section Quant

variable {SK PK Msg Sig : Type*}

/-- **THE λ-INDEXED BRIDGE.** A `ProbCrypto.ForkingFamily` (the quantitative forking substrate) carrying the
GAME leg: at every security parameter, an accepting outcome is a genuine EUF-CMA `Forgery` against
`(Sch, pk, Q)`. This is what makes `forgerAdv` the *game's* advantage ensemble rather than an anonymous
number. -/
structure GameForkingFamily (Sch : SigScheme SK PK Msg Sig) (pk : PK) (Q : Msg → Prop) where
  /-- The underlying quantitative forking family (challenge ring, prefix world, accept predicate, bound). -/
  fam : ForkingFamily
  /-- **The GAME leg** — every accepting outcome at every parameter is an EUF-CMA win. -/
  wins : ∀ (l : ℕ) (ω : fam.World l) (c : fam.Chal l), fam.acc l ω c = true → Forgery Sch pk Q

/-- **THE QUANTITATIVE KEYSTONE.** Under the QUANTITATIVE Module-SIS floor `MSISHardQuant` (every solver's
advantage is negligible — applied to the solver the forking reduction DERIVES) and a super-polynomially
growing challenge space, the GAME forger's advantage ensemble is NEGLIGIBLE. This is the concrete-security
form of "EUF-CMA reduces to MSIS", riding the PROVED `ProbCrypto.forking_reduces_against_floor`. No fork
hypothesis anywhere. -/
theorem game_forger_negl_under_msis_quant {SolverIdx : Type*}
    {Sch : SigScheme SK PK Msg Sig} {pk : PK} {Q : Msg → Prop}
    (GF : GameForkingFamily Sch pk Q)
    (solverAdvOf : SolverIdx → Ensemble) (s : SolverIdx) (hs : solverAdvOf s = GF.fam.solverAdv)
    (hfloor : MSISHardQuant solverAdvOf) (hCneg : Negl GF.fam.invChal) :
    Negl GF.fam.forgerAdv :=
  forking_reduces_against_floor GF.fam solverAdvOf s hs hfloor hCneg

end Quant

/-! ## §7 — TEETH.

(a) THE OBSTRUCTION IS REAL: a single-transcript adversary has `forkProb = 0` and no forked pair — proved
    above, and exercised here on a concrete accept predicate.
(b) THE DERIVED FORK FIRES: a concrete `ZMod 5` game adversary of advantage `2/5 > 1/5 = 1/|C|` produces the
    two distinct-challenge SelfTargetMSIS solutions, with nothing assumed.
(c) THE DISCHARGED KEYSTONE IS NON-VACUOUS AND ITS FLOOR LOAD-BEARING: `brokenToy` verifies everything, so a
    `Forgery` EXISTS and `EufCma` is FALSE; our realizability bridge HOLDS for it; therefore the discharged
    keystone FORCES `¬ MSISHard` on the toy instance — and the toy instance is indeed easy. The MSIS floor is
    exactly what carries the conclusion; strip it and the keystone breaks.
(d) THE CLASSICAL LEG FIRES: a probabilistic Schnorr forger family over `ZMod 5` (where DL is easy) yields a
    `DLSolverF`, refuting `SchnorrDLHardF` — the classical mirror, with the rewind DERIVED. -/

section Teeth

open Dregg2.Crypto.Frost
open Dregg2.Crypto.SchnorrEufCma

/-! ### (a) The obstruction, on concrete data. -/

/-- A single-transcript accept predicate over `ZMod 5`: it accepts on EXACTLY ONE challenge. This is what a
deterministic `Forgery` looks like in the counting model. -/
def singleAcc : Unit → ZMod 5 → Bool := fun _ c => decide (c = 1)

/-- Exactly one accepting challenge. -/
theorem singleAcc_hits : hits singleAcc () = 1 := by decide

/-- **THE OBSTRUCTION FIRES.** The single-transcript adversary admits NO forked pair — so no extraction is
available from it at ANY hardness floor. This is why the deterministic `fork` hypothesis had to be
restated rather than proved. -/
theorem singleAcc_no_fork :
    ¬ ∃ (ω : Unit) (c c' : ZMod 5), c ≠ c' ∧ singleAcc ω c = true ∧ singleAcc ω c' = true :=
  no_forked_pair_of_hits_le_one singleAcc (fun ω => by cases ω; rw [singleAcc_hits])

/-- …and its fork probability is exactly `0`. -/
theorem singleAcc_forkProb_zero : forkProb singleAcc = 0 :=
  forkProb_eq_zero_of_hits_le_one singleAcc (fun ω => by cases ω; rw [singleAcc_hits])

/-! ### (b) The derived fork FIRES on a concrete game adversary. -/

/-- A concrete probabilistic GAME adversary over `ZMod 5`, against the `brokenToy` scheme (which verifies
everything, so every submission is a game win): commitment `0`, response `resp _ c = c`, accepting on
exactly the two challenges `{1, 2}` — advantage `2/5`, above the guessing floor `1/5`. Its `acc_sound` is
the SAME `IsSelfTargetMSISSolution` proof `HermineTSUF.exProbForger` carries, so it is a genuine bridge
object, not a relabel. -/
def exGameForger : ProbGameForger brokenToy () noQueries
    (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 Unit where
  out := fun _ _ => (true, true)
  comm := exProbForger.comm
  resp := exProbForger.resp
  acc := exProbForger.acc
  acc_wins := fun _ _ _ => ⟨not_false, trivial⟩
  acc_sound := exProbForger.acc_sound

/-- Its advantage is a genuine `2/5` — inherited verbatim from the proved `HermineTSUF.exProb_advantage`
(the accept predicates are the same object). -/
theorem exGame_advantage : advantage exGameForger.acc = 2 / 5 := exProb_advantage

/-- Its advantage CLEARS the challenge-guessing floor `1/|C| = 1/5`. -/
theorem exGame_advantage_gt_threshold :
    1 / (Fintype.card (ZMod 5) : ℚ) < advantage exGameForger.acc :=
  exProb_advantage_gt_threshold

/-- **THE GAME LEG FIRES** — the probabilistic adversary genuinely exhibits an EUF-CMA `Forgery`. -/
theorem exGame_is_a_forgery : Forgery brokenToy () noQueries :=
  exGameForger.forgery_of_advantage_pos (by rw [exGame_advantage]; norm_num)

/-- **THE DERIVED FORK FIRES.** The retired `msisFork` hypothesis' EXACT conclusion — two SelfTargetMSIS
solutions on a shared commitment with distinct challenges — PRODUCED from the advantage alone. Nothing
assumed. -/
theorem exGame_fork_produced :
    ∃ (w : ZMod 5) (c c' : ZMod 5) (z z' : ZMod 5), c ≠ c' ∧
      IsSelfTargetMSISSolution (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 z c w ∧
      IsSelfTargetMSISSolution (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 z' c' w :=
  forkPair_of_advantage exGameForger (by decide) (by decide) exGame_advantage_gt_threshold

/-- **`ForgeryRealizable` IS INHABITED** — the residual bridge is non-vacuous: on the toy, any game forgery
is realized by `exGameForger`, whose advantage `2/5` beats the guessing floor `1/5`. -/
theorem exGame_realizable :
    ForgeryRealizable brokenToy () noQueries
      (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 Unit :=
  fun _ => ⟨exGameForger, exGame_advantage_gt_threshold⟩

/-! ### (c) The discharged keystone is NON-VACUOUS and its floor LOAD-BEARING. -/

/-- **THE FLOOR IS LOAD-BEARING — proved THROUGH the discharged keystone.** `brokenToy` verifies everything,
so `Forgery brokenToy () noQueries` HOLDS (`HybridCombiner.brokenToy_forgeable`) and `EufCma` is FALSE. Our
realizability bridge HOLDS for it. So the discharged keystone, applied to the toy, FORCES `¬ MSISHard` on the
toy instance `[id | 1]` over `ZMod 5`. And it is indeed false there (the `2/5` adversary extracts a
solution). Hence: the keystone genuinely CONSUMES its Module-SIS floor — it is not a vacuous relabel, and
stripping the floor breaks the conclusion. -/
theorem keystone_msis_floor_load_bearing :
    ¬ MSISHard (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1) ((0 + 0) + (0 + 0)) :=
  fun hard =>
    pq_euf_cma_grounded_in_msis_discharged brokenToy () noQueries
      (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 Unit (by decide) (by decide)
      exGame_realizable hard brokenToy_forgeable

/-- …and the MSIS witness is genuinely PRODUCED (the extraction is not vacuous): the `2/5` adversary hands
back an actual `IsMSISSolution` on the augmented map. -/
theorem exGame_yields_msis :
    ∃ v, IsMSISSolution (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1) ((0 + 0) + (0 + 0)) v :=
  probGameForger_yields_msis exGameForger (by decide) (by decide) exGame_advantage_gt_threshold

/-! ### (d) The classical leg fires — the rewind DERIVED, not assumed. -/

/-- `ZMod 5` is a field (the teeth's degenerate scalar group). -/
scoped instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- A concrete probabilistic Schnorr forger over the degenerate group `F = G = ZMod 5`, `g = 1` (where DL is
easy): nonce `R = 0`, response `s = c·P`, accepting on `{1, 2}` (advantage `2/5 > 1/5`). Acceptance IS an
accepting Schnorr transcript: `(c·P)·1 = 0 + c·P`. -/
def exSchnorrForger (P : ZMod 5) : ProbSchnorrForger (F := ZMod 5) (1 : ZMod 5) P Unit where
  comm := fun _ => 0
  resp := fun _ c => c * P
  acc := fun _ c => decide (c = 1 ∨ c = 2)
  acc_sound := by
    intro _ c _
    show (c * P) • (1 : ZMod 5) = (0 : ZMod 5) + c • P
    simp [smul_eq_mul]

/-- Its accept predicate is the SAME object as `exProbForger`'s, so its advantage is the proved `2/5`. -/
theorem exSchnorr_advantage_gt_threshold (P : ZMod 5) :
    1 / (Fintype.card (ZMod 5) : ℚ) < advantage (exSchnorrForger P).acc :=
  exProb_advantage_gt_threshold

/-- A probabilistic Schnorr forger FAMILY on the easy group — one noticeable-advantage forger per public
key. The `accepts_rewind` field of `SchnorrEufCma.SchnorrForgeryFamily` is GONE: the second transcript is
derived from the advantage. -/
def exSchnorrFamily : ProbSchnorrFamily (F := ZMod 5) (1 : ZMod 5) Unit where
  forger := exSchnorrForger
  noticeable := exSchnorr_advantage_gt_threshold

/-- **THE CLASSICAL PIPELINE FIRES.** The family yields a `DLSolverF` — so on the easy group the DL floor is
FALSE, exactly as `SchnorrEufCma.ex_dl_not_hard` says over `ℚ`. The classical leg's protection is precisely
the named DL assumption, and the forking that reaches it is proved. -/
theorem exSchnorr_family_breaks_dl : DLSolverF (S := ZMod 5) (1 : ZMod 5) :=
  prob_schnorr_family_yields_dlsolver exSchnorrFamily (by decide) (by decide)

/-- …hence `SchnorrDLHardF` is FALSE on the easy group: the classical keystone genuinely consumes its floor. -/
theorem exSchnorr_dl_not_hard : ¬ SchnorrDLHardF (S := ZMod 5) (1 : ZMod 5) :=
  fun hard => hard exSchnorr_family_breaks_dl

-- The single-transcript adversary has exactly ONE accepting challenge — no fork, no extraction.
#guard decide (hits singleAcc () = 1)
-- The forking adversary has TWO — the fork event is genuinely available.
#guard decide (hits exProbForger.acc () = 2)
-- The advantage `2/5` clears the challenge-guessing floor `1/5`; the fork probability is a positive `2/25`.
#guard decide ((2 : ℚ) / 5 > 1 / 5)
#guard decide ((2 : ℚ) / 25 = (2 / 5) * ((2 / 5) - 1 / 5))

end Teeth

/-! ## Kernel-clean keystones.

The standing obligations after this file are the NAMED FLOORS (`Lattice.MSISHard`,
`SchnorrEufCma.SchnorrDLHardF`) plus the TWO REALIZABILITY bridges (`ForgeryRealizable`,
`ClassicalForgeryRealizable`) — modelling statements, taken as explicit theorem hypotheses, never used to
close a goal. The forking extraction itself is no longer assumed anywhere on this path. -/

#assert_all_clean [
  no_forked_pair_of_hits_le_one,
  forkProb_eq_zero_of_hits_le_one,
  exists_acc_of_advantage_pos,
  ProbGameForger.forgery_of_acc,
  ProbGameForger.forgery_of_advantage_pos,
  forkPair_of_advantage,
  probGameForger_yields_msis,
  pq_advantage_bounded_under_msis,
  fork_of_realizable,
  pq_euf_cma_grounded_in_msis_discharged,
  prob_schnorr_yields_dlog,
  prob_schnorr_family_yields_dlsolver,
  no_prob_schnorr_family_under_dl,
  classical_euf_cma_grounded_in_dl_discharged,
  hybrid_secure_if_either_floor_discharged,
  dregg_pq_is_eufcma_under_msis_discharged,
  game_forger_negl_under_msis_quant,
  singleAcc_no_fork,
  singleAcc_forkProb_zero,
  exGame_advantage,
  exGame_is_a_forgery,
  exGame_fork_produced,
  exGame_realizable,
  keystone_msis_floor_load_bearing,
  exGame_yields_msis,
  exSchnorr_family_breaks_dl,
  exSchnorr_dl_not_hard
]

end Dregg2.Crypto.ForkingDischarge
