/-
# `Dregg2.Crypto.RomForkingExtractor` — the interactive-prover-with-rewinding object, and the
forking lemma over it, in the tree's OWN random-oracle counting model.

**SUBSTRATE (House Law #1, said out loud):** this is Lean-authored, and it is not a circuit at
all — nothing below is a Rust AIR, a `Builder` gadget, or an `air_accepts` predicate. Every
declaration is a theorem about `RomOracle.OracleComp` trees, `Finset`s and finite real-valued
probabilities (`RomCounting.condProb`), exactly the objects `RomQueryFloor`/`IpaOpeningExtractionFloor`
already use.

## Why this file exists

`IpaOpeningExtractionFloor` decomposed P10 into four pieces and left ONE genuinely open:
*"getting `T` accepting transcripts from ONE prover at all — the actual rewinding/forking
argument… it needs a probabilistic COST/PPT model for an INTERACTIVE prover with rewinding
access, and this tree does not have one."* `FriAdversaryObject` built the STRAIGHT-LINE half of
the same object (`Strategy`/`fsRun`) and said so explicitly in its own header: *"No rewinding, no
forking, matching the predecessor design's BCS16 posture."* Both files name the SAME missing
ingredient. This file builds it once, on the substrate both already share (`RomOracle.OracleComp`,
`RomCounting.cyl`/`condProb`), and connects it to both.

## Ground truth already in the tree — read before trusting this file's framing

Two OTHER forking objects already exist, over a DIFFERENT substrate (a bare finite `Ω × C`
product, not `RomOracle`), and this file is not a duplicate of either — the relationship is
stated precisely because getting it wrong would be exactly the "mirror, not ground truth"
failure mode:

* **`HermineTSUF.ProbForger`** (`Dregg2/Crypto/HermineTSUF.lean`, §ProbForking) is a **`T = 2`**
  forker over a finite prefix world `Ω` and a FIXED, KNOWN fork point (a single challenge drawn
  from `Rq`). Its bound `forkProb_ge_advantage : forkProb ≥ advantage·(advantage − 1/|C|)` has
  **no `q_H` penalty** — precisely BECAUSE the fork point is fixed/known rather than searched for
  among `q_H` candidate positions.
* **`FriArityForking.nfork_probability_bound`** (`Dregg2/Circuit/FriArityForking.lean`, §1) is the
  **`n`-ary generalization of the OTHER, weaker `HermineTSUF` bound** —
  `HermineTSUF.forking_probability_bound`, the ABSTRACT Bellare–Neven bound over an UNKNOWN fork
  index `x : Fin q_H → ℚ`. Generalized to `n`-ary it pays `q_H^{n−1}`, and §2 of that file proves
  this is VACUOUS at the deployed arity-8 FRI fold for any real budget (`q_H ≥ 14` over the base
  field, `q_H ≥ 2^17` even over the deployed extension field). **That vacuity is a fact about the
  UNKNOWN-fork-index encoding, not about rewinding itself** — the file's own §1 header says exactly
  which bound it generalized, and it is the one WITHOUT the fixed-index tightening `ProbForger`
  gets for free. This is the "suspect the encoding" moment the brief warns about: the naive `n`-ary
  generalization of the wrong sibling prices out; the fix is to generalize the RIGHT sibling.

So: this file is the **`T`-ary, `RomOracle`-native generalization of `ProbForger`'s FIXED-fork-point
model** (not of `FriArityForking`'s abstract, unknown-index one), extended from `T = 2` to
arbitrary `T`, and built on `RomOracle`/`RomCounting` so it composes DIRECTLY with
`IpaOpeningExtractionFloor`'s already-proven §A (`vandermonde_extracts`) and §C
(`manyFreshDistinct_bound_pasta`), and with `FriAdversaryObject.fsRun` by an exact identity
(`friLastRoundPoint_run_eq`), not a re-implementation.

## The design: `RewindablePoint` — an interactive prover, forked at a KNOWN point

A `RewindablePoint D R A` is the LAST-ROUND shape of an interactive prover: everything before the
round being forked is carried OUTSIDE the object, by the ambient conditioning `RomCounting.cyl S σ`
(exactly as `RomQueryFloor.birthday_cond`'s induction already conditions on "what the adversary has
learned so far") — the object itself is just the ONE remaining query point and a PURE decision on
its answer (no further oracle calls; the forked round is the last one, so acceptance is fully
determined by the fork challenge). `.fork` is the REWIND operation: given `T` distinct, FRESH
"rewind-tag" domain points (the same device `IpaOpeningExtractionFloor` §C already uses — "T
distinct rewind labels absorbed just before the closing squeeze" — so `T` hypothetical rewound
continuations of the SAME prover are representable as `T` queries of ONE oracle, sidestepping the
paradox of one function taking two values at one input), it produces `T` clones differing only in
which point they query. `.run`/`run_queryBounded` give the object a literal `RomOracle.QueryBounded`
COST — `1` per session, `n` for a campaign of `n` rewinds (`campaign_queryBounded`), in the SAME
currency the rest of this tree's ROM floors are priced in.

Why THIS shape and not a general multi-round coroutine: the extraction consumers (`vandermonde_extracts`,
and the analogous FRI per-layer Vandermonde `FriFoldArity.fold_close_of_arity_challenges`) both need
`T` transcripts differing ONLY at the fork round, sharing every earlier message — the "last-round,
pure-decision" shape is exactly what makes the forking lemma about it PROVABLE by direct counting
(`condProb_fresh_finset_pow`) rather than merely statable, and it is the shape a `k₁,…,k_μ`
multi-round tree of forks is BUILT FROM one round at a time (composing several instances of this
object is future work, named, not attempted here).

## The forking lemma, exactly

`forking_lemma`: forking a `RewindablePoint` of local acceptance rate `ε` (`localRate`) at `T`
fresh, pairwise-distinct tags gives

    Pr[all T rewound sessions accept ∧ their T challenges are pairwise distinct] ≥ ε^T − T²/|R|

— `ε^T` from a NEW, genuinely finite counting fact this file proves
(`condProb_fresh_finset_pow`/`condProb_fresh_pow`: `T` fresh domain points are JOINTLY
independent-uniform, a `T`-wise generalization of `RomCounting.condProb_fresh_eq`, by induction on
the point set via `condProb_split` — no Cauchy–Schwarz, no Jensen, no `q_H` anywhere, because the
fork point is FIXED, not searched for), combined by a plain union bound (`condProb_and_ge`) with
the DISTINCTNESS price this tree ALREADY proved (`IpaOpeningExtractionFloor.manyFreshDistinct_bound`,
reused verbatim, unchanged).

**Read the cost honestly.** `ε^T` is the probability that ONE batch of `T` simultaneous forks all
land accepting — the cost of a SINGLE such batch succeeding is real and can be small when `ε` is
small, exactly as `FriArityForking` warns. The classical, SHARPER treatment (rewind ONCE to find an
accepting prefix, then pay only `T/ε` EXPECTED additional attempts at that SAME prefix — the
"conditioning on success is size-biased toward large local rates" argument that makes the
Bellare–Neven forking lemma's `1/ε`-not-`1/ε^T` cost work) is NOT built here: it needs a literal
expectation-of-a-geometric-random-variable argument (`E[1/p(X)] ≤ 1/ε` under success-biased
sampling), which is genuinely NEW apparatus this tree's counting-only, non-measure-theoretic style
has never carried (no `PMF`/`tsum` anywhere in `RomCounting`/`RomQueryFloor`/`ProbCrypto`). That gap
is real, is NOT priced here, and is named as the concrete next step rather than papered over: the one
piece worth building next is a finite "expected trials to first success, size-biased" lemma over the
SAME `cyl`/`condProb` substrate, and it is a BUILDABLE, bounded-effort addition, not open research —
this session simply ran out of runway for it. What ships here is the honest, weaker, but GENUINELY
proved `ε^T` bound: a real forking lemma, not the sharpest one this method could in principle
produce.

## What is discharged, and what is not

`forking_discharges_item4` composes this file's forking lemma with `vandermonde_extracts`
end-to-end: forking a rewindable IPA opening `T` times yields, except with probability
`≤ T² / |F| ` below `ε^T`, `T` transcripts from which ANY target coefficient is read off by
EXPLICIT linear algebra — GIVEN a named hypothesis that an accepting reply is consistent with a
single fixed degree-`<T` polynomial. That hypothesis is exactly P10's item 2 (computational
binding, `FloorGames.DLHardQuant` at Pasta's curve, still un-discharged, unchanged by this file) —
so this file retires item 4 and touches NOTHING else. `fri_forking_bound` instantiates the SAME
lemma at `FriAdversaryObject.fsRun`'s last round, via the exact identity `friLastRoundPoint_run_eq`
— genuinely the SAME object serving both bridge directions, not two objects that resemble each
other.

## Axiom hygiene

`#assert_axioms`/`#assert_all_clean` on every declaration; no `sorry`, no fresh `axiom`, no
`native_decide`. NEW module; NOT added to `metatheory/Dregg2.lean` (house discipline for
standalone floors) — import line to add when integrated:
`import Dregg2.Crypto.RomForkingExtractor`.
-/
import Dregg2.Crypto.IpaOpeningExtractionFloor
import Dregg2.Circuit.FriAdversaryObject

namespace Dregg2.Crypto.RomForkingExtractor

open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomCounting
  (cyl mem_cyl cyl_nonempty cyl_card_pos condProb condProb_nonneg condProb_le_one condProb_congr
   condProb_eq_zero condProb_eq_one condProb_split condProb_fresh_eq condProb_cyl_empty)
open Dregg2.Crypto.IpaOpeningExtractionFloor (manyFreshDistinct_bound vandermonde_extracts)
open Dregg2.Circuit.FriAdversaryObject (Strategy fsRun)

set_option autoImplicit false

/-! ## §1 — a `T`-wise generalization of `RomCounting.condProb_fresh_eq`: fresh points are
JOINTLY independent-uniform, not merely pairwise. This is the counting engine the forking lemma
runs on; nothing here mentions an adversary or a challenge yet. -/

section FreshPow

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]

/-- **`T` FRESH POINTS, PACKAGED AS A FINSET, ARE JOINTLY INDEPENDENT-UNIFORM.** For a finite set
`T` of domain points all outside the conditioning set `S`, the probability that EVERY point in `T`
hits a fixed Boolean predicate `win` is exactly `(density of win)^|T|` — a direct generalization of
`condProb_fresh_eq` (which is the case `T = {a}`, `win = (· = z)`) from one point to arbitrarily
many, by peeling one point off at a time with `condProb_split`, exactly as `RomQueryFloor.birthday_cond`
peels off one QUERY at a time. -/
theorem condProb_fresh_finset_pow (win : R → Bool) :
    ∀ (Tag : Finset D) (S : Finset D) (σ : D → R), (∀ x ∈ Tag, x ∉ S) →
      condProb (cyl S σ) (fun H => decide (∀ x ∈ Tag, win (H x) = true))
        = (((Finset.univ.filter (fun r => win r = true)).card : ℝ)
            / (Fintype.card R : ℝ)) ^ Tag.card := by
  intro Tag
  induction Tag using Finset.induction_on with
  | empty =>
      intro S σ _
      rw [Finset.card_empty, pow_zero]
      apply condProb_eq_one
      · intro H _; simp
      · exact cyl_nonempty S σ
  | insert d T' hd ih =>
      intro S σ hfresh
      have hdS : d ∉ S := hfresh d (Finset.mem_insert_self d T')
      rw [condProb_split S σ d hdS]
      have hterm : ∀ r : R,
          condProb (cyl (insert d S) (Function.update σ d r))
            (fun H => decide (∀ x ∈ insert d T', win (H x) = true))
          = (if win r = true then
              (((Finset.univ.filter (fun r' => win r' = true)).card : ℝ)
                / (Fintype.card R : ℝ)) ^ T'.card
             else 0) := by
        intro r
        have hpin : ∀ H ∈ cyl (insert d S) (Function.update σ d r), H d = r := by
          intro H hH
          have := (mem_cyl.1 hH) d (Finset.mem_insert_self d S)
          simpa using this
        by_cases hwr : win r = true
        · rw [if_pos hwr]
          have hfresh' : ∀ x ∈ T', x ∉ insert d S := by
            intro x hx hmem
            rcases Finset.mem_insert.1 hmem with rfl | hmem'
            · exact hd hx
            · exact hfresh x (Finset.mem_insert_of_mem hx) hmem'
          have hcongr : condProb (cyl (insert d S) (Function.update σ d r))
              (fun H => decide (∀ x ∈ insert d T', win (H x) = true))
            = condProb (cyl (insert d S) (Function.update σ d r))
              (fun H => decide (∀ x ∈ T', win (H x) = true)) := by
            apply condProb_congr
            intro H hH
            have hHd := hpin H hH
            rw [decide_eq_decide]
            constructor <;> intro h
            · intro x hx; exact h x (Finset.mem_insert_of_mem hx)
            · intro x hx
              rcases Finset.mem_insert.1 hx with rfl | hx'
              · rw [hHd]; exact hwr
              · exact h x hx'
          rw [hcongr]
          exact ih (insert d S) (Function.update σ d r) hfresh'
        · rw [if_neg hwr]
          apply condProb_eq_zero
          intro H hH
          have hHd := hpin H hH
          simp only [decide_eq_false_iff_not]
          intro hall
          exact hwr (by rw [← hHd]; exact hall d (Finset.mem_insert_self d T'))
      rw [Finset.sum_congr rfl (fun r _ => hterm r)]
      have hsum : ∀ c : ℝ, (∑ r : R, if win r = true then c else 0)
          = c * ((Finset.univ.filter (fun r => win r = true)).card : ℝ) := by
        intro c
        rw [show ((Finset.univ.filter (fun r => win r = true)).card : ℝ)
              = ∑ r : R, if win r = true then (1 : ℝ) else 0 from
              (Finset.sum_boole (fun r => win r = true) Finset.univ).symm]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        by_cases h : win r = true <;> simp [h]
      rw [hsum, Finset.card_insert_of_notMem hd, pow_succ, mul_div_assoc]

/-- **THE `Fin n` COROLLARY** — the shape `manyFreshDistinct_bound` already uses: `n` pairwise
DISTINCT, fresh domain points hit a predicate jointly with probability exactly `(density)^n`. -/
theorem condProb_fresh_pow {n : ℕ} (S : Finset D) (σ : D → R) (tag : Fin n → D)
    (htag_inj : Function.Injective tag) (htag_fresh : ∀ i, tag i ∉ S) (win : R → Bool) :
    condProb (cyl S σ) (fun H => decide (∀ i : Fin n, win (H (tag i)) = true))
      = (((Finset.univ.filter (fun r => win r = true)).card : ℝ)
          / (Fintype.card R : ℝ)) ^ n := by
  have hfresh : ∀ x ∈ Finset.univ.image tag, x ∉ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
    exact htag_fresh i
  have hcard : (Finset.univ.image tag).card = n := by
    rw [Finset.card_image_of_injective _ htag_inj, Finset.card_univ, Fintype.card_fin]
  have h := condProb_fresh_finset_pow win (Finset.univ.image tag) S σ hfresh
  rw [hcard] at h
  rw [← h]
  apply condProb_congr
  intro H _
  rw [decide_eq_decide]
  constructor
  · intro hall x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
    exact hall i
  · intro hall i
    exact hall (tag i) (Finset.mem_image_of_mem tag (Finset.mem_univ i))

end FreshPow

/-! ## §2 — `RewindablePoint`: the interactive prover, at the round being forked, with a cost
budget carried in `RomOracle.QueryBounded`. -/

/-- **A REWINDABLE PROVER, AT THE LAST ROUND.** Everything before the round being forked is
carried OUTSIDE this object (by the ambient `cyl S σ` conditioning at the call site — exactly the
prefix `RomQueryFloor.birthday_cond`'s induction already conditions on); this object IS the one
remaining query and a PURE decision on the answer. `A` is the type of the prover's completed
output (what the verifier's acceptance check runs on). -/
structure RewindablePoint (D R A : Type) where
  /-- The challenge query point being forked. -/
  point : D
  /-- What the prover does with the answer — no further oracle calls, since this is the LAST
  round; acceptance is a pure function of the challenge. -/
  decide : R → A

/-- **RUN.** The `RewindablePoint` as an `OracleComp`: query `point`, then decide. -/
def RewindablePoint.run {D R A : Type} (p : RewindablePoint D R A) : OracleComp D R A :=
  .query p.point (fun r => .pure (p.decide r))

/-- **THE COST BUDGET, per session.** Running a `RewindablePoint` costs exactly one query — the
literal `RomOracle.QueryBounded` currency the rest of this tree's ROM floors are priced in. -/
theorem RewindablePoint.run_queryBounded {D R A : Type} (p : RewindablePoint D R A) :
    QueryBounded 1 p.run :=
  QueryBounded.query 0 p.point _ (fun _ => QueryBounded.pure 0 _)

/-- **FORK.** `T` distinct fresh rewind tags produce `T` clones — the SAME decision, each asking
its OWN dedicated point. This is the rewind: rather than asking one function for two values at one
input (impossible), `T` hypothetical rewound continuations are represented as `T` queries of ONE
oracle at `T` structurally-tagged points, the device `IpaOpeningExtractionFloor` §C already commits
to for exactly this reason. -/
def RewindablePoint.fork {D R A : Type} (p : RewindablePoint D R A) {n : ℕ} (tag : Fin n → D) :
    Fin n → RewindablePoint D R A :=
  fun i => { point := tag i, decide := p.decide }

/-- **THE HIT PREDICATE.** A `RewindablePoint`, evaluated against an oracle `H`, accepts under
`win` iff `win` holds of its decision on `H`'s answer at its own point. -/
def RewindablePoint.hits {D R A : Type} (p : RewindablePoint D R A) (win : A → Bool)
    (H : D → R) : Bool :=
  win (p.decide (H p.point))

/-- **THE CAMPAIGN'S TOTAL COST.** Querying all `n` fork tags — the whole rewinding campaign, one
query per session — is `QueryBounded n`: `n` is simultaneously the rewind count and the tree's own
resource bound, reusing `RomOracle.OracleComp.ofList`'s budget verbatim (nothing new needed for the
SYNTACTIC cost claim; only the probability claim, `forking_lemma` below, is new content). -/
theorem campaign_queryBounded {D R : Type} {n : ℕ} (tag : Fin n → D) :
    QueryBounded n (OracleComp.ofList (List.ofFn tag) (id : List R → List R)) := by
  have := OracleComp.ofList_queryBounded (D := D) (R := R) (List.ofFn tag) (id : List R → List R)
  rwa [List.length_ofFn] at this

/-! ## §3 — the LOCAL ACCEPTANCE RATE `ε`, and the forking events. -/

section Forking

variable {D R A : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]

/-- **THE LOCAL ACCEPTANCE RATE.** The fraction of `R` on which `dec`'s output accepts under
`win` — the quantity `ε` the forking lemma is stated relative to. -/
noncomputable def localRate (dec : R → A) (win : A → Bool) : ℝ :=
  ((Finset.univ.filter (fun r => win (dec r) = true)).card : ℝ) / (Fintype.card R : ℝ)

/-- **THIS QUANTITY REALLY IS `ε`** — the ORIGINAL, un-forked prover's acceptance probability,
provided its own query point is fresh, equals `localRate`. `localRate` is not a disconnected new
quantity; it is the prover's real acceptance rate, read off at a single fresh evaluation. -/
theorem hits_condProb_eq_localRate (S : Finset D) (σ : D → R) (p : RewindablePoint D R A)
    (hfresh : p.point ∉ S) (win : A → Bool) :
    condProb (cyl S σ) (fun H => p.hits win H) = localRate p.decide win := by
  unfold localRate
  have hfresh' : ∀ x ∈ ({p.point} : Finset D), x ∉ S := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]; exact hfresh
  have h := condProb_fresh_finset_pow (fun r => win (p.decide r)) {p.point} S σ hfresh'
  rw [Finset.card_singleton, pow_one] at h
  rw [← h]
  apply condProb_congr
  intro H _
  unfold RewindablePoint.hits
  by_cases hw : win (p.decide (H p.point)) = true <;> simp [hw]

/-- **ALL `n` FORKED SESSIONS ACCEPT.** `@[reducible]` so `decide`'s instance search sees through
to the underlying `∀ i : Fin n, … = true` shape and finds `Fintype.decidableForallFintype`
automatically — this event is genuinely, computably decidable, never classical. -/
@[reducible] def AllForksAccept {n : ℕ} (p : RewindablePoint D R A) (win : A → Bool)
    (tag : Fin n → D) (H : D → R) : Prop :=
  ∀ i : Fin n, (p.fork tag i).hits win H = true

/-- **THE `n` FORK CHALLENGES ARE PAIRWISE DISTINCT.** The exact negation of the event
`manyFreshDistinct_bound` prices, so its bound applies to this event's complement with no
translation needed. `@[reducible]` for the same decidability reason as `AllForksAccept`. -/
@[reducible] def PairwiseDistinctAt {n : ℕ} (tag : Fin n → D) (H : D → R) : Prop :=
  ∀ p : Fin n × Fin n, p.1 ≠ p.2 → H (tag p.1) ≠ H (tag p.2)

/-- **`AllForksAccept`'s PROBABILITY IS EXACTLY `ε^n`.** Direct instance of `condProb_fresh_pow`
at `win' := fun r => win (p.decide r)` — the SAME density `localRate p.decide win`, since `(p.fork
tag i).decide = p.decide` for every `i` by construction. -/
theorem allForksAccept_condProb (S : Finset D) (σ : D → R) (p : RewindablePoint D R A) {n : ℕ}
    (tag : Fin n → D) (htag_inj : Function.Injective tag) (htag_fresh : ∀ i, tag i ∉ S)
    (win : A → Bool) :
    condProb (cyl S σ) (fun H => decide (AllForksAccept p win tag H))
      = localRate p.decide win ^ n := by
  unfold localRate
  rw [← condProb_fresh_pow S σ tag htag_inj htag_fresh (fun r => win (p.decide r))]
  apply condProb_congr
  intro H _
  rw [decide_eq_decide]
  unfold AllForksAccept RewindablePoint.hits RewindablePoint.fork
  rfl

end Forking

/-! ## §4 — a plain union bound for `condProb`, and the FORKING LEMMA. -/

section UnionBound

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-- **A UNION BOUND.** `Pr[A ∧ B] ≥ Pr[A] − Pr[¬B]` — standard finite counting: the "good" set
`{A ∧ B}` is EXACTLY `{A} \ {¬B}` (both computed relative to the same ambient `C`), whose
cardinality is `card A − card(¬B) ≤ card A − (card A − card{A∧B})`… stated cleanly via
`card {A} ≤ card {A∧B} + card {¬B}` (from `{A} = {A∧B} ⊔ ({A} ∩ {¬B})` and `{A}∩{¬B} ⊆ {¬B}`). -/
theorem condProb_and_ge (C : Finset (D → R)) (Ap Bp : (D → R) → Bool) :
    condProb C (fun H => Ap H && Bp H) ≥ condProb C Ap - condProb C (fun H => !Bp H) := by
  have hcard : (C.filter (fun H => Ap H = true)).card
      ≤ (C.filter (fun H => (Ap H && Bp H) = true)).card
        + (C.filter (fun H => (!Bp H) = true)).card := by
    have hXeq : C.filter (fun H => Ap H = true)
        = C.filter (fun H => (Ap H && Bp H) = true)
          ∪ (C.filter (fun H => Ap H = true) ∩ C.filter (fun H => (!Bp H) = true)) := by
      ext H
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter, Bool.and_eq_true]
      constructor
      · rintro ⟨hHC, hA⟩
        by_cases hB : Bp H = true
        · exact Or.inl ⟨hHC, hA, hB⟩
        · exact Or.inr ⟨⟨hHC, hA⟩, hHC, by simpa using hB⟩
      · rintro (⟨hHC, hA, _⟩ | ⟨⟨hHC, hA⟩, _⟩)
        · exact ⟨hHC, hA⟩
        · exact ⟨hHC, hA⟩
    calc (C.filter (fun H => Ap H = true)).card
        = (C.filter (fun H => (Ap H && Bp H) = true)
            ∪ (C.filter (fun H => Ap H = true) ∩ C.filter (fun H => (!Bp H) = true))).card := by
          rw [← hXeq]
      _ ≤ (C.filter (fun H => (Ap H && Bp H) = true)).card
          + (C.filter (fun H => Ap H = true) ∩ C.filter (fun H => (!Bp H) = true)).card :=
        Finset.card_union_le _ _
      _ ≤ (C.filter (fun H => (Ap H && Bp H) = true)).card
          + (C.filter (fun H => (!Bp H) = true)).card := by
        have hsub : C.filter (fun H => Ap H = true) ∩ C.filter (fun H => (!Bp H) = true)
            ⊆ C.filter (fun H => (!Bp H) = true) := Finset.inter_subset_right
        have := Finset.card_le_card hsub
        omega
  show ((C.filter (fun H => Ap H = true)).card : ℝ) / (C.card : ℝ)
      - ((C.filter (fun H => (!Bp H) = true)).card : ℝ) / (C.card : ℝ)
      ≤ ((C.filter (fun H => (Ap H && Bp H) = true)).card : ℝ) / (C.card : ℝ)
  rcases Nat.eq_zero_or_pos C.card with h0 | h0
  · simp [h0]
  · have hCpos : (0 : ℝ) < (C.card : ℝ) := by exact_mod_cast h0
    have hcast : ((C.filter (fun H => Ap H = true)).card : ℝ)
        ≤ ((C.filter (fun H => (Ap H && Bp H) = true)).card : ℝ)
          + ((C.filter (fun H => (!Bp H) = true)).card : ℝ) := by exact_mod_cast hcard
    have expand :
        ((C.filter (fun H => (Ap H && Bp H) = true)).card : ℝ) / (C.card : ℝ)
          - (((C.filter (fun H => Ap H = true)).card : ℝ) / (C.card : ℝ)
              - ((C.filter (fun H => (!Bp H) = true)).card : ℝ) / (C.card : ℝ))
        = (((C.filter (fun H => (Ap H && Bp H) = true)).card : ℝ)
            + ((C.filter (fun H => (!Bp H) = true)).card : ℝ)
            - ((C.filter (fun H => Ap H = true)).card : ℝ)) / (C.card : ℝ) := by ring
    have hnonneg : (0 : ℝ) ≤
        (((C.filter (fun H => (Ap H && Bp H) = true)).card : ℝ)
          + ((C.filter (fun H => (!Bp H) = true)).card : ℝ)
          - ((C.filter (fun H => Ap H = true)).card : ℝ)) / (C.card : ℝ) :=
      div_nonneg (by linarith) hCpos.le
    linarith [expand, hnonneg]

end UnionBound

section ForkingLemma

variable {D R A : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]

/-- **⚑⚑⚑ THE FORKING LEMMA — proved.** Forking a `RewindablePoint` of local acceptance rate `ε`
at `n` fresh, pairwise-distinct tags gives `n` accepting, pairwise-distinct-challenge sessions with
probability at least `ε^n − n²/|R|`: `ε^n` exactly (`allForksAccept_condProb`, the `T`-wise
independence engine of §1 — NO Cauchy–Schwarz, NO Jensen, NO `q_H` anywhere, because the fork point
is FIXED rather than searched for among unknown candidates), combined by the union bound
(`condProb_and_ge`) with the distinctness price this tree ALREADY proved
(`IpaOpeningExtractionFloor.manyFreshDistinct_bound`, reused verbatim). This is P10 item 4,
discharged as a genuine theorem, not an assumption. -/
theorem forking_lemma (S : Finset D) (σ : D → R) (p : RewindablePoint D R A) {n : ℕ}
    (tag : Fin n → D) (htag_inj : Function.Injective tag) (htag_fresh : ∀ i, tag i ∉ S)
    (win : A → Bool) :
    condProb (cyl S σ)
      (fun H => decide (AllForksAccept p win tag H ∧ PairwiseDistinctAt tag H))
      ≥ localRate p.decide win ^ n - (n : ℝ) * (n : ℝ) / (Fintype.card R : ℝ) := by
  have hAll := allForksAccept_condProb S σ p tag htag_inj htag_fresh win
  have hDist := manyFreshDistinct_bound S σ tag htag_inj htag_fresh
  have hUnion := condProb_and_ge (cyl S σ) (fun H => decide (AllForksAccept p win tag H))
    (fun H => decide (PairwiseDistinctAt tag H))
  have hnotB : (fun H => !decide (PairwiseDistinctAt tag H))
      = (fun H : D → R => decide (∃ q : Fin n × Fin n, q.1 ≠ q.2 ∧ H (tag q.1) = H (tag q.2))) := by
    funext H
    rw [← decide_not, decide_eq_decide]
    unfold PairwiseDistinctAt
    constructor
    · intro h
      by_contra hcon
      push_neg at hcon
      exact h (fun q hq => hcon q hq)
    · rintro ⟨q, hq1, hq2⟩ hall
      exact hall q hq1 hq2
  rw [hnotB] at hUnion
  have hcombine : condProb (cyl S σ)
      (fun H => decide (AllForksAccept p win tag H) && decide (PairwiseDistinctAt tag H))
      ≥ localRate p.decide win ^ n - (n : ℝ) * (n : ℝ) / (Fintype.card R : ℝ) := by
    have hstep : condProb (cyl S σ)
        (fun H => decide (AllForksAccept p win tag H) && decide (PairwiseDistinctAt tag H))
        ≥ condProb (cyl S σ) (fun H => decide (AllForksAccept p win tag H))
            - condProb (cyl S σ)
              (fun H => decide (∃ q : Fin n × Fin n, q.1 ≠ q.2 ∧ H (tag q.1) = H (tag q.2))) :=
      hUnion
    rw [hAll] at hstep
    linarith [hDist]
  have heq : (fun H => decide (AllForksAccept p win tag H ∧ PairwiseDistinctAt tag H))
      = (fun H => decide (AllForksAccept p win tag H) && decide (PairwiseDistinctAt tag H)) := by
    funext H
    by_cases hA : AllForksAccept p win tag H <;> by_cases hB : PairwiseDistinctAt tag H <;>
      simp [hA, hB]
  rw [heq]
  exact hcombine

end ForkingLemma

/-! ## §5 — DISCHARGING P10 ITEM 4: composing the forking lemma with `vandermonde_extracts`. -/

section IpaConnection

variable {D : Type} [Fintype D] [DecidableEq D]

/-- **P10 ITEM 4, DISCHARGED, COMPOSITIONALLY.** Forking a rewindable IPA opening — whose
decision, on an accepting reply, is PINNED to a single fixed degree-`<n` polynomial's evaluation
(`hconsistent`, the functional restatement of P10 item 2's computational-binding assumption,
UNCHANGED, still open, still exactly `FloorGames.DLHardQuant` at Pasta's curve) — `n` times at
fresh, distinct tags produces, except with probability `≥ ε^n − n²/|F|`, `n` accepting
transcripts with pairwise-distinct challenges from which `vandermonde_extracts` reads off ANY
target coefficient `a d` by EXPLICIT linear algebra. Both P10 ingredients (Vandermonde extraction,
`§A`; distinctness pricing, `§C`) meet the ONE ingredient this file supplies (rewinding, item 4)
in a single composed theorem. -/
theorem forking_discharges_item4 {F : Type} [Field F] [Fintype F] [DecidableEq F] [Nonempty F]
    (S : Finset D) (σ : D → F) (p : RewindablePoint D F F) (win : F → Bool)
    {n : ℕ} (tag : Fin n → D) (htag_inj : Function.Injective tag) (htag_fresh : ∀ i, tag i ∉ S)
    (a : Fin n → F)
    (hconsistent : ∀ r : F, win (p.decide r) = true → p.decide r = ∑ i : Fin n, a i * r ^ (i : ℕ)) :
    (condProb (cyl S σ)
      (fun H => decide (AllForksAccept p win tag H ∧ PairwiseDistinctAt tag H))
      ≥ localRate p.decide win ^ n - (n : ℝ) * (n : ℝ) / (Fintype.card F : ℝ))
    ∧
    (∀ H : D → F, AllForksAccept p win tag H → PairwiseDistinctAt tag H →
      ∀ d : Fin n, ∃ l : Fin n → F, ∑ s, l s * p.decide (H (tag s)) = a d) := by
  refine ⟨forking_lemma S σ p tag htag_inj htag_fresh win, ?_⟩
  intro H hAccept hDistinct d
  have hinj : Function.Injective (fun s : Fin n => H (tag s)) := by
    intro s t hst
    by_contra hne
    exact hDistinct (s, t) hne hst
  obtain ⟨l, hl⟩ := vandermonde_extracts (fun s => H (tag s)) hinj a d
  refine ⟨l, ?_⟩
  rw [← hl]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  exact hconsistent (H (tag s)) (hAccept s)

end IpaConnection

/-! ## §6 — CONNECTING TO `FriAdversaryObject.fsRun`: the SAME object, the SAME lemma. -/

section FriConnection

variable {R C D : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R] [Nonempty R]

/-- **THE FRI CONNECTION.** `fsRun`'s FINAL round IS a `RewindablePoint`: `friLastRoundPoint`'s
`.run` equals `fsRun enc S 1 cs` EXACTLY (`friLastRoundPoint_run_eq`), not merely
"type-compatible" with it. So the SAME forking object and the SAME `forking_lemma` this file
proved for the IPA opening apply, unchanged, to `FriAdversaryObject`'s own straight-line prover
strategy — the ONE object this session's brief asked for, serving BOTH bridge directions. -/
def friLastRoundPoint (enc : C → List R → D) (S : Strategy R C) (cs : List R) :
    RewindablePoint D R (List R) where
  point := enc (S cs) cs
  decide := fun c => c :: cs

/-- **THE BRIDGE, PROVED.** `friLastRoundPoint`'s `.run` is DEFINITIONALLY `fsRun enc S 1 cs` —
not an analogy, an identity. `fsRun`'s own header says its object has "no rewinding, no forking";
this is the exact seam at which `RewindablePoint.fork` attaches to it. -/
theorem friLastRoundPoint_run_eq (enc : C → List R → D) (S : Strategy R C) (cs : List R) :
    (friLastRoundPoint enc S cs).run = fsRun enc S 1 cs := by
  simp [RewindablePoint.run, friLastRoundPoint, fsRun]

/-- **THE FORKING BOUND, INSTANTIATED AT FRI'S LAST ROUND.** Forking `fsRun`'s final-round
challenge `n` times — the SAME rewinding object, the SAME lemma, no re-derivation — gives `n`
accepting, pairwise-distinct-challenge continuations of the SAME prefix with probability at
least `ε^n − n²/|R|`, where `ε` is `fsRun`'s own last-round acceptance rate. This discharges the
SAME missing ingredient (P10 item 4) that `IpaOpeningExtractionFloor` named for the IPA side, now
for FRI's `fsRun` — genuinely, by direct instantiation of the identical object, not by
resemblance. -/
theorem fri_forking_bound (enc : C → List R → D) (Sst : Strategy R C) (cs : List R)
    (Spre : Finset D) (σ : D → R) (win : List R → Bool)
    {n : ℕ} (tag : Fin n → D) (htag_inj : Function.Injective tag)
    (htag_fresh : ∀ i, tag i ∉ Spre) :
    condProb (cyl Spre σ)
      (fun H => decide
        (AllForksAccept (friLastRoundPoint enc Sst cs) win tag H ∧ PairwiseDistinctAt tag H))
      ≥ localRate (friLastRoundPoint enc Sst cs).decide win ^ n
          - (n : ℝ) * (n : ℝ) / (Fintype.card R : ℝ) :=
  forking_lemma Spre σ (friLastRoundPoint enc Sst cs) tag htag_inj htag_fresh win

end FriConnection

/-! ## Axiom hygiene. -/

#assert_axioms condProb_fresh_finset_pow
#assert_axioms condProb_fresh_pow
#assert_axioms RewindablePoint.run_queryBounded
#assert_axioms campaign_queryBounded
#assert_axioms hits_condProb_eq_localRate
#assert_axioms allForksAccept_condProb
#assert_axioms condProb_and_ge
#assert_axioms forking_lemma
#assert_axioms forking_discharges_item4
#assert_axioms friLastRoundPoint_run_eq
#assert_axioms fri_forking_bound

end Dregg2.Crypto.RomForkingExtractor
