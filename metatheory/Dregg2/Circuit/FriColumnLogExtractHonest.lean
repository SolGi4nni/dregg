/-
# `Dregg2.Circuit.FriColumnLogExtractHonest` — THE HONEST EXTRACTION STATEMENT
(what the straight-line query-log extractor ACTUALLY yields, over a `Q`-bounded adversary run).

## What this file is (wave-2 of the FRI query-log extractor)

`FriColumnLogExtract` (wave-1) built the BCS16 straight-line extractor `treeExtract` on the
`RomQueryLog` substrate and proved, at increasing force, that the NAIVE reading of sub-seam (a) of
`FriColumnDecode.ColumnDecodeBridge` is FALSE:

  * `no_deterministic_extraction` — "the node check passes ⟹ the extractor recovers the subtree" is
    false even for a `0`-query adversary (a guessed root, empty log);
  * `partial_commitment_verifies_but_no_total_column` — a `QueryBounded 2` adversary VERIFIES an
    opening yet its complete log admits NO total column, DETERMINISTICALLY.

Wave-1 also priced the ONE probabilistic failure mode (a single published node with a never-queried
preimage) at EXACTLY `1/|α|` (`freshHit_prob_le`, `freshHit_prob_eq_of_fresh`), and gave the union
bound over a FIXED list of nodes (`condProb_anyFresh_le`). What wave-1 did NOT do is ASSEMBLE the
honest extraction statement — the one quantified over an ADVERSARY's OWN published node list, tying
the ε to the event that the straight-line extractor has something to read. That is this file.

## ⚑ THE HONEST EXTRACTION STATEMENT — adversary-quantified, explicit ε, non-vacuous

The adversary is `M : OracleComp (α × α) α (List ((α × α) × α))`: a `Q`-query oracle computation
that, alongside its run, PUBLISHES a list of claimed interior nodes `(preimage, value)` (the nodes
of the Merkle tree it commits to). The FORGERY event is `anyFreshHit`: SOME published node verifies
(`H preimage = value`) although its preimage is NOT in the adversary's own query set — precisely the
case where the straight-line extractor has nothing to read.

  1. **THE ε — `anyFreshHit_prob_le` (§1).** Conditioned on EVERYTHING a `Q`-query adversary learned
     (the cylinder over its own `queriedFinset`, `card ≤ Q`), the forgery probability is at most
     `(#published nodes)/|α|`. Quantified over ADVERSARIES `M`, with an explicit numeric ε. Its
     value is TIGHT, not slack: wave-1's `freshHit_prob_eq_of_fresh` gives `= 1/|α|` per genuinely
     fresh node, and §4's `pubGuesser_prob_eq` realises the bound exactly at `|Bool| = 2`.

  2. **THE COMPLEMENT ⟹ EXTRACTABLE — `no_anyFreshHit_accepted_logged` / `_find_succeeds` (§2).** On
     any oracle in the cylinder where `anyFreshHit M H = false` (probability `≥ 1 − ε`), EVERY
     accepted published node `(H p.1 = p.2)` has its preimage LOGGED — `(p.1, p.2) ∈ M.log H` — so
     the straight-line extractor's primitive step (`List.find?` a logged pair whose ANSWER is this
     node value) SUCCEEDS at every accepted node. This is real content, not a tautology: the
     antecedent (the opening verifies) does NOT imply the conclusion — the `partial_commitment`
     witness of wave-1 is exactly an accepted opening WITH a node not in the log. The gap is the ε.

  3. **THE DEPLOYED NUMBER — `deployed_anyFreshHit_prob_le` (§3).** At the shipped BabyBear node
     oracle (`|α| = |F| = 2013265921`), a depth-`d` tree of `≤ 2^d − 1` interior nodes has forgery
     probability `≤ (2^d − 1)/2013265921`. Read this honestly: at `logN = 21` it is `≈ 2^−9.9` — the
     union bound over the tree, NOT a cryptographic margin.

  4. **THE BUNDLE — `honest_extraction` (§2).** `(1) ∧ (2)`: the single honest verdict. And
     `honest_extraction_binds` (reusing wave-1's `log_column_total_and_binds`) closes the loop: WHEN
     the prover published a COMPLETE tree (`treeExtract` succeeds), the extracted column is total,
     unique-up-to-collision, and binds every accepted opening — the object
     `FriColumnDecode.decodeColumn` consumes (`getD … 0`), modulo the leaf-digest layer (a1).

## What this ε does NOT price (the named residual, NOT papered)

The forgery mode is ONE of two extraction failures wave-1 exhibited. The OTHER —
`partial_commitment_verifies_but_no_total_column` — is the prover leaving a subtree UN-PUBLISHED
(un-hashed): it is DETERMINISTIC, pays no `1/|α|`, exhibits no collision, and survives every spot
check that avoids it. `anyFreshHit_prob_le` says NOTHING about that mode: it bounds only nodes the
adversary DID publish and that verify freshly. The un-published remainder is sub-seam (b), the
spot-check gap, with cost `(1 − μ)^k` in the query parameter (`FriQuerySamplingBias.epsQueryBias`'s
exponent) — NOT a Merkle-binding term. So the honest verdict of the (a)-seam is:

  > Except with probability `≤ (#published nodes)/|α|` over the `Q`-bounded run, the straight-line
  > extractor reads back EVERY node the prover published and the verifier accepts. The gap to a
  > TOTAL column at every domain position is what the prover left un-published — sub-seam (b),
  > deterministic, priced `(1 − μ)^k`, NOT by this ε.

## Discipline

Sorry-free; no `axiom`; no `native_decide`; no `def …Sound` carrier. `#assert_all_clean` ⊆
`{propext, Classical.choice, Quot.sound}`. ADDITIVE: `FriColumnLogExtract` (wave-1),
`FriVerifierMerkle`, `RomOracle`, `RomQueryLog`, `RomCounting` imported read-only / untouched. The
extractor, `condProb_anyFresh_le`, `eval_const_on_own_cylinder`, and `log_column_total_and_binds`
are REUSED from wave-1, not forked.
-/
import Dregg2.Circuit.FriColumnLogExtract

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.FriColumnLogExtractHonest

open Dregg2.Crypto.RomOracle
open Dregg2.Crypto.RomCounting
open Dregg2.Circuit.FriVerifierMerkle (queriedFinset mem_queriedFinset_iff merkleRecO)
open Dregg2.Circuit.FriColumnLogExtract

/-! ## §0 — Two log/list read-back lemmas the assembly needs. -/

/-- **A LOGGED QUERY IS A LOGGED FAITHFUL PAIR.** If the adversary queried `d`, then the faithful
pair `(d, H d)` is in its log. (`log`'s domain projection is `queried`; the recorded answer is
`H`.) -/
theorem mem_queried_pair_in_log {α A : Type} (M : OracleComp (α × α) α A) (H : α × α → α)
    {d : α × α} (hd : d ∈ M.queried H) : (d, H d) ∈ M.log H := by
  have hmap : d ∈ (M.log H).map Prod.fst := by
    rw [M.log_map_fst_eq_queried]; exact hd
  rw [List.mem_map] at hmap
  obtain ⟨pair, hpair, hfst⟩ := hmap
  obtain ⟨p1, p2⟩ := pair
  have hfst' : p1 = d := hfst
  subst hfst'
  have hans : H p1 = p2 := M.mem_log_answer H hpair
  rw [hans]; exact hpair

/-- **`find?` SUCCEEDS WHEN A MATCH IS PRESENT.** If some `x ∈ l` satisfies `pred`, then
`l.find? pred` is `some`. The generic list fact the extractor's per-node step needs. -/
theorem find?_isSome_of_mem {β : Type} (pred : β → Bool) :
    ∀ (l : List β) (x : β), x ∈ l → pred x = true → (l.find? pred).isSome = true := by
  intro l
  induction l with
  | nil => intro x hx _; simp at hx
  | cons a t ih =>
      intro x hx hpx
      by_cases hpa : pred a = true
      · rw [List.find?_cons_of_pos hpa]; rfl
      · rw [List.find?_cons_of_neg hpa]
        rcases List.mem_cons.1 hx with rfl | ht
        · exact absurd hpx hpa
        · exact ih x ht hpx

section Honest

variable {α : Type} [Fintype α] [DecidableEq α]

/-! ## §1 — The forgery event over an adversary's PUBLISHED node list, and its ε. -/

/-- **⚑ THE FORGERY EVENT (adversary-published node list).** The adversary `M` publishes a list of
claimed interior nodes `(preimage, value)`. `anyFreshHit M H` fires iff SOME published node both
verifies against the oracle (`H preimage = value`) and has a preimage the adversary NEVER queried —
exactly the node at which the straight-line extractor has nothing to read. -/
def anyFreshHit (M : OracleComp (α × α) α (List ((α × α) × α))) (H : α × α → α) : Bool :=
  (M.eval H).any (fun p => decide (H p.1 = p.2) && decide (p.1 ∉ queriedFinset M H))

/-- **⚑ THE ε — AGAINST ANY `Q`-QUERY ADVERSARY, WITH AN EXPLICIT VALUE.** Conditioned on the whole
of what a `Q`-query adversary learned (its own `queriedFinset`, `card ≤ Q`), the probability that
its published node list contains ANY freshly-verifying node — i.e. the probability the straight-line
extractor has nothing to read at some published node — is at most `(#published nodes)/|α|`.

Quantified over ADVERSARIES `M`, not over words; the bound is a number. The route: inside the
adversary's OWN cylinder its output and query set are CONSTANT (`eval_const_on_own_cylinder`), so the
event reduces to wave-1's fixed-list union bound `condProb_anyFresh_le` at `ps := M.eval σ`. -/
theorem anyFreshHit_prob_le (M : OracleComp (α × α) α (List ((α × α) × α))) (σ : α × α → α) :
    condProb (cyl (queriedFinset M σ) σ) (anyFreshHit M)
      ≤ ((M.eval σ).length : ℝ) / (Fintype.card α : ℝ) := by
  have hcongr : condProb (cyl (queriedFinset M σ) σ) (anyFreshHit M)
      = condProb (cyl (queriedFinset M σ) σ)
          (fun H => (M.eval σ).any
            (fun p => decide (H p.1 = p.2) && decide (p.1 ∉ queriedFinset M σ))) := by
    refine condProb_congr (fun H hH => ?_)
    obtain ⟨hev, hq⟩ := eval_const_on_own_cylinder M σ H hH
    unfold anyFreshHit
    rw [hev, hq]
  rw [hcongr]
  exact condProb_anyFresh_le (queriedFinset M σ) σ (M.eval σ)

/-! ## §2 — The complement: on `¬anyFreshHit`, every accepted published node is extractable. -/

/-- **⚑ THE COMPLEMENT ⟹ EXTRACTABLE.** On any oracle where `anyFreshHit M H = false`, EVERY
accepted published node — `p ∈ M.eval H` with `H p.1 = p.2` — has its preimage in the LOG:
`(p.1, p.2) ∈ M.log H`. So the extractor's data really is present at that node. This is the honest
positive content, and it is NOT vacuous: `partial_commitment_verifies_but_no_total_column` (wave-1)
is exactly an accepted opening whose tree has a node NOT in the log — that node is the `anyFreshHit`
event this rules out on the good branch. -/
theorem no_anyFreshHit_accepted_logged
    (M : OracleComp (α × α) α (List ((α × α) × α))) (H : α × α → α)
    (hno : anyFreshHit M H = false)
    {p : (α × α) × α} (hp : p ∈ M.eval H) (hacc : H p.1 = p.2) :
    (p.1, p.2) ∈ M.log H := by
  by_contra hcontra
  -- If the preimage were queried, the faithful pair would be logged — contradicting `hcontra`.
  have hfresh : p.1 ∉ queriedFinset M H := by
    intro hin
    have hq : p.1 ∈ M.queried H := (mem_queriedFinset_iff M H p.1).1 hin
    have hlog : (p.1, H p.1) ∈ M.log H := mem_queried_pair_in_log M H hq
    rw [hacc] at hlog
    exact hcontra hlog
  -- Then `p` is a fresh accepted node, so `anyFreshHit` FIRES — contradicting `hno`.
  have hbit : (decide (H p.1 = p.2) && decide (p.1 ∉ queriedFinset M H)) = true := by
    rw [show decide (H p.1 = p.2) = true from by simp [hacc],
        show decide (p.1 ∉ queriedFinset M H) = true from by simp [hfresh], Bool.and_self]
  have hfire : anyFreshHit M H = true := by
    unfold anyFreshHit
    exact List.any_eq_true.2 ⟨p, hp, hbit⟩
  rw [hno] at hfire
  exact Bool.noConfusion hfire

/-- **⚑ THE EXTRACTOR'S PER-NODE STEP SUCCEEDS.** On the good branch (`anyFreshHit M H = false`),
`treeExtract`'s primitive lookup at an accepted published node's value — `find?` a logged pair whose
ANSWER is that value — returns `some`. So the extractor never dies at a node the prover published and
the verifier accepts; the only way it dies is the un-published remainder (sub-seam (b)). -/
theorem no_anyFreshHit_find_succeeds
    (M : OracleComp (α × α) α (List ((α × α) × α))) (H : α × α → α)
    (hno : anyFreshHit M H = false)
    {p : (α × α) × α} (hp : p ∈ M.eval H) (hacc : H p.1 = p.2) :
    ((M.log H).find? (fun e => decide (e.2 = p.2))).isSome = true := by
  have hlog : (p.1, p.2) ∈ M.log H := no_anyFreshHit_accepted_logged M H hno hp hacc
  exact find?_isSome_of_mem (fun e => decide (e.2 = p.2)) (M.log H) (p.1, p.2) hlog (by simp)

/-- **⚑ THE HONEST EXTRACTION THEOREM (the bundle).** For EVERY `Q`-query adversary `M` and any
conditioning `σ`:
  1. the forgery probability is `≤ (#published nodes)/|α|` — adversary-quantified, explicit ε; and
  2. on its complement (`≥ 1 − ε`), every accepted published node is in the log — extractable.
No hypothesis on `M` beyond it being an oracle computation; the ε holds for the honest prover too. -/
theorem honest_extraction (M : OracleComp (α × α) α (List ((α × α) × α))) (σ : α × α → α) :
    condProb (cyl (queriedFinset M σ) σ) (anyFreshHit M)
        ≤ ((M.eval σ).length : ℝ) / (Fintype.card α : ℝ)
      ∧ (∀ H ∈ cyl (queriedFinset M σ) σ, anyFreshHit M H = false →
          ∀ p ∈ M.eval H, H p.1 = p.2 → (p.1, p.2) ∈ M.log H) :=
  ⟨anyFreshHit_prob_le M σ,
   fun H _ hno _p hp hacc => no_anyFreshHit_accepted_logged M H hno hp hacc⟩

/-- **⚑ CLOSING THE LOOP TO THE COMMITTED COLUMN (wave-1 reuse).** When the prover published a
COMPLETE depth-`d` tree — i.e. `treeExtract (M.log H) d root = some xs` — the extracted column `xs`
is total (`2^d` entries), a genuine `H`-tree, and every opening the DEPLOYED verifier accepts reads
back one of its entries, unless `H` collides. Combined with `honest_extraction`: except with prob
`≤ ε`, the extractor's per-node steps all succeed, so this hypothesis holds whenever the prover
published EVERY node; the residual `treeExtract = none` with no fresh hit is the un-published subtree
= sub-seam (b). (`xs.getD … dflt` is `FriColumnDecode.decodeColumn`'s shape, modulo (a1).) -/
theorem honest_extraction_binds
    (M : OracleComp (α × α) α (List ((α × α) × α))) (H : α × α → α)
    (d : ℕ) (root : α) (xs : List α) (dflt : α)
    (hex : treeExtract (M.log H) d root = some xs) :
    xs.length = 2 ^ d ∧ IsTree H d root xs
      ∧ (∀ (i : ℕ) (v : α) (sibs : List α), sibs.length = d →
          merkleRecO H i v sibs = root → xs.getD (i % 2 ^ d) dflt = v ∨ HasCollision H) :=
  log_column_total_and_binds M H d root xs dflt hex

/-! ## §3 — The deployed number. -/

/-- **⚑ THE DEPLOYED FORGERY BOUND.** At the shipped BabyBear node oracle (`|α| = 2013265921`), a
`Q`-query adversary publishing a depth-`d` tree of `≤ 2^d − 1` interior nodes forges an
extractor-unreadable node with probability `≤ (2^d − 1)/2013265921`. At `logN = 21` this is `≈ 2^−9.9`
— the union bound over the tree, NOT a cryptographic margin, and NOT the un-published remainder. -/
theorem deployed_anyFreshHit_prob_le (hcard : Fintype.card α = 2013265921)
    (M : OracleComp (α × α) α (List ((α × α) × α))) (σ : α × α → α) (d : ℕ)
    (hlen : (M.eval σ).length ≤ 2 ^ d - 1) :
    condProb (cyl (queriedFinset M σ) σ) (anyFreshHit M)
      ≤ ((2 ^ d - 1 : ℕ) : ℝ) / (2013265921 : ℝ) := by
  have h := anyFreshHit_prob_le M σ
  rw [hcard] at h
  have hden : ((2013265921 : ℕ) : ℝ) = (2013265921 : ℝ) := by norm_num
  rw [hden] at h
  refine h.trans ?_
  rw [div_le_div_iff_of_pos_right (show (0 : ℝ) < 2013265921 by norm_num)]
  exact_mod_cast hlen

end Honest

/-! ## §4 — TEETH: the ε is REAL and TIGHT (a degenerate instance cannot make it vacuous). -/

section Teeth

/-- A `QueryBounded 0` adversary over `α = Bool` that PUBLISHES one guessed node `((true,true),false)`
without querying anything. -/
def pubGuesser : OracleComp (Bool × Bool) Bool (List ((Bool × Bool) × Bool)) :=
  .pure [((true, true), false)]

theorem pubGuesser_bounded : QueryBounded 0 pubGuesser := QueryBounded.pure 0 _

/-- The guesser queries nothing, so its conditioning set is empty. -/
theorem pubGuesser_queriedFinset (σ : Bool × Bool → Bool) :
    queriedFinset pubGuesser σ = (∅ : Finset (Bool × Bool)) := by
  unfold queriedFinset pubGuesser
  simp [OracleComp.queried]

/-- **⚑ THE ε IS TIGHT — not vacuously zero.** The guesser publishes ONE node with a preimage it
never queried; its forgery probability is EXACTLY `1/|Bool| = 1/2` — the `anyFreshHit_prob_le` bound
at `#published = 1` realised. So the ε in `honest_extraction` is a genuine, achieved budget: no
sharpening drives it to `0`, and no degenerate instance satisfies the honest statement vacuously. -/
theorem pubGuesser_prob_eq (σ : Bool × Bool → Bool) :
    condProb (cyl (queriedFinset pubGuesser σ) σ) (anyFreshHit pubGuesser)
      = 1 / (Fintype.card Bool : ℝ) := by
  rw [pubGuesser_queriedFinset]
  have hcongr : condProb (cyl (∅ : Finset (Bool × Bool)) σ) (anyFreshHit pubGuesser)
      = condProb (cyl (∅ : Finset (Bool × Bool)) σ) (fun H => decide (H (true, true) = false)) := by
    refine condProb_congr (fun H _ => ?_)
    show anyFreshHit pubGuesser H = decide (H (true, true) = false)
    unfold anyFreshHit pubGuesser
    simp [OracleComp.eval, OracleComp.queried, queriedFinset]
  rw [hcongr]
  exact condProb_fresh_eq (∅ : Finset (Bool × Bool)) σ (true, true) (by simp) false

/-- **THE FORGERY EVENT GENUINELY FIRES.** Against the constant-`false` oracle the guesser's
published node verifies and is fresh, so `anyFreshHit` is `true`. The good branch of
`honest_extraction` is a real restriction, not the whole space. -/
theorem pubGuesser_fires : anyFreshHit pubGuesser (fun _ => false) = true := by
  unfold anyFreshHit pubGuesser
  simp [OracleComp.eval, OracleComp.queried, queriedFinset]

end Teeth

/-! ## §5 — The honest verdict, in Lean vocabulary.

`honest_extraction` is what the straight-line extractor DELIVERS over a `Q`-bounded adversary run:
except with probability `≤ (#published nodes)/|α|` (`anyFreshHit_prob_le`, tight per
`pubGuesser_prob_eq`), EVERY node the prover published and the verifier accepts is in the log and
therefore extractable (`no_anyFreshHit_accepted_logged`, `no_anyFreshHit_find_succeeds`). When the
prover published a COMPLETE tree, the extracted column is total, unique-up-to-collision, and binds
every opening (`honest_extraction_binds`, wave-1).

This is adversary-quantified, has an explicit ε (`deployed_anyFreshHit_prob_le` at
`|α| = 2013265921`), and is non-trivializable: the antecedent (an opening verifies) does NOT imply
the conclusion — the `partial_commitment` witness of wave-1 is an accepted opening whose tree omits a
node, and that omission is precisely what costs the ε (or, if UN-published rather than freshly
forged, is the DETERMINISTIC sub-seam (b) this ε does not price).

NAMED, not papered: the un-published remainder — the prover leaving a subtree un-hashed — is
sub-seam (b), cost `(1 − μ)^k` in the spot-check parameter, NOT a Merkle-binding term. The
felt↔leaf-digest layer (a1), the `α`-pin (a2), and root↔`verifyAlgo` plumbing (a3) remain wave-1's
named carriers, unchanged. -/

#assert_all_clean [
  mem_queried_pair_in_log,
  find?_isSome_of_mem,
  anyFreshHit_prob_le,
  no_anyFreshHit_accepted_logged,
  no_anyFreshHit_find_succeeds,
  honest_extraction,
  honest_extraction_binds,
  deployed_anyFreshHit_prob_le,
  pubGuesser_bounded,
  pubGuesser_queriedFinset,
  pubGuesser_prob_eq,
  pubGuesser_fires
]

end Dregg2.Circuit.FriColumnLogExtractHonest
