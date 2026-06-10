/-
# Dregg2.Authority.ConfluenceClassifier — the I-CONFLUENCE GUARD CLASSIFIER (DREGG3 §8 dual).

The guard-algebra uplift (`Exec.RelationalCaveat` axis 1, the record-level relational guard;
`Authority.CausalGuard` axis 2, the causal guard atoms) gives an app author a richer guard
vocabulary — guards that read the record, the past, the order. That power has a REAL cost, and this
module makes the cost a DECIDABLE, PROVED question instead of folklore.

The cost is I-confluence (the third logic of `CONSTRUCTIVE-KNOWLEDGE.md` §4, the independence
lattice). A guard installs an invariant on the cell. Two concurrent turns each preserve that
invariant locally; do their results MERGE (join, `⊔`) invariant-safely? If yes, the guard runs
COORDINATION-FREE — tier-1, partition-tolerant, no consensus. If no, the system must serialize the
two turns — it forces ORDERING (consensus). This is not a bug in the guard; it is the system telling
the app author the TRUE COST of the guard they asked for.

`Authority.CausalGuard` established the two POLES (`monotone_guard_is_iconfluent`,
`bounded_resource_not_iconfluent`); `Confluence.lean` gives the merge lattice (`MergeState`) and the
judgement (`IConfluent`). THIS module builds the general CLASSIFIER between the poles:

  * `Guard S` — a small guard language over a merge-state: a `monotone` floor, a `bounded` ceiling,
    and an arbitrary `relational` invariant (the record-level relational guard's shape).
  * `guardInv g` — the invariant a guard installs on the cell.
  * `guardKeepsConfluence g := IConfluent (guardInv g)` — THE classifier, connected to the existing
    `Confluence.IConfluent` machinery; decidably TRUE on the monotone pole, decidably FALSE on the
    bounded pole, and DECIDED-BY-MERGE on the relational arm.
  * `CoordinationFree g` — the cost verdict: the guard's cell may select the tier-1 finality rule
    (`Confluence.Tier1Eligible`). The PAYOFF: `guardKeepsConfluence g ↔ CoordinationFree g` — an app
    author installing a guard gets a PROOF of its coordination cost (and the contrapositive: a guard
    that is NOT confluence-keeping forces ordering, with a constructive clashing-pair witness).

The three classification theorems (the dichotomy, crisply):
  (a) `monotone_keeps`        — a grow-only floor guard is ALWAYS confluence-keeping (runs free);
  (b) `bounded_breaks`        — a ceiling/cardinality-bound guard is NOT, unless serialized;
  (c) `relational_decided_by_merge` — a relational guard keeps confluence IFF its relation is
      preserved under the pointwise-max merge (the join). The decision is the merge, nothing else.

NON-VACUITY: a concrete monotone guard classified confluence-keeping AND runs free; a concrete
ceiling guard classified NOT, AND forced to order (a constructive clashing pair). Both witnessed.

NEW file only. Reuses `Confluence` (the lattice + `IConfluent` + `Tier1Eligible` + the escalation
witness) and the two poles' shapes; defines no new lattice. Every keystone `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}` — no sorry, no `:= True`.
-/
import Dregg2.Confluence
import Dregg2.Confluence.CRDT
import Dregg2.Authority.CausalGuard

namespace Dregg2.Authority.ConfluenceClassifier

open Dregg2.Confluence

universe u

/-! ## §1 — The guard language (over a merge-state).

A `Guard S` is one installable invariant-bearing guard over a cell whose mergeable state is a
`MergeState S`. Three arms span the §8 vocabulary's confluence-relevant shapes:

  * `monotone proj c` — a grow-only FLOOR: a value-projection `proj : S → ℕ` is `≥ c`. This is the
    `aboveFloor`/`monotoneOverForks` shape (a high-water mark, a sequence number, a grow-only count).
  * `bounded proj c` — a resource CEILING: a value-projection `proj : S → ℕ` is `≤ c`. The
    `balance ≥ 0` / `card ≤ 1` / `withinBudget` shape (a bounded resource).
  * `relational P` — an ARBITRARY record-level invariant `P : Invariant S` (the
    `Exec.RelationalCaveat.FieldLteOther` shape: a cross-slot relation read off the whole record).
    Whether it keeps confluence is DECIDED by the merge, not by the syntactic arm. -/

/-- **`Guard S`** — an installable guard over a cell with mergeable state `S`. The three arms are the
confluence-relevant shapes of the §8 guard vocabulary; each DENOTES an invariant (`guardInv`). -/
inductive Guard (S : Type u) [MergeState S] where
  /-- A grow-only FLOOR: the projection `proj` is `≥ c` (a high-water mark / monotone value). -/
  | monotone (proj : S → ℕ) (c : ℕ)
  /-- A resource CEILING: the projection `proj` is `≤ c` (a bounded resource — the `balance ≥ 0`
  shape). -/
  | bounded (proj : S → ℕ) (c : ℕ)
  /-- An ARBITRARY relational invariant (the record-level relational guard's shape) — its confluence
  is decided by the merge. -/
  | relational (P : Invariant S)

/-- **`guardInv g` — the invariant a guard installs on the cell.** The classifier asks whether THIS
invariant is preserved by the merge. -/
def guardInv {S : Type u} [MergeState S] : Guard S → Invariant S
  | .monotone proj c   => fun s => c ≤ proj s
  | .bounded proj c    => fun s => proj s ≤ c
  | .relational P      => P

/-! ## §2 — THE CLASSIFIER and the cost verdict.

`guardKeepsConfluence g` is the classifier: is the guard's installed invariant I-confluent (preserved
by every concurrent merge)? It is exactly `Confluence.IConfluent` over the guard's invariant, so it
plugs into all the existing machinery (`admits_sound`, `nonpairwise_escalation`, `Tier1Eligible`).

`CoordinationFree g` is the cost verdict: the guard's cell may select the tier-1 (causal-only,
coordination-free, partition-tolerant) finality rule — i.e. `Confluence.Tier1Eligible (guardInv g)`. -/

/-- **`guardKeepsConfluence g` — THE classifier.** A guard keeps coordination-freedom IFF its
installed invariant is I-confluent: every pair of concurrent invariant-preserving versions merges
invariant-safely (`Confluence.IConfluent`). The decidable-in-spirit "is this guard cheap?" question,
connected to the existing third-judgement machinery. -/
def guardKeepsConfluence {S : Type u} [MergeState S] (g : Guard S) : Prop :=
  IConfluent (guardInv g)

/-- **`CoordinationFree g` — the cost VERDICT.** A guard runs coordination-free (tier-1,
partition-tolerant, no consensus) iff its cell is `Confluence.Tier1Eligible` — the static
well-formedness side-condition BEC Thm 3.1 requires for the causal-only finality rule. Definitionally
`Tier1Eligible (guardInv g)`. -/
def CoordinationFree {S : Type u} [MergeState S] (g : Guard S) : Prop :=
  Tier1Eligible (guardInv g)

/-- **`ForcesOrdering g` — the dual verdict.** A guard that is NOT confluence-keeping forces the cell
to SERIALIZE concurrent turns (escalate to consensus / a global order). Stated as the negation of the
classifier — the system's honest "this guard is not cheap". -/
def ForcesOrdering {S : Type u} [MergeState S] (g : Guard S) : Prop :=
  ¬ guardKeepsConfluence g

/-! ## §3 — THE COST-PAYOFF THEOREM (the dichotomy, crisply).

An app author installing a guard gets a PROOF of its coordination cost. The classifier verdict IS the
tier-1 eligibility verdict (the iff), and a non-keeping guard forces ordering with a CONSTRUCTIVE
clashing-pair witness — not a mere declaration. -/

/-- **`keeps_iff_coordinationFree` — THE PAYOFF (the dichotomy).** A guard keeps confluence IFF it
runs coordination-free. Definitionally an `Iff.rfl` (the classifier and the cost verdict are the same
predicate under different names), but stated as the load-bearing app-author guarantee: classifying a
guard confluence-keeping IS a proof it runs tier-1 (and conversely). -/
theorem keeps_iff_coordinationFree {S : Type u} [MergeState S] (g : Guard S) :
    guardKeepsConfluence g ↔ CoordinationFree g :=
  -- `CoordinationFree g = Tier1Eligible (guardInv g) = IConfluent (guardInv g) = guardKeepsConfluence g`.
  Iff.rfl

/-- **`keeps_runs_free` — confluence-keeping ⇒ runs coordination-free.** The forward payoff: a
confluence-keeping guard's concurrent merges genuinely preserve its invariant
(`Confluence.admits_sound`), so the cell may run tier-1. The proof an app author is handed when the
classifier says YES. -/
theorem keeps_runs_free {S : Type u} [MergeState S] (g : Guard S)
    (h : guardKeepsConfluence g) : CoordinationFree g :=
  (keeps_iff_coordinationFree g).mp h

/-- **`not_keeps_forces_ordering` — the CONTRAPOSITIVE (the honest cost).** A guard that is NOT
confluence-keeping forces ordering: there is a CONCRETE clashing pair of states, each preserving the
guard's invariant, whose merge VIOLATES it (`Confluence.nonpairwise_escalation`). Escalation to
consensus is forced by a constructive counterexample, not merely declared — the system tells the app
author, with a witness, exactly why their guard is not cheap. -/
theorem not_keeps_forces_ordering {S : Type u} [MergeState S] (g : Guard S)
    (h : ¬ guardKeepsConfluence g) :
    ForcesOrdering g ∧
      ∃ x y : S, guardInv g x ∧ guardInv g y ∧ ¬ guardInv g (x ⊔ y) :=
  ⟨h, nonpairwise_escalation (guardInv g) h⟩

/-! ## §4 — THE THREE CLASSIFICATION THEOREMS.

The dichotomy made syntactic: the monotone arm ALWAYS keeps confluence (generalizing
`CausalGuard.monotone_guard_is_iconfluent`); the bounded arm BREAKS it for a non-trivial ceiling
(generalizing `CausalGuard.bounded_resource_not_iconfluent`); the relational arm's verdict is the
merge itself — confluence-keeping IFF the relation survives the pointwise-max join. -/

/-! ### §4(a) — MONOTONE keeps (always confluence-keeping, runs free).

A grow-only floor guard `monotone proj c` is confluence-keeping for ANY projection `proj` that is
MONOTONE under the merge (`x ≤ y → proj x ≤ proj y`) — the merge only raises the projection, so the
floor survives. Every join-semilattice projection of practical interest (a coordinate read, a
high-water mark, `id` on `ℕ`) is monotone; we state the general theorem and then the canonical
`ℕ`-mark instance the causal-monotone pole lands on. -/

/-- **`monotone_keeps` — (a) a MONOTONE FLOOR guard ALWAYS keeps confluence (PROVED).** If the
projection is monotone under the merge (`x ≤ y → proj x ≤ proj y` — the grow-only / high-water-mark
property a `monotoneOverForks` guard maintains), the floor invariant `c ≤ proj s` is I-confluent: a
merge only RAISES the projection (`le_sup_left` + monotonicity), so two branches above the floor merge
above the floor. The guard runs coordination-free (tier-1) — the I-confluence side the monotone pole
lands on, generalized off the concrete `aboveFloor`. -/
theorem monotone_keeps {S : Type u} [MergeState S] (proj : S → ℕ) (c : ℕ)
    (hmono : ∀ x y : S, x ≤ y → proj x ≤ proj y) :
    guardKeepsConfluence (Guard.monotone proj c) := by
  intro x y hx _hy
  -- the merge raises the projection: `proj x ≤ proj (x ⊔ y)` by monotonicity on `x ≤ x ⊔ y`.
  exact le_trans hx (hmono x (x ⊔ y) le_sup_left)

/-- **`monotone_keeps_runs_free` — the monotone pole's cost VERDICT.** A monotone floor guard (with a
merge-monotone projection) runs coordination-free — `monotone_keeps` through the payoff. The proof an
app author is handed for a grow-only guard: no consensus, partition-tolerant. -/
theorem monotone_keeps_runs_free {S : Type u} [MergeState S] (proj : S → ℕ) (c : ℕ)
    (hmono : ∀ x y : S, x ≤ y → proj x ≤ proj y) :
    CoordinationFree (Guard.monotone proj c) :=
  keeps_runs_free _ (monotone_keeps proj c hmono)

/-! ### §4(b) — BOUNDED breaks (not confluence-keeping, unless serialized).

A resource ceiling guard `bounded proj c` is NOT confluence-keeping whenever the projection can be
SPLIT across two branches that each sit at-or-below the ceiling but whose merge raises the projection
over it — the `balance ≥ 0` / bounded-budget shape. We give the general "breaks" criterion (a clashing
pair exists) and then instantiate it on the canonical two-replica budget, reusing the catalog's proved
non-confluence. -/

/-- **`bounded_breaks` — (b) a BOUNDED CEILING guard BREAKS confluence given a clashing split (PROVED).**
If two states `x`, `y` each sit within the ceiling (`proj ≤ c`) but their merge overshoots it
(`¬ proj (x ⊔ y) ≤ c` — the "two concurrent spends that each fit, but not together" shape), the
ceiling guard is NOT I-confluent. The cell must SERIALIZE: it forfeits tier-1 and forces ordering
(consensus). This is the bounded-resource pole, generalized off `cardLeOne_not_iconfluent`. -/
theorem bounded_breaks {S : Type u} [MergeState S] (proj : S → ℕ) (c : ℕ)
    {x y : S} (hx : proj x ≤ c) (hy : proj y ≤ c) (hbad : ¬ proj (x ⊔ y) ≤ c) :
    ¬ guardKeepsConfluence (Guard.bounded proj c) := by
  intro h
  -- `h` says the ceiling invariant `proj · ≤ c` is I-confluent; apply at the clashing pair.
  exact hbad (h x y hx hy)

/-- **`bounded_forces_ordering` — the bounded pole's cost VERDICT (with the constructive witness).**
A ceiling guard with a clashing split forces ordering, and exhibits the clashing pair: each branch
within the ceiling, their merge over it. The honest cost the system reports for a bounded-resource
guard — consensus, with a counterexample, never a bare claim. -/
theorem bounded_forces_ordering {S : Type u} [MergeState S] (proj : S → ℕ) (c : ℕ)
    {x y : S} (hx : proj x ≤ c) (hy : proj y ≤ c) (hbad : ¬ proj (x ⊔ y) ≤ c) :
    ForcesOrdering (Guard.bounded proj c) ∧
      ∃ a b : S, guardInv (Guard.bounded proj c) a ∧ guardInv (Guard.bounded proj c) b ∧
        ¬ guardInv (Guard.bounded proj c) (a ⊔ b) :=
  not_keeps_forces_ordering _ (bounded_breaks proj c hx hy hbad)

/-! ### §4(c) — RELATIONAL: confluence is DECIDED by the merge.

A relational guard `relational P` carries an arbitrary record-level invariant `P` (the
`FieldLteOther` cross-slot relation's shape). Its confluence verdict is NOT read off the syntax — it
is EXACTLY whether `P` is preserved under the pointwise-max merge (the join). The classifier reduces
to the merge-preservation question; that is the dichotomy's only honest answer for a general
relation. -/

/-- **`relational_decided_by_merge` — (c) a RELATIONAL guard's confluence is DECIDED by the merge
(PROVED).** A relational guard keeps confluence IFF its invariant `P` is preserved under the pointwise
join: `(∀ x y, P x → P y → P (x ⊔ y)) ↔ guardKeepsConfluence (relational P)`. The verdict is the
merge, nothing else — there is no syntactic shortcut for a general cross-slot relation; the app author
must show (or the executor must check) that the join preserves `P`. -/
theorem relational_decided_by_merge {S : Type u} [MergeState S] (P : Invariant S) :
    (∀ x y : S, P x → P y → P (x ⊔ y)) ↔ guardKeepsConfluence (Guard.relational P) :=
  -- `guardKeepsConfluence (relational P) = IConfluent P`, which unfolds to exactly the LHS.
  Iff.rfl

/-- **`relational_keeps_of_join_preserved` — the relational app-author lever.** If the app author
SUPPLIES a proof that their relation survives the join, the relational guard is classified
confluence-keeping and therefore runs coordination-free. The decision is handed back as a tier-1
verdict. -/
theorem relational_keeps_of_join_preserved {S : Type u} [MergeState S] (P : Invariant S)
    (hjoin : ∀ x y : S, P x → P y → P (x ⊔ y)) :
    CoordinationFree (Guard.relational P) :=
  keeps_runs_free _ ((relational_decided_by_merge P).mp hjoin)

/-! ## §5 — NON-VACUITY: both poles witnessed concretely.

The teeth: a concrete MONOTONE guard classified confluence-keeping AND running free; a concrete
CEILING guard classified NOT AND forced to order (with the constructive clashing pair). The classifier
is genuinely two-sided, never vacuous. -/

namespace Witness

open Dregg2.Confluence.CRDT

/-! ### §5(a) — A monotone guard that runs FREE.

A `ℕ` high-water mark with the identity projection and floor `c`: `id` is monotone (`le` is `le`), so
`monotone_keeps` fires. The mark runs coordination-free — the grow-only pole. -/

/-- The concrete monotone guard: a `ℕ` high-water mark with floor `3` (`id`-projection ≥ 3). -/
def markGuard : Guard ℕ := Guard.monotone id 3

/-- **`markGuard_keeps` — the monotone guard IS classified confluence-keeping (PROVED).** The
identity projection on `ℕ` is monotone (`x ≤ y → x ≤ y`), so the floor `3 ≤ ·` is I-confluent: two
marks ≥ 3 merge (by `max`) to a mark still ≥ 3. -/
theorem markGuard_keeps : guardKeepsConfluence markGuard :=
  monotone_keeps id 3 (fun _ _ h => h)

/-- **`markGuard_runs_free` — and therefore RUNS COORDINATION-FREE (PROVED).** The cost verdict for
the monotone pole: the mark guard is `Tier1Eligible` — partition-tolerant, no consensus. The proof an
app author gets for a grow-only guard. -/
theorem markGuard_runs_free : CoordinationFree markGuard :=
  keeps_runs_free markGuard markGuard_keeps

-- The classifier verdict, executable: a merge of two above-floor marks stays above the floor.
#guard (decide (3 ≤ (5 ⊔ 9 : ℕ)))                         -- true  (5,9 ≥ 3 ⇒ max 9 ≥ 3: stays free)
#guard (decide (3 ≤ id (5 : ℕ)))                          -- true  (guardInv markGuard 5 = 3 ≤ 5)

/-! ### §5(b) — A ceiling guard that FORCES ORDERING.

A two-replica budget (`Budget = GCounter (Fin 2)`) with the `consumed` projection and ceiling `1`: the
catalog's `withinBudget_not_iconfluent` is exactly this guard's non-confluence. `(1,0)` and `(0,1)`
each consume ≤ 1, but their merge consumes 2 — the clashing split. The guard forces ordering. -/

/-- The concrete ceiling guard: a two-replica budget with `consumed ≤ 1` (the bounded resource). -/
def budgetGuard : Guard Budget := Guard.bounded consumed 1

/-- The clashing split: replica-0 at the ceiling, replica-1 at the ceiling — each within budget. -/
def splitX : Budget := fun i => if i = 0 then 1 else 0
def splitY : Budget := fun i => if i = 0 then 0 else 1

/-- **`budgetGuard_breaks` — the ceiling guard is classified NOT confluence-keeping (PROVED).** The
clashing split `(1,0)`, `(0,1)`: each consumes ≤ 1, but their merge `(1,1)` consumes 2 > 1. So the
ceiling invariant is not I-confluent — `bounded_breaks` on the concrete split. -/
theorem budgetGuard_breaks : ¬ guardKeepsConfluence budgetGuard :=
  bounded_breaks consumed 1
    (show consumed splitX ≤ 1 by decide)
    (show consumed splitY ≤ 1 by decide)
    (show ¬ consumed (splitX ⊔ splitY) ≤ 1 by decide)

/-- **`budgetGuard_forces_ordering` — and therefore FORCES ORDERING (PROVED, with the witness).** The
cost verdict for the bounded pole: the budget guard forces serialization (consensus), and the
constructive clashing pair is exhibited — each branch within budget, their merge over it. The honest
cost the system reports, with a counterexample, never a bare claim. -/
theorem budgetGuard_forces_ordering :
    ForcesOrdering budgetGuard ∧
      ∃ a b : Budget, guardInv budgetGuard a ∧ guardInv budgetGuard b ∧
        ¬ guardInv budgetGuard (a ⊔ b) :=
  not_keeps_forces_ordering budgetGuard budgetGuard_breaks

-- The classifier verdict, executable: the split each fits, the merge overshoots ⇒ forces ordering.
#guard ((consumed splitX, consumed splitY, consumed (splitX ⊔ splitY)) == (1, 1, 2))  -- (1,1,2)
#guard (decide (¬ consumed (splitX ⊔ splitY) ≤ 1))        -- true  (merge overshoots ⇒ not free)

end Witness

/-! ## §6 — Axiom-hygiene pins (the honesty tripwires over every keystone).

Each pin elaborates to an error if the keystone depends on any axiom outside
`{propext, Classical.choice, Quot.sound}` (notably `sorryAx`). -/

-- §3 the cost-payoff theorem (the dichotomy)
#assert_axioms keeps_iff_coordinationFree
#assert_axioms keeps_runs_free
#assert_axioms not_keeps_forces_ordering
-- §4 the three classification theorems
#assert_axioms monotone_keeps
#assert_axioms monotone_keeps_runs_free
#assert_axioms bounded_breaks
#assert_axioms bounded_forces_ordering
#assert_axioms relational_decided_by_merge
#assert_axioms relational_keeps_of_join_preserved
-- §5 the two non-vacuity witnesses
#assert_axioms Witness.markGuard_keeps
#assert_axioms Witness.markGuard_runs_free
#assert_axioms Witness.budgetGuard_breaks
#assert_axioms Witness.budgetGuard_forces_ordering

end Dregg2.Authority.ConfluenceClassifier
