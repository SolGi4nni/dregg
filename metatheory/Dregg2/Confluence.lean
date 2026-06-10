/-
# Dregg2.Confluence — I-confluence: the third judgement (the invariant-merge property).

I-confluence (BEC Thm 3.1): do concurrent invariant-preserving versions merge
invariant-safely? It is independent of conservation and ordering:
  - `balance ≥ 0` is linear but NOT I-confluent (two withdrawals merge to overdraft);
  - a grow-only set is I-confluent but NOT linear.

It is the static well-formedness condition that determines whether a cell may run at
tier-1 (causal-only, coordination-free) or must escalate to consensus. The I-confluent
fragment compiles coordination-free (Hydro/Dedalus/CALM); the non-I-confluent (coupled)
fragment escalates via CryptoConcurrency's sum/coverage.

Literature: Gomes–Kleppmann (Isabelle SEC); Burckhardt et al. (RDT spec & verification).
-/
import Mathlib.Order.Lattice
import Mathlib.Data.Finset.Card

namespace Dregg2.Confluence

universe u

/-- A cell's mergeable state is a join-semilattice; concurrent versions merge by `⊔`
(the CvRDT join — Gomes–Kleppmann / Burckhardt). -/
class MergeState (S : Type u) extends SemilatticeSup S

/-- A cell invariant: the property admissible turns must preserve (e.g. `balance ≥ 0`,
nullifier-uniqueness, a `WriteOnce` slot). -/
abbrev Invariant (S : Type u) := S → Prop

/-- **I-confluence (the third judgement).** `I` is I-confluent over a merge-state iff
concurrent invariant-preserving versions merge invariant-safely (BEC Thm 3.1). -/
def IConfluent {S : Type u} [MergeState S] (I : Invariant S) : Prop :=
  ∀ x y : S, I x → I y → I (x ⊔ y)

/-- **Tier-1 eligibility = the well-formedness side-condition.** A cell may select the
tier-1 (causal-only, coordination-free, partition-tolerant) finality rule **iff** its
invariant is I-confluent. Tier-1 on a non-I-confluent cell is the object BEC Thm 3.1
forbids — a static type error the finality classifier MUST reject. -/
def Tier1Eligible {S : Type u} [MergeState S] (I : Invariant S) : Prop :=
  IConfluent I

/-- **The `FinalityRule.admits` gate (the static check).** The classifier rejects a
tier-1 declaration unless `Tier1Eligible`; soundness = a tier-1 cell's concurrent
merges preserve `I`. (Obligation; the real classifier is over the cell's
write-set × state-lattice — `discoveries §3.7`.) -/
theorem admits_sound {S : Type u} [MergeState S] (I : Invariant S)
    (h : Tier1Eligible I) (x y : S) (hx : I x) (hy : I y) : I (x ⊔ y) := by
  exact h x y hx hy

/-- **`nonpairwise_escalation`** — when `I` is not I-confluent, a concrete clashing pair
`x`, `y` exists: each satisfies `I` but their merge `x ⊔ y` violates it. Escalation to
consensus is forced by a constructive counterexample, not merely declared. -/
theorem nonpairwise_escalation {S : Type u} [MergeState S] (I : Invariant S)
    (hI : ¬ IConfluent I) :
    ∃ x y : S, I x ∧ I y ∧ ¬ I (x ⊔ y) := by
  -- `IConfluent I` is `∀ x y, I x → I y → I (x ⊔ y)`; its negation gives, classically,
  -- the existential clashing-pair witness.
  unfold IConfluent at hI
  by_contra hcon
  apply hI
  intro x y hx hy
  by_contra hbad
  exact hcon ⟨x, y, hx, hy, hbad⟩

/-! ## I-confluence is non-trivial: both directions witnessed concretely.

Over `Finset ℕ` (⊔ = ∪): a bounded invariant (`card ≤ 1`) is NOT I-confluent and must
escalate; a grow-only invariant IS I-confluent and runs tier-1. This proves the judgement
is falsifiable, not vacuous. -/

instance : MergeState (Finset ℕ) := { toSemilatticeSup := inferInstance }

/-- **An I-confluent invariant exists:** the grow-only `True` invariant is
preserved by any merge — grow-only sets run coordination-free (tier-1). -/
theorem top_iconfluent : IConfluent (S := Finset ℕ) (fun _ => True) :=
  fun _ _ _ _ => trivial

/-- **A concrete non-I-confluent invariant: "at most one element."** Two singletons each
satisfy `card ≤ 1`, but their merge `{1} ⊔ {2} = {1,2}` does not — so a cell with this
invariant must escalate (≥tier-2). The `balance ≥ 0` shape: a bounded resource whose
concurrent merges overflow the bound. -/
theorem cardLeOne_not_iconfluent :
    ¬ IConfluent (S := Finset ℕ) (fun s => s.card ≤ 1) := by
  intro h
  have hbad := h {1} {2} (by decide) (by decide)
  exact absurd hbad (by decide)

end Dregg2.Confluence
