/-
# ConfigBoundary — the federation's install discipline: step bound, refusal, and the chain

**This module is the AUTHORED CONSENSUS RULE for configuration (roster) changes.** The Rust
side (`blocklace/src/constitution.rs::config_step_allowed`) is a byte-for-byte transcription
of `classifyStep` below, the same pairing discipline `QuorumThreshold.lean` has with
`blocklace/src/ordering.rs::supermajority_threshold`. Nothing here is a model of Rust; the
Rust is a transcription of this.

Design source: `docs/reference/READING-RECONFIGURATION-2026-08-08.md` (D0–D8). The three
facts this module discharges as THEOREMS (each was a stated proof obligation there):

* **D5, the step bound** — a roster step of `j` joins and `l` leaves keeps cross-configuration
  quorum intersection above the Byzantine budget of the SMALLER roster. Stated over the
  actual `supermajorityThreshold` (`⌊2n/3⌋+1`), quantified over `n` — not a `#guard` over a
  table. The derivation is DZ (Duan & Zhang, *Foundations of Dynamic BFT*) Lemma C.8's
  counting argument; DZ's own stated constant (`q ≤ ⌈l/3⌉`) is arithmetically FALSE and is
  not used (the reading doc §3.1b refutes it; correct is `⌈2l/3⌉`, and this module enforces
  the inequality itself rather than any closed-form cap).
* **D1, the chain** — the configuration history is a CHAIN: the config at committed position
  `k` is a function of the committed prefix up to `k` alone, immutable under extension of the
  log (`install_position_immutable`). Comparability of installed configurations is inherited
  from the total order — Mysticeti §IV-D's argument ("owing to the total ordering property
  inherent in consensus"), which is why a blocklace needs no separate view-agreement.
* **Refusal totality** — `classifyStep` yields `install` exactly when `stepAllowed` holds,
  and otherwise yields a NAMED refusal (`classifyStep_total`); a step is never silently
  reinterpreted or clamped.

## The corrected arithmetic (and one sharpening the reading doc's tables missed)

The commissioning rule was "`l ≤ 2` changes per configuration step". Recovered here as
theorems — `joinStepOk_of_le_two` and `leaveStepOk_of_le_two` hold for ALL `n` — but the flat
cap is the WRONG QUANTITY in two directions, so the enforced rule is the inequality itself:

* Too tight: at `n ≡ 0 (mod 3)` larger batches are safe (the reading doc §3.3's own table).
* ⚑ Too loose: a MIXED step of one join AND one leave at `n = 4` (within "2 changes")
  BREAKS the intersection bound — `churnStepOk_breaks_at_one_one_from_four`. Rosters
  {A,B,C,D} → {A,B,C,E}: quorums {B,C,D} and {A,B,E} intersect in exactly {B}, which may be
  the one Byzantine member. The pure-join and pure-leave tables never exhibit this because
  they never price a step in which `n` is unchanged while the membership moves.

The leave direction's non-contiguity trap is witnessed as theorems: at `n = 7`, `l = 3`
FAILS while `l = 4` passes — and passes only because the survivor roster's fault budget is
zero (`leaveStepOk_vacuous_at_four_from_seven`). The roster floor (`4 ≤ n → 4 ≤ n′`) is what
closes that trap: no step from a BFT-capable roster may land on a roster that tolerates
nothing. Rosters already below 4 (bootstrap / solo shapes) are exempt from the floor — their
budgets are zero everywhere, safety there is vacuous and NAMED so, not manufactured.

State transfer (D4, the learner phase) lifts the ceiling for JOINS ONLY, and only once a
temporary member provably cannot act — that phase is not built, so joins stay counted here.
Leaves are bounded permanently: DZ Case (2) is pure counting and nothing can substitute for
it (there is no new member whose state could be constrained).

Pure, computable, `decide`-able. `#assert_axioms`-clean.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Dregg2.Tactics
import Dregg2.Distributed.QuorumThreshold

namespace Dregg2.Distributed.ConfigBoundary

open Dregg2.Distributed.QuorumThreshold (supermajorityThreshold)

/-- The Byzantine budget the Rust side pins: `f(n) = ⌊(n−1)/3⌋`
(`blocklace/src/ordering.rs`'s stated budget; `supermajorityThreshold n = n − f n` for
`n ≥ 1`, `closed_form`). `faultBudget 0 = 0`. -/
def faultBudget (n : Nat) : Nat := (n - 1) / 3

@[simp] theorem faultBudget_zero : faultBudget 0 = 0 := rfl

/-- Below 4 members the budget is zero: such a roster TOLERATES NOTHING, which is why the
roster floor refuses to land there from above. -/
theorem faultBudget_eq_zero_below_four {n : Nat} (h : n < 4) : faultBudget n = 0 := by
  unfold faultBudget; omega

theorem faultBudget_pos_of_four_le {n : Nat} (h : 4 ≤ n) : 1 ≤ faultBudget n := by
  unfold faultBudget; omega

/-! ## The step conditions (DZ Lemma C.8's counting argument, Nat-safe form)

A quorum under the old roster (`n` members) has `T n` members, all in the old roster. A
quorum under the new roster (`n′ = n + j − l`) has `T n′` members, of which at most `j` are
joiners, so at least `T n′ − j` lie in the old roster. Inclusion–exclusion inside the old
roster: the two quorums share at least `T n + T n′ − j − n` members of the old roster — all
of them members of BOTH rosters. For safety that overlap must STRICTLY exceed the Byzantine
budget of the smaller roster (a member correct in both rosters cannot equivocate; the bad
set inside the shared roster is bounded by `faultBudget (min n n′)`). Written additively so
Nat subtraction never truncates. -/

/-- The general (mixed) step condition: `j` joins and `l` leaves from an `n`-roster keep
cross-configuration quorum intersection strictly above the smaller roster's fault budget. -/
def churnStepOk (n j l : Nat) : Prop :=
  n + j + faultBudget (min n (n + j - l)) + 1 ≤
    supermajorityThreshold n + supermajorityThreshold (n + j - l)

/-- Pure joins (`l = 0`). -/
def joinStepOk (n l : Nat) : Prop := churnStepOk n l 0

/-- Pure leaves (`j = 0`). -/
def leaveStepOk (n l : Nat) : Prop := churnStepOk n 0 l

instance (n j l : Nat) : Decidable (churnStepOk n j l) := by
  unfold churnStepOk; exact inferInstance

instance (n l : Nat) : Decidable (joinStepOk n l) := by
  unfold joinStepOk; exact inferInstance

instance (n l : Nat) : Decidable (leaveStepOk n l) := by
  unfold leaveStepOk; exact inferInstance

/-! ## The commissioned rule, recovered as theorems — and its two corrections -/

/-- **Up to two JOINS per step are safe at EVERY roster size** — the commissioning's `l ≤ 2`
rule for joins, quantified over `n` (tight at `n ≡ 1 (mod 3)`: 4→6 lands the bound with zero
slack). -/
theorem joinStepOk_of_le_two {n l : Nat} (hl : l ≤ 2) : joinStepOk n l := by
  unfold joinStepOk churnStepOk faultBudget supermajorityThreshold
  omega

/-- **Up to two LEAVES per step satisfy the intersection bound at every roster size** that
survives them (`l < n`). ⚠ This is the COUNTING bound only — at survivor rosters below 4 it
holds vacuously (`faultBudget = 0`); the roster floor in `stepAllowed` is the teeth for
that. -/
theorem leaveStepOk_of_le_two {n l : Nat} (hl : l ≤ 2) (hln : l < n) : leaveStepOk n l := by
  unfold leaveStepOk churnStepOk faultBudget supermajorityThreshold
  omega

/-- **Refutability of the join bound** (the floor is FALSE where it should be): three joins
from `n = 4` (the 4→7 step) break the intersection bound. `T 4 + T 7 − 3 − 4 = 1`, and one
shared member may be the Byzantine one. -/
theorem joinStepOk_breaks_at_three_from_four : ¬ joinStepOk 4 3 := by decide

/-- **The leave direction's non-contiguity trap, half 1**: three leaves from `n = 7` FAIL
(`T 7 + T 4 − 7 = 1 ≤ faultBudget 4 = 1`). -/
theorem leaveStepOk_breaks_at_three_from_seven : ¬ leaveStepOk 7 3 := by decide

/-- **The non-contiguity trap, half 2**: FOUR leaves from `n = 7` pass the counting bound —
but only because the survivor roster (`n′ = 3`) tolerates nothing at all. A `max_l`
implementation that checks the endpoint rather than the contiguous prefix would admit
7 → 3 as "safe". The roster floor refuses it instead. -/
theorem leaveStepOk_vacuous_at_four_from_seven :
    leaveStepOk 7 4 ∧ faultBudget (7 - 4) = 0 := by decide

/-- ⚑ **The sharpening: "at most two changes" is NOT a safe rule for MIXED steps.** One join
plus one leave at `n = 4` — two changes — breaks the bound: `n′ = 4`, the quorums intersect
in `T 4 + T 4 − 1 − 4 = 1 ≤ faultBudget 4 = 1` member, who may be Byzantine and equivocate
across the two configurations. The enforced rule is therefore the inequality, never a flat
change cap. -/
theorem churnStepOk_breaks_at_one_one_from_four : ¬ churnStepOk 4 1 1 := by decide

/-! ## The keystone: cross-configuration quorum intersection (Finset form)

The DAG-analogue-in-counting-form of DZ Lemma C.8 — the reading doc §3.2's "central new
theorem", at the resolution this pass can discharge: two supermajority quorums under two
rosters one allowed step apart share an HONEST member, whenever the Byzantine set inside the
shared roster respects the smaller roster's budget. (What remains OPEN is the τ-anchored
form — threading this through wave anchors and the finalized order; stated in the module
header of the Rust transcription.) -/

section Finsets

variable {α : Type*} [DecidableEq α]

/-- **`cross_config_quorums_share_honest`** — rosters `M` (old) and `M'` (new) with at most
`j` joiners; quorums `A ⊆ M`, `B ⊆ M'` at their respective rosters' supermajority
thresholds; a bad set whose overlap with the SHARED roster is within the smaller roster's
fault budget. If the step inequality (`churnStepOk`-shaped, hypothesis `hstep`) holds, the
two quorums share a member outside `bad` — the member whose honesty forbids equivocation
across the configuration boundary. -/
theorem cross_config_quorums_share_honest
    {M M' A B bad : Finset α} {j : Nat}
    (hA : A ⊆ M) (hB : B ⊆ M')
    (hjoin : (M' \ M).card ≤ j)
    (hAq : supermajorityThreshold M.card ≤ A.card)
    (hBq : supermajorityThreshold M'.card ≤ B.card)
    (hbad : (bad ∩ (M ∩ M')).card ≤ faultBudget (min M.card M'.card))
    (hstep : M.card + j + faultBudget (min M.card M'.card) + 1 ≤
      supermajorityThreshold M.card + supermajorityThreshold M'.card) :
    ∃ x, x ∈ A ∧ x ∈ B ∧ x ∉ bad := by
  -- `B`'s members outside the old roster are joiners: `B \ M ⊆ M' \ M`.
  have hBjoin : (B \ M).card ≤ j :=
    le_trans (Finset.card_le_card (Finset.sdiff_subset_sdiff hB (Finset.Subset.refl M))) hjoin
  -- Split `B` over the old roster.
  have hBsplit : (B ∩ M).card + (B \ M).card = B.card := Finset.card_inter_add_card_sdiff B M
  -- Both `A` and `B ∩ M` live inside `M`.
  have hUnion : (A ∪ B ∩ M).card ≤ M.card :=
    Finset.card_le_card (Finset.union_subset hA Finset.inter_subset_right)
  have hIE : (A ∪ B ∩ M).card + (A ∩ (B ∩ M)).card = A.card + (B ∩ M).card :=
    Finset.card_union_add_card_inter A (B ∩ M)
  -- `A ∩ (B ∩ M) = A ∩ B` since `A ⊆ M`.
  have hAM : A ∩ M = A := Finset.inter_eq_left.mpr hA
  have hEq : A ∩ (B ∩ M) = A ∩ B := by
    rw [Finset.inter_comm B M, ← Finset.inter_assoc, hAM]
  rw [hEq] at hIE
  -- The shared quorum members are members of BOTH rosters.
  have hshared : A ∩ B ⊆ M ∩ M' := fun x hx =>
    Finset.mem_inter.mpr
      ⟨hA (Finset.mem_of_mem_inter_left hx), hB (Finset.mem_of_mem_inter_right hx)⟩
  by_contra h
  -- Then every shared quorum member is bad, inside the shared roster.
  have hsub : A ∩ B ⊆ bad ∩ (M ∩ M') := by
    intro x hx
    refine Finset.mem_inter.mpr ⟨?_, hshared hx⟩
    by_contra hxbad
    exact h ⟨x, Finset.mem_of_mem_inter_left hx,
      Finset.mem_of_mem_inter_right hx, hxbad⟩
  have hcard := Finset.card_le_card hsub
  omega

end Finsets

/-! ## The decision rule the node enforces, and its named refusals -/

/-- **`stepAllowed`** — the computable rule. A step of `j` joins and `l` leaves from an
`n`-roster is allowed iff: leaves only remove existing members; the survivors are nonempty;
the intersection bound holds; and the roster floor holds (a roster at or above 4 never
shrinks below 4 — the non-contiguity trap's teeth; sub-4 bootstrap rosters are exempt).
This is the Bool the Rust transcription (`constitution.rs::config_step_allowed`) mirrors. -/
def stepAllowed (n j l : Nat) : Bool :=
  decide (l ≤ n) && decide (1 ≤ n + j - l)
    && decide (n + j + faultBudget (min n (n + j - l)) + 1 ≤
        supermajorityThreshold n + supermajorityThreshold (n + j - l))
    && decide (4 ≤ n → 4 ≤ n + j - l)

/-- An allowed step satisfies the intersection condition — the hypothesis
`cross_config_quorums_share_honest` consumes. -/
theorem stepAllowed_churnOk {n j l : Nat} (h : stepAllowed n j l = true) :
    churnStepOk n j l := by
  unfold stepAllowed at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- The composition: an allowed step's quorums share an honest member. This is the theorem
the install discipline rests on — `stepAllowed` is exactly strong enough for
`cross_config_quorums_share_honest`. -/
theorem stepAllowed_quorums_share_honest {α : Type*} [DecidableEq α]
    {M M' A B bad : Finset α} {j l : Nat}
    (hstep : stepAllowed M.card j l = true)
    (hcard : M'.card = M.card + j - l)
    (hA : A ⊆ M) (hB : B ⊆ M')
    (hjoin : (M' \ M).card ≤ j)
    (hAq : supermajorityThreshold M.card ≤ A.card)
    (hBq : supermajorityThreshold M'.card ≤ B.card)
    (hbad : (bad ∩ (M ∩ M')).card ≤ faultBudget (min M.card M'.card)) :
    ∃ x, x ∈ A ∧ x ∈ B ∧ x ∉ bad := by
  have hok := stepAllowed_churnOk hstep
  unfold churnStepOk at hok
  rw [← hcard] at hok
  exact cross_config_quorums_share_honest hA hB hjoin hAq hBq hbad hok

/-- The verdicts. A step is `install`ed or refused BY NAME — there is no third outcome and
no clamping. The Rust `StepRefusal` enum mirrors the refusal constructors one-for-one. -/
inductive StepVerdict where
  /-- The step installs; the payload is the survivor roster size `n + j − l`. -/
  | install (survivors : Nat)
  /-- More leaves than the roster has members. -/
  | refuseLeavesExceedRoster
  /-- The step would leave an empty roster (which could never certify anything again). -/
  | refuseEmptySurvivors
  /-- The step breaks cross-configuration quorum intersection (DZ C.8 counting). -/
  | refuseIntersectionBound
  /-- The step would shrink a BFT-capable roster (`n ≥ 4`) below 4 members — landing on a
  roster whose fault budget is zero (the 7→3-via-vacuous-7→4 trap). -/
  | refuseRosterFloor
  deriving DecidableEq, Repr

/-- **`classifyStep`** — the total classification: the first failing check names the
refusal; no check failing installs. Byte-for-byte the Rust `config_step_allowed`. -/
def classifyStep (n j l : Nat) : StepVerdict :=
  if ¬ (l ≤ n) then .refuseLeavesExceedRoster
  else if ¬ (1 ≤ n + j - l) then .refuseEmptySurvivors
  else if ¬ (n + j + faultBudget (min n (n + j - l)) + 1 ≤
      supermajorityThreshold n + supermajorityThreshold (n + j - l)) then
    .refuseIntersectionBound
  else if ¬ (4 ≤ n → 4 ≤ n + j - l) then .refuseRosterFloor
  else .install (n + j - l)

/-- Installation is EXACTLY `stepAllowed` — the classification never installs a refused
step and never refuses an allowed one. -/
theorem classifyStep_install_iff (n j l : Nat) :
    classifyStep n j l = .install (n + j - l) ↔ stepAllowed n j l = true := by
  unfold classifyStep stepAllowed
  split_ifs <;> simp_all

/-- **Refusal totality**: every step either installs or is refused by one of the four
names. (With `classifyStep_install_iff` this is the "REFUSED by name" pole: a disallowed
step always lands on a named refusal, never on a reinterpretation.) -/
theorem classifyStep_total (n j l : Nat) :
    classifyStep n j l = .install (n + j - l)
      ∨ classifyStep n j l = .refuseLeavesExceedRoster
      ∨ classifyStep n j l = .refuseEmptySurvivors
      ∨ classifyStep n j l = .refuseIntersectionBound
      ∨ classifyStep n j l = .refuseRosterFloor := by
  unfold classifyStep
  split_ifs <;> simp

/-! Named golden instances (the Rust tests pin the same values — the transcription
differential). Both polarities. -/

example : stepAllowed 4 1 0 = true := by decide   -- 4→5 join
example : stepAllowed 4 2 0 = true := by decide   -- 4→6 join (tight)
example : stepAllowed 4 3 0 = false := by decide  -- 4→7 join BREAKS (DZ's own example)
example : stepAllowed 7 2 0 = true := by decide   -- 7→9 join (tight)
example : stepAllowed 7 3 0 = false := by decide  -- 7→10 join breaks
example : stepAllowed 6 4 0 = true := by decide   -- n ≡ 0 (mod 3) admits MORE than 2
example : stepAllowed 5 0 1 = true := by decide   -- 5→4 leave (floor holds)
example : stepAllowed 4 0 1 = false := by decide  -- 4→3 leave: ROSTER FLOOR refuses
example : classifyStep 4 0 1 = .refuseRosterFloor := by decide
example : stepAllowed 7 0 3 = false := by decide  -- the non-contiguous failure
example : classifyStep 7 0 3 = .refuseIntersectionBound := by decide
example : stepAllowed 7 0 4 = false := by decide  -- vacuously-safe endpoint REFUSED (floor)
example : classifyStep 7 0 4 = .refuseRosterFloor := by decide
example : stepAllowed 4 1 1 = false := by decide  -- the mixed-step sharpening
example : classifyStep 4 1 1 = .refuseIntersectionBound := by decide
example : stepAllowed 1 0 1 = false := by decide  -- solo leaving itself: empty survivors
example : classifyStep 1 0 1 = .refuseEmptySurvivors := by decide
example : stepAllowed 1 1 0 = true := by decide   -- solo growth path is open
example : stepAllowed 1 2 0 = true := by decide
example : stepAllowed 3 2 0 = true := by decide   -- bootstrap 3→5
example : stepAllowed 0 1 0 = true := by decide   -- genesis from empty: 0→1 installs

/-! ## D1 — the configuration history is a CHAIN, derived from the committed order -/

section Chain

variable {κ : Type*} [DecidableEq κ]

/-- One installed roster change: the join-set and leave-set of a committed, ratified
membership step. (The identity is the CHANGE-SET, per DBRB `v.changes` / KT20's lattice —
a counter alone could not express D2's merge when it lands.) -/
structure RosterDelta (κ : Type*) [DecidableEq κ] where
  joins : Finset κ
  leaves : Finset κ

/-- Apply one delta: leaves out, joins in. -/
def applyDelta (M : Finset κ) (d : RosterDelta κ) : Finset κ := (M \ d.leaves) ∪ d.joins

/-- The roster after a committed install log, from genesis. `config_seq` of a position is
the number of installed deltas before it — `log.length` here. -/
def rosterAt (genesis : Finset κ) (log : List (RosterDelta κ)) : Finset κ :=
  log.foldl applyDelta genesis

/-- Install composes over the committed order: the roster after `pre ++ suf` is the roster
after `suf` applied to the roster after `pre`. (`config_seq` is likewise additive:
`(pre ++ suf).length = pre.length + suf.length`.) -/
theorem rosterAt_append (g : Finset κ) (pre suf : List (RosterDelta κ)) :
    rosterAt g (pre ++ suf) = rosterAt (rosterAt g pre) suf :=
  List.foldl_append ..

/-- **Install agreement / D0 derivability, the model-level statement**: the configuration
at committed position `k` is a function of the committed prefix up to `k` ALONE — a node
that later learns more of the log (`ext`) derives the IDENTICAL roster at `k`. Two honest
nodes sharing a committed prefix therefore install identically at the same position; the
install point never moves retroactively. -/
theorem install_position_immutable (g : Finset κ) (log ext : List (RosterDelta κ))
    (k : Nat) (hk : k ≤ log.length) :
    rosterAt g ((log ++ ext).take k) = rosterAt g (log.take k) := by
  rw [List.take_append_of_le_length hk]

/-- **D1, comparability**: the installed configurations of one committed log form a chain —
any two history entries are prefix-comparable, i.e. the earlier one's derivation is a
prefix-fold of the later one's. (In a blocklace this is inherited from the total order τ;
this is Mysticeti's "owing to the total ordering property inherent in consensus", stated
rather than assumed.) -/
theorem config_history_chain (g : Finset κ) (log : List (RosterDelta κ))
    {k₁ k₂ : Nat} (h : k₁ ≤ k₂) :
    rosterAt g (log.take k₁) = rosterAt g ((log.take k₂).take k₁) := by
  rw [List.take_take, Nat.min_eq_left h]

end Chain

/-! ## Non-vacuity demo — the keystone FIRES on the measured hazard's own shape

The measured defect (reading doc §5.3): a block at 3-of-4 loses quorum when a join moves
the threshold to 4. Here: the 4→5 join is an allowed step, and the intersection theorem
produces the honest witness across exactly that boundary. -/
namespace Demo

def oldRoster : Finset Nat := {0, 1, 2, 3}
def newRoster : Finset Nat := {0, 1, 2, 3, 4}
/-- A supermajority quorum under the OLD roster (3-of-4). -/
def qOld : Finset Nat := {0, 1, 2}
/-- A supermajority quorum under the NEW roster (4-of-5). -/
def qNew : Finset Nat := {1, 2, 3, 4}
def bad : Finset Nat := {1}

example : stepAllowed oldRoster.card 1 0 = true := by decide
example : supermajorityThreshold oldRoster.card ≤ qOld.card := by decide
example : supermajorityThreshold newRoster.card ≤ qNew.card := by decide
-- The honest shared member exists concretely (member 2), outside `bad`.
example : 2 ∈ qOld ∩ qNew ∧ 2 ∉ bad := by decide
-- And the general theorem applies to this instance (hypotheses all decidable).
example : ∃ x, x ∈ qOld ∧ x ∈ qNew ∧ x ∉ bad :=
  stepAllowed_quorums_share_honest (M := oldRoster) (M' := newRoster)
    (j := 1) (l := 0)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

end Demo

-- Axiom hygiene: keystones rest only on the three kernel axioms.
#assert_axioms joinStepOk_of_le_two
#assert_axioms leaveStepOk_of_le_two
#assert_axioms churnStepOk_breaks_at_one_one_from_four
#assert_axioms cross_config_quorums_share_honest
#assert_axioms stepAllowed_churnOk
#assert_axioms stepAllowed_quorums_share_honest
#assert_axioms classifyStep_install_iff
#assert_axioms classifyStep_total
#assert_axioms install_position_immutable
#assert_axioms config_history_chain

end Dregg2.Distributed.ConfigBoundary
