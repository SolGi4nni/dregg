/-
# QuorumThreshold — the ONE quorum formula, verified (the #170 unification's Lean twin)

The Rust side unified every quorum computation in the system onto a single
formula: the strict SUPERMAJORITY threshold

    supermajority_threshold n = ⌊2n/3⌋ + 1

(`blocklace/src/ordering.rs::supermajority_threshold`, to which
`dregg_federation::quorum_threshold` DELEGATES — there is exactly ONE quorum
formula in the running system). This module is its Lean twin: a byte-for-byte
transcription plus the four properties the protocol actually leans on, proved
unconditionally — in particular WITHOUT the `StrictBft` (`3 ∤ n`) hypothesis
that `Dregg2/Distributed/BlsQuorumCert.lean` must carry for the historical
`n − ⌊n/3⌋` formula (which admitted a quorum of exactly `2n/3` at `n = 3f`,
where two quorums can intersect in a single — possibly Byzantine — member).

What is proved here:

* `supermajorityThreshold_zero` / `supermajorityThreshold_pos` — the `n = 0`
  FAIL-CLOSED pin: an empty committee's threshold is `1`, never `0`, so an
  empty vote set can NEVER certify anything (the vacuous-quorum hole).
* `threshold_monotone` — a larger committee never needs fewer votes.
* `supermajority_formable` / `closed_form` — for `n ≥ 1` the threshold is
  formable (`≤ n`) and equals `n − ⌊(n−1)/3⌋` (ordering.rs's stated
  equivalent).
* `intersection_count_exceeds_faults` — the arithmetic core: two vote counts
  at threshold over an `n`-committee overlap in STRICTLY more than `⌊n/3⌋`
  members (hence also more than the Rust-pinned budget `⌊(n−1)/3⌋`),
  UNCONDITIONALLY in `n`.
* `supermajority_intersection` — the Byzantine-intersection lemma actually
  used: any two `Finset` quorums of size `≥ ⌊2n/3⌋+1` inside an `n`-member
  committee intersect in `> ⌊n/3⌋` members.
* `two_quorums_share_honest` — the consumption form: under a corrupt set of
  size `≤ ⌊n/3⌋`, two quorums always share an HONEST member — the
  non-forgeability/non-equivocation backbone, now with NO `3 ∤ n` caveat.

## Differential

The Rust differential lives in `federation/src/bls_quorum_diff.rs` (formula
relation vs the Lean transcriptions over the `#guard` golden values AND an
exhaustive `0..=512` sweep, incl. the exact `+1 at 3 ∣ n` relation to the
historical formula, driven through the REAL `hints` BLS aggregate), with the
golden values themselves pinned in `blocklace/src/ordering.rs`
(`test_supermajority_threshold` / `test_supermajority_quorum_intersection_unconditional`)
and `epoch_diff.rs` / `membership_safety_differential.rs` for the consumers.

Residual lane (HORIZONLOG "Quorum unification (#170) Lean lift"): migrate
`BlsQuorumCert.lean` / `EpochReconfig.lean` / `MembershipSafety.lean` onto
this module and discharge their `StrictBft` / `n = 0 ↦ 0` carve-outs; the
bridging lemmas `historical_le_supermajority` / `historical_relation` below
state the exact gap those modules close over.

Pure, computable, `#eval`-able. `#assert_axioms`-clean
(⊆ {propext, Classical.choice, Quot.sound}); both-polarity `#guard`s.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Distributed.QuorumThreshold

/-- **`supermajorityThreshold n = ⌊2n/3⌋ + 1`** — the smallest vote count
STRICTLY greater than `2n/3`. Byte-for-byte
`blocklace/src/ordering.rs::supermajority_threshold` (`(n * 2 / 3) + 1`). -/
def supermajorityThreshold (n : Nat) : Nat := 2 * n / 3 + 1

/-- The `n = 0` FAIL-CLOSED pin: an EMPTY committee can never certify anything
(threshold `1`, which no empty vote set reaches) — rather than a vacuous
threshold of `0`. Matches `ordering.rs` (`supermajority_threshold(0) = 1`);
this is precisely the lift `MembershipSafety.computeThreshold`'s `n = 0 ↦ 0`
guard still owes (HORIZONLOG #170 tail). -/
@[simp] theorem supermajorityThreshold_zero : supermajorityThreshold 0 = 1 := rfl

/-- Fail-closed, all `n`: the threshold is never `0`, so the empty vote set
never certifies. -/
theorem supermajorityThreshold_pos (n : Nat) : 0 < supermajorityThreshold n :=
  Nat.succ_pos _

/-! The Rust golden values (`ordering.rs::test_supermajority_threshold`),
re-run here as kernel-checked guards. -/
example : supermajorityThreshold 0 = 1 := by decide  -- empty: fail-closed
example : supermajorityThreshold 1 = 1 := by decide  -- solo: own block suffices
example : supermajorityThreshold 2 = 2 := by decide
example : supermajorityThreshold 3 = 3 := by decide  -- NOT 2: the n = 3f point
example : supermajorityThreshold 4 = 3 := by decide
example : supermajorityThreshold 6 = 5 := by decide  -- n = 3f again: strictly > 2n/3
example : supermajorityThreshold 7 = 5 := by decide
example : supermajorityThreshold 10 = 7 := by decide

-- NEGATIVE polarity on the pin: the fail-closed threshold is NOT the
-- vacuously-satisfiable `0`.
#guard supermajorityThreshold 0 ≠ 0
-- NEGATIVE polarity on the `3 ∣ n` closure: at `n = 3` the threshold is NOT
-- the historical `n − ⌊n/3⌋ = 2` (the `StrictBft` hole).
#guard supermajorityThreshold 3 ≠ 3 - 3 / 3

/-- A larger committee never needs FEWER votes. -/
theorem threshold_monotone {m n : Nat} (h : m ≤ n) :
    supermajorityThreshold m ≤ supermajorityThreshold n := by
  unfold supermajorityThreshold
  omega

/-- For a NONEMPTY committee the threshold is formable: `⌊2n/3⌋ + 1 ≤ n`.
(At `n = 0` it deliberately is NOT — that IS the fail-closed pin.) -/
theorem supermajority_formable {n : Nat} (hn : 1 ≤ n) :
    supermajorityThreshold n ≤ n := by
  unfold supermajorityThreshold
  omega

/-- The equivalent closed form `ordering.rs` documents and the Rust sweep
pins: `supermajorityThreshold n = n − ⌊(n−1)/3⌋` for `n ≥ 1`. -/
theorem closed_form {n : Nat} (hn : 1 ≤ n) :
    supermajorityThreshold n = n - (n - 1) / 3 := by
  unfold supermajorityThreshold
  omega

/-- A supermajority is in particular a STRICT majority: `n < 2·q`. -/
theorem supermajority_gt_half (n : Nat) : n < 2 * supermajorityThreshold n := by
  unfold supermajorityThreshold
  omega

/-- **The arithmetic core of quorum intersection**, unconditional in `n`: two
vote counts `a, b` at threshold drawn from an `n`-committee overlap in at
least `a + b − n` members, and that overlap STRICTLY exceeds `⌊n/3⌋` — the
canonical BFT fault budget (`BlsQuorumCert.faultBudget`), and a fortiori the
Rust-pinned `⌊(n−1)/3⌋`. This is the property the historical `n − ⌊n/3⌋`
formula LACKED at `3 ∣ n` (see the negative guard below). -/
theorem intersection_count_exceeds_faults {n a b : Nat}
    (ha : supermajorityThreshold n ≤ a) (hb : supermajorityThreshold n ≤ b) :
    n / 3 < a + b - n := by
  unfold supermajorityThreshold at *
  omega

-- NEGATIVE polarity (the hole this formula closes): at `n = 3` the
-- HISTORICAL threshold `n − ⌊n/3⌋ = 2` does NOT clear the fault budget — two
-- 2-quorums can intersect in a single member, `1 ≤ ⌊3/3⌋`.
example : ¬ (3 / 3 < 2 + 2 - 3) := by decide
-- POSITIVE polarity at the same point: the supermajority `3` does —
-- `3 + 3 − 3 = 3 > 1`.
example : 3 / 3 < supermajorityThreshold 3 + supermajorityThreshold 3 - 3 := by decide

section Finsets

variable {α : Type*} [DecidableEq α]

/-- **`supermajority_intersection`** — the Byzantine-intersection lemma in set
form: any two quorums `A, B ⊆ committee` each of size
`≥ supermajorityThreshold n` (where `n = committee.card`) intersect in
STRICTLY more than `⌊n/3⌋` members. Unconditional — no `3 ∤ n` caveat. -/
theorem supermajority_intersection {committee A B : Finset α}
    (hA : A ⊆ committee) (hB : B ⊆ committee)
    (hAq : supermajorityThreshold committee.card ≤ A.card)
    (hBq : supermajorityThreshold committee.card ≤ B.card) :
    committee.card / 3 < (A ∩ B).card := by
  have hUnion : (A ∪ B).card ≤ committee.card :=
    Finset.card_le_card (Finset.union_subset hA hB)
  have hIE : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have core := intersection_count_exceeds_faults hAq hBq
  omega

/-- **`two_quorums_share_honest`** — the consumption form (what
`BlsQuorumCert.two_quorums_share_honest_member` carries `StrictBft` for):
under ANY corrupt subset `bad ⊆ committee` within the fault budget
`|bad| ≤ ⌊n/3⌋`, two supermajority quorums share a member OUTSIDE `bad`.
The corrupt set alone can neither forge a second certificate nor equivocate
across two quorums — at EVERY committee size, including `3 ∣ n`. -/
theorem two_quorums_share_honest {committee A B bad : Finset α}
    (hA : A ⊆ committee) (hB : B ⊆ committee)
    (hAq : supermajorityThreshold committee.card ≤ A.card)
    (hBq : supermajorityThreshold committee.card ≤ B.card)
    (hbad : bad.card ≤ committee.card / 3) :
    ∃ x, x ∈ A ∧ x ∈ B ∧ x ∉ bad := by
  have hinter := supermajority_intersection hA hB hAq hBq
  by_contra h
  have hsub : A ∩ B ⊆ bad := by
    intro x hx
    by_contra hxbad
    exact h ⟨x, Finset.mem_of_mem_inter_left hx,
      Finset.mem_of_mem_inter_right hx, hxbad⟩
  have := Finset.card_le_card hsub
  omega

end Finsets

section Bridges

/-! Bridging lemmas to the HISTORICAL formulas still transcribed in
`EpochReconfig.lean` (`quorumThreshold n = n − n/3`) and
`MembershipSafety.lean` — they state the EXACT relation
`bls_quorum_diff.rs` pins ("`+1` at `3 ∣ n`, equal otherwise"), so migrating
those modules onto `supermajorityThreshold` is a strictly safe-side move:
the new formula never demands fewer votes. -/

/-- The unified threshold dominates the historical `n − ⌊n/3⌋`: migration is
safe-side (never fewer signers demanded). -/
theorem historical_le_supermajority (n : Nat) :
    n - n / 3 ≤ supermajorityThreshold n := by
  unfold supermajorityThreshold
  omega

/-- The exact gap: `+1` precisely at `3 ∣ n` (the `StrictBft` hole points),
equal everywhere else. This is relation (1) of `bls_quorum_diff.rs`. -/
theorem historical_relation (n : Nat) :
    supermajorityThreshold n = (n - n / 3) + (if 3 ∣ n then 1 else 0) := by
  unfold supermajorityThreshold
  by_cases hd : 3 ∣ n <;> simp only [hd, if_true, if_false] <;> omega

-- Golden checks of the relation at the hole points and around them.
#guard supermajorityThreshold 3 = (3 - 3 / 3) + 1
#guard supermajorityThreshold 6 = (6 - 6 / 3) + 1
#guard supermajorityThreshold 9 = (9 - 9 / 3) + 1
#guard supermajorityThreshold 4 = 4 - 4 / 3
#guard supermajorityThreshold 5 = 5 - 5 / 3
#guard supermajorityThreshold 7 = 7 - 7 / 3

end Bridges

/-! ## Non-vacuity demo — the lemmas FIRE on a concrete committee. -/
namespace Demo

/-- A concrete 6-member committee (`3 ∣ 6` — the historical hole point). -/
def committee : Finset Nat := {0, 1, 2, 3, 4, 5}
/-- Two overlapping supermajority quorums (size 5 = `supermajorityThreshold 6`). -/
def q1 : Finset Nat := {0, 1, 2, 3, 4}
def q2 : Finset Nat := {1, 2, 3, 4, 5}
/-- The fault-budget-sized corrupt set (`⌊6/3⌋ = 2`). -/
def bad : Finset Nat := {1, 2}

#guard committee.card = 6
#guard q1.card = supermajorityThreshold committee.card
#guard q2.card = supermajorityThreshold committee.card
-- POSITIVE: the intersection {1,2,3,4} strictly exceeds the budget 2 …
#guard committee.card / 3 < (q1 ∩ q2).card
-- … and contains honest members 3, 4 (outside `bad`).
#guard 3 ∈ q1 ∩ q2
#guard 3 ∉ bad
-- NEGATIVE: a sub-threshold "quorum" of the historical size 4 = 6 − 6/3 can
-- intersect another in exactly the corrupt set — the hole, witnessed.
#guard ({0, 1, 2, 3} : Finset Nat) ∩ ({1, 2, 4, 5} : Finset Nat) = bad

end Demo

-- Axiom hygiene: every keystone rests only on the three kernel axioms.
#assert_axioms supermajorityThreshold_pos
#assert_axioms threshold_monotone
#assert_axioms supermajority_formable
#assert_axioms closed_form
#assert_axioms intersection_count_exceeds_faults
#assert_axioms supermajority_intersection
#assert_axioms two_quorums_share_honest
#assert_axioms historical_le_supermajority
#assert_axioms historical_relation

end Dregg2.Distributed.QuorumThreshold
