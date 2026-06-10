/-
# Dregg2.Distributed.MembershipSafety — a FAITHFUL, EXECUTABLE model of the node's REAL
# governed-membership / constitution rule (`blocklace/src/constitution.rs`), wired to the
# blocklace causal order and the verified finality tower.

**The gap this closes.** `Dregg2/Distributed/BlocklaceFinality.lean` models `ordering.rs::tau`
(WHICH blocks finalize, in what order) and `Dregg2/Authority/Blocklace.lean` models the DAG +
equivocation (WHO forked). NEITHER models `constitution.rs` — the *self-amending membership rule*
that the federation runs ON TOP of finality: who is a participant, what the supermajority
threshold is, and the discipline by which Join / Leave / expel proposals are admitted.

The running node (`blocklace/src/constitution.rs`) computes membership changes with a CONCRETE
rule, not an abstract governance oracle:

  1. `Constitution::required_votes_for`  — the votes a proposal needs. For a threshold amendment
     `T → T'` it is the **H-rule** `max(T, T')` (`constitution.rs:94..104`); for Join / Leave /
     route changes it is the current `threshold`.
  2. `VoteTracker::record_vote`          — a vote counts ONLY if the voter `is_participant` and is
     deduped into a `HashSet` per proposal — i.e. **DISTINCT current-member** approvals
     (`constitution.rs:288..317`). Votes are carried as block payloads that reference the proposal
     block in their **causal past** (`constitution.rs:236..244`).
  3. `VoteTracker::has_passed`           — `approval_count ≥ required_votes_for` and not already
     applied (`constitution.rs:336..346`).
  4. `Constitution::apply_proposal`      — mutate the participant set, **recompute the threshold**
     `compute_threshold(n) = 2n/3 + 1` for Join / Leave, bump the version (`constitution.rs:111..160`).
  5. `auto_evict_equivocator`            — an equivocation proof removes the equivocator WITHOUT a
     vote (`constitution.rs:168..177`).

This module models THAT rule — `computeThreshold` / `requiredVotesFor` / `applyProposal` /
`distinctApprovers` / `hasPassed` as genuine **executable Lean functions** — and proves the REAL
safety properties the federation relies on:

* **H-rule lower bound** (`requiredVotes_amend_ge_both` / `…_eq_max`): a threshold amendment can
  NEVER pass with fewer than BOTH the old and new thresholds' worth of distinct approvals — so a
  minority cannot lower the bar to seize control, nor a majority raise it to lock others out.
* **Threshold-recomputation correctness** (`apply_join_threshold` / `apply_leave_threshold` /
  `applied_threshold_is_supermajority`): after Join / Leave the threshold is EXACTLY the
  `2n/3 + 1` supermajority of the NEW participant count, and that count moved by exactly one.
* **Distinct-current-member admission** (`passed_needs_threshold_distinct_members` and the
  causal-past form `passed_needs_quorum_in_past`): a proposal passes ONLY with at least
  `requiredVotesFor` approvals from DISTINCT keys that are ALL current participants — the vote set
  is `Nodup` and a subset of the constitution's participants, so a Byzantine voter cannot
  double-count and a non-member cannot vote.
* **Auto-eviction soundness** (`autoEvict_removes` / `autoEvict_threshold`): an equivocation proof
  removes the equivocator immediately and recomputes the threshold — no vote, faithful to the
  byzantine-repelling discipline (the equivocation is the `Blocklace.Equivocation` proof object).

and CONNECTS to the rest of the tower: votes live in the **causal past** of the proposal block
(`Authority.Blocklace.precedes` / `BlocklaceFinality.causalPastIncl`), and the per-version
participant set is exactly the `participants` list `ordering.rs::tau` / `BlocklaceFinality` round-
robins its `waveLeader` over (`asWaveParticipants`). Finally a **Rust differential** (`#guard`
golden vectors) reproduces, value-for-value, the exact numbers the `constitution.rs` unit tests
assert (n=3 join needs 3 votes; n=1→2 needs 1; H-rule 2→3 and 3→2 both need 3; `compute_threshold`
table).

## SCOPE — what is faithful, what is the named seam.

FAITHFUL (matches `constitution.rs` as pure functions):
* `computeThreshold n = 2n/3 + 1` (`compute_threshold`), with the `n = 0 ↦ 0` guard.
* `requiredVotesFor` including the H-rule `max(current, new)` for `AmendThreshold` (`required_votes_for`).
* `applyProposal` — the Join / Leave / AmendThreshold / AmendRoutes branch logic, the validity
  guards (`new_threshold ∈ [1, n]`, "already a member", "not a member"), the threshold recompute,
  and the version bump (`apply_proposal`).
* `distinctApprovers` — the `is_participant`-gated, per-proposal-deduped voter set
  (`VoteTracker::record_vote` + `approval_count`), here computed over a vote LIST keyed by the
  proposal block, dropping non-members and deduping by voter key (the `HashSet` semantics).
* `hasPassed` — `distinctApprovers.length ≥ requiredVotesFor` (`VoteTracker::has_passed`).

NAMED SEAM (a hypothesis, never a fake Lean theorem — same status as the `§8` crypto seam in
`Authority.Blocklace`): we treat a vote's *causal-past membership* as a checkable predicate
`InPast` supplied by the blocklace layer (`BlocklaceFinality.causalPastIncl` computes it; the §8
hash/signature obligations that authenticate a vote-block's author are discharged by the circuit +
Rust cascade, NOT here). Every theorem below is a semantic counting / arithmetic fact that does not
assume anything about hashing or signing — it assumes only that the supplied vote list is honest
about who voted (the authentication seam), exactly as `BlocklaceFinality` assumes the lace is
honest about its edges.

The single-machine `n = 1` case (threshold 1, the sole participant is always the leader and a
single self-vote suffices) is the **scales-to-zero special case**, exhibited in §9 but NOT the
target: the safety theorems are proved for ARBITRARY `n` and the non-vacuity witnesses run at
`n = 3` and `n = 4` (`n > 1`).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); NO `sorry` / `:=True` /
`native_decide`. Verified with `lake build Dregg2.Distributed.MembershipSafety`.
-/
import Dregg2.Distributed.BlocklaceFinality

namespace Dregg2.Distributed.MembershipSafety

open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId Equivocation precedes)
open Dregg2.Distributed.BlocklaceFinality (causalPastIncl superMajority)

/-! ## 1. The constitution + proposals (`constitution.rs::Constitution` / `MembershipProposal`). -/

/-- **`computeThreshold n`** — the default supermajority `⌊2n/3⌋ + 1`, with the `n = 0 ↦ 0`
guard (`constitution.rs::compute_threshold`). Identical arithmetic to
`BlocklaceFinality.superMajority` for `n > 0`; we keep the explicit zero-guard because the
constitution can transiently reach `n = 0` (final leave) where `tau` never runs. -/
def computeThreshold (n : Nat) : Nat := if n == 0 then 0 else (n * 2 / 3) + 1

/-- **`Constitution`** — the federation's amendable state (`constitution.rs::Constitution`): the
current participant set (public keys), the supermajority `threshold`, the silence `timeoutWaves`,
and a monotone `version`. (Routes-commitment / partition-detection knobs are carried as the
opaque `routes` field; the membership-safety theorems do not depend on them.) -/
structure Constitution where
  participants : List AuthorId
  threshold    : Nat
  timeoutWaves : Nat
  version      : Nat
  routes       : Option Nat := none
  deriving DecidableEq, Inhabited

/-- `Constitution::new` — build a constitution from an initial (deduped) participant set, with the
default supermajority threshold and version 0 (`constitution.rs:63..77`). -/
def Constitution.new (ps : List AuthorId) (timeoutWaves : Nat) : Constitution :=
  let ps := ps.dedup
  { participants := ps, threshold := computeThreshold ps.length,
    timeoutWaves := timeoutWaves, version := 0, routes := none }

/-- `is_participant` — key is a current participant (`constitution.rs:85`). -/
def Constitution.isParticipant (c : Constitution) (k : AuthorId) : Bool := c.participants.contains k

/-- The participant count `n` (`constitution.rs::participant_count`). -/
def Constitution.n (c : Constitution) : Nat := c.participants.length

/-- **`MembershipProposal`** — a Join / Leave / threshold-amend / route-amend proposal
(`constitution.rs::MembershipProposal`). The `Leave` reason and `Join` justification payloads are
elided (they do not affect admission counting); the route amendment carries its new commitment. -/
inductive MembershipProposal where
  | join (nodeKey : AuthorId)
  | leave (nodeKey : AuthorId)
  | amendThreshold (newThreshold : Nat)
  | amendRoutes (newRoutes : Nat)
  deriving DecidableEq, Inhabited

/-! ## 2. `required_votes_for` — the H-rule (`constitution.rs:94..104`). -/

/-- **`requiredVotesFor c p`** — how many DISTINCT current-member approvals proposal `p` needs.

The **H-rule**: amending the threshold from the current `T` to `T'` requires `max(T, T')` votes —
so a minority cannot lower `T` to seize control, nor a majority raise it to lock others out. Join /
Leave / route changes use the current `threshold`. (`Constitution::required_votes_for`.) -/
def requiredVotesFor (c : Constitution) (p : MembershipProposal) : Nat :=
  match p with
  | .amendThreshold t' => max c.threshold t'
  | _                  => c.threshold

/-! ## 3. `apply_proposal` — the mutate-and-recompute rule (`constitution.rs:111..160`). -/

/-- **`applyProposal c p`** — the executable mirror of `Constitution::apply_proposal`: returns the
updated constitution and a `Bool` saying whether the change was actually applied. Faithful to the
Rust branch-by-branch:

* `join k`           — if `k` already a member, no-op (`false`); else insert (deduped), recompute
  threshold = `computeThreshold (n+1)`, bump version.
* `leave k`          — if `k` not a member, no-op; else remove, recompute threshold, bump version.
* `amendThreshold t` — reject if `t = current`, `t = 0`, or `t > n`; else set threshold, bump version.
* `amendRoutes r`    — set routes, bump version (applied immediately).

(`apply_proposal`.) -/
def applyProposal (c : Constitution) (p : MembershipProposal) : Constitution × Bool :=
  match p with
  | .join k =>
      if c.participants.contains k then (c, false)
      else
        let ps := (c.participants ++ [k]).dedup
        ({ c with participants := ps, threshold := computeThreshold ps.length,
                  version := c.version + 1 }, true)
  | .leave k =>
      if c.participants.contains k then
        let ps := c.participants.filter (· ≠ k)
        ({ c with participants := ps, threshold := computeThreshold ps.length,
                  version := c.version + 1 }, true)
      else (c, false)
  | .amendThreshold t =>
      if t == c.threshold || t == 0 || t > c.n then (c, false)
      else ({ c with threshold := t, version := c.version + 1 }, true)
  | .amendRoutes r => ({ c with routes := some r, version := c.version + 1 }, true)

/-! ## 4. Distinct-member approvals via the causal past (`VoteTracker` + `MembershipVote`). -/

/-- A **vote record** — a voter key and the id of the BLOCK that carried the vote. The block
references the proposal block in its causal past (`MembershipVote.proposal_block`). The actual
signature on the vote block is the §8 seam; here the voter key is the authenticated author. -/
structure VoteRec where
  voter      : AuthorId
  voteBlock  : BlockId
  deriving DecidableEq, Inhabited

/-- The causal-past predicate the vote tracker relies on: `inPast proposalBlock voteBlock = true`
iff the vote block is in the proposal block's causal past — i.e. the vote *was cast on this
proposal*. A `Bool` (the Rust `contains` returns a bool), kept abstract here as the `InPast` seam so
the counting theorems do not re-derive the BFS; the concrete instance is `inPastOf`. -/
abbrev InPast := BlockId → BlockId → Bool

/-- The concrete causal-past instance from the verified finality model: `inPastOf B` says
`voteBlock` is in `proposalBlock`'s inclusive causal past in lace `B`. This is the function the
NODE uses (`constitution.rs` votes carry the proposal block in their causal past, resolved via
`finality.rs::causal_past`, the SAME closure `BlocklaceFinality.causalPastIncl` walks). -/
def inPastOf (B : Lace) : InPast :=
  fun proposalBlock voteBlock => (causalPastIncl B proposalBlock).contains voteBlock

/-- **`distinctApprovers c proposalBlock votes inPast`** — the set of DISTINCT current-member keys
that approved the proposal whose block is `proposalBlock`. Mirrors `VoteTracker::record_vote` +
`approval_count` exactly: keep only votes (i) by a current participant (`is_participant`) and
(ii) cast on THIS proposal (the vote block is in the proposal block's causal past), then dedup by
voter key (the per-proposal `HashSet<voter>`). -/
def distinctApprovers (c : Constitution) (proposalBlock : BlockId)
    (votes : List VoteRec) (inPast : InPast) :
    List AuthorId :=
  ((votes.filter (fun v => c.isParticipant v.voter && inPast proposalBlock v.voteBlock)).map (·.voter)).dedup

/-- **`hasPassed`** — the proposal has reached its required distinct-approval count
(`VoteTracker::has_passed`). The `applied` double-application guard is the executor's idempotence
concern (it does not weaken admission), so the safety statement is exactly the count condition. -/
def hasPassed (c : Constitution) (p : MembershipProposal) (proposalBlock : BlockId)
    (votes : List VoteRec) (inPast : InPast) :
    Prop :=
  (distinctApprovers c proposalBlock votes inPast).length ≥ requiredVotesFor c p

/-! ## 5. THRESHOLD-RECOMPUTATION CORRECTNESS — the supermajority is exactly `2n/3 + 1`.

After a Join or Leave the threshold is recomputed to the supermajority of the NEW participant
count, and the count moves by exactly one. This is the property `ordering.rs` then relies on when
it round-robins `waveLeader` over the (new) participant set and counts `superMajority` ratifiers. -/

/-- `computeThreshold` agrees with `BlocklaceFinality.superMajority` on `n > 0` — the constitution's
recomputed threshold is the SAME supermajority the finality model counts ratifiers against. -/
theorem computeThreshold_eq_superMajority {n : Nat} (hn : 0 < n) :
    computeThreshold n = superMajority n := by
  unfold computeThreshold superMajority
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have : (n == 0) = false := by simp [hne]
  simp [this]

/-- **`apply_join_threshold` (threshold-recomputation correctness for Join).** When a Join
applies (the key was NOT already a member), the resulting threshold is EXACTLY the supermajority
`computeThreshold` of the new participant count, and that count is the old participants plus the new
key (deduped). Read straight off `apply_proposal`'s Join branch — the node never forgets to
recompute. -/
theorem apply_join_threshold (c : Constitution) (k : AuthorId)
    (hnew : c.participants.contains k = false) :
    (applyProposal c (.join k)).2 = true ∧
    (applyProposal c (.join k)).1.participants = (c.participants ++ [k]).dedup ∧
    (applyProposal c (.join k)).1.threshold
      = computeThreshold (applyProposal c (.join k)).1.participants.length := by
  have happ : applyProposal c (.join k)
      = ({ c with participants := (c.participants ++ [k]).dedup,
                  threshold := computeThreshold (c.participants ++ [k]).dedup.length,
                  version := c.version + 1 }, true) := by
    simp only [applyProposal, hnew, Bool.false_eq_true, if_false]
  rw [happ]; exact ⟨rfl, rfl, rfl⟩

/-- **`apply_leave_threshold` (threshold-recomputation correctness for Leave).** When a
Leave applies (the key WAS a member), the threshold is recomputed to the supermajority of the
new (smaller) participant set, which is the old set with `k` filtered out. -/
theorem apply_leave_threshold (c : Constitution) (k : AuthorId)
    (hmem : c.participants.contains k = true) :
    (applyProposal c (.leave k)).2 = true ∧
    (applyProposal c (.leave k)).1.participants = c.participants.filter (· ≠ k) ∧
    (applyProposal c (.leave k)).1.threshold
      = computeThreshold (applyProposal c (.leave k)).1.participants.length := by
  have happ : applyProposal c (.leave k)
      = ({ c with participants := c.participants.filter (· ≠ k),
                  threshold := computeThreshold (c.participants.filter (· ≠ k)).length,
                  version := c.version + 1 }, true) := by
    simp only [applyProposal, hmem, if_true]
  rw [happ]; exact ⟨rfl, rfl, rfl⟩

/-- **`apply_bumps_version`.** Every APPLIED proposal strictly bumps the version — the
linearizable amendment history `constitution.rs` keeps (`history.push`). A `false` (no-op) apply
leaves the constitution untouched. -/
theorem apply_bumps_version (c : Constitution) (p : MembershipProposal)
    (happly : (applyProposal c p).2 = true) :
    (applyProposal c p).1.version = c.version + 1 := by
  cases p with
  | join k =>
      simp only [applyProposal] at happly ⊢
      split
      · rename_i h; rw [if_pos h] at happly; exact absurd happly (by simp)
      · rfl
  | leave k =>
      simp only [applyProposal] at happly ⊢
      split
      · rfl
      · rename_i h; rw [if_neg h] at happly; exact absurd happly (by simp)
  | amendThreshold t =>
      simp only [applyProposal] at happly ⊢
      split
      · rename_i h; rw [if_pos h] at happly; exact absurd happly (by simp)
      · rfl
  | amendRoutes r => simp only [applyProposal]

/-! ## 6. THE H-RULE — `max(T, T')` is a genuine LOWER BOUND on votes to amend the threshold.

The core constitutional-safety property: a threshold amendment `T → T'` can never pass with fewer
than BOTH `T` and `T'` distinct approvals. So the bar to *change the bar* dominates both the old
and the new bar — neither a minority lowering nor a majority raising can sneak through. -/

/-- **`requiredVotes_amend_eq_max` (the H-rule, exact form).** The votes required to amend
the threshold from the current `T` to `T'` are EXACTLY `max(T, T')` (`required_votes_for`). -/
theorem requiredVotes_amend_eq_max (c : Constitution) (t' : Nat) :
    requiredVotesFor c (.amendThreshold t') = max c.threshold t' := rfl

/-- **`requiredVotes_amend_ge_current` (H-rule lower bound, old threshold).** Amending the
threshold needs AT LEAST the current threshold's worth of approvals: a majority cannot raise the
threshold to lock others out without the current quorum's consent. -/
theorem requiredVotes_amend_ge_current (c : Constitution) (t' : Nat) :
    requiredVotesFor c (.amendThreshold t') ≥ c.threshold :=
  le_max_left _ _

/-- **`requiredVotes_amend_ge_new` (H-rule lower bound, new threshold).** Amending the
threshold needs AT LEAST the NEW threshold's worth of approvals: a minority cannot lower the
threshold to seize control, because the move already requires the (higher) old-bar quorum AND
cannot dip below the new bar either. -/
theorem requiredVotes_amend_ge_new (c : Constitution) (t' : Nat) :
    requiredVotesFor c (.amendThreshold t') ≥ t' :=
  le_max_right _ _

/-- **`h_rule_dominates_both` (the full H-rule bound).** A threshold amendment requires at
least BOTH the old and the new threshold's worth of distinct approvals — the conjunction that
defeats both the seize-control (lower) and the lock-out (raise) attacks in one statement. -/
theorem h_rule_dominates_both (c : Constitution) (t' : Nat) :
    requiredVotesFor c (.amendThreshold t') ≥ c.threshold ∧
    requiredVotesFor c (.amendThreshold t') ≥ t' :=
  ⟨le_max_left _ _, le_max_right _ _⟩

/-- **`h_rule_passing_needs_both` (H-rule, on the passing side).** If a threshold
amendment PASSES, then the number of distinct current-member approvers is ≥ the old threshold AND
≥ the new threshold. So no passed amendment ever undershoots either bar — the H-rule is enforced at
the point of admission, not merely declared. -/
theorem h_rule_passing_needs_both (c : Constitution) (t' : Nat) (proposalBlock : BlockId)
    (votes : List VoteRec) (inPast : InPast)
    (hpass : hasPassed c (.amendThreshold t') proposalBlock votes inPast) :
    (distinctApprovers c proposalBlock votes inPast).length ≥ c.threshold ∧
    (distinctApprovers c proposalBlock votes inPast).length ≥ t' := by
  unfold hasPassed requiredVotesFor at hpass
  exact ⟨le_trans (le_max_left _ _) hpass, le_trans (le_max_right _ _) hpass⟩

/-! ## 7. DISTINCT-CURRENT-MEMBER ADMISSION — no double vote, no non-member vote.

A proposal passes ONLY with at least `requiredVotesFor` approvals from DISTINCT keys that are ALL
current participants. The approver set is `Nodup` (dedup) and a subset of `c.participants`, so a
Byzantine voter cannot double-count and a non-member cannot vote. -/

/-- **`approvers_nodup`.** The distinct-approver set has no duplicates — it is built by
`dedup`, exactly the `HashSet<voter>` of `VoteTracker`. A single key cannot be counted twice toward
threshold. -/
theorem approvers_nodup (c : Constitution) (proposalBlock : BlockId)
    (votes : List VoteRec) (inPast : InPast) :
    (distinctApprovers c proposalBlock votes inPast).Nodup :=
  List.nodup_dedup _

/-- **`approvers_are_participants`.** Every distinct approver is a CURRENT participant: the
`is_participant` gate in `record_vote` is enforced, so a non-member's vote is dropped before it can
count. The approver list is a subset of `c.participants`. -/
theorem approvers_are_participants (c : Constitution) (proposalBlock : BlockId)
    (votes : List VoteRec) (inPast : InPast) :
    ∀ k ∈ distinctApprovers c proposalBlock votes inPast, c.isParticipant k = true := by
  intro k hk
  unfold distinctApprovers at hk
  have hk' := List.mem_dedup.mp hk
  rw [List.mem_map] at hk'
  obtain ⟨v, hvf, rfl⟩ := hk'
  have hf := List.mem_filter.mp hvf
  rw [Bool.and_eq_true] at hf
  exact hf.2.1

/-- **`approvers_votes_in_past`.** Every distinct approver cast its vote ON THIS PROPOSAL —
there is a vote record by that key whose vote block is in the proposal block's causal past. So an
approval cannot be forged from a vote on a DIFFERENT proposal: the causal-past binding
(`MembershipVote.proposal_block`) is enforced. -/
theorem approvers_votes_in_past (c : Constitution) (proposalBlock : BlockId)
    (votes : List VoteRec) (inPast : InPast) :
    ∀ k ∈ distinctApprovers c proposalBlock votes inPast,
      ∃ v ∈ votes, v.voter = k ∧ c.isParticipant v.voter = true ∧ inPast proposalBlock v.voteBlock = true := by
  intro k hk
  unfold distinctApprovers at hk
  have hk' := List.mem_dedup.mp hk
  rw [List.mem_map] at hk'
  obtain ⟨v, hvf, rfl⟩ := hk'
  have hf := List.mem_filter.mp hvf
  rw [Bool.and_eq_true] at hf
  exact ⟨v, hf.1, rfl, hf.2.1, hf.2.2⟩

/-- **`passed_needs_threshold_distinct_members` (the master admission theorem).** A passed
proposal has at least `requiredVotesFor` approvals from a `Nodup` set of keys that are ALL current
participants. Spelled out: there is a list `S` of approvers with `|S| ≥ requiredVotesFor`, `S` has
no duplicates, and every key in `S` is a current participant. This is the federation's membership-
change safety invariant — admission requires a genuine distinct-current-member quorum, the property
no Byzantine voter (double-voting or impersonating non-members) can subvert. -/
theorem passed_needs_threshold_distinct_members (c : Constitution) (p : MembershipProposal)
    (proposalBlock : BlockId) (votes : List VoteRec) (inPast : InPast)
    (hpass : hasPassed c p proposalBlock votes inPast) :
    ∃ S : List AuthorId,
      S = distinctApprovers c proposalBlock votes inPast ∧
      S.length ≥ requiredVotesFor c p ∧
      S.Nodup ∧
      (∀ k ∈ S, c.isParticipant k = true) := by
  exact ⟨distinctApprovers c proposalBlock votes inPast, rfl, hpass,
         approvers_nodup c proposalBlock votes inPast,
         approvers_are_participants c proposalBlock votes inPast⟩

/-- **`passed_needs_quorum_in_past` (admission via the CAUSAL PAST, the n>1 tower wire).**
The causal-past instantiation: with the blocklace `inPastOf B`, a passed proposal's `requiredVotesFor`
distinct approvers each have a vote BLOCK in `proposalBlock`'s causal past in `B`, are distinct, and
are all current members. This is the form the node actually checks — votes are blocks referencing
the proposal in their causal past (`finality.rs::causal_past`, the SAME closure `BlocklaceFinality`
walks). At `n > 1` it says: to change membership you need a real quorum of distinct members who each
provably observed the proposal. -/
theorem passed_needs_quorum_in_past (c : Constitution) (p : MembershipProposal) (B : Lace)
    (proposalBlock : BlockId) (votes : List VoteRec)
    (hpass : hasPassed c p proposalBlock votes (inPastOf B)) :
    ∃ S : List AuthorId,
      S.length ≥ requiredVotesFor c p ∧ S.Nodup ∧
      (∀ k ∈ S, c.isParticipant k = true) ∧
      (∀ k ∈ S, ∃ v ∈ votes, v.voter = k ∧
        (causalPastIncl B proposalBlock).contains v.voteBlock) := by
  refine ⟨distinctApprovers c proposalBlock votes (inPastOf B), hpass,
          approvers_nodup c proposalBlock votes (inPastOf B),
          approvers_are_participants c proposalBlock votes (inPastOf B), ?_⟩
  intro k hk
  obtain ⟨v, hv, hvk, _, hpast⟩ := approvers_votes_in_past c proposalBlock votes (inPastOf B) k hk
  exact ⟨v, hv, hvk, hpast⟩

/-! ## 8. AUTO-EVICTION — the equivocator is removed without a vote (`auto_evict_equivocator`).

An equivocation proof (a `Blocklace.Equivocation` object — two incomparable same-author blocks) is
self-evident, so it removes the equivocator immediately, recomputes the threshold, bumps the version.
No quorum: the byzantine-repelling discipline of `Authority.Blocklace`. -/

/-- **`autoEvict c k`** — remove key `k` (an equivocator) without a vote, recomputing the threshold
to the supermajority of the new set and bumping the version. Returns `(c', applied?)`; `applied?`
is `false` iff `k` was not a member. (`auto_evict_equivocator`.) -/
def autoEvict (c : Constitution) (k : AuthorId) : Constitution × Bool :=
  if c.participants.contains k then
    let ps := c.participants.filter (· ≠ k)
    ({ c with participants := ps, threshold := computeThreshold ps.length,
              version := c.version + 1 }, true)
  else (c, false)

/-- **`autoEvict_removes`.** If the equivocation proof's creator was a current participant,
auto-eviction applies, the creator is filtered OUT of the new participant set, and the threshold is
recomputed — all WITHOUT any vote. The `Equivocation` proof object (from `Authority.Blocklace`) is
the only authorization needed: the fork is its own warrant. -/
theorem autoEvict_removes (c : Constitution) (B : Lace) (k : AuthorId) (a b : Block)
    (_ : Equivocation B k a b) (hmem : c.participants.contains k = true) :
    (autoEvict c k).2 = true ∧
    (autoEvict c k).1.participants = c.participants.filter (· ≠ k) ∧
    (autoEvict c k).1.threshold = computeThreshold (autoEvict c k).1.participants.length ∧
    k ∉ (autoEvict c k).1.participants := by
  have happ : autoEvict c k
      = ({ c with participants := c.participants.filter (· ≠ k),
                  threshold := computeThreshold (c.participants.filter (· ≠ k)).length,
                  version := c.version + 1 }, true) := by
    simp only [autoEvict, hmem, if_true]
  rw [happ]
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp [List.mem_filter]

/-- **`autoEvict_threshold`.** After auto-eviction the threshold equals the supermajority
of the new participant count — the SAME recompute as a voted Leave, so the post-eviction federation
is in a consistent constitutional state (the threshold finality counts against is correct). -/
theorem autoEvict_threshold (c : Constitution) (k : AuthorId)
    (hmem : c.participants.contains k = true) :
    (autoEvict c k).1.threshold = computeThreshold (autoEvict c k).1.participants.length := by
  simp only [autoEvict, hmem, if_true]

/-! ## 9. THE FINALITY/EXECUTOR CONNECTION — the participant set IS what `tau` round-robins over.

The constitution's per-version participant set is exactly the `participants : List AuthorId` that
`BlocklaceFinality.waveLeader` round-robins its leader over and `superMajority` counts ratifiers
against. So a membership change is not free-floating governance: it RE-PARAMETERIZES the finality
rule that drives the verified executor (`ConsensusExec.executeFinalized`). -/

/-- The participant set the finality model consumes (`BlocklaceFinality.waveLeader …` /
`findAllFinalLeaders … participants …`). The constitution's `participants` IS this list. -/
def Constitution.asWaveParticipants (c : Constitution) : List AuthorId := c.participants

/-- **`membership_change_reparameterizes_finality` (the connection).** After an applied
Join / Leave, the participant list that `BlocklaceFinality` round-robins `waveLeader` over is
exactly the constitution's NEW participant set, AND the supermajority finality counts against equals
the constitution's recomputed threshold (`computeThreshold_eq_superMajority`, given `n > 0`). So the
amendment correctly re-parameterizes the finality rule that feeds the verified executor — the
membership tower and the finality tower TOUCH at the participant set + threshold. -/
theorem membership_change_reparameterizes_finality (c : Constitution) (k : AuthorId)
    (hmem : c.participants.contains k = true)
    (hpos : 0 < (applyProposal c (.leave k)).1.participants.length) :
    (applyProposal c (.leave k)).1.asWaveParticipants = (applyProposal c (.leave k)).1.participants ∧
    (applyProposal c (.leave k)).1.threshold
      = superMajority (applyProposal c (.leave k)).1.asWaveParticipants.length := by
  obtain ⟨_, _, hthr⟩ := apply_leave_threshold c k hmem
  refine ⟨rfl, ?_⟩
  show (applyProposal c (.leave k)).1.threshold
        = superMajority (applyProposal c (.leave k)).1.participants.length
  rw [hthr, computeThreshold_eq_superMajority hpos]

/-! ## 10. NON-VACUITY — CONCRETE traces the model ADMITS / REJECTS (n > 1), the Rust
differential.

These `#guard`s reproduce, value-for-value, the numbers the `constitution.rs` unit tests assert.
A false `#guard` is a BUILD ERROR (the sanctioned non-vacuity tooth for executable `def`s). They
establish, against CONCRETE constitutions at n > 1: the supermajority table, the H-rule vote
counts, Join/Leave threshold recompute, and that a 3-member join passes with exactly 3 distinct
in-past approvals but FAILS with 2 (the admission theorem constrains a real, non-trivial vote). -/

/-- A concrete 3-participant federation (keys 1,2,3), default supermajority threshold. -/
def fed3 : Constitution := Constitution.new [1, 2, 3] 10
/-- A concrete 4-participant federation (keys 1,2,3,4). -/
def fed4 : Constitution := Constitution.new [1, 2, 3, 4] 10
/-- A single-participant federation — the scales-to-zero n=1 special case. -/
def fed1 : Constitution := Constitution.new [1] 10

-- compute_threshold table (constitution.rs::constitution_threshold_values).
#guard computeThreshold 1 == 1
#guard computeThreshold 3 == 3
#guard computeThreshold 4 == 3
#guard computeThreshold 7 == 5
#guard computeThreshold 10 == 7
#guard computeThreshold 0 == 0

-- the federations carry the right thresholds.
#guard fed3.threshold == 3      -- n=3 ⇒ 3 (constitution_new_computes_threshold shape)
#guard fed4.threshold == 3      -- n=4 ⇒ 3
#guard fed1.threshold == 1      -- n=1 ⇒ 1 (n1_single_participant_threshold_is_one)

-- H-RULE golden vectors (h_rule_amend_threshold_from_2_to_3 / _from_3_to_2).
-- a constitution at threshold 2 amending to 3 needs max(2,3) = 3.
#guard requiredVotesFor { fed4 with threshold := 2 } (.amendThreshold 3) == 3
-- at threshold 3 amending DOWN to 2 ALSO needs max(3,2) = 3 (the current bar wins).
#guard requiredVotesFor fed4 (.amendThreshold 2) == 3

-- JOIN threshold recompute (propose_join_threshold_approvals_member_added):
-- n=3 federation admits key 4 ⇒ n=4, threshold stays 3.
#guard ((applyProposal fed3 (.join 4)).2 == true)
#guard ((applyProposal fed3 (.join 4)).1.participants.length == 4)
#guard ((applyProposal fed3 (.join 4)).1.threshold == 3)
#guard ((applyProposal fed3 (.join 4)).1.version == 1)
-- joining an EXISTING member is a no-op (already a member).
#guard ((applyProposal fed3 (.join 2)).2 == false)

-- LEAVE threshold recompute (propose_leave_threshold_approvals_member_removed):
-- n=4 federation removes key 4 ⇒ n=3, threshold stays 3.
#guard ((applyProposal fed4 (.leave 4)).2 == true)
#guard ((applyProposal fed4 (.leave 4)).1.participants.length == 3)
#guard ((applyProposal fed4 (.leave 4)).1.threshold == 3)
-- n=2 → n=1: peer leaves, threshold drops to 1 (n2_to_n1_peer_timeout_decreases_threshold).
#guard ((applyProposal (Constitution.new [1,2] 5) (.leave 2)).1.threshold == 1)
-- n=1 → n=2: peer joins, threshold rises to 2 (n1_to_n2_peer_joins_threshold_increases).
#guard ((applyProposal fed1 (.join 2)).1.threshold == 2)

-- AMEND-THRESHOLD validity guards: t=0 rejected, t>n rejected, t=current rejected.
#guard ((applyProposal fed4 (.amendThreshold 0)).2 == false)
#guard ((applyProposal fed4 (.amendThreshold 5)).2 == false)   -- > n=4
#guard ((applyProposal fed4 (.amendThreshold 3)).2 == false)   -- = current
#guard ((applyProposal fed4 (.amendThreshold 2)).2 == true)    -- valid down-amend

-- AUTO-EVICTION: equivocator key 3 removed from the 3-fed without a vote, threshold ⇒ supermajority(2).
#guard ((autoEvict fed3 3).2 == true)
#guard ((autoEvict fed3 3).1.participants == [1, 2])
#guard ((autoEvict fed3 3).1.threshold == computeThreshold 2)  -- = 2

/-! ### Distinct-approval admission on a CONCRETE vote trace (n=3, votes in the proposal's past). -/

/-- Proposal block id for the demo join. -/
def joinProp : BlockId := 100
/-- Three honest votes from the current members 1,2,3, each carried by its own vote block whose id
we will place in the proposal block's causal past via `voteInPast`. -/
def votes3 : List VoteRec := [⟨1, 11⟩, ⟨2, 12⟩, ⟨3, 13⟩]
/-- A two-vote prefix (only members 1 and 2 voted) — below threshold for the 3-fed. -/
def votes2 : List VoteRec := [⟨1, 11⟩, ⟨2, 12⟩]
/-- A trace with a NON-member voter (key 9) and a DOUBLE vote by member 1 — both must be dropped /
deduped, so this counts as only ONE distinct approval. -/
def votesByz : List VoteRec := [⟨1, 11⟩, ⟨1, 14⟩, ⟨9, 15⟩]

/-- The concrete causal-past instance for the demo: all three vote blocks (11,12,13,14) are in the
proposal block's causal past; the non-member's block (15) is too (membership is still rejected by
the `is_participant` gate, not by the past — exactly the Rust separation of the two checks). -/
def voteInPast : InPast := fun pb vb => pb == joinProp && vb ∈ ([11, 12, 13, 14, 15] : List BlockId)

-- 3 DISTINCT current-member approvals on the proposal ⇒ PASSES (needs threshold = 3).
#guard (distinctApprovers fed3 joinProp votes3 voteInPast).length == 3
#guard decide ((distinctApprovers fed3 joinProp votes3 voteInPast).length ≥ requiredVotesFor fed3 (.join 4))
-- only 2 distinct approvals ⇒ FAILS (below threshold 3) — admission is non-trivially constrained.
#guard (distinctApprovers fed3 joinProp votes2 voteInPast).length == 2
#guard decide ((distinctApprovers fed3 joinProp votes2 voteInPast).length ≥ requiredVotesFor fed3 (.join 4)) == false
-- a double-vote + a NON-member vote ⇒ only ONE distinct member approval (9 dropped, 1 deduped).
#guard (distinctApprovers fed3 joinProp votesByz voteInPast).length == 1
#guard (distinctApprovers fed3 joinProp votesByz voteInPast) == [1]

/-! The `#guard`s above are machine-checked non-vacuity teeth: against CONCRETE n > 1 constitutions
they establish (i) the supermajority table and the federations' thresholds; (ii) the H-rule
`max(T,T')` vote counts (2→3 and 3→2 both need 3); (iii) Join/Leave threshold recompute including
n=1↔n=2; (iv) the amend-threshold validity guards; (v) auto-eviction without a vote; and (vi) on a
real vote trace, a 3-member join PASSES with 3 distinct in-past approvals but FAILS with 2, and a
Byzantine trace (non-member + double-vote) collapses to ONE distinct approval. So the safety
theorems constrain a REAL, non-trivial admission rule, and the model reproduces the `constitution.rs`
unit-test numbers value-for-value. -/

/-! ## 11. Axiom hygiene — the governed-membership rule + its safety teeth are kernel-clean. -/

#assert_axioms computeThreshold_eq_superMajority
#assert_axioms apply_join_threshold
#assert_axioms apply_leave_threshold
#assert_axioms apply_bumps_version
#assert_axioms requiredVotes_amend_eq_max
#assert_axioms requiredVotes_amend_ge_current
#assert_axioms requiredVotes_amend_ge_new
#assert_axioms h_rule_dominates_both
#assert_axioms h_rule_passing_needs_both
#assert_axioms approvers_nodup
#assert_axioms approvers_are_participants
#assert_axioms approvers_votes_in_past
#assert_axioms passed_needs_threshold_distinct_members
#assert_axioms passed_needs_quorum_in_past
#assert_axioms autoEvict_removes
#assert_axioms autoEvict_threshold
#assert_axioms membership_change_reparameterizes_finality

end Dregg2.Distributed.MembershipSafety
