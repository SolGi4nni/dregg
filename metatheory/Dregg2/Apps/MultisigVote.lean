/-
# Dregg2.Apps.MultisigVote — a verified MULTI-PARTY APPROVAL / MULTISIG VOTE over the REAL kernel.

A proposal `p` resolves to PASSED once `≥ threshold` DISTINCT, ENFRANCHISED voters have approved it,
each voter approving AT MOST ONCE. This runs on the GENUINE `RecordKernelState` (NOT the `DemoRes`
toy): the approval set IS the kernel's spent-note nullifier seen-set (`k.nullifiers`), each cast vote
inserting the voter's `CellId` as a "vote nullifier" exactly the way `apply_note_spend`
(`turn/src/executor/apply.rs:941`) inserts a spend nullifier — so DOUBLE-VOTE is rejected by the SAME
fail-closed set gate that prevents a double-spend (`note_no_double_spend`/`note_spend_inserts`).

It is **composition, not new kernel theory**: the no-double-vote keystone INSTANTIATES the proved
`RecordKernel` nullifier-set lemmas, and the AUTHORITY gate REUSES the cap-table branch of
`Exec/Kernel.authorizedB` — a voter is enfranchised iff they are in the published `registry` OR hold a
vote-capability `Cap.node proposalCell` (the `endpoint`/`node` cap branch that `authorizedB` consults,
NOT the reflexive `actor == src` tautology). What this module ADDS is the multisig COMPOSITION and the
four end-user guarantees:

  * **SAFETY (no double-vote)** — a voter already in the approval set, re-approving, does NOT change
    the approval set, so the tally cannot be inflated by re-voting (`castVote` fails-closed via the
    nullifier set, and the approval set is idempotent under a re-insert — `revote_no_change`,
    `revote_tally_unchanged`). Teeth: a concrete double approval is counted ONCE.
  * **SAFETY/AUTHORITY (enfranchisement)** — only voters in the `registry` OR holding the vote-cap
    count: a NON-enfranchised approval is REJECTED by `castVote` (`outsider_vote_rejected`). This
    EXERCISES A REAL GATE — `enfranchisedB` consults the registry membership AND the cap table — NOT
    the `actor == src` reflexive tautology. Teeth: an outsider (not in registry, no cap) is rejected,
    while a cap-bearer (NOT in the registry) is ADMITTED via the cap branch (`capbearer_admitted`).
  * **CORRECTNESS (pass iff threshold)** — the proposal PASSES iff the distinct-enfranchised approval
    count meets the threshold: `passes p k ↔ threshold ≤ tally p k`, BOTH directions (`passes_iff`).
  * **LIVENESS (◇ resolves)** — once `threshold` distinct enfranchised approvals have arrived, the
    proposal RESOLVES to passed: a concrete fixture reaches `passes = true` after exactly `threshold`
    cast votes (`votes_reach_quorum`, a decide witness on a real-kernel fixture).

TEETH (decide on a concrete fixture): a sub-threshold proposal does NOT pass; a double-voter is
counted once; an outsider is rejected; the cap-bearer is admitted. Runs on real kernel state.
-/
import Dregg2.Exec.RecordKernel

namespace Dregg2.Apps.MultisigVote

open Dregg2.Exec
open Dregg2.Authority (Cap Auth)

/-! ## 1. The proposal config + the enfranchisement gate.

A `Proposal` bundles the on-chain target cell `proposalCell`, the published `registry` of enfranchised
voter cells, and the `threshold` (the quorum: number of distinct enfranchised approvals required to
pass). The approval set itself lives in the REAL kernel's `nullifiers` seen-set — a cast vote inserts
the voter's `CellId` as a vote nullifier, so the set is genuinely on-chain and the no-double-vote gate
is the kernel's own. -/

/-- **`Proposal`** — the multisig proposal config: the target cell `proposalCell`, the published
`registry` of enfranchised voter cells, and the `threshold` quorum (distinct enfranchised approvals
needed to pass). -/
structure Proposal where
  /-- the on-chain proposal cell (the target the vote-cap is `Cap.node`-keyed to). -/
  proposalCell : CellId
  /-- the published registry of enfranchised voter cells. -/
  registry     : Finset CellId
  /-- the quorum: number of distinct enfranchised approvals needed to pass. -/
  threshold    : Nat

/-- **`voteCap p`** — the enfranchisement capability for proposal `p`: a `Cap.node` keyed to the
proposal cell. A voter holding this cap is enfranchised even if NOT in the registry — exactly the
cap-table branch (`Cap.node turn.src`) that `Exec/Kernel.authorizedB` consults. -/
def voteCap (p : Proposal) : Cap := Cap.node p.proposalCell

/-- **`enfranchisedB p k voter`** — is `voter` enfranchised to vote on `p` in kernel state `k`? TRUE
iff the voter is in the published `registry` OR holds the vote-cap `Cap.node proposalCell` in the
kernel cap table `k.caps`. This is the REAL authority gate — it consults BOTH the registry AND the
cap table (the `Cap.node` branch of `authorizedB`), NEVER the reflexive `actor == src` tautology.
Decidable, computable, FAIL-CLOSED (a voter in neither is rejected). -/
def enfranchisedB (p : Proposal) (k : RecordKernelState) (voter : CellId) : Bool :=
  decide (voter ∈ p.registry) || (k.caps voter).contains (voteCap p)

/-! ## 2. Casting a vote on the REAL kernel (the fail-closed approval).

A cast vote inserts the voter's `CellId` into the kernel's `nullifiers` seen-set — the SAME set
`apply_note_spend` uses — gated by enfranchisement AND no-double-vote. Fail-closed (`none`) if the
voter is not enfranchised or has already approved. -/

/-- **`castVote p k voter`** — cast `voter`'s approval on proposal `p` over the REAL kernel state `k`.
Fail-closed (`none`) if the voter is NOT enfranchised (neither in the registry nor cap-bearing) OR has
already approved (`voter ∈ k.nullifiers`, the double-vote gate). On success, inserts `voter` into the
nullifier seen-set (the approval set) — exactly the way `noteSpendNullifier` inserts a spend
nullifier. -/
def castVote (p : Proposal) (k : RecordKernelState) (voter : CellId) : Option RecordKernelState :=
  if enfranchisedB p k voter = true ∧ voter ∉ k.nullifiers then
    some { k with nullifiers := voter :: k.nullifiers }
  else
    none

/-- **`approvalSet k`** — the set of voters who have approved (the on-chain `nullifiers` seen-set,
deduplicated to a `Finset`). The approval set is the kernel's own spent-nullifier set. -/
def approvalSet (k : RecordKernelState) : Finset CellId := k.nullifiers.toFinset

/-- **`tally p k`** — the number of DISTINCT, ENFRANCHISED approvals: the count of approval-set voters
who are actually enfranchised on `p`. Only enfranchised approvals are counted toward the quorum (so a
later-defranchised entry, or any non-enfranchised id, never inflates the tally). -/
def tally (p : Proposal) (k : RecordKernelState) : Nat :=
  ((approvalSet k).filter (fun v => enfranchisedB p k v = true)).card

/-- **`passes p k`** — does proposal `p` PASS in kernel state `k`? TRUE iff the distinct-enfranchised
approval count meets the threshold quorum. -/
def passes (p : Proposal) (k : RecordKernelState) : Bool := decide (p.threshold ≤ tally p k)

/-! ## 3. KEYSTONE — AUTHORITY/ENFRANCHISEMENT: a non-enfranchised vote is REJECTED.

The authority headline: `castVote` consults the REAL gate `enfranchisedB` (registry membership OR the
`Cap.node` cap branch), so a voter in NEITHER is fail-closed. This is the cap-table branch of
`authorizedB`, NOT the reflexive `actor == src` arm. -/

/-- **`castVote_enfranchised` (AUTHORITY)** — a committed vote was cast by an ENFRANCHISED voter: any
successful `castVote` forces `enfranchisedB p k voter = true`. The kernel never records an approval
from a voter outside the registry who holds no vote-cap. -/
theorem castVote_enfranchised {p : Proposal} {k k' : RecordKernelState} {voter : CellId}
    (h : castVote p k voter = some k') : enfranchisedB p k voter = true := by
  unfold castVote at h
  by_cases hg : enfranchisedB p k voter = true ∧ voter ∉ k.nullifiers
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`unenfranchised_vote_rejected` (AUTHORITY — fail-closed)** — a voter who is NOT enfranchised
(`enfranchisedB = false`) is REJECTED by `castVote` (`none`). The contrapositive face of the gate:
no approval is recorded from a non-enfranchised actor. This exercises the registry/cap gate, not the
`actor == src` tautology. -/
theorem unenfranchised_vote_rejected {p : Proposal} {k : RecordKernelState} {voter : CellId}
    (h : enfranchisedB p k voter = false) : castVote p k voter = none := by
  unfold castVote
  rw [if_neg]
  rintro ⟨he, _⟩
  rw [h] at he; exact absurd he (by simp)

/-! ## 4. KEYSTONE — SAFETY: no double-vote (re-approving cannot inflate the tally).

The safety headline composes the kernel's own nullifier-set anti-replay: a voter already in the
approval set cannot be inserted again (`castVote` fails-closed), and even at the SET level a re-insert
is idempotent — the approval set, hence the tally, is unchanged. -/

/-- **`revote_rejected` (SAFETY — fail-closed double-vote)** — a voter already in the approval set
(`voter ∈ k.nullifiers`) re-approving is REJECTED by `castVote` (`none`). Mirrors the kernel's
`note_no_double_spend`: the SAME seen-set gate that stops a double-spend stops a double-vote. -/
theorem revote_rejected {p : Proposal} {k : RecordKernelState} {voter : CellId}
    (h : voter ∈ k.nullifiers) : castVote p k voter = none := by
  unfold castVote
  rw [if_neg]
  rintro ⟨_, hnin⟩
  exact hnin h

/-- **`vote_inserts` — a committed vote actually inserts the voter** into the approval seen-set (so a
SUBSEQUENT vote by the same voter is rejected by `revote_rejected`). The positive face: the approval
genuinely lands on-chain. -/
theorem vote_inserts {p : Proposal} {k k' : RecordKernelState} {voter : CellId}
    (h : castVote p k voter = some k') : voter ∈ k'.nullifiers := by
  unfold castVote at h
  by_cases hg : enfranchisedB p k voter = true ∧ voter ∉ k.nullifiers
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; simp
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`revote_no_change` (SAFETY — set idempotence)** — re-inserting a voter ALREADY in the approval
set leaves the approval set UNCHANGED: `(voter :: k.nullifiers).toFinset = k.nullifiers.toFinset`.
This is `Finset.insert` idempotence — the SET-level reason a double-vote cannot inflate the count even
if the gate were bypassed. -/
theorem revote_no_change {k : RecordKernelState} {voter : CellId} (h : voter ∈ k.nullifiers) :
    approvalSet { k with nullifiers := voter :: k.nullifiers } = approvalSet k := by
  unfold approvalSet
  simp only [List.toFinset_cons]
  exact Finset.insert_eq_self.mpr (List.mem_toFinset.mpr h)

/-- **`revote_tally_unchanged` (SAFETY — the headline)** — re-recording a voter already in the approval
set does NOT change the tally for ANY proposal: the distinct-enfranchised count is fixed under a
re-insert. A double-vote is counted once. Composes `revote_no_change` (the approval set is unchanged)
under the tally's filter+card. -/
theorem revote_tally_unchanged {p : Proposal} {k : RecordKernelState} {voter : CellId}
    (h : voter ∈ k.nullifiers) :
    tally p { k with nullifiers := voter :: k.nullifiers } = tally p k := by
  unfold tally
  have hset : approvalSet { k with nullifiers := voter :: k.nullifiers } = approvalSet k :=
    revote_no_change h
  -- `enfranchisedB` reads `caps`/`registry`, both unchanged by the nullifier re-insert.
  simp only [enfranchisedB] at *
  rw [hset]

/-! ## 5. KEYSTONE — CORRECTNESS: the proposal PASSES iff the threshold is met (an IFF, both ways). -/

/-- **`passes_iff` (CORRECTNESS — the headline IFF)** — proposal `p` PASSES in `k` IFF the
distinct-enfranchised approval count meets the threshold quorum: `passes p k = true ↔ threshold ≤
tally p k`. BOTH directions, by the definition of `passes` as the decidable threshold test. -/
theorem passes_iff (p : Proposal) (k : RecordKernelState) :
    passes p k = true ↔ p.threshold ≤ tally p k := by
  unfold passes; exact decide_eq_true_iff

/-- **`passes_of_quorum` (CORRECTNESS — the ⇐ resolve direction)** — if the distinct-enfranchised
approval count reaches the threshold, the proposal PASSES. The liveness payload: enough approvals ⇒
resolved-to-passed. -/
theorem passes_of_quorum {p : Proposal} {k : RecordKernelState} (h : p.threshold ≤ tally p k) :
    passes p k = true := (passes_iff p k).mpr h

/-- **`not_passes_of_subquorum` (CORRECTNESS — the ⇒ safety direction)** — if the tally is BELOW the
threshold, the proposal does NOT pass. A sub-threshold proposal cannot resolve. -/
theorem not_passes_of_subquorum {p : Proposal} {k : RecordKernelState} (h : tally p k < p.threshold) :
    passes p k = false := by
  rw [Bool.eq_false_iff, ne_eq, passes_iff]; omega

/-! ## 6. The FIXTURE — a concrete 3-of-{0,1,2,3} multisig on REAL kernel state.

Enfranchised registry `{0, 1, 2}` over proposal cell `100`, threshold `2`. Cell `3` is an OUTSIDER
(not in the registry, holds no vote-cap). Cell `4` is a CAP-BEARER (NOT in the registry, but holds the
vote-cap `Cap.node 100`) — admitted via the cap branch. The kernel state is a real `RecordKernelState`
with the genuine `accounts`/`caps` and an empty `nullifiers` (no votes yet). -/

/-- The vote fixture: a fresh proposal-bearing kernel state. Cells `{0,1,2,3,4}` are live; the cap
table grants ONLY cell `4` the vote-cap `Cap.node 100` (so `4` is enfranchised by cap, NOT registry);
no votes cast yet (`nullifiers = []`). -/
def voteK0 : RecordKernelState :=
  { accounts := {0, 1, 2, 3, 4}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 4 then [Cap.node 100] else [] }

/-- The 3-of registry proposal: enfranchised `{0, 1, 2}`, proposal cell `100`, threshold `2`. -/
def prop0 : Proposal := { proposalCell := 100, registry := {0, 1, 2}, threshold := 2 }

/-! ## 7. The TEETH — decided on the concrete fixture.

Real discriminating instances on `voteK0`/`prop0`: the empty proposal is sub-threshold (does NOT
pass); the outsider (cell 3) is rejected while the registry voter (cell 0) and the cap-bearer (cell 4)
are admitted; a double-voter is counted once; and reaching the threshold genuinely resolves the
proposal to passed. -/

/-- **`empty_does_not_pass` (TEETH — sub-threshold)** — with NO votes cast, the tally is `0 < 2`, so
the proposal does NOT pass. The vacuous-quorum guard. -/
theorem empty_does_not_pass : passes prop0 voteK0 = false := by decide

/-- **`outsider_vote_rejected` (TEETH — AUTHORITY)** — cell `3` is an OUTSIDER (not in registry `{0,1,2}`
and holds no vote-cap), so its approval is REJECTED (`castVote = none`). This exercises the REAL gate:
`enfranchisedB` fails on BOTH arms (`3 ∉ {0,1,2}`, and `caps 3 = []` has no `Cap.node 100`) — the
cap-table branch the `actor == src` tautology never touches. -/
theorem outsider_vote_rejected : castVote prop0 voteK0 3 = none := by decide

/-- **`registry_voter_admitted` (TEETH — non-vacuity of the gate, registry arm)** — cell `0` IS in the
registry, so its approval is ADMITTED (`castVote` is `some`). The gate is discriminating, not
"everything rejected". -/
theorem registry_voter_admitted : (castVote prop0 voteK0 0).isSome = true := by decide

/-- **`capbearer_admitted` (TEETH — the cap branch, genuine authority content)** — cell `4` is NOT in
the registry `{0,1,2}`, yet holds the vote-cap `Cap.node 100`, so it is ADMITTED via the CAP BRANCH of
`enfranchisedB` (`(caps 4).contains (Cap.node 100)`). This is the genuine cap-gated enfranchisement —
the same `Cap.node` branch `authorizedB` consults — distinguished from the outsider `3` who has
neither registry membership nor cap. -/
theorem capbearer_admitted : (castVote prop0 voteK0 4).isSome = true := by decide

/-- **`double_vote_counted_once` (TEETH — SAFETY)** — cell `0` votes, then `0` re-votes: the SECOND
vote is REJECTED (`none`), so the approval set holds `0` exactly once and the tally is `1`, NOT `2`.
A double-voter cannot inflate the quorum. Decided end-to-end on the real-kernel fixture. -/
theorem double_vote_counted_once :
    ((castVote prop0 voteK0 0).bind (fun k => castVote prop0 k 0)) = none ∧
    ((castVote prop0 voteK0 0).map (fun k => tally prop0 k)) = some 1 := by decide

/-- **`votes_reach_quorum` (TEETH — LIVENESS ◇)** — voters `0` then `1` (both enfranchised, distinct)
cast their approvals; the resulting state reaches the threshold-2 quorum and the proposal RESOLVES to
PASSED. Once `threshold` distinct enfranchised approvals arrive, `passes = true` — a concrete decide
witness of the liveness ◇ on the real-kernel fixture. -/
theorem votes_reach_quorum :
    ((castVote prop0 voteK0 0).bind (fun k => castVote prop0 k 1)).map (fun k => passes prop0 k)
      = some true := by decide

/-- **`subquorum_does_not_pass` (TEETH — CORRECTNESS, sub-threshold after a real vote)** — after only
ONE enfranchised approval (cell `0`), the tally is `1 < 2`, so the proposal still does NOT pass. A
single vote is not a quorum. -/
theorem subquorum_does_not_pass :
    ((castVote prop0 voteK0 0).map (fun k => passes prop0 k)) = some false := by decide

/-- **`capbearer_counts_toward_quorum` (TEETH — the cap branch reaches quorum)** — a registry voter
(`0`) plus the CAP-BEARER (`4`, not in registry but cap-enfranchised) together form a distinct quorum
of `2`, and the proposal PASSES. The cap branch is load-bearing for liveness, not merely admitted. -/
theorem capbearer_counts_toward_quorum :
    ((castVote prop0 voteK0 0).bind (fun k => castVote prop0 k 4)).map (fun k => passes prop0 k)
      = some true := by decide

/-! ## 8. `#eval` smoke — the vote's load-bearing bits, decided by the model alone. -/

-- empty proposal: tally 0, does not pass.
#guard (tally prop0 voteK0, passes prop0 voteK0) == (0, false)                             -- (0, false)
-- outsider (3) rejected; registry voter (0) and cap-bearer (4) admitted.
#guard (castVote prop0 voteK0 3).isSome == false                                          -- false
#guard ((castVote prop0 voteK0 0).isSome, (castVote prop0 voteK0 4).isSome) == (true, true)  -- (true, true)
-- one vote: tally 1, still sub-threshold.
#guard (castVote prop0 voteK0 0).map (fun k => (tally prop0 k, passes prop0 k)) == some (1, false)  -- some (1, false)
-- double vote rejected; tally stays 1.
#guard ((castVote prop0 voteK0 0).bind (fun k => castVote prop0 k 0)).isSome == false      -- false
-- two distinct enfranchised votes (0 then 1): quorum reached, PASSES.
#guard (((castVote prop0 voteK0 0).bind (fun k => castVote prop0 k 1)).map
        (fun k => (tally prop0 k, passes prop0 k))) == some (2, true)                      -- some (2, true)
-- registry + cap-bearer (0 then 4): quorum reached via the cap branch.
#guard (((castVote prop0 voteK0 0).bind (fun k => castVote prop0 k 4)).map
        (fun k => (tally prop0 k, passes prop0 k))) == some (2, true)                      -- some (2, true)

/-! ## 9. Axiom hygiene — every keystone pinned to the standard kernel triple.

`#assert_axioms` walks each keystone and errors if any escapes `{propext, Classical.choice,
Quot.sound}` — a `sorryAx`/`native_decide` anywhere would fail the build. -/

#assert_axioms castVote_enfranchised
#assert_axioms unenfranchised_vote_rejected
#assert_axioms revote_rejected
#assert_axioms vote_inserts
#assert_axioms revote_no_change
#assert_axioms revote_tally_unchanged
#assert_axioms passes_iff
#assert_axioms passes_of_quorum
#assert_axioms not_passes_of_subquorum
#assert_axioms empty_does_not_pass
#assert_axioms outsider_vote_rejected
#assert_axioms registry_voter_admitted
#assert_axioms capbearer_admitted
#assert_axioms double_vote_counted_once
#assert_axioms votes_reach_quorum
#assert_axioms subquorum_does_not_pass
#assert_axioms capbearer_counts_toward_quorum

end Dregg2.Apps.MultisigVote
