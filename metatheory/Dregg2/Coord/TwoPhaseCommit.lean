/-
# Dregg2.Coord.TwoPhaseCommit — the 2PC COORDINATOR DECISION machine (`evaluate_votes`),
# and the no-conflicting-decision safety the vote count enforces.

**The gap this closes.** `Distributed/EntangledJoint.lean` models the *post-commit* ledger effect of
an atomic multi-party turn — `jointApplyAll`, the all-or-none fold over the verified per-cell
executor — and proves atomicity/conservation OF THE APPLIED FOREST. It does NOT model the **decision
procedure** that decides *whether to apply at all*: `coord/src/atomic.rs`'s `Coordinator` runs a
2-phase commit (`atomic.rs:1-7`, `Propose → Vote → Commit/Abort`) whose heart is `evaluate_votes`
(`atomic.rs:761-779`): from the collected Yes/No votes and the `threshold`, it yields a `Decision`
∈ {Commit, Abort, Pending}. THAT vote-counting state machine — and the safety property that it never
simultaneously decides Commit AND Abort — is uncovered. This module models it faithfully
and proves the 2PC agreement / no-conflicting-decision property.

## What is modelled (faithful to `coord/src/atomic.rs`)

  * `Tally` = the vote bag the coordinator accumulates in `CoordinatorState::Proposing.votes`
    (`atomic.rs:310-316`): a count of `yes`, a count of `no`, over `n` participants, with a
    `threshold` (`atomic.rs:363`, the minimum Yes votes to commit). We track the COUNTS — the safety
    content of `evaluate_votes` is purely counting (`atomic.rs:767-769` `yes_count`/`no_count`).
  * `evaluate` = `Coordinator::evaluate_votes` (`atomic.rs:761-779`), BYTE-FOR-BYTE:
    `if yes ≥ threshold then Commit else if no > n - threshold then Abort else Pending`. The middle
    clause is the real "too many No votes — threshold can never be reached" abort (`atomic.rs:773`).
  * `castYes`/`castNo` = `receive_vote` (`atomic.rs:484-543`) admitting one more validated vote: the
    duplicate-vote reject (`atomic.rs:510-512`) and the participant-bound check (`atomic.rs:505-507`)
    mean each of the `n` participants contributes at most one vote, so `yes + no ≤ n` is the standing
    invariant. The Ed25519 signature verification (`atomic.rs:521-532`) is the named crypto premise:
    here a cast vote is one that PASSED verification — we do not fake the signature scheme.
  * The `Decision` type and `CoordinatorState` lifecycle (`atomic.rs:253-261`, `:305-327`):
    `Idle → Proposing → {Committed, Aborted}`, the terminal states being mutually exclusive.

## Safety properties PROVED (the 2PC agreement the running vote count enforces)

  1. **NO CONFLICTING DECISION** (`evaluate_not_commit_and_abort`): on a well-formed tally
     (`yes + no ≤ n`, `0 < threshold ≤ n` — the `propose` guards `atomic.rs:439-444`), `evaluate`
     never yields BOTH a Commit-able and an Abort-able verdict — Commit and Abort are mutually
     exclusive. This is THE 2PC safety: the coordinator cannot tell some participants "commit" and
     others "abort"; every honest participant that recomputes `evaluate_votes` on the same QC reaches
     the SAME terminal decision. Proven from `yes ≥ threshold` and `no > n - threshold` being jointly
     impossible when `yes + no ≤ n`.
  2. **COMMIT ⇒ THRESHOLD MET** (`commit_needs_threshold`): `evaluate = Commit` implies `yes ≥
     threshold` — the QC the `commit()` path (`atomic.rs:565-572`) re-checks really has a threshold
     of Yes voters. No commit without a real quorum.
  3. **ABORT ⇒ THRESHOLD UNREACHABLE** (`abort_is_irrevocable` / `abort_no_late_commit`): once
     `no > n - threshold`, even if EVERY remaining (un-voted) participant later votes Yes, the Yes
     count can never reach `threshold` — the abort is sound and irreversible. This is the liveness-
     safety bridge `atomic.rs:773`'s comment asserts ("threshold can never be reached"); we PROVE it:
     the max achievable Yes is `n - no < threshold`.
  4. **DECISION MONOTONICITY** (`commit_stable_under_more_yes`, `decision_total`): a Commit stays a
     Commit as more Yes votes arrive (Yes count only grows); and `evaluate` is total — exactly one of
     Commit/Abort/Pending, never undefined. (The running code returns `Decision::Pending` until a
     terminal verdict, then transitions state once — `receive_vote` `atomic.rs:537-542`.)
  5. **UNANIMOUS THRESHOLD = TRUE ALL-OR-NONE** (`unanimous_commit_iff_all_yes`): when
     `threshold = n` (the EntangledJoint setting, `entangled_diff.rs:283` "unanimous threshold: all 3
     must vote Yes"), Commit holds iff all `n` voted Yes, and a single No forces Abort — the decision
     layer's witness that the all-or-none fold is gated by genuine unanimity. This is the precise
     bridge to `EntangledJoint.jointApplyAll` (commit the forest exactly when the 2PC commits).

## Connection to the running code + to EntangledJoint

`evaluate` is `evaluate_votes` transcribed; the Rust differential (`coord/src/coord_diff.rs`) runs the
GENUINE `atomic::Coordinator` (`propose`/`receive_vote` with real Ed25519 votes) over N = 3 scenarios
and asserts its emitted `Decision` agrees, vote-for-vote, with this Lean `evaluate`. The bridge to
`EntangledJoint`: the 2PC `Decision::Commit` is exactly the precondition under which
`EntangledJoint.jointApplyAll` is invoked to apply the forest — this module is the *gate*, that one
is the *effect*. Together they cover the whole Layer-2 atomic turn (decision + application).

## Scope

The Ed25519 vote-signature verification is the named crypto assumption (a cast vote = a verified
vote); we do not re-derive signature unforgeability. We model the *counting* `evaluate_votes` does on
verified votes, which is what the safety reduces to. No `sorry`/`:=True`/`native_decide`.
`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}). No executor import.
-/
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Coord.TwoPhaseCommit

/-! ## 1. The `Decision` and the vote `Tally`. -/

/-- The 2PC voting outcome (`atomic.rs::Decision`, `atomic.rs:253-261`). -/
inductive Decision where
  /-- Enough Yes votes: threshold reached, proceed to commit (`atomic.rs:255`). -/
  | commit
  /-- Too many No votes: threshold impossible, abort (`atomic.rs:257`). -/
  | abort
  /-- Still waiting for more votes (`atomic.rs:259`). -/
  | pending
  deriving DecidableEq, Repr

/-- The vote bag the coordinator accumulates (`CoordinatorState::Proposing.votes`,
`atomic.rs:310-316`), projected to its SAFETY content: how many Yes, how many No, the participant
count `n`, and the commit `threshold`. -/
structure Tally where
  /-- Number of Yes votes collected so far. -/
  yes       : Nat
  /-- Number of No votes collected so far. -/
  no        : Nat
  /-- Total participant count (`forest.participants.len()`, `atomic.rs:767`). -/
  n         : Nat
  /-- Minimum Yes votes required to commit (`Coordinator.threshold`, `atomic.rs:363`). -/
  threshold : Nat
  deriving Repr

/-- **Well-formed tally** — the invariants `propose`/`receive_vote` maintain:
each of the `n` participants votes at most once so `yes + no ≤ n` (`atomic.rs:505-512`), and the
threshold is a valid quorum `0 < threshold ≤ n` (`atomic.rs:439-444` rejects `threshold = 0` or
`threshold > participants.len()`). -/
structure Tally.wf (t : Tally) : Prop where
  /-- At most one vote per participant: Yes+No never exceeds the participant count. -/
  votes_le_n  : t.yes + t.no ≤ t.n
  /-- A valid quorum threshold (the `propose` guard). -/
  thr_pos     : 0 < t.threshold
  /-- Threshold cannot exceed the participant count (the `propose` guard). -/
  thr_le_n    : t.threshold ≤ t.n

/-! ## 2. `evaluate` — the real `evaluate_votes` (`atomic.rs:761-779`), byte-for-byte. -/

/-- **`evaluate` — `Coordinator::evaluate_votes` (`atomic.rs:767-778`).**
`if yes ≥ threshold then Commit else if no > n - threshold then Abort else Pending`. The middle
clause is the genuine "too many No votes — threshold can never be reached" abort. -/
def evaluate (t : Tally) : Decision :=
  if t.threshold ≤ t.yes then Decision.commit
  else if t.n - t.threshold < t.no then Decision.abort
  else Decision.pending

/-- `castYes` — admit one more (verified, non-duplicate) Yes vote (`receive_vote` Yes arm,
`atomic.rs:522-526` then `:534` insert). -/
def Tally.castYes (t : Tally) : Tally := { t with yes := t.yes + 1 }

/-- `castNo` — admit one more (verified, non-duplicate) No vote (`receive_vote` No arm). -/
def Tally.castNo (t : Tally) : Tally := { t with no := t.no + 1 }

/-! ## 3. NO CONFLICTING DECISION — the core 2PC agreement safety. -/

/-- **`evaluate_not_commit_and_abort` — NO CONFLICTING DECISION.** On a well-formed tally,
the Commit condition (`yes ≥ threshold`) and the Abort condition (`no > n - threshold`) are NEVER
both true. Hence `evaluate` yields a single, unambiguous verdict — the coordinator cannot tell one
participant "commit" and another "abort". This is the heart of 2PC safety: every honest replayer of
`evaluate_votes` on the same QC reaches the SAME decision. -/
theorem evaluate_not_commit_and_abort (t : Tally) (hwf : t.wf) :
    ¬ (t.threshold ≤ t.yes ∧ t.n - t.threshold < t.no) := by
  rintro ⟨hyes, hno⟩
  -- yes ≥ threshold AND no > n - threshold ⇒ yes + no > threshold + (n - threshold) = n,
  -- contradicting yes + no ≤ n (with threshold ≤ n so n - threshold + threshold = n).
  have h1 := hwf.votes_le_n
  have h2 := hwf.thr_le_n
  omega

/-- **`evaluate_commit_xor_abort` — the verdict is Commit XOR Abort XOR Pending, exclusively
.** A direct corollary: if `evaluate t = commit` then it is NOT `abort`, and vice versa.
`evaluate` is a function so this is definitional, but we record the *semantic* exclusivity: the two
TERMINAL decisions never coexist as available verdicts. -/
theorem commit_excludes_abort (t : Tally)
    (hc : evaluate t = Decision.commit) : evaluate t ≠ Decision.abort := by
  rw [hc]; decide

/-! ## 4. COMMIT ⇒ threshold met;  ABORT ⇒ threshold unreachable. -/

/-- **`commit_needs_threshold`.** `evaluate t = Commit` implies `yes ≥ threshold`: the
committing QC has at least `threshold` Yes voters (what `commit()` re-checks,
`atomic.rs:565-572`). No commit without a real quorum. -/
theorem commit_needs_threshold (t : Tally) (h : evaluate t = Decision.commit) :
    t.threshold ≤ t.yes := by
  unfold evaluate at h
  by_cases hc : t.threshold ≤ t.yes
  · exact hc
  · rw [if_neg hc] at h
    by_cases hd : t.n - t.threshold < t.no <;> simp [hd] at h

/-- **`abort_needs_too_many_no`.** `evaluate t = Abort` implies the No count already
exceeds `n - threshold` (and the threshold was not yet met). The abort fires only on a genuine
"threshold unreachable" condition. -/
theorem abort_needs_too_many_no (t : Tally) (h : evaluate t = Decision.abort) :
    t.n - t.threshold < t.no ∧ ¬ t.threshold ≤ t.yes := by
  unfold evaluate at h
  by_cases hc : t.threshold ≤ t.yes
  · rw [if_pos hc] at h; exact absurd h (by decide)
  · rw [if_neg hc] at h
    by_cases hd : t.n - t.threshold < t.no
    · exact ⟨hd, hc⟩
    · rw [if_neg hd] at h; exact absurd h (by decide)

/-- **`abort_no_late_commit` — ABORT IS SOUND / IRREVOCABLE.** Once the abort condition
holds (`no > n - threshold`) on a well-formed tally, the Yes count can NEVER reach `threshold` even
if every remaining un-voted participant votes Yes: the maximum achievable Yes is `n - no`, and
`n - no < threshold`. So aborting is safe — no later QC can form. This PROVES `atomic.rs:773`'s
comment ("threshold can never be reached"). -/
theorem abort_no_late_commit (t : Tally) (hwf : t.wf) (hno : t.n - t.threshold < t.no) :
    t.n - t.no < t.threshold := by
  have h1 := hwf.votes_le_n
  have h2 := hwf.thr_le_n
  omega

/-- **`abort_max_yes_below_threshold` — even all-remaining-Yes stays below threshold.**
The strongest form: if the current No count triggers abort, then `yes + (unvoted) < threshold` where
`unvoted = n - yes - no` is every participant who has not yet voted. So no admissible future vote
stream can flip the decision to Commit. -/
theorem abort_max_yes_below_threshold (t : Tally) (hwf : t.wf)
    (hno : t.n - t.threshold < t.no) :
    t.yes + (t.n - t.yes - t.no) < t.threshold := by
  have h1 := hwf.votes_le_n
  have h2 := hwf.thr_le_n
  omega

/-! ## 5. DECISION MONOTONICITY + totality. -/

/-- **`commit_stable_under_more_yes`.** If a tally already commits, casting another Yes vote
keeps it committing — a reached commit decision is stable as more Yes votes arrive (the Yes count
only grows). The coordinator never un-commits. -/
theorem commit_stable_under_more_yes (t : Tally) (h : evaluate t = Decision.commit) :
    evaluate t.castYes = Decision.commit := by
  have hthr : t.threshold ≤ t.yes := commit_needs_threshold t h
  unfold evaluate Tally.castYes
  simp only
  rw [if_pos (by omega)]

/-- **`decision_total`.** `evaluate` always returns exactly one of the three decisions —
it is total and never gets stuck. (The running `receive_vote` returns `Some(decision)` on a terminal
verdict and `None` (Pending) otherwise — `atomic.rs:537-542`.) -/
theorem decision_total (t : Tally) :
    evaluate t = Decision.commit ∨ evaluate t = Decision.abort ∨ evaluate t = Decision.pending := by
  unfold evaluate
  by_cases hc : t.threshold ≤ t.yes
  · left; rw [if_pos hc]
  · rw [if_neg hc]
    by_cases hd : t.n - t.threshold < t.no
    · right; left; rw [if_pos hd]
    · right; right; rw [if_neg hd]

/-! ## 6. UNANIMOUS THRESHOLD = TRUE ALL-OR-NONE (bridge to EntangledJoint). -/

/-- **`unanimous_commit_iff_all_yes`.** With `threshold = n` (the EntangledJoint /
`entangled_diff.rs:283` setting), Commit holds iff ALL `n` participants voted Yes. So the 2PC commit
gate IS unanimity — exactly the condition under which `EntangledJoint.jointApplyAll` applies the
whole forest all-or-none. -/
theorem unanimous_commit_iff_all_yes (t : Tally) (hwf : t.wf) (huni : t.threshold = t.n) :
    evaluate t = Decision.commit ↔ t.yes = t.n := by
  constructor
  · intro h
    have := commit_needs_threshold t h
    have hle := hwf.votes_le_n
    omega
  · intro h
    unfold evaluate
    rw [if_pos (by omega)]

/-- **`unanimous_one_no_aborts`.** With `threshold = n`, a SINGLE No vote (and the rest
not-yet-Yes) makes the threshold unreachable — the decision can only be Abort or Pending, NEVER
Commit. So under unanimity any dissent kills the joint turn: the all-or-none of EntangledJoint at the
decision layer. -/
theorem unanimous_one_no_blocks_commit (t : Tally) (hwf : t.wf) (huni : t.threshold = t.n)
    (hno : 0 < t.no) : evaluate t ≠ Decision.commit := by
  intro h
  have hyes := commit_needs_threshold t h
  have hle := hwf.votes_le_n
  omega

/-! ## 7. It RUNS — N = 3 unanimous 2PC (mirroring `entangled_diff.rs` / `atomic.rs` tests). -/

/-- A 3-participant unanimous proposal: `threshold = n = 3`. -/
def t3 (yes no : Nat) : Tally := { yes := yes, no := no, n := 3, threshold := 3 }

-- COMMIT path: all 3 vote Yes ⇒ Commit (the `diff_atomic_commit_all` scenario).
#guard evaluate (t3 3 0) == Decision.commit
-- ABORT path: 2 Yes, 1 No ⇒ threshold (3) unreachable ⇒ Abort (the `diff_atomic_abort` scenario).
#guard evaluate (t3 2 1) == Decision.abort
-- PENDING: 2 Yes, 0 No so far ⇒ still waiting for the 3rd.
#guard evaluate (t3 2 0) == Decision.pending
-- A single No, nothing else yet ⇒ already unreachable (n - threshold = 0 < 1 No) ⇒ Abort.
#guard evaluate (t3 0 1) == Decision.abort
-- Non-unanimous threshold 2-of-3: 2 Yes ⇒ Commit even with a No outstanding.
#guard evaluate { yes := 2, no := 1, n := 3, threshold := 2 } == Decision.commit
-- 2-of-3, 1 Yes 1 No ⇒ still Pending (the 3rd could be the 2nd Yes).
#guard evaluate { yes := 1, no := 1, n := 3, threshold := 2 } == Decision.pending
-- 2-of-3, 2 No ⇒ threshold (2) unreachable (only 1 voter left) ⇒ Abort.
#guard evaluate { yes := 0, no := 2, n := 3, threshold := 2 } == Decision.abort

/-! ## 8. Axiom-hygiene tripwires. -/

#assert_axioms evaluate_not_commit_and_abort
#assert_axioms commit_excludes_abort
#assert_axioms commit_needs_threshold
#assert_axioms abort_needs_too_many_no
#assert_axioms abort_no_late_commit
#assert_axioms abort_max_yes_below_threshold
#assert_axioms commit_stable_under_more_yes
#assert_axioms decision_total
#assert_axioms unanimous_commit_iff_all_yes
#assert_axioms unanimous_one_no_blocks_commit

end Dregg2.Coord.TwoPhaseCommit
