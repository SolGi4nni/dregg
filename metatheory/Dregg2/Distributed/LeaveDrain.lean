/-
# LeaveDrain — D7: the drain rule, as an obligation on the SURVIVORS

**This module is the AUTHORED CONSENSUS RULE for what must happen to a departing member's
outstanding finalization votes at the moment its `Leave` installs.** The Rust side
(`node/src/finalization_votes.rs::VoteCollector::retire_departed_votes`, called from
`reconfigure`) is a transcription of `drainTally` below. `ConfigBoundary.lean` is its
sibling: that module decides *whether a roster step may install at all*, this one decides
*what the install does to work already in flight*.

Design source: `docs/reference/READING-RECONFIGURATION-2026-08-08.md` §2.2 and D7.

## The impossibility this is designed AROUND, not against

DBRB App. A.6 **Theorem 81 (Strong Validity Impossibility)** and **Theorem 82 (Strong
Totality Impossibility)** prove — in a crash-only model with at most one failure, strictly
weaker than ours — that no algorithm can promise a departing participant that what it
broadcast is delivered. So a drain rule of the form *"the leaver's outstanding work is
guaranteed to land"* is **not implementable**, and nothing here states one. What is stated
instead, in three parts:

1. **An obligation on the survivors** (`drainTally`): at the install, every vote cast by a
   departing member is RETIRED from any tally that has not already crossed. The survivors
   must re-vote to carry such a block; the leaver's vote will never carry it for them.
2. **What is NOT retracted** (`drain_preserves_pinned`): a block that had already crossed
   under the old configuration keeps its tally and its pin, so it stays assemblable against
   the old snapshot forever. Retirement is not retroactive.
3. **A SIGNAL, not a delivery guarantee** (SKM17 §3: an operator *"can safely switch `s` off
   immediately once `ChangeConfig({−s})` returns"*). `departureIndex` is that signal: the
   install position is a function of the committed prefix alone (`departureIndex_immutable`),
   so an honest leaver derives it rather than being told it, and every honest survivor
   derives the same one.

## The defect this closes, stated as the theorem that FAILS without it

The deployed tally counts DISTINCT RECORDED SIGNERS (`VoteCollector::record`'s
`signers.len()`, and `marshal_quorum_wire`'s entry list) against the LIVE threshold, while
`assembled_quorum` looks each signer up in the GOVERNING configuration's key map and drops
anyone missing. `reconfigure` swapped the committee and never pruned the tally. So after a
`Leave`, a block could cross the NEW (smaller) threshold on a tally that still contained the
DEPARTED member's vote — and then assemble to nothing:

* `straddle_crosses_without_drain` — the crossing happens, and
* `straddle_unassemblable_without_drain` — the assembled quorum is empty.

That is the reading doc §5.3 defect ("one node has it final, another cannot reconstruct that
it ever was") surviving in the LEAVE direction past the `config_seq` pin that closed the join
direction, and it is a same-configuration-delivery violation in DZ §III.E's exact sense: one
quorum, two configurations. `drain_closes_the_straddle` is the same instance with the rule
applied.

## ⚠ WHAT THIS RULE DOES NOT COVER — the BLOCK layer, read at source and named here

This module drains the VOTE layer. There is a second half it does not touch, and stating it inside
the rule is the point: a drain rule whose scope is only in the commit message is a scope nobody
re-reads.

`blocklace/src/ordering.rs::order_over_anchor_chain` filters every anchor segment by
`participant_set.contains(&block.creator)` — against the **LIVE** roster, the one
`poll_finalized_blocks` recomputes τ with on each poll. So a `Leave` removes not only the member's
future authority but **every block it ever authored** from τ's recomputed output, including blocks
that were already ordered. That is not a drain hazard this rule can close, and it is not one the
step bound can refuse either: the correct predicate is *"the creator was a participant at the block's
own wave"*, which needs the roster-as-of-each-wave re-anchoring — the D3 prerequisite named in
`node/src/blocklace_sync.rs::apply_passed_proposal` ("τ itself still reads the LIVE roster … not the
roster-as-of-each-wave") and gated behind the append-only floor over the committed order that the
reading doc's D3 says we do not have.

Until that lands, the honest statement of a leave's scope is: **a departing member's VOTES are
retired soundly and its already-crossed quorums are preserved; its BLOCKS are at the mercy of a live
roster read.** Read at source on 2026-08-09; not measured on a running federation.

Pure, computable, `decide`-able. `#assert_axioms`-clean.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Dregg2.Tactics
import Dregg2.Distributed.QuorumThreshold
import Dregg2.Distributed.ConfigBoundary

namespace Dregg2.Distributed.LeaveDrain

-- The tally lives over two type parameters and most theorems need only one of the two
-- `DecidableEq`s; the linter's suggestion (a per-theorem `omit`) would put noise on almost
-- every declaration to say nothing.
set_option linter.unusedSectionVars false

open Dregg2.Distributed.QuorumThreshold (supermajorityThreshold)
open Dregg2.Distributed.ConfigBoundary (faultBudget stepAllowed classifyStep StepVerdict)

/-! ## The objects

A **tally** is what `VoteCollector.votes[block]` holds: one entry per DISTINCT signer
(first-write-wins in the Rust, so duplicates never arrive), each naming the attested root
that signer signed. A **configuration** is a roster with the threshold derived from it —
never an independent scalar (reading doc §5.2: every construction in the cluster indexes the
threshold by the configuration; none uses an unindexed one). -/

/-- One recorded vote: a signer and the root it attested. -/
structure Vote (κ ρ : Type*) where
  voter : κ
  root : ρ
  deriving DecidableEq, Repr

/-- A block's deduped tally, in recording order. -/
abbrev Tally (κ ρ : Type*) := List (Vote κ ρ)

/-- An installed configuration: the roster, and the threshold derived from it. -/
structure Config (κ : Type*) [DecidableEq κ] where
  roster : Finset κ

variable {κ ρ : Type*} [DecidableEq κ] [DecidableEq ρ]

/-- The configuration's quorum bar — `⌊2n/3⌋+1` over its OWN roster. Never a free scalar. -/
def Config.threshold (c : Config κ) : Nat := supermajorityThreshold c.roster.card

/-- How many distinct signers in `t` attested `r`. (The Rust tally is already deduped by
signer, so a plain count is the distinct count.) -/
def rootSupport (t : Tally κ ρ) (r : ρ) : Nat := (t.filter (fun v => v.root = r)).length

/-- **The deployed counting rule**: some root is supported by at least `thr` RECORDED
signers — no roster re-check. This is `record`'s `distinct_votes >= quorum_threshold` and
`marshal_quorum_wire`'s `n=<live committee>;V=<every recorded signer>`. Modelled as it IS,
because the whole point is that it disagrees with `assemblableIn` across an undrained
boundary. -/
def crossesAt (thr : Nat) (t : Tally κ ρ) (r : ρ) : Bool := decide (thr ≤ rootSupport t r)

/-- **The assembly rule**: `assembled_quorum` keeps only signers the GOVERNING
configuration holds a key for, then requires the governing threshold on one root. -/
def assemblableIn (c : Config κ) (t : Tally κ ρ) (r : ρ) : Bool :=
  decide (c.threshold ≤ rootSupport (t.filter (fun v => v.voter ∈ c.roster)) r)

/-! ## The drain

`departed old new` is the leave's change-set: exactly the members the install removes. For a
JOIN it is empty, and `drainTally` is then the identity (`drain_join_is_identity`) — one rule
for both directions, with the leave direction the only one that does anything. -/

/-- The members this install removes. (`RosterDelta.leaves` of `ConfigBoundary`, computed
from the two rosters so it cannot disagree with them.) -/
def departed (old new : Config κ) : Finset κ := old.roster \ new.roster

/-- **`drainTally`** — the rule, byte-for-byte what the Rust transcription does:

* a tally that has ALREADY CROSSED (`pinned = true`) is returned UNTOUCHED — its quorum is a
  fact about the old configuration, assembled against the old snapshot, and retracting it
  would make finality lie backwards in time;
* otherwise every departing member's vote is RETIRED, so no future crossing can count it.

There is no third case and nothing is clamped. -/
def drainTally (old new : Config κ) (pinned : Bool) (t : Tally κ ρ) : Tally κ ρ :=
  if pinned then t else t.filter (fun v => v.voter ∉ departed old new)

/-- The named outcomes, one per branch of `drainTally`. The Rust `DrainOutcome` mirrors
these; `dropped` is the count the survivors must make up by re-voting. -/
inductive DrainVerdict where
  /-- The block had crossed under the old configuration: pinned, untouched, still
  assemblable against the old snapshot. -/
  | pinned
  /-- The block had not crossed: `dropped` departing votes were retired from its tally. -/
  | retired (dropped : Nat)
  deriving DecidableEq, Repr

/-- The total classification. Every block lands on exactly one verdict. -/
def classifyDrain (old new : Config κ) (pinned : Bool) (t : Tally κ ρ) : DrainVerdict :=
  if pinned then .pinned
  else .retired ((t.filter (fun v => v.voter ∈ departed old new)).length)

/-- Verdict totality: a block is pinned or retired, never reinterpreted. -/
theorem classifyDrain_total (old new : Config κ) (pinned : Bool) (t : Tally κ ρ) :
    classifyDrain old new pinned t = .pinned
      ∨ ∃ k, classifyDrain old new pinned t = .retired k := by
  unfold classifyDrain; split <;> simp

/-- A filter and its complement partition a list's length. (Stated here because the drain's
verdict count and the drain's own mutation must be the SAME number, not two computations that
could drift.) -/
private theorem length_filter_add_not {α : Type*} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun a => !p a)).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => cases hp : p a <;> simp [hp] <;> omega

/-- The verdict and the transform agree: `retired k` means exactly `k` votes left the tally —
the count is not an independently-computed number that could drift from the mutation. -/
theorem classifyDrain_retired_counts (old new : Config κ) (t : Tally κ ρ) :
    ∃ k, classifyDrain old new false t = .retired k
      ∧ k + (drainTally old new false t).length = t.length := by
  refine ⟨(t.filter (fun v => v.voter ∈ departed old new)).length, by unfold classifyDrain; simp,
    ?_⟩
  unfold drainTally
  simp only [if_neg (by simp : ¬ (false = true)), decide_not]
  exact length_filter_add_not _ t

/-! ## What the drain guarantees the SURVIVORS -/

/-- A drained (unpinned) tally holds no departing member's vote. -/
theorem drain_removes_departed {old new : Config κ} {t : Tally κ ρ} {v : Vote κ ρ}
    (hv : v ∈ drainTally old new false t) : v.voter ∉ departed old new := by
  unfold drainTally at hv
  simp only [if_neg (by simp : ¬ (false = true)), List.mem_filter, decide_eq_true_eq] at hv
  exact hv.2

/-- ⚑ **The keystone.** `record` admits a vote only from a member of the configuration live
at recording time, so every recorded voter lies in the OLD roster. After the drain, every
remaining voter lies in the NEW roster — hence any post-boundary crossing is a quorum of the
new configuration ALONE. This is DZ §III.E's same-configuration delivery at the vote layer:
one quorum never straddles two configurations. -/
theorem drained_voters_in_new_roster {old new : Config κ} {t : Tally κ ρ}
    (hold : ∀ v ∈ t, v.voter ∈ old.roster) {v : Vote κ ρ}
    (hv : v ∈ drainTally old new false t) : v.voter ∈ new.roster := by
  have hnd := drain_removes_departed hv
  have hmem : v ∈ t := by
    unfold drainTally at hv
    simp only [if_neg (by simp : ¬ (false = true)), List.mem_filter] at hv
    exact hv.1
  have hin := hold v hmem
  unfold departed at hnd
  simp only [Finset.mem_sdiff, not_and, Decidable.not_not] at hnd
  exact hnd hin

/-- ⚑ **The deployed rule and the sound rule AGREE on a drained tally.** The whole content of
the defect is that they disagree on an undrained one: `crossesAt` counts every recorded
signer, `assemblableIn` counts only signers the governing configuration knows. After the
drain the two populations coincide, so a crossing is an assembly. -/
theorem drained_crossing_is_assemblable {old new : Config κ} {t : Tally κ ρ} {r : ρ}
    (hold : ∀ v ∈ t, v.voter ∈ old.roster)
    (h : crossesAt new.threshold (drainTally old new false t) r = true) :
    assemblableIn new (drainTally old new false t) r = true := by
  unfold crossesAt at h
  unfold assemblableIn
  simp only [decide_eq_true_eq] at h ⊢
  have hfil : (drainTally old new false t).filter (fun v => v.voter ∈ new.roster)
      = drainTally old new false t :=
    List.filter_eq_self.mpr (fun v hv => by
      simpa using drained_voters_in_new_roster hold hv)
  rw [hfil]
  exact h

/-- Nothing is retracted: a pinned (already-crossed) tally survives the boundary intact, so
`assembled_quorum` still assembles it against the OLD configuration's snapshot. -/
theorem drain_preserves_pinned (old new : Config κ) (t : Tally κ ρ) :
    drainTally old new true t = t := by
  unfold drainTally; simp

/-- A join drains nothing — the same rule, inert in the direction where no member leaves. -/
theorem drain_join_is_identity {old new : Config κ} (h : old.roster ⊆ new.roster)
    (pinned : Bool) (t : Tally κ ρ) : drainTally old new pinned t = t := by
  unfold drainTally departed
  cases pinned with
  | true => simp
  | false =>
      simp only [if_neg (by simp : ¬ (false = true))]
      refine List.filter_eq_self.mpr (fun v _ => ?_)
      simp only [decide_eq_true_eq, Finset.mem_sdiff, not_and, Decidable.not_not]
      exact fun hv => h hv

/-- Support is additive over concatenation (the survivors' votes append to the drained
tally). -/
theorem rootSupport_append (t u : Tally κ ρ) (r : ρ) :
    rootSupport (t ++ u) r = rootSupport t r + rootSupport u r := by
  unfold rootSupport; simp [List.filter_append]

/-- A block of votes all naming `r` supports `r` with its full cardinality. -/
theorem rootSupport_uniform (S : Finset κ) (r : ρ) :
    rootSupport (S.toList.map (fun k => (⟨k, r⟩ : Vote κ ρ))) r = S.card := by
  unfold rootSupport
  have h : (S.toList.map (fun k => (⟨k, r⟩ : Vote κ ρ))).filter (fun v => decide (v.root = r))
      = S.toList.map (fun k => (⟨k, r⟩ : Vote κ ρ)) := by
    refine List.filter_eq_self.mpr (fun v hv => ?_)
    simp only [List.mem_map] at hv
    obtain ⟨k, _, rfl⟩ := hv
    simp
  rw [h]
  simp

/-- **The obligation, discharged**: the drain never makes a block permanently uncrossable.
Any `T(n′)` survivors who agree on a root carry it, with no help from the departed. (The
witness is constructive — the survivors' own votes appended to the drained tally.) -/
theorem survivors_can_still_cross (old new : Config κ) (r : ρ) (t : Tally κ ρ)
    (S : Finset κ) (hS : new.threshold ≤ S.card) :
    crossesAt new.threshold
      (drainTally old new false t ++ S.toList.map (fun k => ⟨k, r⟩)) r = true := by
  unfold crossesAt
  simp only [decide_eq_true_eq, rootSupport_append, rootSupport_uniform]
  omega

/-! ## What the leaver is NOT promised — stated so it cannot be mistaken for a promise

DBRB Thms. 81/82 forbid the positive statement. These are the negative ones, and they are
theorems ABOUT OUR RULE rather than citations of theirs: the rule actively drops the
leaver's contribution, and the resulting gap is filled by the survivors or not at all. -/

section NotPromised

/-- Three members; `2` leaves. `T(3) = 3`, `T(2) = 2`. -/
def oldC : Config Nat := ⟨{0, 1, 2}⟩
def newC : Config Nat := ⟨{0, 1}⟩

/-- A block one vote short under the old configuration, where the short vote is the
LEAVER's: signer `0` and the departing signer `2` agree on root `7`. -/
def leaverTally : Tally Nat Nat := [⟨0, 7⟩, ⟨2, 7⟩]

theorem departed_is_the_leaver : departed oldC newC = {2} := by decide

/-- ⚑ **The leaver is promised nothing.** Its vote is dropped, and the block it voted for
does NOT cross afterwards — even though the surviving threshold `T(2) = 2` was met by the
recorded signer count `2` before the drain. The block is not lost: survivor `1` can carry it
(`survivors_can_still_cross`). But that is an obligation the SURVIVORS discharge; nothing
here delivers anything to the member that left. -/
theorem leaver_vote_is_dropped_and_block_does_not_cross :
    crossesAt newC.threshold leaverTally 7 = true
      ∧ crossesAt newC.threshold (drainTally oldC newC false leaverTally) 7 = false := by
  decide

/-- And the drop is *by name*: the verdict says exactly one vote was retired. -/
theorem leaver_drop_is_named :
    classifyDrain oldC newC false leaverTally = .retired 1 := by decide

end NotPromised

/-! ## Non-vacuity: the straddle the rule closes, both polarities

`n = 5 → 4`. `T(5) = 4`, `T(4) = 3`. A block carries two survivor votes and the departing
member's vote — three recorded signers on one root. -/

section Straddle

def cfg5 : Config Nat := ⟨{0, 1, 2, 3, 4}⟩
def cfg4 : Config Nat := ⟨{0, 1, 2, 3}⟩
/-- Survivors `0`, `1` and the DEPARTING member `4`, all on root `9`. -/
def straddleTally : Tally Nat Nat := [⟨0, 9⟩, ⟨1, 9⟩, ⟨4, 9⟩]

theorem straddle_thresholds : cfg5.threshold = 4 ∧ cfg4.threshold = 3 := by decide

/-- Under the OLD configuration the block had NOT crossed — `3 < T(5) = 4`. So it carries no
pin, and the boundary finds it in flight. -/
theorem straddle_had_not_crossed : crossesAt cfg5.threshold straddleTally 9 = false := by decide

/-- ⚑ **Half 1 of the defect**: WITHOUT the drain the block crosses the new, smaller
threshold — on a tally that still contains the departed member's vote. -/
theorem straddle_crosses_without_drain : crossesAt cfg4.threshold straddleTally 9 = true := by
  decide

/-- ⚑ **Half 2**: and it assembles to NOTHING, because the departed signer has no key in the
new configuration. Consensus-attested with no reconstructible quorum — the reading doc §5.3
shape, in the leave direction. -/
theorem straddle_unassemblable_without_drain :
    assemblableIn cfg4 straddleTally 9 = false := by decide

/-- ⚑ **The rule closes it**: after the drain the block does not cross, so the two rules
never disagree. The survivors owe it one more vote; nothing claims it is already final. -/
theorem drain_closes_the_straddle :
    crossesAt cfg4.threshold (drainTally cfg5 cfg4 false straddleTally) 9 = false
      ∧ assemblableIn cfg4 (drainTally cfg5 cfg4 false straddleTally) 9 = false := by decide

/-- The step itself is ALLOWED (`ConfigBoundary`): this is not a boundary the step bound would
have refused, so the drain is doing work the bound cannot do. Without this the whole section
could be vacuous — refused steps never reach the vote layer. -/
theorem straddle_step_is_allowed : stepAllowed 5 0 1 = true := by decide

/-- And the pinned direction is genuinely different at the same instance: a block that HAD
crossed under `cfg5` keeps its tally and assembles against `cfg5` afterwards. -/
def pinnedTally : Tally Nat Nat := [⟨0, 9⟩, ⟨1, 9⟩, ⟨2, 9⟩, ⟨4, 9⟩]

theorem pinned_survives_the_boundary :
    crossesAt cfg5.threshold pinnedTally 9 = true
      ∧ drainTally cfg5 cfg4 true pinnedTally = pinnedTally
      ∧ assemblableIn cfg5 (drainTally cfg5 cfg4 true pinnedTally) 9 = true := by decide

/-- ⚠ And the pin is load-bearing, not decoration: the SAME crossed tally judged against the
NEW configuration would not assemble (`4`'s key is gone and only three of its signers remain
— which is exactly the bar, so this is tight rather than lucky). Stated as the fact that the
governing configuration is a real choice. -/
theorem pinned_needs_its_own_configuration :
    assemblableIn cfg4 pinnedTally 9 = true
      ∧ rootSupport (pinnedTally.filter (fun v => v.voter ∈ cfg4.roster)) 9 = 3 := by decide

end Straddle

/-! ## D7's signal: the install position is DERIVED, never delivered

SKM17 §3 — the protocol owes the leaver a signal, not a delivery. Here the signal is a
function of the committed prefix, so the leaver computes it, every survivor computes the
same one, and no message has to reach the departing node for it to know it is out. -/

section Signal

variable {κ : Type*} [DecidableEq κ]

open Dregg2.Distributed.ConfigBoundary (RosterDelta rosterAt)

/-- **The signal**: is `d` out at committed position `k`? A pure function of the committed
prefix — nobody has to tell the leaver, and nobody can tell it something different from what
the survivors compute. -/
def outAt (g : Finset κ) (log : List (RosterDelta κ)) (d : κ) (k : Nat) : Prop :=
  d ∉ rosterAt g (log.take k)

/-- ⚑ **The signal is immutable under extension of the committed log.** A node that later
learns more of the order computes the SAME answer at every position it already had — so a
leaver's switch-off point and the survivors' install point can never drift apart, and neither
can two survivors'. This is what SKM17 §3 means by owing the leaver a *signal*: the departure
position is DERIVED from committed structure, not delivered, which is why DBRB Thms. 81/82
(nothing can be guaranteed *delivered* to a leaver) does not bite here. -/
theorem outAt_immutable (g : Finset κ) (log ext : List (RosterDelta κ)) (d : κ)
    (k : Nat) (hk : k ≤ log.length) :
    outAt g (log ++ ext) d k ↔ outAt g log d k := by
  unfold outAt
  rw [Dregg2.Distributed.ConfigBoundary.install_position_immutable g log ext k hk]

/-- The same fact read as agreement between two honest nodes: one holding the committed
prefix `log`, one holding `log ++ ext`, decide the leaver's status identically at every
position the shorter one has. -/
theorem departure_signal_agrees (g : Finset κ) (log ext : List (RosterDelta κ)) (d : κ) :
    ∀ k ≤ log.length, (outAt g log d k ↔ outAt g (log ++ ext) d k) :=
  fun k hk => (outAt_immutable g log ext d k hk).symm

end Signal

/-! ## The composed leave verdict: the step bound REFUSES, the drain then RUNS

A leave is two decisions in sequence and they are different in kind. `ConfigBoundary`'s is a
REFUSAL over committed structure — a pure function of roster shape, identical on every node.
The drain is NOT a refusal and must not be one: a tally is node-local (votes arrive by
gossip, not in the committed order), so conditioning the install on a local tally would make
a live read decide WHAT τ emits — the exact criterion `auto_evict_equivocator` failed (reading
doc D8). So the install is unconditional at its committed position, and the drain is what the
install DOES. -/

/-- The leave's two-stage outcome. A refused step never reaches the drain. -/
inductive LeaveVerdict where
  /-- The configuration step was refused by name; nothing installed, nothing drained. -/
  | refusedStep (why : StepVerdict)
  /-- The step installed; the drain ran with this verdict on the block in question. -/
  | installed (survivors : Nat) (drain : DrainVerdict)
  deriving Repr

/-- The composition. `classifyStep` decides admission; only an `install` reaches the drain. -/
def classifyLeave (n l : Nat) (old new : Config κ) (pinned : Bool) (t : Tally κ ρ) :
    LeaveVerdict :=
  match classifyStep n 0 l with
  | .install s => .installed s (classifyDrain old new pinned t)
  | v => .refusedStep v

/-- A refused step drains nothing — the refusal is total and prior. -/
theorem refused_step_drains_nothing (n l : Nat) (old new : Config κ) (pinned : Bool)
    (t : Tally κ ρ) (h : stepAllowed n 0 l = false) :
    ∃ v, classifyLeave n l old new pinned t = .refusedStep v := by
  unfold classifyLeave
  have hne : classifyStep n 0 l ≠ .install (n + 0 - l) := by
    intro hc
    rw [Dregg2.Distributed.ConfigBoundary.classifyStep_install_iff] at hc
    simp [hc] at h
  cases hc : classifyStep n 0 l with
  | install s =>
      exfalso
      have := Dregg2.Distributed.ConfigBoundary.classifyStep_total n 0 l
      rw [hc] at this
      rcases this with h' | h' | h' | h' | h' <;> simp_all
  | refuseLeavesExceedRoster => exact ⟨_, rfl⟩
  | refuseEmptySurvivors => exact ⟨_, rfl⟩
  | refuseIntersectionBound => exact ⟨_, rfl⟩
  | refuseRosterFloor => exact ⟨_, rfl⟩

/-- ⚑ The two named leave refusals the reading doc's non-contiguity trap turns on, composed
here so the leave path names them rather than a flat `l ≤ 2`: three leaves from `n = 7` fail
the counting bound, four leaves from `n = 7` pass it VACUOUSLY and are caught by the roster
floor instead. -/
theorem leave_refusals_are_named :
    classifyLeave (κ := Nat) (ρ := Nat) 7 3 oldC newC false []
        = .refusedStep .refuseIntersectionBound
      ∧ classifyLeave (κ := Nat) (ρ := Nat) 7 4 oldC newC false []
        = .refusedStep .refuseRosterFloor := by
  unfold classifyLeave
  constructor <;> · norm_num [Dregg2.Distributed.ConfigBoundary.classifyStep,
    Dregg2.Distributed.ConfigBoundary.faultBudget, supermajorityThreshold]

-- Axiom hygiene: every keystone rests only on the three kernel axioms.
#assert_axioms classifyDrain_total
#assert_axioms classifyDrain_retired_counts
#assert_axioms drain_removes_departed
#assert_axioms drained_voters_in_new_roster
#assert_axioms drained_crossing_is_assemblable
#assert_axioms drain_preserves_pinned
#assert_axioms drain_join_is_identity
#assert_axioms survivors_can_still_cross
#assert_axioms leaver_vote_is_dropped_and_block_does_not_cross
#assert_axioms straddle_crosses_without_drain
#assert_axioms straddle_unassemblable_without_drain
#assert_axioms drain_closes_the_straddle
#assert_axioms pinned_survives_the_boundary
#assert_axioms outAt_immutable
#assert_axioms departure_signal_agrees
#assert_axioms refused_step_drains_nothing
#assert_axioms leave_refusals_are_named

end Dregg2.Distributed.LeaveDrain
