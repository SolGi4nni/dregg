/-
# Black Box Reconstruction — recover the recorder's channel order by probing it

Substrate note: this is Lean-authored game semantics.  Nothing here is an AIR, a
constraint system or a gadget; Rust and TypeScript only dispatch the tables the
Lean emitter writes, they do not carry a second copy of the rules.

## ⚠ What this file used to be, and why it was not a game

The previous kernel asked the player to place five fragments in one order and
compared the finished sequence against `orderFromSeed`.  Three facts about it,
each measurable from the file itself:

* `orderForOffset` read ONE byte mod 5 and returned a cyclic rotation, so the
  instance space was **5 of the 120 permutations** — the seed picked a rotation,
  never a permutation.
* `MAX_TURNS = FRAGMENT_COUNT = 5` and every action placed one fragment, so a run
  was **exactly one attempt**.
* Nothing in `step` returned any observation.  The player learned **nothing**
  during a run.

Five instances, one attempt, zero feedback: a 1-in-5 coin flip with a permutation
proof attached.  The theorems below it were all true and none of them was about a
decision.  The information floor was undefined (an instance cannot be identified
with one answer class) and the execution floor was one lucky guess.

## What it is now

The recorder has five sequence positions and five recovered fragments.  A hidden
permutation says which fragment belongs at which position.  One action —
`probe slot fragment` — asks the recorder a single question:

    does this fragment belong at this position?

A **match** settles that position, and both the position and the fragment leave
play.  A **mismatch** costs the turn and eliminates that pair.  A run wins when
every position is settled, and loses by running out of probes.

`MAX_TURNS = 15` is not a taste: it is the exact worst case under optimal play
against an adversary answering any way still consistent with some permutation.
`five_positions_cost_exactly_fifteen_probes` proves the achievability half over
every one of the 120 instances; the matching lower bound is stated in
`docs`/the design gate (a cell of `K(5,5)` becomes forced only after four
eliminations in its row or column, and those eliminations vanish with the row and
column when the position settles, so each of the five positions costs 5, 4, 3, 2
and 1 probes: 15).  The mean over a uniform instance is 10.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Games.PathOfAngels.SeedDraw
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.BlackBoxReconstruction

open Dregg2.Games.PathOfAngels

/-- Positions in the recovered sequence, and fragments to place in them. -/
abbrev SLOT_COUNT : Nat := 5

/-- The exact worst case under optimal play; see the module docblock. -/
abbrev MAX_TURNS : Nat := 15

/-- Every permutation of five fragments is reachable: 5! = 120. -/
abbrev ORDER_SPACE : Nat := 120

abbrev Slot := Fin SLOT_COUNT
abbrev Fragment := Fin SLOT_COUNT
abbrev Probe := Slot × Fragment

def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by omega)⟩

def allSlots : List Slot := List.finRange SLOT_COUNT
def allFragments : List Fragment := List.finRange SLOT_COUNT

/-! ## The hidden order

The instance is a permutation, decoded from its Lehmer code.  Four CONSUMING
draws (`SeedDraw.drawBelow?`, bounds 5, 4, 3, 2) read disjoint prefixes of the
run seed, so the order is a function of four independent bytes and not of one
byte wearing four hats — the wound `SeedDraw` was written to close. -/

def lehmerDigits (seed : Fin ORDER_SPACE) : List Nat :=
  [seed.val / 24, (seed.val % 24) / 6, (seed.val % 6) / 2, seed.val % 2]

/-- The permutation a seed names, position 0 first.  Each digit selects from what
is left, so distinct Lehmer codes give distinct permutations. -/
def orderRow (seed : Fin ORDER_SPACE) : List Fragment :=
  let d := lehmerDigits seed
  let r0 : List Fragment := [0, 1, 2, 3, 4]
  let a := r0.getD (d.getD 0 0) 0
  let r1 := r0.filter (fun x => x != a)
  let b := r1.getD (d.getD 1 0) 0
  let r2 := r1.filter (fun x => x != b)
  let c := r2.getD (d.getD 2 0) 0
  let r3 := r2.filter (fun x => x != c)
  let e := r3.getD (d.getD 3 0) 0
  let r4 := r3.filter (fun x => x != e)
  [a, b, c, e, r4.getD 0 0]

/-- The fragment that belongs at `slot` under the order `seed` names. -/
def orderAt (seed : Fin ORDER_SPACE) (slot : Slot) : Fragment :=
  (orderRow seed).getD slot.val 0

def allOrderRows : List (List Fragment) :=
  (List.finRange ORDER_SPACE).map orderRow

theorem orderRow_length (seed : Fin ORDER_SPACE) :
    (orderRow seed).length = SLOT_COUNT := by
  simp [orderRow]

theorem orderRow_nodup : ∀ seed : Fin ORDER_SPACE, (orderRow seed).Nodup := by
  decide

theorem orderRow_perm : ∀ seed : Fin ORDER_SPACE, (orderRow seed).Perm allFragments := by
  decide

/-- The seed space names 120 DISTINCT orders.  Together with `orderRow_perm` and
the independent enumeration below, the instance space is exactly the symmetric
group on five fragments — no seed is drawn twice and none is unreachable. -/
theorem allOrderRows_nodup : allOrderRows.Nodup := by
  decide

theorem allOrderRows_length : allOrderRows.length = ORDER_SPACE := by
  simp [allOrderRows]

/-- Every candidate row of five fragments, enumerated INDEPENDENTLY of `orderRow`
so the coverage theorem below cannot be satisfied by the construction agreeing
with itself. -/
def candidateRows : List (List Fragment) :=
  (allFragments.flatMap fun a =>
    allFragments.flatMap fun b =>
      allFragments.flatMap fun c =>
        allFragments.flatMap fun d =>
          allFragments.map fun e => [a, b, c, d, e])

def permutationRows : List (List Fragment) :=
  candidateRows.filter (fun row => decide row.Nodup)

theorem candidateRows_length : candidateRows.length = 3125 := by
  simp [candidateRows, allFragments]
  rfl

/-- The image of the seed space is EXACTLY the set of permutations, measured
against the independently enumerated 5^5 candidate domain.

⚑ The evaluation moved out of the `Dregg2.FFI` closure (2026-08-08): a
`native_decide` here made every game-fixture regression a hard failure of every
Rust proving target. Statements stay as evaluation-free `check_* : Bool` defs;
each is pinned `= true` by `native_decide` + `#assert_compiled` in
`BlackBoxReconstructionFixtures.lean`, rooted in the `PathOfAngelsGuards`
library. Named residue: none — every evaluation moved.
(Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_order_space_is_exactly_the_permutations : Bool :=
  decide (permutationRows.length = ORDER_SPACE) &&
  permutationRows.all (fun row => decide (row ∈ allOrderRows))

/-! ## The hidden order comes from the run seed -/

def orderFromRunSeed? (runSeed : Digest32) : Option (Fin ORDER_SPACE) :=
  match SeedDraw.drawBelow? 5 (by decide) runSeed.bytes with
  | none => none
  | some (a, s1) =>
    match SeedDraw.drawBelow? 4 (by decide) s1 with
    | none => none
    | some (b, s2) =>
      match SeedDraw.drawBelow? 3 (by decide) s2 with
      | none => none
      | some (c, s3) =>
        match SeedDraw.drawBelow? 2 (by decide) s3 with
        | none => none
        | some (d, _) =>
          some ⟨24 * a.val + 6 * b.val + 2 * c.val + d.val, by
            have ha : a.val < 5 := a.isLt
            have hb : b.val < 4 := b.isLt
            have hc : c.val < 3 := c.isLt
            have hd : d.val < 2 := d.isLt
            show 24 * a.val + 6 * b.val + 2 * c.val + d.val < 120
            omega⟩

/-! ## Configuration, state and the probe -/

structure Config where
  order : Fin ORDER_SPACE
  mission : MissionSpec
  reward : Contribution
  reward_accepted : mission.acceptsContribution reward = true
  order_eq : some order = orderFromRunSeed? mission.runSeed

/-- What a run has asked so far.  The ANSWERS are not stored: a probe's answer is
`orderAt order slot == fragment`, so the settled positions are a function of
the transcript and the instance, and a transcript cannot claim a match it did not
receive. -/
structure State where
  probed : List Probe
  turns : Nat
deriving Repr, DecidableEq

def initialState : State := { probed := [], turns := 0 }

inductive Action where
  | probe (slot : Slot) (fragment : Fragment)
deriving Repr, DecidableEq

def Action.slot : Action → Slot
  | .probe slot _ => slot

def Action.fragment : Action → Fragment
  | .probe _ fragment => fragment

def Action.pair : Action → Probe
  | .probe slot fragment => (slot, fragment)

/-- A probe MATCHED iff it named the fragment that belongs at that position. -/
def hitB (order : Fin ORDER_SPACE) (p : Probe) : Bool :=
  orderAt order p.1 == p.2

/-- A position is settled once the run has probed its correct fragment. -/
def settledSlotB (order : Fin ORDER_SPACE) (s : State) (slot : Slot) : Bool :=
  decide ((slot, orderAt order slot) ∈ s.probed)

/-- A fragment is settled once the position it belongs to is settled. -/
def settledFragmentB (order : Fin ORDER_SPACE) (s : State) (fragment : Fragment) : Bool :=
  allSlots.any fun slot =>
    (orderAt order slot == fragment) && settledSlotB order s slot

def solvedB (order : Fin ORDER_SPACE) (s : State) : Bool :=
  allSlots.all (settledSlotB order s)

/-- Every refusal this kernel can produce.  The design gate checks that each of
these is REACHABLE; a declared reason that never fires is decoration. -/
inductive Refusal where
  | solved
  | turnLimit
  | repeatedProbe
  | settledSlot
  | settledFragment
deriving Repr, DecidableEq

/-- ⚑ **PRECEDENCE-ORDERED, and the descriptor's `refusals` array is this list.**
`refusal?` below is a chain of guards, so when two conditions hold at once the
EARLIER one is the reason reported.  That order is semantics a client renders, so
it is emitted rather than left to the reader — and `settled-slot` holds at every
`solved` state (a solved run has settled every slot), which is exactly why the
order cannot be dropped. -/
def allRefusals : List Refusal :=
  [.solved, .turnLimit, .repeatedProbe, .settledSlot, .settledFragment]

theorem allRefusals_complete (r : Refusal) : r ∈ allRefusals := by
  cases r <;> decide

def Refusal.tag : Refusal → String
  | .solved => "solved"
  | .turnLimit => "turn-limit"
  | .repeatedProbe => "repeated-probe"
  | .settledSlot => "settled-slot"
  | .settledFragment => "settled-fragment"

theorem refusal_tags_are_distinct :
    (allRefusals.map Refusal.tag).eraseDups = allRefusals.map Refusal.tag := by decide

def refusal? (order : Fin ORDER_SPACE) (s : State) : Action → Option Refusal
  | .probe slot fragment =>
      if solvedB order s then some .solved
      else if MAX_TURNS ≤ s.turns then some .turnLimit
      else if (slot, fragment) ∈ s.probed then some .repeatedProbe
      else if settledSlotB order s slot then some .settledSlot
      else if settledFragmentB order s fragment then some .settledFragment
      else none

/-- The authoritative partial transition.  Every refusal is fail-stop `none`, not
an accepted no-op. -/
def step (order : Fin ORDER_SPACE) (s : State) : Action → Option State
  | .probe slot fragment =>
      match refusal? order s (.probe slot fragment) with
      | some _ => none
      | none => some { probed := s.probed ++ [(slot, fragment)], turns := s.turns + 1 }

def replay (order : Fin ORDER_SPACE) : State → List Action → Option State
  | s, [] => some s
  | s, a :: as =>
      match step order s a with
      | none => none
      | some s' => replay order s' as

def remaining (s : State) : Nat := MAX_TURNS - s.turns

private def terminalOutput (cfg : Config) (s : State) : Option (Contribution × ArtifactRef) :=
  if solvedB cfg.order s then some (cfg.reward, cfg.mission.artifact) else none

/-! ## Transcript

At most fifteen probes, each a pair below five, so `5 * slot + fragment` is one
byte below 25.  Byte zero binds the length and bytes 1..15 bind the probes. -/

def probeCode (p : Probe) : Nat := SLOT_COUNT * p.1.val + p.2.val

def codeAt (actions : List Action) (i : Nat) : Nat :=
  match actions[i]? with
  | some action => probeCode action.pair
  | none => 255

def transcriptDigest (actions : List Action) : Digest32 where
  bytes := List.ofFn (fun i : Fin 32 =>
    if i.val = 0 then byte actions.length else byte (codeAt actions (i.val - 1)))
  length_eq := by simp

structure JudgeContext where
  actorRoot : Digest32
  playerKey : Digest32
  previousPlayerCounter : Nat

structure JudgedRun where
  finalState : State
  afterWorld : WorldState
  receipt : RunReceipt

def judge (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) : Option JudgedRun :=
  match replay cfg.order initialState actions with
  | none => none
  | some finalState =>
      match terminalOutput cfg finalState with
      | none => none
      | some (contribution, _artifact) =>
          match happlied : applyContribution cfg.mission contribution before with
          | none => none
          | some afterWorld =>
              some {
                finalState
                afterWorld
                receipt := {
                  mission := cfg.mission
                  federationId := cfg.mission.federationId
                  contentRoot := cfg.mission.contentRoot
                  activationDigest := cfg.mission.activationDigest
                  contentSession := cfg.mission.contentSession
                  contentEpoch := cfg.mission.epoch
                  actorRoot := ctx.actorRoot
                  playerKey := ctx.playerKey
                  previousPlayerCounter := ctx.previousPlayerCounter
                  playerCounter := ctx.previousPlayerCounter + 1
                  runSeed := cfg.mission.runSeed
                  preWorld := before
                  postWorld := afterWorld
                  contribution
                  transcriptDigest := transcriptDigest actions
                  federation_matches := rfl
                  content_root_matches := rfl
                  activation_matches := rfl
                  content_session_matches := rfl
                  content_epoch_matches := rfl
                  run_seed_matches := rfl
                  player_counter_advances := rfl
                  applied := happlied
                }
              }

/-! ## Transition and refusal theorems -/

theorem step_deterministic (order : Fin ORDER_SPACE) (s : State) (a : Action) {s₁ s₂ : State}
    (h₁ : step order s a = some s₁) (h₂ : step order s a = some s₂) : s₁ = s₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem step_refused_iff (order : Fin ORDER_SPACE) (s : State) (a : Action) :
    step order s a = none ↔ (refusal? order s a).isSome = true := by
  cases a with
  | probe slot fragment =>
      simp only [step]
      cases refusal? order s (.probe slot fragment) <;> simp

theorem step_eq_none_of_refused (order : Fin ORDER_SPACE) (s : State) (a : Action)
    (h : (refusal? order s a).isSome = true) : step order s a = none :=
  (step_refused_iff order s a).mpr h

/-- An accepted probe was inside the budget.  Stated separately because every
bound below reads it. -/
theorem refusal_none_turns_lt (order : Fin ORDER_SPACE) (s : State) (a : Action)
    (h : refusal? order s a = none) : s.turns < MAX_TURNS := by
  rcases Nat.lt_or_ge s.turns MAX_TURNS with hlt | hge
  · exact hlt
  · exfalso
    cases a with
    | probe slot fragment =>
        simp only [refusal?] at h
        split at h <;> simp_all

theorem step_some_turns (order : Fin ORDER_SPACE) (s : State) (a : Action) {s' : State}
    (h : step order s a = some s') : s'.turns = s.turns + 1 := by
  cases a with
  | probe slot fragment =>
      simp only [step] at h
      split at h
      · contradiction
      · simp only [Option.some.injEq] at h
        subst s'
        rfl

theorem step_some_probed (order : Fin ORDER_SPACE) (s : State) (slot : Slot) (fragment : Fragment)
    {s' : State} (h : step order s (.probe slot fragment) = some s') :
    s'.probed = s.probed ++ [(slot, fragment)] := by
  simp only [step] at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    subst s'
    rfl

theorem step_some_bound (order : Fin ORDER_SPACE) (s : State) (a : Action) {s' : State}
    (h : step order s a = some s') : s'.turns ≤ MAX_TURNS := by
  have ht := step_some_turns order s a h
  cases a with
  | probe slot fragment =>
      simp only [step] at h
      split at h
      · contradiction
      · rename_i hnone
        have hlt := refusal_none_turns_lt order s (.probe slot fragment) hnone
        omega

theorem remaining_strictly_decreases (order : Fin ORDER_SPACE) (s : State) (a : Action) {s' : State}
    (h : step order s a = some s') : remaining s' < remaining s := by
  have ht := step_some_turns order s a h
  have hb := step_some_bound order s a h
  simp only [remaining]
  omega

theorem solved_refuses (order : Fin ORDER_SPACE) (s : State) (a : Action)
    (h : solvedB order s = true) : step order s a = none := by
  apply step_eq_none_of_refused
  cases a with
  | probe slot fragment => simp only [refusal?, if_pos h, Option.isSome_some]

theorem exhausted_refuses (order : Fin ORDER_SPACE) (s : State) (a : Action)
    (h : MAX_TURNS ≤ s.turns) : step order s a = none := by
  apply step_eq_none_of_refused
  cases a with
  | probe slot fragment =>
      simp only [refusal?]
      split <;> simp_all

theorem repeated_probe_refused (order : Fin ORDER_SPACE) (s : State) (slot : Slot) (fragment : Fragment)
    (h : (slot, fragment) ∈ s.probed) : step order s (.probe slot fragment) = none := by
  apply step_eq_none_of_refused
  simp only [refusal?]
  repeat' split
  all_goals simp_all

theorem settled_slot_refused (order : Fin ORDER_SPACE) (s : State) (slot : Slot) (fragment : Fragment)
    (h : settledSlotB order s slot = true) :
    step order s (.probe slot fragment) = none := by
  apply step_eq_none_of_refused
  simp only [refusal?]
  repeat' split
  all_goals simp_all

theorem settled_fragment_refused (order : Fin ORDER_SPACE) (s : State) (slot : Slot) (fragment : Fragment)
    (h : settledFragmentB order s fragment = true) :
    step order s (.probe slot fragment) = none := by
  apply step_eq_none_of_refused
  simp only [refusal?]
  repeat' split
  all_goals simp_all

/-- An accepted probe never un-settles a position: the transcript only grows. -/
theorem step_settled_never_shrinks (order : Fin ORDER_SPACE) (s : State) (a : Action) (slot : Slot)
    {s' : State} (h : step order s a = some s')
    (hset : settledSlotB order s slot = true) :
    settledSlotB order s' slot = true := by
  cases a with
  | probe pslot pfragment =>
      have hp := step_some_probed order s pslot pfragment h
      simp only [settledSlotB, decide_eq_true_eq] at hset ⊢
      rw [hp]
      exact List.mem_append_left _ hset

theorem step_solved_never_unsolves (order : Fin ORDER_SPACE) (s : State) (a : Action) {s' : State}
    (h : step order s a = some s') (hsolved : solvedB order s = true) :
    solvedB order s' = true := by
  simp only [solvedB, List.all_eq_true] at hsolved ⊢
  intro slot hslot
  exact step_settled_never_shrinks order s a slot h (hsolved slot hslot)

/-! ## Replay -/

theorem replay_append (order : Fin ORDER_SPACE) (s : State) (xs ys : List Action) :
    replay order s (xs ++ ys) = (replay order s xs).bind (fun s' => replay order s' ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, replay]
      split <;> simp_all

theorem refused_prefix_refuses_replay (order : Fin ORDER_SPACE) (s : State) (a : Action)
    (as : List Action) (h : step order s a = none) : replay order s (a :: as) = none := by
  simp [replay, h]

theorem replay_some_turns (order : Fin ORDER_SPACE) (s : State) (actions : List Action)
    {s' : State} (h : replay order s actions = some s') :
    s'.turns = s.turns + actions.length := by
  induction actions generalizing s s' with
  | nil =>
      simp only [replay, Option.some.injEq] at h
      subst s'
      simp
  | cons a as ih =>
      simp only [replay] at h
      split at h
      · contradiction
      · rename_i next hstep
        have htail := ih (s := next) h
        have hturn := step_some_turns order s a hstep
        simp only [List.length_cons]
        rw [htail, hturn]
        omega

theorem replay_some_turn_bound (order : Fin ORDER_SPACE) (s : State) (actions : List Action)
    {s' : State} (hstart : s.turns ≤ MAX_TURNS) (h : replay order s actions = some s') :
    s'.turns ≤ MAX_TURNS := by
  induction actions generalizing s s' with
  | nil =>
      simp only [replay, Option.some.injEq] at h
      subst s'
      exact hstart
  | cons a as ih =>
      simp only [replay] at h
      split at h
      · contradiction
      · rename_i next hstep
        exact ih (s := next) (step_some_bound order s a hstep) h

/-- Exactly one pair joins the transcript per accepted probe. -/
theorem replay_probed_length (order : Fin ORDER_SPACE) (s : State) (actions : List Action)
    {s' : State} (h : replay order s actions = some s') :
    s'.probed.length = s.probed.length + actions.length := by
  induction actions generalizing s s' with
  | nil =>
      simp only [replay, Option.some.injEq] at h
      subst s'
      simp
  | cons a as ih =>
      simp only [replay] at h
      split at h
      · contradiction
      · rename_i next hstep
        have htail := ih (s := next) h
        cases a with
        | probe slot fragment =>
            have hp := step_some_probed order s slot fragment hstep
            rw [htail, hp]
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega

/-- ⚑ **The budget is enforced, not advisory.**  No accepted run exceeds fifteen
probes, which is what makes `MAX_TURNS` a way to lose rather than a suggestion. -/
theorem replay_initial_length_bounded (order : Fin ORDER_SPACE) (actions : List Action)
    {s : State} (h : replay order initialState actions = some s) :
    actions.length ≤ MAX_TURNS := by
  have hturns := replay_some_turns order initialState actions h
  have hbound := replay_some_turn_bound order initialState actions (by simp [initialState]) h
  simp only [initialState] at hturns
  omega

/-! ## Terminality -/

theorem terminalOutput_none_before_solution (cfg : Config) (s : State)
    (h : solvedB cfg.order s = false) : terminalOutput cfg s = none := by
  simp [terminalOutput, h]

theorem terminalOutput_is_mission_accepted (cfg : Config) (s : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg s = some out) :
    cfg.mission.acceptsContribution out.1 = true := by
  simp only [terminalOutput] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst out
    exact cfg.reward_accepted
  · contradiction

theorem terminalOutput_names_exact_beta_artifact (cfg : Config) (s : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg s = some out) :
    out.2 = cfg.mission.artifact := by
  simp only [terminalOutput] at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
  · contradiction

theorem terminalOutput_canonical (cfg : Config) (s : State)
    {contribution : Contribution} {artifact : ArtifactRef}
    (h : terminalOutput cfg s = some (contribution, artifact)) :
    terminalOutput cfg s = some (contribution, cfg.mission.artifact) := by
  have hart := terminalOutput_names_exact_beta_artifact cfg s h
  change artifact = cfg.mission.artifact at hart
  rw [hart] at h
  exact h

/-- ⚑ **A rewarded run has probed all five correct pairs.**  The reward gate is
the settled-position predicate and nothing else, so a transcript that never asked
the recorder the right questions cannot be paid. -/
theorem solved_probed_every_correct_pair (order : Fin ORDER_SPACE) (s : State)
    (h : solvedB order s = true) :
    ∀ slot : Slot, (slot, orderAt order slot) ∈ s.probed := by
  simp only [solvedB, List.all_eq_true] at h
  intro slot
  have hmem : slot ∈ allSlots := by simp [allSlots]
  have := h slot hmem
  simpa [settledSlotB] using this

/-- ⚑ **Five probes at minimum, and the budget is fifteen.**  With the pair list
carrying five distinct required entries, no accepted run of fewer than five
actions is ever rewarded. -/
theorem solved_needs_five_actions (order : Fin ORDER_SPACE) (actions : List Action)
    {s : State} (hreplay : replay order initialState actions = some s)
    (h : solvedB order s = true) : SLOT_COUNT ≤ actions.length := by
  have hpairs := solved_probed_every_correct_pair order s h
  -- the five required pairs are distinct, and every one of them was probed
  have hsub : (allSlots.map fun slot => (slot, orderAt order slot)) ⊆ s.probed := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨slot, _, rfl⟩ := hp
    exact hpairs slot
  have hnodup : (allSlots.map fun slot => (slot, orderAt order slot)).Nodup := by
    apply List.Nodup.map_on
    · intro x _ y _ hxy
      exact congrArg Prod.fst hxy
    · decide
  have hlen := (List.Nodup.subperm hnodup hsub).length_le
  simp only [List.length_map] at hlen
  have hall : allSlots.length = 5 := by simp [allSlots]
  rw [hall] at hlen
  have hprobed := replay_probed_length order initialState actions hreplay
  simp only [initialState, List.length_nil, Nat.zero_add] at hprobed
  show 5 ≤ actions.length
  omega

/-! ## Judge -/

theorem judge_some_sound (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    replay cfg.order initialState actions = some run.finalState ∧
    terminalOutput cfg run.finalState =
      some (run.receipt.contribution, cfg.mission.artifact) ∧
    applyContribution cfg.mission run.receipt.contribution before = some run.afterWorld ∧
    run.receipt.mission = cfg.mission ∧
    run.receipt.transcriptDigest = transcriptDigest actions := by
  unfold judge at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · simp only [Option.some.injEq] at h
        subst run
        refine ⟨by assumption, ?_, by assumption, rfl, rfl⟩
        apply terminalOutput_canonical
        assumption

theorem judge_final_state_solved (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    solvedB cfg.order run.finalState = true := by
  have hterminal := (judge_some_sound cfg before ctx actions h).2.1
  simp only [terminalOutput] at hterminal
  split at hterminal
  · assumption
  · contradiction

theorem judge_action_count_bounded (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    actions.length ≤ MAX_TURNS :=
  replay_initial_length_bounded cfg.order actions (judge_some_sound cfg before ctx actions h).1

theorem judge_receipt_binds_transcript (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
    run.receipt.transcriptDigest = transcriptDigest actions :=
  (judge_some_sound cfg before ctx actions h).2.2.2.2

/-- The played instance is the one the run seed derives; a judge cannot be run
against a board the seed does not name. -/
theorem judge_binds_run_seed (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    some cfg.order = orderFromRunSeed? run.receipt.runSeed := by
  have hs := judge_some_sound cfg before ctx actions h
  rw [run.receipt.run_seed_matches, hs.2.2.2.1]
  exact cfg.order_eq

/-! ## The budget is exactly the worst case

`MAX_TURNS` is a design claim and it has two halves.  The ACHIEVABILITY half is
proved here over every one of the 120 instances: the reference policy wins on all
of them and never spends more than fifteen probes.  It also ATTAINS fifteen on at
least one instance, so the budget is not slack.

The matching lower bound — that no policy does better than fifteen in the worst
case — is a statement about all strategies, not about this one; it is measured by
`scripts/poa-design-gate.py`, which searches the adversarial minimax exactly.  The
argument is short enough to record: in `K(5,5)` a cell becomes forced only once
four cells of its row or column are eliminated, and those eliminations vanish
together with the row and the column when the position settles, so the five
positions cost 5, 4, 3, 2 and 1 probes. -/

/-- One position of the reference sweep: try the still-unsettled fragments in
order and stop at the match. -/
def scanForSlot (order : Fin ORDER_SPACE) (remaining : List Fragment) (slot : Slot) :
    List Action × List Fragment :=
  let correct := orderAt order slot
  let tried := remaining.takeWhile (fun f => f != correct)
  ((tried ++ [correct]).map (Action.probe slot),
    remaining.filter (fun f => f != correct))

def scanActions (order : Fin ORDER_SPACE) : List Action :=
  (allSlots.foldl
    (fun acc slot =>
      let out := scanForSlot order acc.2 slot
      (acc.1 ++ out.1, out.2))
    (([] : List Action), allFragments)).1

def scanWinsB (order : Fin ORDER_SPACE) : Bool :=
  decide ((scanActions order).length ≤ MAX_TURNS) &&
  (match replay order initialState (scanActions order) with
   | none => false
   | some s => solvedB order s)

def scanWinsEverywhereB : Bool := (List.finRange ORDER_SPACE).all scanWinsB

def scanLengths : List Nat :=
  (List.finRange ORDER_SPACE).map (fun order => (scanActions order).length)

/-- ⚑ **Every instance is winnable inside the budget.**  Without this the game
could ship unplayable on some seeds — the design gate's `unwinnable-instance`
FAIL, proved by pin instead of measured after the fact.
(Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_five_positions_cost_exactly_fifteen_probes : Bool := scanWinsEverywhereB

/-- ⚑ **The budget is attained, so it is not slack.**  Some instance costs the
reference policy all fifteen probes, and none costs more.
(Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_scan_worst_case_is_the_budget : Bool :=
  scanLengths.all (fun n => decide (n ≤ MAX_TURNS)) && decide (MAX_TURNS ∈ scanLengths)

/-- A transcript that is accepted at every step, spends the whole budget, and is
NOT rewarded.  Fifteen probes that never name a correct pair: the run is legal
throughout and loses. -/
def losingTranscript : List Action :=
  (allSlots.flatMap fun slot =>
    allFragments.filterMap fun fragment =>
      if fragment == orderAt 0 slot then none else some (Action.probe slot fragment)).take MAX_TURNS

/-- ⚑ **A run can be lost.**  The design gate names `cannot-lose` as a WARN for a
reason: if failure is unrepresentable then no choice carries a consequence.
Fail-closed: a refused replay answers `false`.
(Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_a_run_can_be_lost : Bool :=
  match replay 0 initialState losingTranscript with
  | none => false
  | some s => !solvedB 0 s && decide (s.turns = MAX_TURNS)

/-! ## Refusal reachability, witnessed

⚑ **A declared refusal reason that cannot fire is decoration.**  The design gate
measures that from a total transition table for every other Path-of-Angels game;
this one has no such table (the state space is a subset lattice, `2^25`), so the
gate reported the vocabulary as UNCHECKED — `black-box-reconstruction/refusals-\
declared-not-checked`, a gap in the instrument rather than a property of the game.

The gap closes by EMITTING the evidence.  Each witness is a legal transcript
prefix and one further probe; the kernel replays it and reports the reason, the
descriptor carries the witness, and `scripts/poa-design-gate.py` replays the same
witness against the emitted ORACLE TABLE and re-derives the reason from the
declared `settles` semantics without reading any of these definitions.  Two
sources for one fact, which is the only shape that catches a disagreement.

⚠ The witnesses are the shortest transcripts that reach each guard, on the
identity instance (order 0), EXCEPT `turnLimit`, which needs the budget spent:
`losingTranscript` is the fifteen legal non-matching probes `a_run_can_be_lost`
already replays. -/

structure RefusalWitness where
  reason : Refusal
  order : Fin ORDER_SPACE
  /-- Legal transcript prefix; `replay` must accept it in full. -/
  history : List Action
  /-- The probe the run is refused at. -/
  probe : Action
deriving Repr

/-- Order 0 is the identity permutation, so `probe i i` matches and `probe 0 1`
does not — the two facts every witness below is built from, and both are cells of
the emitted table rather than claims of this comment. -/
def refusalWitnesses : List RefusalWitness :=
  [ { reason := .solved, order := 0
      history := [.probe 0 0, .probe 1 1, .probe 2 2, .probe 3 3, .probe 4 4]
      probe := .probe 0 1 }
  , { reason := .turnLimit, order := 0
      history := losingTranscript
      probe := .probe 0 0 }
  , { reason := .repeatedProbe, order := 0
      history := [.probe 0 1]
      probe := .probe 0 1 }
  , { reason := .settledSlot, order := 0
      history := [.probe 0 0]
      probe := .probe 0 1 }
  , { reason := .settledFragment, order := 0
      history := [.probe 0 0]
      probe := .probe 1 0 } ]

/-- A witness FIRES when its prefix is accepted at every step and the further
probe is refused with exactly the reason it names. -/
def witnessFiresB (w : RefusalWitness) : Bool :=
  match replay w.order initialState w.history with
  | none => false
  | some s => decide (refusal? w.order s w.probe = some w.reason)

/-- ⚑ **Every declared refusal reason is reachable.**  Not "one theorem per
reason asserted in prose" — every witness replays, and every constructor of
`Refusal` is named by one.  The design gate re-derives all five from the emitted
artifact. -/
def everyRefusalIsWitnessedB : Bool :=
  refusalWitnesses.all witnessFiresB &&
    allRefusals.all fun r => refusalWitnesses.any fun w => decide (w.reason = r)

/-- (Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_every_refusal_is_witnessed : Bool := everyRefusalIsWitnessedB

/-- The falsifier, constructed rather than asserted: a witness whose prefix is
legal and whose further probe is NOT refused at all does not fire.  Probing
`(0,1)` after `(0,2)` on the identity is a perfectly ordinary accepted move, so
`witnessFiresB` must reject any claim that it refuses.
(Pinned `= true` in `BlackBoxReconstructionFixtures`.) -/
def check_a_probe_that_is_accepted_witnesses_nothing : Bool :=
  !(allRefusals.any fun r =>
    witnessFiresB { reason := r, order := 0, history := [.probe 0 2],
                    probe := .probe 0 1 })

#assert_axioms orderRow_length
#assert_axioms orderRow_nodup
#assert_axioms orderRow_perm
#assert_axioms allOrderRows_nodup
#assert_axioms allOrderRows_length
#assert_axioms candidateRows_length
#assert_axioms step_deterministic
#assert_axioms step_refused_iff
#assert_axioms step_eq_none_of_refused
#assert_axioms refusal_none_turns_lt
#assert_axioms step_some_turns
#assert_axioms step_some_probed
#assert_axioms step_some_bound
#assert_axioms remaining_strictly_decreases
#assert_axioms solved_refuses
#assert_axioms exhausted_refuses
#assert_axioms repeated_probe_refused
#assert_axioms settled_slot_refused
#assert_axioms settled_fragment_refused
#assert_axioms step_settled_never_shrinks
#assert_axioms step_solved_never_unsolves
#assert_axioms replay_append
#assert_axioms refused_prefix_refuses_replay
#assert_axioms replay_some_turns
#assert_axioms replay_some_turn_bound
#assert_axioms replay_probed_length
#assert_axioms replay_initial_length_bounded
#assert_axioms terminalOutput_none_before_solution
#assert_axioms terminalOutput_is_mission_accepted
#assert_axioms terminalOutput_names_exact_beta_artifact
#assert_axioms terminalOutput_canonical
#assert_axioms solved_probed_every_correct_pair
#assert_axioms solved_needs_five_actions
#assert_axioms judge_some_sound
#assert_axioms judge_final_state_solved
#assert_axioms judge_action_count_bounded
#assert_axioms judge_receipt_binds_transcript
#assert_axioms judge_binds_run_seed
#assert_axioms allRefusals_complete
#assert_axioms refusal_tags_are_distinct

-- The six pins (`#assert_compiled` + `native_decide`) live in
-- `BlackBoxReconstructionFixtures.lean`, rooted in `PathOfAngelsGuards` — see the
-- note on `check_order_space_is_exactly_the_permutations` above.

end Dregg2.Games.PathOfAngels.BlackBoxReconstruction
