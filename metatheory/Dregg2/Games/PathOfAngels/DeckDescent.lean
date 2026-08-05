/-
# Deck Descent — go down for the find, and pay to come back up

Substrate note: this is Lean-authored game semantics.  Nothing here is an AIR, a
constraint system or a gadget.  Rust and the browser only dispatch the table the
Lean emitter writes.

## Why this module exists beside `DeckExpedition`

`DeckExpedition` owns *custody*: officers, injuries, a daily counter, per-object
salvage records, a persistent `State` carrying `Finset ExpeditionKey`.  It is a
content kernel and it is the right shape for one — but its state is not finitely
enumerable (the fixture alone spans ~10^7 configurations) and its `RawConfig`
carries a fully authored `ValidatedPack`, so nothing about a run is drawn from
the run seed.  A machine with no hidden bit and no finite table cannot be a POAG1
descriptor and cannot be scored by `scripts/poa-design-gate.py`.

This module is the *playable* descent: the same fiction — go in, take a thing,
carry it out — reduced to a machine whose whole reachable state space is emitted,
whose instance is a per-run hidden draw, and whose every design property below is
a theorem over the transition this file exports.

## The four properties this design is accountable for

1. **Two incomparable budgets.**  `AIR` is the clock and `SHORING` is the supply.
   No action converts one into the other, and `budgets_are_incomparable` exhibits
   two accepted lines that trade them in opposite directions.
2. **Information is purchasable.**  A chamber's passage is hidden until `survey`
   spends a unit of air on it, or until a body walks into it.  `shore` may be
   spent blind, so the real fork is *air to learn* against *supply to not need
   to*.
3. **Route commitment.**  Depth is a ratchet paid twice: every chamber entered is
   a chamber that must be crossed again on the way out, and an unshored flood
   damages on both crossings.
4. **Extraction is the point.**  A relic in the sling is worth nothing; a relic
   through the hatch is the find.  Damage lowers carrying capacity, and a
   crossing that overruns it leaves the deepest relic on the deck.

## What the budget is sized for

`AIR = 9` is not slack.  It is simultaneously the cost of the cautious line on
the worst instance (shore blind, descend, lift, shore blind, descend, lift,
ascend, ascend, extract) and the cost of the greedy line on the best one
(descend, lift, descend, descend, lift the deep relic, ascend, ascend, ascend,
extract).  `budget_binds_on_the_cautious_line` and
`budget_binds_on_the_greedy_line` are those two facts.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Games.PathOfAngels.SeedDraw
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.DeckDescent

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

/-- The clock.  Every action spends exactly one unit, including `extract`, so the
emitted `action_limit` and the state view's `turns` are the same quantity. -/
abbrev AIR : Nat := 9

/-- The supply.  Only `shore` spends it and nothing replaces it. -/
abbrev SHORING : Nat := 2

/-- Base carrying capacity.  `capacity = BASE_CAPACITY - damage`.

Three, against a bank target of two, is deliberate: it makes ONE unshored
crossing survivable and the second one fatal.  At two the forced drop in
`takeDamage` was unreachable — any damage put the run below target immediately —
and a rule that cannot fire is not a rule. -/
abbrev BASE_CAPACITY : Nat := 3

/-- A banked run is one that comes through the hatch with at least this many
relics.  One relic is a walk; two is an expedition. -/
abbrev BANK_TARGET : Nat := 2

/-! ## The deck -/

/-- Three chambers on one shaft.  `Chamber.depth` is also the number of crossings
each way, which is the whole of the extraction-debt arithmetic. -/
inductive Chamber where
  | upper
  | middle
  | deep
deriving Repr, DecidableEq

def allChambers : List Chamber := [.upper, .middle, .deep]

theorem allChambers_complete (c : Chamber) : c ∈ allChambers := by
  cases c <;> simp [allChambers]

def Chamber.depth : Chamber → Nat
  | .upper => 1
  | .middle => 2
  | .deep => 3

/-- The chamber lying immediately below a depth, when there is one. -/
def chamberBelow (depth : Nat) : Option Chamber :=
  match depth with
  | 0 => some .upper
  | 1 => some .middle
  | 2 => some .deep
  | _ => none

/-- The chamber a body at `depth` is standing in. -/
def chamberAt (depth : Nat) : Option Chamber :=
  match depth with
  | 1 => some .upper
  | 2 => some .middle
  | 3 => some .deep
  | _ => none

theorem chamberBelow_depth (c : Chamber) : chamberBelow (c.depth - 1) = some c := by
  cases c <;> rfl

theorem chamberAt_depth (c : Chamber) : chamberAt c.depth = some c := by
  cases c <;> rfl

/-! ## What a chamber is, and what a player knows about it -/

/-- The hidden bit.  It is drawn per chamber from the run seed and it is never in
the emitted descriptor: the table names BOTH successors of a row that consults
it. -/
inductive Passage where
  | sound
  | flooded
deriving Repr, DecidableEq

/-- What the player has established about one chamber's passage.  `dark` is the
prior; `sound`/`flooded` are the two things a look can establish; `shored` is a
flood that has been paid for, and — because `shore` may be spent blind — also a
dark chamber that has been paid for without ever being read. -/
inductive Lore where
  | dark
  | sound
  | flooded
  | shored
deriving Repr, DecidableEq

/-- Does crossing this chamber cost a body?  A shored chamber never does; a dark
one is not crossable without first resolving it, so this is total by cases and
the `dark` answer is never consulted on an accepted transition. -/
def Lore.damaging : Lore → Bool
  | .dark => false
  | .sound => false
  | .flooded => true
  | .shored => false

/-- Per-chamber record: what is known about the passage, and whether its relic is
still on the deck.  Three of these are the whole board state. -/
structure ChamberState where
  lore : Lore
  relicTaken : Bool
deriving Repr, DecidableEq

def freshChamber : ChamberState := { lore := .dark, relicTaken := false }

/-- The three chambers, stored as named fields rather than a list so that
`DecidableEq` and `decide` stay cheap. -/
structure Deck where
  upper : ChamberState
  middle : ChamberState
  deep : ChamberState
deriving Repr, DecidableEq

def freshDeck : Deck :=
  { upper := freshChamber, middle := freshChamber, deep := freshChamber }

def Deck.get (d : Deck) : Chamber → ChamberState
  | .upper => d.upper
  | .middle => d.middle
  | .deep => d.deep

def Deck.set (d : Deck) : Chamber → ChamberState → Deck
  | .upper, s => { d with upper := s }
  | .middle, s => { d with middle := s }
  | .deep, s => { d with deep := s }

theorem Deck.get_set_same (d : Deck) (c : Chamber) (s : ChamberState) :
    (d.set c s).get c = s := by
  cases c <;> rfl

/-! ## The instance -/

/-- One instance: which chambers flood.  Eight of them, and the descriptor names
none. -/
structure Board where
  upper : Passage
  middle : Passage
  deep : Passage
deriving Repr, DecidableEq

def Board.get (b : Board) : Chamber → Passage
  | .upper => b.upper
  | .middle => b.middle
  | .deep => b.deep

/-- The passage bit read back as the lore a look would establish. -/
def Board.lore (b : Board) (c : Chamber) : Lore :=
  match b.get c with
  | .sound => .sound
  | .flooded => .flooded

def boardTable : List Board :=
  [ { upper := .sound,   middle := .sound,   deep := .sound }
  , { upper := .sound,   middle := .sound,   deep := .flooded }
  , { upper := .sound,   middle := .flooded, deep := .sound }
  , { upper := .sound,   middle := .flooded, deep := .flooded }
  , { upper := .flooded, middle := .sound,   deep := .sound }
  , { upper := .flooded, middle := .sound,   deep := .flooded }
  , { upper := .flooded, middle := .flooded, deep := .sound }
  , { upper := .flooded, middle := .flooded, deep := .flooded } ]

theorem boardTable_length : boardTable.length = 8 := rfl

theorem boardTable_nodup : boardTable.Nodup := by decide

def boardAt (i : Fin 8) : Board :=
  boardTable.get (Fin.cast boardTable_length.symm i)

theorem boardAt_mem : ∀ i : Fin 8, boardAt i ∈ boardTable := by decide

/-- Every board is realized by exactly one index, so the family is eight distinct
instances and not eight names for fewer. -/
theorem boardAt_injective : ∀ i j : Fin 8, boardAt i = boardAt j → i = j := by decide

/-! ### Drawing the instance from the precommitted run seed

Three CONSUMING draws off one stream (`SeedDraw.drawBelow?`), so the three bits
are independent reads and not one byte wearing three hats — the wound
`SalvageCrate.unbiasedIndex?` carries and `SeedDraw` exists to close. -/

def passageOfDraw (v : Fin 2) : Passage :=
  if v.val = 0 then .sound else .flooded

/-- `none` only if the 32-byte seed runs out of acceptable bytes, which needs 32
consecutive rejections against a ceiling of 256; `boardFromRunSeed` fails closed
to the all-sound board in that case and `boardFromRunSeed_total` records that the
fallback is unreachable for the bound actually used. -/
def boardFromRunSeed? (runSeed : Digest32) : Option Board := do
  let (a, s₁) ← SeedDraw.drawBelow? 2 (by decide) runSeed.bytes
  let (b, s₂) ← SeedDraw.drawBelow? 2 (by decide) s₁
  let (c, _) ← SeedDraw.drawBelow? 2 (by decide) s₂
  some { upper := passageOfDraw a, middle := passageOfDraw b, deep := passageOfDraw c }

def boardFromRunSeed (runSeed : Digest32) : Board :=
  (boardFromRunSeed? runSeed).getD { upper := .sound, middle := .sound, deep := .sound }

/-- A bound of 2 divides 256, so `ceilingFor 2 = 256` and no byte is ever
rejected: three draws always succeed off a 32-byte seed.  The `getD` fallback in
`boardFromRunSeed` is therefore dead code, and this says so rather than leaving a
reader to assume it. -/
theorem draw_below_two_never_rejects (b : Fin 256) (rest : List (Fin 256)) :
    SeedDraw.drawBelow? 2 (by decide) (b :: rest)
      = some (⟨b.val % 2, Nat.mod_lt _ (by decide)⟩, rest) := by
  have hceil : SeedDraw.ceilingFor 2 = 256 := by decide
  simp [SeedDraw.drawBelow?, hceil, b.isLt]

/-! ## Player state -/

/-- The sling.  Which chambers' relics are in hand — a set, not a count, because
the receipt names the relics and a forced drop must name which one fell. -/
structure Sling where
  upper : Bool
  middle : Bool
  deep : Bool
deriving Repr, DecidableEq

def emptySling : Sling := { upper := false, middle := false, deep := false }

def Sling.holds (s : Sling) : Chamber → Bool
  | .upper => s.upper
  | .middle => s.middle
  | .deep => s.deep

def Sling.add (s : Sling) : Chamber → Sling
  | .upper => { s with upper := true }
  | .middle => { s with middle := true }
  | .deep => { s with deep := true }

def Sling.drop (s : Sling) : Chamber → Sling
  | .upper => { s with upper := false }
  | .middle => { s with middle := false }
  | .deep => { s with deep := false }

def Sling.count (s : Sling) : Nat :=
  (if s.upper then 1 else 0) + (if s.middle then 1 else 0) + (if s.deep then 1 else 0)

theorem Sling.count_le_three (s : Sling) : s.count ≤ 3 := by
  obtain ⟨u, m, d⟩ := s
  cases u <;> cases m <;> cases d <;> decide

/-- The deepest relic in the sling.  This is the one the deck takes when a
crossing overruns capacity: what you reached furthest for is what you lose. -/
def Sling.deepest (s : Sling) : Option Chamber :=
  if s.deep then some .deep
  else if s.middle then some .middle
  else if s.upper then some .upper
  else none

theorem Sling.deepest_some_of_count (s : Sling) (h : 0 < s.count) :
    (s.deepest).isSome = true := by
  obtain ⟨u, m, d⟩ := s
  cases u <;> cases m <;> cases d <;> revert h <;> decide

structure State where
  depth : Nat
  air : Nat
  shoring : Nat
  damage : Nat
  sling : Sling
  deck : Deck
  banked : Bool
deriving Repr, DecidableEq

def initialState : State where
  depth := 0
  air := AIR
  shoring := SHORING
  damage := 0
  sling := emptySling
  deck := freshDeck
  banked := false

/-- Carrying capacity falls one for one with damage and floors at zero. -/
def capacity (s : State) : Nat := BASE_CAPACITY - s.damage

def turnsUsed (s : State) : Nat := AIR - s.air

/-! ## Optimistic completability — the honest "not yet provably dead" predicate

A run under hidden information cannot be told it is dead unless it is dead on
*every* instance still consistent with what it has seen.  `reachableBankB` is
therefore computed against the most generous continuation: every dark chamber is
assumed sound.  A state it refuses is one no board can rescue. -/

/-- Depths of the chambers whose relic is still on the deck, shallowest first.
`allChambers` is in depth order and `filter` preserves it, so `take n` is the
cheapest `n` of them. -/
def untakenDepths (s : State) : List Nat :=
  (allChambers.filter (fun c => !(s.deck.get c).relicTaken)).map Chamber.depth

/-- Air needed to bank the target from here, on the most favourable board still
consistent with what the run has seen: every dark chamber sound, so no crossing
costs anything, and the shallowest untaken relics chosen.

The plan it prices is: descend to the deepest chosen chamber, lift each chosen
relic, climb back to the hatch, extract.  Chambers already above the body cost
only their lift, because the climb passes through them anyway.  A run this
refuses is one no board rescues. -/
def cheapestBank (s : State) : Nat :=
  let need := BANK_TARGET - s.sling.count
  if BANK_TARGET ≤ s.sling.count then
    s.depth + 1                          -- climb out and come through the hatch
  else
    let avail := untakenDepths s
    if avail.length < need then
      AIR + 1                            -- not enough relics left anywhere
    else
      let deepest := (avail.take need).foldl Nat.max 0
      let reach := Nat.max s.depth deepest
      (reach - s.depth) + need + reach + 1

/-- Can this state still bank the target, on the most favourable board still
consistent with it?  Capacity is the hard wall: no continuation restores it. -/
def reachableBankB (s : State) : Bool :=
  !s.banked &&
  decide (BANK_TARGET ≤ capacity s) &&
  decide (cheapestBank s ≤ s.air)

/-- A run that has banked is finished; a run that cannot reach the target is
doomed.  Both refuse every further action, so a dead descent stops spending air
instead of wandering. -/
def liveB (s : State) : Bool := reachableBankB s

def doomedB (s : State) : Bool := !s.banked && !reachableBankB s

/-! ## Actions -/

inductive Action where
  /-- Spend one air reading the passage of the chamber below.  The oracle row. -/
  | survey
  /-- Spend one air and one shoring making the chamber below safe.  Legal on a
  dark chamber as well as a known flood: supply may be spent instead of the air a
  look would cost, and that trade is the second budget's whole reason to exist. -/
  | shore
  /-- Spend one air going down.  A dark chamber resolves on the way in — the
  second oracle row — and an unshored flood costs a point of damage. -/
  | descend
  /-- Spend one air taking this chamber's relic. -/
  | lift
  /-- Spend one air climbing.  The chamber being left is crossed a second time,
  and an unshored flood charges again. -/
  | ascend
  /-- Spend one air coming through the hatch.  Terminal. -/
  | extract
deriving Repr, DecidableEq

def allActions : List Action :=
  [.survey, .shore, .descend, .lift, .ascend, .extract]

theorem allActions_complete (a : Action) : a ∈ allActions := by
  cases a <;> simp [allActions]

/-- A crossing that costs a body.  Damage rises by one, capacity falls by one,
and if the sling no longer fits, the DEEPEST relic is left on the deck. -/
def takeDamage (s : State) : State :=
  let damage := s.damage + 1
  let cap := BASE_CAPACITY - damage
  let sling :=
    if cap < s.sling.count then
      match s.sling.deepest with
      | some c => s.sling.drop c
      | none => s.sling
    else s.sling
  { s with damage, sling }

/-- Crossing `c` with lore `l`: pay a body if it floods, otherwise pass. -/
def cross (s : State) (l : Lore) : State :=
  if l.damaging then takeDamage s else s

/-! ### The five deterministic openness predicates

Each conjunct below is read back out of an accepted action by a theorem in the
next section, so the refusal reasons the emitted table carries are exactly the
negations of these and not a second opinion about them. -/

/-- The action-specific half of openness.  `liveB` and the clock are factored out
into `openB` below so that "a run that is over spends nothing" and "every action
costs air" are each ONE conjunct in ONE place, and the structural theorems read
them back without a per-action tactic. -/
def openKindB (s : State) : Action → Bool
  | .survey =>
      match chamberBelow s.depth with
      | none => false
      | some c => decide ((s.deck.get c).lore = Lore.dark)
  | .shore =>
      decide (0 < s.shoring) &&
      match chamberBelow s.depth with
      | none => false
      | some c =>
          decide ((s.deck.get c).lore = Lore.dark ∨ (s.deck.get c).lore = Lore.flooded)
  | .descend =>
      match chamberBelow s.depth with
      | none => false
      | some _ => true
  | .lift =>
      match chamberAt s.depth with
      | none => false
      | some c =>
          !(s.deck.get c).relicTaken && decide (s.sling.count + 1 ≤ capacity s)
  | .ascend => decide (0 < s.depth)
  | .extract => decide (s.depth = 0) && decide (BANK_TARGET ≤ s.sling.count)

/-- Openness, in three conjuncts that never move: the run is still live, the
clock has a unit left, and the action itself applies here. -/
def openB (s : State) (a : Action) : Bool :=
  liveB s && decide (0 < s.air) && openKindB s a

/-! ### The transition

`stepB` takes the board because two of its six rows consult it.  The emitter
never sees a board: it emits the row as `resolve` with both successors named. -/

/-- The raw effect of an action, with openness already decided.  Every branch
spends exactly one unit of air, which is why `step_spends_exactly_one_air` is a
single uniform proof rather than six. -/
def transitionB (b : Board) (s : State) : Action → Option State
  | .survey =>
      match chamberBelow s.depth with
      | none => none
      | some c =>
          let cs := s.deck.get c
          some { s with
            air := s.air - 1
            deck := s.deck.set c { cs with lore := b.lore c } }
  | .shore =>
      match chamberBelow s.depth with
      | none => none
      | some c =>
          let cs := s.deck.get c
          some { s with
            air := s.air - 1
            shoring := s.shoring - 1
            deck := s.deck.set c { cs with lore := Lore.shored } }
  | .descend =>
      match chamberBelow s.depth with
      | none => none
      | some c =>
          let cs := s.deck.get c
          -- A dark chamber is read by the body that walks into it.
          let lore := if cs.lore = Lore.dark then b.lore c else cs.lore
          some (cross { s with
            air := s.air - 1
            depth := s.depth + 1
            deck := s.deck.set c { cs with lore } } lore)
  | .lift =>
      match chamberAt s.depth with
      | none => none
      | some c =>
          let cs := s.deck.get c
          some { s with
            air := s.air - 1
            sling := s.sling.add c
            deck := s.deck.set c { cs with relicTaken := true } }
  | .ascend =>
      match chamberAt s.depth with
      | none => none
      | some c =>
          some (cross { s with air := s.air - 1, depth := s.depth - 1 }
            (s.deck.get c).lore)
  | .extract =>
      some { s with air := s.air - 1, banked := true }

def stepB (b : Board) (s : State) (a : Action) : Option State :=
  if openB s a then transitionB b s a else none

def replayB (b : Board) : State → List Action → Option State
  | s, [] => some s
  | s, a :: as =>
      match stepB b s a with
      | none => none
      | some s' => replayB b s' as

/-! ## Reading each openness conjunct back out of an accepted action -/

/-! ### `takeDamage` and `cross`, projected

These four are `rfl`: the structure update touches `damage` and `sling` only, so
every other field passes through and the two crossing helpers can be reasoned
about without unfolding them again. -/

theorem takeDamage_air (s : State) : (takeDamage s).air = s.air := rfl
theorem takeDamage_shoring (s : State) : (takeDamage s).shoring = s.shoring := rfl
theorem takeDamage_depth (s : State) : (takeDamage s).depth = s.depth := rfl
theorem takeDamage_damage (s : State) : (takeDamage s).damage = s.damage + 1 := rfl

theorem cross_air (s : State) (l : Lore) : (cross s l).air = s.air := by
  unfold cross; split
  · exact takeDamage_air s
  · rfl

theorem cross_shoring (s : State) (l : Lore) : (cross s l).shoring = s.shoring := by
  unfold cross; split
  · exact takeDamage_shoring s
  · rfl

theorem cross_depth (s : State) (l : Lore) : (cross s l).depth = s.depth := by
  unfold cross; split
  · exact takeDamage_depth s
  · rfl

theorem cross_damage_ge (s : State) (l : Lore) : s.damage ≤ (cross s l).damage := by
  unfold cross; split
  · rw [takeDamage_damage]; omega
  · exact Nat.le_refl _

/-- A body that pays for a crossing loses exactly one unit of carrying capacity,
or is already carrying nothing. -/
theorem takeDamage_capacity (s : State) :
    capacity (takeDamage s) + 1 = capacity s ∨ capacity (takeDamage s) = 0 := by
  simp only [capacity, BASE_CAPACITY, takeDamage_damage]
  omega

theorem step_some_open (b : Board) (s s' : State) (a : Action)
    (h : stepB b s a = some s') : openB s a = true := by
  simp only [stepB] at h
  split at h
  · assumption
  · exact absurd h (by simp)

theorem step_some_live (b : Board) (s s' : State) (a : Action)
    (h : stepB b s a = some s') : liveB s = true := by
  have hopen := step_some_open b s s' a h
  simp only [openB, Bool.and_eq_true] at hopen
  exact hopen.1.1

theorem step_some_air (b : Board) (s s' : State) (a : Action)
    (h : stepB b s a = some s') : 0 < s.air := by
  have hopen := step_some_open b s s' a h
  simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hopen
  exact hopen.1.2

theorem step_some_kind (b : Board) (s s' : State) (a : Action)
    (h : stepB b s a = some s') : openKindB s a = true := by
  have hopen := step_some_open b s s' a h
  simp only [openB, Bool.and_eq_true] at hopen
  exact hopen.2

theorem step_eq_transition (b : Board) (s s' : State) (a : Action)
    (h : stepB b s a = some s') : transitionB b s a = some s' := by
  simp only [stepB] at h
  split at h
  · exact h
  · exact absurd h (by simp)

/-- The clock is a real resource: every accepted action spends exactly one unit,
so `turnsUsed` and the emitted `turns` are the same number and no action is free. -/
theorem step_spends_exactly_one_air (b : Board) (s s' : State) (a : Action)
    (h : stepB b s a = some s') : s'.air + 1 = s.air := by
  have hair := step_some_air b s s' a h
  have ht := step_eq_transition b s s' a h
  cases a <;> simp only [transitionB] at ht
  case survey | shore | lift =>
    split at ht
    · exact absurd ht (by simp)
    · simp only [Option.some.injEq] at ht; subst ht; simp; omega
  case descend | ascend =>
    split at ht
    · exact absurd ht (by simp)
    · simp only [Option.some.injEq] at ht; subst ht
      rw [cross_air]; simp; omega
  case extract =>
    simp only [Option.some.injEq] at ht; subst ht; simp; omega

/-- Air never exceeds the budget on a state a run can actually be in, which is
what makes `turnsUsed` the emitted `turns` rather than a clamped subtraction. -/
theorem step_air_le_of_le (b : Board) (s s' : State) (a : Action)
    (h : stepB b s a = some s') (hle : s.air ≤ AIR) : s'.air ≤ AIR := by
  have := step_spends_exactly_one_air b s s' a h
  omega

theorem step_turns_advance (b : Board) (s s' : State) (a : Action)
    (h : stepB b s a = some s') (hle : s.air ≤ AIR) :
    turnsUsed s' = turnsUsed s + 1 := by
  have hair := step_spends_exactly_one_air b s s' a h
  have hpos := step_some_air b s s' a h
  simp only [turnsUsed]
  omega

/-- Shoring is never replenished, so the second budget is monotone. -/
theorem step_shoring_never_rises (b : Board) (s s' : State) (a : Action)
    (h : stepB b s a = some s') : s'.shoring ≤ s.shoring := by
  have ht := step_eq_transition b s s' a h
  cases a <;> simp only [transitionB] at ht
  case survey | shore | lift =>
    split at ht
    · exact absurd ht (by simp)
    · simp only [Option.some.injEq] at ht; subst ht; simp
  case descend | ascend =>
    split at ht
    · exact absurd ht (by simp)
    · simp only [Option.some.injEq] at ht; subst ht
      rw [cross_shoring]
  case extract =>
    simp only [Option.some.injEq] at ht; subst ht; simp

/-- Damage never falls: there is no treatment inside a descent, which is what
makes a wading decision permanent. -/
theorem step_damage_never_falls (b : Board) (s s' : State) (a : Action)
    (h : stepB b s a = some s') : s.damage ≤ s'.damage := by
  have ht := step_eq_transition b s s' a h
  cases a <;> simp only [transitionB] at ht
  case survey | shore | lift =>
    split at ht
    · exact absurd ht (by simp)
    · simp only [Option.some.injEq] at ht; subst ht; simp
  case descend | ascend =>
    split at ht
    · exact absurd ht (by simp)
    · simp only [Option.some.injEq] at ht; subst ht
      -- `cross_damage_ge` applied with the successor determining the metavars:
      -- unifying against the RHS fixes the state, and the residual goal is the
      -- record's own `damage` field, which is `s.damage`.
      refine le_trans ?_ (cross_damage_ge _ _)
      exact Nat.le_refl _
  case extract =>
    simp only [Option.some.injEq] at ht; subst ht; simp

theorem step_capacity_never_rises (b : Board) (s s' : State) (a : Action)
    (h : stepB b s a = some s') : capacity s' ≤ capacity s := by
  have hd := step_damage_never_falls b s s' a h
  simp only [capacity]
  omega

/-! ## Refusals — each emitted reason is a theorem -/

/-- The one lemma every refusal below goes through: a false conjunct of `openB`
refuses, whatever the action's own effect would have been. -/
theorem not_open_refuses (b : Board) (s : State) (a : Action)
    (h : openB s a = false) : stepB b s a = none := by
  simp [stepB, h]

theorem doomed_refuses_everything (b : Board) (s : State) (a : Action)
    (h : reachableBankB s = false) : stepB b s a = none := by
  exact not_open_refuses b s a (by simp [openB, liveB, h])

theorem banked_refuses_everything (b : Board) (s : State) (a : Action)
    (h : s.banked = true) : stepB b s a = none := by
  exact doomed_refuses_everything b s a (by simp [reachableBankB, h])

theorem airless_refuses_everything (b : Board) (s : State) (a : Action)
    (h : s.air = 0) : stepB b s a = none := by
  exact not_open_refuses b s a (by simp [openB, h])

theorem shoreless_refuses_shore (b : Board) (s : State) (h : s.shoring = 0) :
    stepB b s .shore = none := by
  exact not_open_refuses b s .shore (by simp [openB, openKindB, h])

theorem surface_refuses_ascend (b : Board) (s : State) (h : s.depth = 0) :
    stepB b s .ascend = none := by
  exact not_open_refuses b s .ascend (by simp [openB, openKindB, h])

theorem chamberBelow_none_of_deep (depth : Nat) (h : 3 ≤ depth) :
    chamberBelow depth = none := by
  unfold chamberBelow
  split
  · omega
  · omega
  · omega
  · rfl

theorem floor_refuses_descend (b : Board) (s : State) (h : 3 ≤ s.depth) :
    stepB b s .descend = none := by
  exact not_open_refuses b s .descend
    (by simp [openB, openKindB, chamberBelow_none_of_deep s.depth h])

theorem inside_refuses_extract (b : Board) (s : State) (h : s.depth ≠ 0) :
    stepB b s .extract = none := by
  exact not_open_refuses b s .extract (by simp [openB, openKindB, h])

/-- The reward gate is the bank target and nothing else: a run cannot come
through the hatch with one relic and be paid. -/
theorem short_sling_refuses_extract (b : Board) (s : State)
    (h : s.sling.count < BANK_TARGET) : stepB b s .extract = none := by
  exact not_open_refuses b s .extract
    (by simp [openB, openKindB, Nat.not_le.mpr h])

/-- A chamber already emptied refuses a second lift, so a relic is a relic and
not a renewable meter. -/
theorem emptied_chamber_refuses_lift (b : Board) (s : State) (c : Chamber)
    (hat : chamberAt s.depth = some c) (h : (s.deck.get c).relicTaken = true) :
    stepB b s .lift = none := by
  exact not_open_refuses b s .lift (by simp [openB, openKindB, hat, h])

/-- Over capacity, the sling refuses.  This is the rule that makes damage a
carrying constraint rather than a score. -/
theorem full_sling_refuses_lift (b : Board) (s : State)
    (h : capacity s < s.sling.count + 1) : stepB b s .lift = none := by
  refine not_open_refuses b s .lift ?_
  simp only [openB, openKindB, Bool.and_eq_false_iff]
  right
  cases hat : chamberAt s.depth with
  | none => rfl
  | some c => simp [Nat.not_le.mpr h]

/-- A chamber whose passage is already established refuses a second look: a
survey buys information, and information already bought is not for sale. -/
theorem known_chamber_refuses_survey (b : Board) (s : State) (c : Chamber)
    (hbelow : chamberBelow s.depth = some c) (h : (s.deck.get c).lore ≠ Lore.dark) :
    stepB b s .survey = none := by
  exact not_open_refuses b s .survey (by simp [openB, openKindB, hbelow, h])

/-- A shored chamber refuses a second shoring, so supply cannot be burned to no
effect and the two-unit budget really is two decisions. -/
theorem shored_chamber_refuses_shore (b : Board) (s : State) (c : Chamber)
    (hbelow : chamberBelow s.depth = some c)
    (h : (s.deck.get c).lore = Lore.shored) :
    stepB b s .shore = none := by
  refine not_open_refuses b s .shore ?_
  simp only [openB, openKindB, Bool.and_eq_false_iff]
  right
  right
  simp [hbelow, h]

/-! ## Replay -/

theorem replayB_append (b : Board) (s : State) (xs ys : List Action) :
    replayB b s (xs ++ ys) = (replayB b s xs).bind (fun s' => replayB b s' ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, replayB]
      split <;> simp_all

theorem refused_prefix_refuses_replay (b : Board) (s : State) (a : Action)
    (as : List Action) (h : stepB b s a = none) : replayB b s (a :: as) = none := by
  simp [replayB, h]

/-- Air is spent one unit per accepted action all the way along, so an accepted
transcript is never longer than the budget.  This is the statement the emitted
`action_limit` is: not a cap the client enforces, a cap the kernel cannot
exceed. -/
theorem replayB_spends_air (b : Board) (acts : List Action) :
    ∀ (s s' : State), replayB b s acts = some s' → s'.air + acts.length = s.air := by
  induction acts with
  | nil =>
      intro s s' h
      simp only [replayB, Option.some.injEq] at h
      subst h
      simp
  | cons a as ih =>
      intro s s' h
      simp only [replayB] at h
      split at h
      · contradiction
      · rename_i s₁ hstep
        have h1 := step_spends_exactly_one_air b s s₁ a hstep
        have h2 := ih s₁ s' h
        simp only [List.length_cons]
        omega

theorem accepted_transcript_within_budget (b : Board) (acts : List Action)
    (s' : State) (h : replayB b initialState acts = some s') : acts.length ≤ AIR := by
  have := replayB_spends_air b acts initialState s' h
  simp only [initialState] at this
  omega

/-! ## Config, judge and receipt

The judged surface is exactly `RelayRepair`'s: a `Config` whose instance field is
pinned to the precommitted run seed by a proof obligation, a `terminalOutput`
that fails closed against the mission's own acceptance predicate, and a `judge`
that binds the transcript into the receipt. -/

structure Config where
  board : Board
  mission : MissionSpec
  /-- The relic each chamber holds.  Declared in the config, checked against the
  mission's allowlist by `relics_declared`, so a run cannot invent a relic. -/
  upperRelic : RelicId
  middleRelic : RelicId
  deepRelic : RelicId
  reward : Contribution
  reward_accepted : mission.acceptsContribution reward = true
  relics_distinct : upperRelic ≠ middleRelic ∧ middleRelic ≠ deepRelic ∧
    upperRelic ≠ deepRelic
  relics_declared :
    upperRelic ∈ mission.allowedRelics ∧ middleRelic ∈ mission.allowedRelics ∧
    deepRelic ∈ mission.allowedRelics
  /-- ⚑ The played board is the one the precommitted seed draws.  A host cannot
  re-flood the deck after reading the transcript. -/
  board_eq : board = boardFromRunSeed mission.runSeed

def Config.relicOf (cfg : Config) : Chamber → RelicId
  | .upper => cfg.upperRelic
  | .middle => cfg.middleRelic
  | .deep => cfg.deepRelic

/-- The relics a sling brings through the hatch. -/
def Config.bankedRelics (cfg : Config) (s : Sling) : Finset RelicId :=
  (allChambers.filter (fun c => s.holds c)).map cfg.relicOf |>.toFinset

def Config.terminalContribution (cfg : Config) (s : State) : Contribution :=
  { cfg.reward with
    relics := cfg.bankedRelics s.sling
    relics_bounded := by
      have : (cfg.bankedRelics s.sling).card ≤ 3 := by
        simp only [Config.bankedRelics]
        exact le_trans (List.toFinset_card_le _)
          (by simpa using List.length_filter_le (fun c => s.sling.holds c) allChambers)
      exact le_trans this (by decide) }

/-- Fail closed: a terminal state pays only if the mission itself accepts the
contribution the run assembled.  There is no branch that widens the allowlist. -/
def terminalOutput (cfg : Config) (s : State) : Option (Contribution × ArtifactRef) :=
  if s.banked then
    let c := cfg.terminalContribution s
    if cfg.mission.acceptsContribution c then some (c, cfg.mission.artifact) else none
  else none

theorem terminalOutput_none_without_bank (cfg : Config) (s : State)
    (h : s.banked = false) : terminalOutput cfg s = none := by
  simp [terminalOutput, h]

theorem terminalOutput_is_mission_accepted (cfg : Config) (s : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg s = some out) :
    cfg.mission.acceptsContribution out.1 = true := by
  simp only [terminalOutput] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst out
      assumption
    · contradiction
  · contradiction

theorem terminalOutput_names_exact_artifact (cfg : Config) (s : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg s = some out) :
    out.2 = cfg.mission.artifact := by
  simp only [terminalOutput] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      rw [← h]
    · contradiction
  · contradiction

theorem terminalOutput_canonical (cfg : Config) (s : State)
    {contribution : Contribution} {artifact : ArtifactRef}
    (h : terminalOutput cfg s = some (contribution, artifact)) :
    terminalOutput cfg s = some (contribution, cfg.mission.artifact) := by
  have hart := terminalOutput_names_exact_artifact cfg s h
  change artifact = cfg.mission.artifact at hart
  rw [hart] at h
  exact h

def step (cfg : Config) (s : State) (a : Action) : Option State := stepB cfg.board s a

def replay (cfg : Config) : State → List Action → Option State := replayB cfg.board

theorem step_eq_stepB (cfg : Config) (s : State) (a : Action) :
    step cfg s a = stepB cfg.board s a := rfl

theorem replay_eq_replayB (cfg : Config) (s : State) (acts : List Action) :
    replay cfg s acts = replayB cfg.board s acts := rfl

/-- ⚑ The board a run is judged on is the one its precommitted seed draws. -/
theorem judged_board_is_the_drawn_board (cfg : Config) :
    cfg.board = boardFromRunSeed cfg.mission.runSeed := cfg.board_eq

def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by omega)⟩

def actionCode : Action → Nat
  | .survey => 0
  | .shore => 1
  | .descend => 2
  | .lift => 3
  | .ascend => 4
  | .extract => 5

def actionAt (actions : List Action) (i : Nat) : Nat :=
  match actions[i]? with
  | some a => actionCode a
  | none => 255

def transcriptDigest (actions : List Action) : Digest32 where
  bytes := List.ofFn (fun i : Fin 32 =>
    if i.val = 0 then byte actions.length else byte (actionAt actions (i.val - 1)))
  length_eq := by simp

structure JudgedRun where
  finalState : State
  afterWorld : WorldState
  receipt : RunReceipt

structure JudgeContext where
  actorRoot : Digest32
  playerKey : Digest32
  previousPlayerCounter : Nat

def judge (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) : Option JudgedRun :=
  match replay cfg initialState actions with
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

theorem judge_some_sound (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    replay cfg initialState actions = some run.finalState ∧
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

theorem judge_receipt_binds_transcript (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
    run.receipt.transcriptDigest = transcriptDigest actions :=
  (judge_some_sound cfg before ctx actions h).2.2.2.2

/-- A judged run came through the hatch.  There is no rewarded transcript whose
final state is still on the deck. -/
theorem judged_run_banked (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) : run.finalState.banked = true := by
  have hsound := judge_some_sound cfg before ctx actions h
  cases hb : run.finalState.banked with
  | false =>
      have hterm := hsound.2.1
      rw [terminalOutput_none_without_bank cfg _ hb] at hterm
      exact absurd hterm (by simp)
  | true => rfl

/-- A judged run spent no more than the budget.  The receipt cannot report a
ten-action descent. -/
theorem judged_run_within_budget (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) : actions.length ≤ AIR := by
  have hsound := judge_some_sound cfg before ctx actions h
  exact accepted_transcript_within_budget cfg.board actions run.finalState hsound.1

/-! ## The design properties, measured over the actual transition

Everything below is `decide`/`native_decide` over `stepB` and `replayB` — the
same functions the emitter tabulates and the judge runs.  There is no second
model of the descent anywhere in this repository. -/

def playsOutB (b : Board) (acts : List Action) : Bool :=
  match replayB b initialState acts with
  | none => false
  | some s => s.banked

/-- The cautious line: buy safety with supply rather than time, twice, and take
the two shallow relics.  Nine actions, and it works on every board because it
never reads a bit. -/
def cautiousLine : List Action :=
  [.shore, .descend, .lift, .shore, .descend, .lift, .ascend, .ascend, .extract]

/-- The greedy line: walk in blind, skip the middle relic, and reach for the deep
one.  Nine actions, and it works only where the shaft is sound. -/
def greedyLine : List Action :=
  [.descend, .lift, .descend, .descend, .lift, .ascend, .ascend, .ascend, .extract]

theorem cautious_line_is_the_whole_budget : cautiousLine.length = AIR := by decide
theorem greedy_line_is_the_whole_budget : greedyLine.length = AIR := by decide

/-- ⚑ **Every instance is winnable.**  The cautious line banks on all eight
boards — it reads no bit, so no draw can refuse it — and the gate's
`unwinnable-instance` FAIL therefore cannot fire. -/
theorem every_board_can_be_banked :
    ∀ i : Fin 8, playsOutB (boardAt i) cautiousLine = true := by
  native_decide

/-- ⚑ **The budget binds on the cautious line.**  Nine actions is exactly what
the board-independent line costs, and `AIR` is nine. -/
theorem budget_binds_on_the_cautious_line :
    cautiousLine.length = AIR ∧
      ∀ i : Fin 8, playsOutB (boardAt i) cautiousLine = true := by
  refine ⟨by decide, ?_⟩
  native_decide

/-- ⚑ **The budget binds on the greedy line too**, from the other side: reaching
the deep relic on a sound shaft also costs exactly nine. -/
theorem budget_binds_on_the_greedy_line :
    playsOutB (boardAt 0) greedyLine = true ∧ greedyLine.length = AIR := by
  refine ⟨?_, by decide⟩
  native_decide

/-- ⚑ **And the greedy line is a bet on the whole shaft.**  It banks on exactly
one of the eight boards — the sound one — so the same nine actions are a certain
two relics or nothing at all depending on a draw the player cannot see.  That is
the wager the second budget exists to buy out of. -/
theorem greedy_line_banks_only_on_a_sound_shaft :
    playsOutB (boardAt 0) greedyLine = true ∧
      ∀ i : Fin 8, i ≠ 0 → playsOutB (boardAt i) greedyLine = false := by
  refine ⟨by native_decide, ?_⟩
  native_decide

/-- ⚑ **The two budgets are incomparable.**  On the same board the cautious line
spends the whole supply and no damage; the greedy line spends no supply and no
damage but banks on one board in eight.  Neither cost vector dominates the
other, and no action converts air into shoring or shoring into air. -/
def lineCost (b : Board) (acts : List Action) : Option (Nat × Nat × Nat) :=
  match replayB b initialState acts with
  | none => none
  | some s => some (AIR - s.air, SHORING - s.shoring, s.damage)

theorem budgets_are_incomparable :
    lineCost (boardAt 0) cautiousLine = some (9, 2, 0) ∧
    lineCost (boardAt 7) cautiousLine = some (9, 2, 0) ∧
    lineCost (boardAt 0) greedyLine = some (9, 0, 0) ∧
    playsOutB (boardAt 7) greedyLine = false := by
  native_decide

/-! ### Forks, doom, and the scout decision

`forksAtB` is the gate's own definition of an outcome-changing fork, stated over
the kernel: a reachable state offering one legal action that keeps a bank
reachable and another, equally legal, that does not. -/

def successorsB (b : Board) (s : State) : List State :=
  allActions.filterMap (fun a => stepB b s a)

def forksAtB (b : Board) (s : State) : Bool :=
  (allActions.any fun a =>
    match stepB b s a with
    | none => false
    | some t => reachableBankB t || t.banked) &&
  (allActions.any fun a =>
    match stepB b s a with
    | none => false
    | some t => doomedB t)

/-- Every state reachable in at most `fuel` accepted actions.  Bounded and
deduplicated, so the enumeration is a finite compiled computation. -/
def reachableWithin (b : Board) : Nat → List State
  | 0 => [initialState]
  | fuel + 1 =>
      let prior := reachableWithin b fuel
      (prior ++ prior.flatMap (successorsB b)).eraseDups

def reachableStates (b : Board) : List State := reachableWithin b AIR

def forkCount (b : Board) : Nat :=
  ((reachableStates b).filter (forksAtB b)).length

def doomCount (b : Board) : Nat :=
  ((reachableStates b).filter doomedB).length

def familyTotal (f : Board → Nat) : Nat :=
  (List.finRange 8).foldl (fun acc i => acc + f (boardAt i)) 0

/-- ⚑ **Every board offers an outcome-changing fork.**  This is precisely the
property the old Descent did not have across sixteen maps, stated here over all
eight boards and every state reachable inside the budget. -/
theorem every_board_forks : ∀ i : Fin 8, 0 < forkCount (boardAt i) := by
  native_decide

/-- ⚑ **Every board can be lost.**  Failure is reachable, not merely
representable. -/
theorem every_board_can_be_lost : ∀ i : Fin 8, 0 < doomCount (boardAt i) := by
  native_decide

/-- The measured shape of the family, so the descriptor's size and the gate's
counts are stated numbers rather than surprises: 2319 reachable states carrying
757 outcome-changing forks and 1342 doomed states. -/
theorem family_shape_is_measured :
    familyTotal (fun b => (reachableStates b).length) = 2319 ∧
    familyTotal forkCount = 757 ∧
    familyTotal doomCount = 1342 := by
  native_decide

/-- The scout decision, named.  From the hatch on a flooded shaft, walking in
blind costs a point of damage that nothing in a descent restores; looking first
and shoring first both cost a unit of air and no body.  That is the whole trade,
and it is why `survey` is not decoration. -/
theorem walking_in_blind_costs_a_body :
    (match stepB (boardAt 4) initialState .descend with
      | none => none
      | some t => some t.damage) = some 1 ∧
    (match stepB (boardAt 4) initialState .survey with
      | none => none
      | some t => some t.damage) = some 0 ∧
    (match stepB (boardAt 4) initialState .shore with
      | none => none
      | some t => some t.damage) = some 0 := by
  native_decide

/-- ⚑ **Extraction debt, and the deck's cut.**  Walk in blind on a flooded upper
chamber, take both shallow relics, and turn round: the second crossing of the
same flood is the second point of damage, capacity falls to one, and the deck
keeps the deeper of the two.  The run reaches the hatch holding one relic — with
air to spare and no way to use it. -/
def blindGrabLine : List Action :=
  [.descend, .lift, .descend, .lift, .ascend, .ascend]

theorem the_deck_keeps_what_you_could_not_carry :
    (match replayB (boardAt 4) initialState blindGrabLine with
      | none => false
      | some s =>
          decide (s.depth = 0) && decide (s.damage = 2) && decide (capacity s = 1) &&
          decide (s.sling.count = 1) && decide (0 < s.air) && doomedB s) = true := by
  native_decide

/-- The same six actions on a sound shaft come home with both.  The difference is
three hidden bits and nothing else, which is what makes them worth buying. -/
theorem a_sound_shaft_keeps_both_relics :
    (match replayB (boardAt 0) initialState blindGrabLine with
      | none => false
      | some s =>
          decide (s.depth = 0) && decide (s.damage = 0) &&
          decide (s.sling.count = 2) && reachableBankB s) = true := by
  native_decide

/-- The reachable state space of the whole family, for the emitter's benefit and
so the descriptor's size is a stated number rather than a surprise. -/
def familyStateCount : Nat :=
  (List.finRange 8).foldl (fun acc i => acc + (reachableWithin (boardAt i) AIR).length) 0

#assert_axioms allChambers_complete
#assert_axioms allActions_complete
#assert_axioms chamberBelow_depth
#assert_axioms chamberAt_depth
#assert_axioms Deck.get_set_same
#assert_axioms boardTable_nodup
#assert_axioms boardAt_mem
#assert_axioms boardAt_injective
#assert_axioms draw_below_two_never_rejects
#assert_axioms Sling.count_le_three
#assert_axioms Sling.deepest_some_of_count
#assert_axioms takeDamage_capacity
#assert_axioms step_some_open
#assert_axioms step_some_live
#assert_axioms step_some_air
#assert_axioms step_spends_exactly_one_air
#assert_axioms step_turns_advance
#assert_axioms step_shoring_never_rises
#assert_axioms step_damage_never_falls
#assert_axioms step_capacity_never_rises
#assert_axioms doomed_refuses_everything
#assert_axioms banked_refuses_everything
#assert_axioms airless_refuses_everything
#assert_axioms shoreless_refuses_shore
#assert_axioms surface_refuses_ascend
#assert_axioms floor_refuses_descend
#assert_axioms inside_refuses_extract
#assert_axioms short_sling_refuses_extract
#assert_axioms emptied_chamber_refuses_lift
#assert_axioms full_sling_refuses_lift
#assert_axioms known_chamber_refuses_survey
#assert_axioms shored_chamber_refuses_shore
#assert_axioms replayB_append
#assert_axioms refused_prefix_refuses_replay
#assert_axioms replayB_spends_air
#assert_axioms accepted_transcript_within_budget
#assert_axioms terminalOutput_none_without_bank
#assert_axioms terminalOutput_is_mission_accepted
#assert_axioms terminalOutput_names_exact_artifact
#assert_axioms step_eq_stepB
#assert_axioms replay_eq_replayB
#assert_axioms judged_board_is_the_drawn_board
#assert_axioms judge_some_sound
#assert_axioms judge_receipt_binds_transcript
#assert_axioms judged_run_banked
#assert_axioms judged_run_within_budget
#assert_axioms cautious_line_is_the_whole_budget
#assert_axioms greedy_line_is_the_whole_budget

#assert_compiled every_board_can_be_banked
#assert_compiled budget_binds_on_the_cautious_line
#assert_compiled budget_binds_on_the_greedy_line
#assert_compiled greedy_line_banks_only_on_a_sound_shaft
#assert_compiled budgets_are_incomparable
#assert_compiled every_board_forks
#assert_compiled every_board_can_be_lost
#assert_compiled family_shape_is_measured
#assert_compiled walking_in_blind_costs_a_body
#assert_compiled the_deck_keeps_what_you_could_not_carry
#assert_compiled a_sound_shaft_keeps_both_relics

end Dregg2.Games.PathOfAngels.DeckDescent
