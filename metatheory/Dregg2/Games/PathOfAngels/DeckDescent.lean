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

## The shaft forks

⚑ 2026-08-05, second pass.  The first shaft was a straight line, so "route
commitment" was only *paying twice* — there was no option a descent could close
behind it.  There is now a junction: the mouth chamber has two children, and a
body that commits to one spur pays two units of air to be standing at the other.
`sweepLine` is the transcript that visits both, and it costs the entire budget.

⚑ 2026-08-06, third pass.  The junction existed but its branches were MIRROR
IMAGES: same depth, same parent, same one relic, crossing table invariant under
the swap — so cautious-east was cautious-west relabelled and the branch only
became a decision AFTER a bit was revealed.  `scripts/poa-design-gate.py`
measured the candidate repairs over its own reconstruction: pricing a spur
higher (extra air to enter, with or without an extra relic behind the toll)
turns the 18/18 junction split into 26/0 — a labelled corridor nobody takes —
while a SECOND RELIC on the east spur at the SAME distance breaks the mirror and
keeps the branch: all eight draws become distinct games, outcome-changing forks
rise 1145 → 1360, the junction splits 18/19, and the clock still binds at nine.
So the east spur holds two relics, the asymmetry is in the PRIZE and never the
PRICE (`asymmetry_is_prize_not_price`), and `Sling`/`ChamberState` count relics
per chamber instead of flagging them.

## The four properties this design is accountable for

1. **Two incomparable budgets.**  `AIR` is the clock and `SHORING` is the supply.
   No action converts one into the other, and `budgets_are_incomparable` exhibits
   two accepted lines that trade them in opposite directions.
2. **Information is purchasable.**  A chamber's passage is hidden until `survey`
   spends a unit of air on it, or until a body walks into it.  `shore` may be
   spent blind, so the real fork is *air to learn* against *supply to not need
   to*.
3. **Route commitment.**  Two kinds, and the junction is what adds the second.
   Every chamber entered must be crossed again on the way out, and an unshored
   flood damages on both crossings; and beyond the mouth the shaft *branches*, so
   choosing a spur puts the other one two units of air away.
4. **Extraction is the point.**  A relic in the sling is worth nothing; a relic
   through the hatch is the find.  Damage lowers carrying capacity, and a
   crossing that overruns it leaves the deepest relic on the deck.

## What the budget is sized for

`AIR = 9` is not slack.  FOUR different lines cost exactly nine and no fewer:
the cautious line down the west spur, the same discipline down the east spur,
the deep-east line that shores twice and lifts BOTH east relics, and the sweep
that takes the mouth relic out of the plan and visits both spurs instead.  The
first three bank on every board because they read no bit; the sweep banks on one
board in eight because it reads three.  Same budget, opposite wagers.
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

/-! ## The deck

A rooted tree, not a line.  The hatch has one child — the mouth — and the mouth
has two: the west spur and the east spur.  Every edge is walked in both
directions, so `Node.parent` is the only way back up and there is no shortcut
between spurs. -/

/-- The three chambers.  `mouth` is the one every descent passes through; `west`
and `east` are the spurs it opens onto. -/
inductive Chamber where
  | mouth
  | west
  | east
deriving Repr, DecidableEq

def allChambers : List Chamber := [.mouth, .west, .east]

theorem allChambers_complete (c : Chamber) : c ∈ allChambers := by
  cases c <;> simp [allChambers]

/-- Where a body can be: through the hatch, or in a chamber. -/
inductive Node where
  | hatch
  | inside (chamber : Chamber)
deriving Repr, DecidableEq

def allNodes : List Node :=
  Node.hatch :: allChambers.map Node.inside

theorem allNodes_complete (n : Node) : n ∈ allNodes := by
  cases n with
  | hatch => simp [allNodes]
  | inside c => cases c <;> simp [allNodes, allChambers]

/-- Climbing.  Total, and the hatch is its own parent only in the sense that
`ascend` is refused there — see `surface_refuses_ascend`. -/
def Node.parent : Node → Node
  | .hatch => .hatch
  | .inside .mouth => .hatch
  | .inside .west => .inside .mouth
  | .inside .east => .inside .mouth

/-- The child on the main line: hatch to mouth, mouth to west.  The spurs are
leaves. -/
def Node.mainChild : Node → Option Chamber
  | .hatch => some .mouth
  | .inside .mouth => some .west
  | .inside .west => none
  | .inside .east => none

/-- The child on the spur.  It exists at exactly one node, and that is the whole
of the junction. -/
def Node.eastChild : Node → Option Chamber
  | .inside .mouth => some .east
  | _ => none

/-- Crossings between a node and the hatch — the extraction debt owed from here. -/
def Node.debt : Node → Nat
  | .hatch => 0
  | .inside .mouth => 1
  | .inside .west => 2
  | .inside .east => 2

def Chamber.debt (c : Chamber) : Nat := (Node.inside c).debt

/-- The junction is real: the mouth has two distinct children, and they are the
only two chambers that are not the mouth. -/
theorem mouth_is_a_junction :
    (Node.inside Chamber.mouth).mainChild = some Chamber.west ∧
    (Node.inside Chamber.mouth).eastChild = some Chamber.east ∧
    Chamber.west ≠ Chamber.east := by
  refine ⟨rfl, rfl, by decide⟩

/-- Only the mouth forks: everywhere else the spur action has no target, so the
nine-action alphabet collapses to the ordinary six away from the junction. -/
theorem only_the_mouth_forks (n : Node) (h : n ≠ Node.inside Chamber.mouth) :
    n.eastChild = none := by
  cases n with
  | hatch => rfl
  | inside c => cases c <;> first | rfl | exact absurd rfl h

/-- The spurs are leaves, so a body in one is two units of air from the other.
This is the commitment: it is not that the other spur is forbidden, it is that
reaching it costs the budget the run was going to spend on coming home. -/
theorem spurs_are_leaves :
    (Node.inside Chamber.west).mainChild = none ∧
    (Node.inside Chamber.west).eastChild = none ∧
    (Node.inside Chamber.east).mainChild = none ∧
    (Node.inside Chamber.east).eastChild = none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem crossing_between_spurs_costs_two :
    (Node.inside Chamber.west).parent = Node.inside Chamber.mouth ∧
    (Node.inside Chamber.east).parent = Node.inside Chamber.mouth ∧
    Chamber.west.debt = 2 ∧ Chamber.east.debt = 2 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- How many relics each chamber holds on a fresh deck.  ⚑ The east spur holds
TWO — this is the measured repair of the west/east mirror.  The gate found that
making a spur more EXPENSIVE kills the branch (nobody takes a priced spur: the
junction split goes 26/0), while a second relic at the SAME distance breaks the
symmetry and keeps both directions live (18/19, family forks 1145 → 1360). -/
def Chamber.relicCount : Chamber → Nat
  | .mouth => 1
  | .west => 1
  | .east => 2

/-- ⚑ **The spurs differ in prize, never in price.**  Both sit the same two
crossings from the hatch; what tells them apart is what they hold.  A spur made
asymmetric by COST is a corridor with a toll — this is the shape the gate
measured as the one that works. -/
theorem asymmetry_is_prize_not_price :
    Chamber.west.debt = Chamber.east.debt ∧
    Chamber.west.relicCount ≠ Chamber.east.relicCount := by
  refine ⟨rfl, by decide⟩

/-- The east spur alone meets the bank target; the west spur alone cannot.
Committing east is a self-contained expedition, committing west is a leg of a
larger one — which is why the branch is a real decision before any bit is
read. -/
theorem the_east_spur_is_an_expedition_by_itself :
    BANK_TARGET ≤ Chamber.east.relicCount ∧ Chamber.west.relicCount < BANK_TARGET := by
  refine ⟨by decide, by decide⟩

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

/-- Per-chamber record: what is known about the passage, and how many of its
relics have left the deck.  A COUNT, not a flag: the east spur holds two relics,
so "is it emptied" is `relicCount ≤ relicsTaken` and not a Bool.  Three of these
are the whole board state. -/
structure ChamberState where
  lore : Lore
  relicsTaken : Nat
deriving Repr, DecidableEq

def freshChamber : ChamberState := { lore := .dark, relicsTaken := 0 }

/-- The three chambers, stored as named fields rather than a list so that
`DecidableEq` and `decide` stay cheap. -/
structure Deck where
  mouth : ChamberState
  west : ChamberState
  east : ChamberState
deriving Repr, DecidableEq

def freshDeck : Deck :=
  { mouth := freshChamber, west := freshChamber, east := freshChamber }

def Deck.get (d : Deck) : Chamber → ChamberState
  | .mouth => d.mouth
  | .west => d.west
  | .east => d.east

def Deck.set (d : Deck) : Chamber → ChamberState → Deck
  | .mouth, s => { d with mouth := s }
  | .west, s => { d with west := s }
  | .east, s => { d with east := s }

theorem Deck.get_set_same (d : Deck) (c : Chamber) (s : ChamberState) :
    (d.set c s).get c = s := by
  cases c <;> rfl

/-! ## The instance -/

/-- One instance: which chambers flood.  Eight of them, and the descriptor names
none of them — it names both successors of every row that consults one. -/
structure Board where
  mouth : Passage
  west : Passage
  east : Passage
deriving Repr, DecidableEq

def Board.get (b : Board) : Chamber → Passage
  | .mouth => b.mouth
  | .west => b.west
  | .east => b.east

/-- The passage bit read back as the lore a look would establish. -/
def Board.lore (b : Board) (c : Chamber) : Lore :=
  match b.get c with
  | .sound => .sound
  | .flooded => .flooded

def boardTable : List Board :=
  [ { mouth := .sound,   west := .sound,   east := .sound }
  , { mouth := .sound,   west := .sound,   east := .flooded }
  , { mouth := .sound,   west := .flooded, east := .sound }
  , { mouth := .sound,   west := .flooded, east := .flooded }
  , { mouth := .flooded, west := .sound,   east := .sound }
  , { mouth := .flooded, west := .sound,   east := .flooded }
  , { mouth := .flooded, west := .flooded, east := .sound }
  , { mouth := .flooded, west := .flooded, east := .flooded } ]

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
  some { mouth := passageOfDraw a, west := passageOfDraw b, east := passageOfDraw c }

def boardFromRunSeed (runSeed : Digest32) : Board :=
  (boardFromRunSeed? runSeed).getD { mouth := .sound, west := .sound, east := .sound }

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

/-- The sling.  How many of each chamber's relics are in hand — counts, not
flags, because the east spur holds two.  Identity survives the counting: the
relics of one chamber leave the deck in a declared order and forfeit in the
reverse of it (see `Config.slingRelics`), so a count still names WHICH relics
are held and the receipt still names which one fell. -/
structure Sling where
  mouth : Nat
  west : Nat
  east : Nat
deriving Repr, DecidableEq

def emptySling : Sling := { mouth := 0, west := 0, east := 0 }

def Sling.get (s : Sling) : Chamber → Nat
  | .mouth => s.mouth
  | .west => s.west
  | .east => s.east

def Sling.holds (s : Sling) (c : Chamber) : Bool := decide (0 < s.get c)

def Sling.add (s : Sling) : Chamber → Sling
  | .mouth => { s with mouth := s.mouth + 1 }
  | .west => { s with west := s.west + 1 }
  | .east => { s with east := s.east + 1 }

def Sling.drop (s : Sling) : Chamber → Sling
  | .mouth => { s with mouth := s.mouth - 1 }
  | .west => { s with west := s.west - 1 }
  | .east => { s with east := s.east - 1 }

def Sling.count (s : Sling) : Nat := s.mouth + s.west + s.east

/-- What the deck takes when a crossing overruns capacity: one relic of whatever
was reached furthest for.  The spurs are equally far, so the tie is broken
west-then-east and that order is DECLARED here rather than falling out of a
field ordering. -/
def Sling.forfeit (s : Sling) : Option Chamber :=
  if 0 < s.west then some .west
  else if 0 < s.east then some .east
  else if 0 < s.mouth then some .mouth
  else none

/-- ⚑ What the deck takes is what the run reached furthest for: nothing still in
the sling is deeper than the relic forfeited.  Stated over every chamber the
sling holds, not just the one that fell. -/
theorem Sling.forfeit_is_deepest (s : Sling) (c held : Chamber)
    (h : s.forfeit = some c) (hheld : s.holds held = true) : held.debt ≤ c.debt := by
  simp only [Sling.forfeit] at h
  simp only [Sling.holds, decide_eq_true_eq] at hheld
  split at h
  · -- the west relic fell, and nothing is deeper than a spur
    cases h; cases held <;> decide
  · split at h
    · cases h; cases held <;> decide
    · split at h
      · -- the mouth relic fell, so the sling held nothing from a spur
        cases h
        cases held with
        | mouth => exact Nat.le_refl _
        | west => simp only [Sling.get] at hheld; omega
        | east => simp only [Sling.get] at hheld; omega
      · exact absurd h (by simp)

theorem Sling.forfeit_some_of_count (s : Sling) (h : 0 < s.count) :
    (s.forfeit).isSome = true := by
  simp only [Sling.count] at h
  simp only [Sling.forfeit]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · omega

structure State where
  position : Node
  air : Nat
  shoring : Nat
  damage : Nat
  sling : Sling
  deck : Deck
  banked : Bool
deriving Repr, DecidableEq

def initialState : State where
  position := .hatch
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
*every* board still consistent with what it has seen.  `reachableBankB` is
therefore computed against the most generous continuation: every dark chamber is
assumed sound, so no crossing costs anything.  A state it refuses is one no board
rescues. -/

/-- Crossings between two nodes of the shaft.  Enumerated rather than derived:
the tree has four nodes and an explicit table cannot drift from the topology the
transition walks. -/
def Node.dist : Node → Node → Nat
  | .hatch,         .hatch        => 0
  | .hatch,         .inside c     => c.debt
  | .inside c,      .hatch        => c.debt
  | .inside .mouth, .inside .mouth => 0
  | .inside .mouth, .inside .west  => 1
  | .inside .mouth, .inside .east  => 1
  | .inside .west,  .inside .mouth => 1
  | .inside .east,  .inside .mouth => 1
  | .inside .west,  .inside .west  => 0
  | .inside .east,  .inside .east  => 0
  | .inside .west,  .inside .east  => 2
  | .inside .east,  .inside .west  => 2

theorem Node.dist_self (n : Node) : n.dist n = 0 := by
  cases n with
  | hatch => rfl
  | inside c => cases c <;> rfl

/-- ⚑ The junction, priced.  Standing in one spur, the other is two crossings
away — the same two crossings the run needs to come home.  This is the number
that makes a spur choice a commitment rather than a label. -/
theorem the_other_spur_costs_the_way_home :
    (Node.inside Chamber.west).dist (.inside Chamber.east) = 2 ∧
    (Node.inside Chamber.west).dist .hatch = 2 := by
  refine ⟨rfl, rfl⟩

/-- Air spent walking `seq` in order from `p` and then coming home. -/
def walkCost (p : Node) (seq : List Chamber) : Nat :=
  let stepped := seq.foldl
    (fun (acc : Nat × Node) c => (acc.1 + acc.2.dist (.inside c), Node.inside c)) (0, p)
  stepped.1 + stepped.2.dist .hatch

/-- Relics a chamber still holds. -/
def availableRelics (s : State) (c : Chamber) : Nat :=
  c.relicCount - (s.deck.get c).relicsTaken

/-- Every ordered visit plan over the chambers still holding relics that
collects exactly `need` of them.  A chamber appears in a plan once per relic
lifted there, so `[east, east]` is the plan that walks to the east spur and
lifts twice — `Node.dist_self` prices the second visit at zero, which is what
"a second relic at the SAME distance" means for the reserve. -/
def visitPlans (s : State) (need : Nat) : List (List Chamber) :=
  let avail := allChambers.filter (fun c => 0 < availableRelics s c)
  if need = 1 then avail.map (fun a => [a])
  else avail.flatMap (fun a =>
    (if 2 ≤ availableRelics s a then [[a, a]] else []) ++
    (avail.filter (fun b => b != a)).map (fun b => [a, b]))

/-- Air needed to bank the target from here, on the most favourable board still
consistent with what the run has seen: the cheapest ordered walk that collects
the relics still needed and ends at the hatch, plus one lift per relic and the
extraction. -/
def cheapestBank (s : State) : Nat :=
  if BANK_TARGET ≤ s.sling.count then
    s.position.dist .hatch + 1
  else
    let need := BANK_TARGET - s.sling.count
    (visitPlans s need).foldl
      (fun best seq => Nat.min best (walkCost s.position seq + need + 1)) (AIR + 1)

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
  /-- Spend one air reading the passage of the chamber on the main line below. -/
  | survey
  /-- The same look, down the spur.  Legal only at the junction. -/
  | surveyEast
  /-- Spend one air and one shoring making the main-line chamber below safe.
  Legal on a dark chamber as well as a known flood: supply may be spent instead
  of the air a look would cost, and that trade is the second budget's whole
  reason to exist. -/
  | shore
  | shoreEast
  /-- Spend one air going down the main line.  A dark chamber resolves on the way
  in, and an unshored flood costs a point of damage. -/
  | descend
  /-- ⚑ The commitment.  From the junction this enters the east spur, and a body
  in one spur is two crossings from the other. -/
  | descendEast
  /-- Spend one air taking this chamber's relic. -/
  | lift
  /-- Spend one air climbing.  The chamber being left is crossed a second time,
  and an unshored flood charges again. -/
  | ascend
  /-- Spend one air coming through the hatch.  Terminal. -/
  | extract
deriving Repr, DecidableEq

def allActions : List Action :=
  [.survey, .surveyEast, .shore, .shoreEast, .descend, .descendEast, .lift, .ascend,
   .extract]

theorem allActions_complete (a : Action) : a ∈ allActions := by
  cases a <;> simp [allActions]

/-- Which chamber an action reaches for, from a given node.  The spur variants
resolve to `none` everywhere but the junction, which is why the nine-action
alphabet is an ordinary six away from it. -/
def Action.target : Action → Node → Option Chamber
  | .surveyEast, n => n.eastChild
  | .shoreEast, n => n.eastChild
  | .descendEast, n => n.eastChild
  | .survey, n => n.mainChild
  | .shore, n => n.mainChild
  | .descend, n => n.mainChild
  | _, _ => none

/-- A crossing that costs a body.  Damage rises by one, capacity falls by one,
and if the sling no longer fits, the deck keeps what was reached furthest for. -/
def takeDamage (s : State) : State :=
  let damage := s.damage + 1
  let cap := BASE_CAPACITY - damage
  let sling :=
    if cap < s.sling.count then
      match s.sling.forfeit with
      | some c => s.sling.drop c
      | none => s.sling
    else s.sling
  { s with damage, sling }

/-- Crossing a chamber with lore `l`: pay a body if it floods, otherwise pass. -/
def cross (s : State) (l : Lore) : State :=
  if l.damaging then takeDamage s else s

/-- The action-specific half of openness.  `liveB` and the clock are factored out
into `openB` below so that "a run that is over spends nothing" and "every action
costs air" are each ONE conjunct in ONE place. -/
def openKindB (s : State) (a : Action) : Bool :=
  match a with
  | .survey | .surveyEast =>
      match a.target s.position with
      | none => false
      | some c => decide ((s.deck.get c).lore = Lore.dark)
  | .shore | .shoreEast =>
      decide (0 < s.shoring) &&
      (match a.target s.position with
       | none => false
       | some c =>
           decide ((s.deck.get c).lore = Lore.dark ∨ (s.deck.get c).lore = Lore.flooded))
  | .descend | .descendEast =>
      (match a.target s.position with
       | none => false
       | some _ => true)
  | .lift =>
      (match s.position with
       | .hatch => false
       | .inside c =>
           decide ((s.deck.get c).relicsTaken < c.relicCount) &&
             decide (s.sling.count + 1 ≤ capacity s))
  | .ascend => decide (s.position ≠ Node.hatch)
  | .extract =>
      decide (s.position = Node.hatch) && decide (BANK_TARGET ≤ s.sling.count)

/-- Openness, in three conjuncts that never move: the run is still live, the
clock has a unit left, and the action itself applies here. -/
def openB (s : State) (a : Action) : Bool :=
  liveB s && decide (0 < s.air) && openKindB s a

/-- The raw effect of an action, with openness already decided.  Every branch
spends exactly one unit of air, which is why `step_spends_exactly_one_air` is a
single uniform proof rather than nine. -/
def transitionB (b : Board) (s : State) (a : Action) : Option State :=
  match a with
  | .survey | .surveyEast =>
      match a.target s.position with
      | none => none
      | some c =>
          let cs := s.deck.get c
          some { s with
            air := s.air - 1
            deck := s.deck.set c { cs with lore := b.lore c } }
  | .shore | .shoreEast =>
      match a.target s.position with
      | none => none
      | some c =>
          let cs := s.deck.get c
          some { s with
            air := s.air - 1
            shoring := s.shoring - 1
            deck := s.deck.set c { cs with lore := Lore.shored } }
  | .descend | .descendEast =>
      match a.target s.position with
      | none => none
      | some c =>
          let cs := s.deck.get c
          -- A dark chamber is read by the body that walks into it.
          let lore := if cs.lore = Lore.dark then b.lore c else cs.lore
          some (cross { s with
            air := s.air - 1
            position := Node.inside c
            deck := s.deck.set c { cs with lore } } lore)
  | .lift =>
      match s.position with
      | .hatch => none
      | .inside c =>
          let cs := s.deck.get c
          some { s with
            air := s.air - 1
            sling := s.sling.add c
            deck := s.deck.set c { cs with relicsTaken := cs.relicsTaken + 1 } }
  | .ascend =>
      match s.position with
      | .hatch => none
      | .inside c =>
          some (cross { s with air := s.air - 1, position := s.position.parent }
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
theorem takeDamage_position (s : State) : (takeDamage s).position = s.position := rfl
theorem takeDamage_damage (s : State) : (takeDamage s).damage = s.damage + 1 := rfl

theorem cross_air (s : State) (l : Lore) : (cross s l).air = s.air := by
  unfold cross; split
  · exact takeDamage_air s
  · rfl

theorem cross_shoring (s : State) (l : Lore) : (cross s l).shoring = s.shoring := by
  unfold cross; split
  · exact takeDamage_shoring s
  · rfl

theorem cross_position (s : State) (l : Lore) : (cross s l).position = s.position := by
  unfold cross; split
  · exact takeDamage_position s
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
  case survey | surveyEast | shore | shoreEast | lift =>
    split at ht
    · exact absurd ht (by simp)
    · simp only [Option.some.injEq] at ht; subst ht; simp; omega
  case descend | descendEast | ascend =>
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
  case survey | surveyEast | shore | shoreEast | lift =>
    split at ht
    · exact absurd ht (by simp)
    · simp only [Option.some.injEq] at ht; subst ht; simp
  case descend | descendEast | ascend =>
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
  case survey | surveyEast | shore | shoreEast | lift =>
    split at ht
    · exact absurd ht (by simp)
    · simp only [Option.some.injEq] at ht; subst ht; simp
  case descend | descendEast | ascend =>
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

theorem surface_refuses_ascend (b : Board) (s : State) (h : s.position = Node.hatch) :
    stepB b s .ascend = none := by
  exact not_open_refuses b s .ascend (by simp [openB, openKindB, h])

/-- ⚑ **A spur has no spur.**  The east actions are refused everywhere but the
junction, so the fork exists at exactly one node and a run cannot slide sideways
between spurs. -/
theorem only_the_junction_accepts_the_spur (b : Board) (s : State)
    (h : s.position ≠ Node.inside Chamber.mouth) :
    stepB b s .descendEast = none ∧ stepB b s .surveyEast = none ∧
      stepB b s .shoreEast = none := by
  have hnone : s.position.eastChild = none := only_the_mouth_forks s.position h
  refine ⟨not_open_refuses b s .descendEast ?_, not_open_refuses b s .surveyEast ?_,
    not_open_refuses b s .shoreEast ?_⟩
  · simp [openB, openKindB, Action.target, hnone]
  · simp [openB, openKindB, Action.target, hnone]
  · simp [openB, openKindB, Action.target, hnone]

/-- A leaf refuses the main line too, so the spurs are ends and not corridors. -/
theorem a_spur_refuses_going_deeper (b : Board) (s : State) (c : Chamber)
    (hpos : s.position = Node.inside c) (hleaf : c ≠ Chamber.mouth) :
    stepB b s .descend = none := by
  have hnone : s.position.mainChild = none := by
    rw [hpos]; cases c <;> first | rfl | exact absurd rfl hleaf
  exact not_open_refuses b s .descend (by simp [openB, openKindB, Action.target, hnone])

theorem inside_refuses_extract (b : Board) (s : State) (h : s.position ≠ Node.hatch) :
    stepB b s .extract = none := by
  exact not_open_refuses b s .extract (by simp [openB, openKindB, h])

/-- The reward gate is the bank target and nothing else: a run cannot come
through the hatch with one relic and be paid. -/
theorem short_sling_refuses_extract (b : Board) (s : State)
    (h : s.sling.count < BANK_TARGET) : stepB b s .extract = none := by
  exact not_open_refuses b s .extract
    (by simp [openB, openKindB, Nat.not_le.mpr h])

theorem hatch_refuses_lift (b : Board) (s : State) (h : s.position = Node.hatch) :
    stepB b s .lift = none := by
  exact not_open_refuses b s .lift (by simp [openB, openKindB, h])

/-- A chamber already emptied refuses another lift, so a relic is a relic and
not a renewable meter.  "Emptied" now means the COUNT is exhausted: the mouth
and west after one lift, the east spur after two. -/
theorem emptied_chamber_refuses_lift (b : Board) (s : State) (c : Chamber)
    (hpos : s.position = Node.inside c)
    (h : c.relicCount ≤ (s.deck.get c).relicsTaken) :
    stepB b s .lift = none := by
  exact not_open_refuses b s .lift
    (by simp [openB, openKindB, hpos, Nat.not_lt.mpr h])

/-- Over capacity, the sling refuses.  This is the rule that makes damage a
carrying constraint rather than a score. -/
theorem full_sling_refuses_lift (b : Board) (s : State)
    (h : capacity s < s.sling.count + 1) : stepB b s .lift = none := by
  refine not_open_refuses b s .lift ?_
  simp only [openB, openKindB, Bool.and_eq_false_iff]
  right
  cases hpos : s.position with
  | hatch => rfl
  | inside c => simp [Nat.not_le.mpr h]

/-- A chamber whose passage is already established refuses a second look. -/
theorem known_chamber_refuses_survey (b : Board) (s : State) (c : Chamber)
    (hbelow : s.position.mainChild = some c) (h : (s.deck.get c).lore ≠ Lore.dark) :
    stepB b s .survey = none := by
  exact not_open_refuses b s .survey
    (by simp [openB, openKindB, Action.target, hbelow, h])

/-- A shored chamber refuses a second shoring, so supply cannot be burned to no
effect and the two-unit budget really is two decisions. -/
theorem shored_chamber_refuses_shore (b : Board) (s : State) (c : Chamber)
    (hbelow : s.position.mainChild = some c)
    (h : (s.deck.get c).lore = Lore.shored) :
    stepB b s .shore = none := by
  refine not_open_refuses b s .shore ?_
  simp only [openB, openKindB, Bool.and_eq_false_iff]
  right
  right
  simp [Action.target, hbelow, h]

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
  /-- The relics each chamber holds — four of them, because the east spur holds
  two.  Declared in the config, checked against the mission's allowlist by
  `relics_declared`, so a run cannot invent a relic. -/
  mouthRelic : RelicId
  westRelic : RelicId
  eastRelic : RelicId
  /-- The east spur's second relic.  East relics leave the deck in a DECLARED
  order — `eastRelic` on the first lift, `eastSecondRelic` on the second — and a
  forfeit returns the later-lifted one, so an east count of one always means
  `eastRelic` is the one in hand and the receipt still names which relic fell. -/
  eastSecondRelic : RelicId
  reward : Contribution
  reward_accepted : mission.acceptsContribution reward = true
  relics_distinct : mouthRelic ≠ westRelic ∧ westRelic ≠ eastRelic ∧
    mouthRelic ≠ eastRelic ∧ eastSecondRelic ≠ mouthRelic ∧
    eastSecondRelic ≠ westRelic ∧ eastSecondRelic ≠ eastRelic
  relics_declared :
    mouthRelic ∈ mission.allowedRelics ∧ westRelic ∈ mission.allowedRelics ∧
    eastRelic ∈ mission.allowedRelics ∧ eastSecondRelic ∈ mission.allowedRelics
  /-- ⚑ The played board is the one the precommitted seed draws.  A host cannot
  re-flood the deck after reading the transcript. -/
  board_eq : board = boardFromRunSeed mission.runSeed

/-- The relics a sling's counts name, under the declared lift/forfeit order:
one east relic in hand is always `eastRelic`, the second is `eastSecondRelic`. -/
def Config.slingRelics (cfg : Config) (s : Sling) : List RelicId :=
  (if 0 < s.mouth then [cfg.mouthRelic] else []) ++
  (if 0 < s.west then [cfg.westRelic] else []) ++
  (if 0 < s.east then [cfg.eastRelic] else []) ++
  (if 2 ≤ s.east then [cfg.eastSecondRelic] else [])

theorem Config.slingRelics_length_le (cfg : Config) (s : Sling) :
    (cfg.slingRelics s).length ≤ 4 := by
  simp only [Config.slingRelics, List.length_append]
  split <;> split <;> split <;> split <;> simp

/-- The relics a sling brings through the hatch. -/
def Config.bankedRelics (cfg : Config) (s : Sling) : Finset RelicId :=
  (cfg.slingRelics s).toFinset

def Config.terminalContribution (cfg : Config) (s : State) : Contribution :=
  { cfg.reward with
    relics := cfg.bankedRelics s.sling
    relics_bounded := by
      have : (cfg.bankedRelics s.sling).card ≤ 4 := by
        simp only [Config.bankedRelics]
        exact le_trans (List.toFinset_card_le _) (Config.slingRelics_length_le cfg s.sling)
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

/-- The transcript alphabet.  One code per action, spur variants distinct from
their main-line twins, so a receipt records WHICH spur a run committed to. -/
def actionCode : Action → Nat
  | .survey => 0
  | .surveyEast => 1
  | .shore => 2
  | .shoreEast => 3
  | .descend => 4
  | .descendEast => 5
  | .lift => 6
  | .ascend => 7
  | .extract => 8

theorem actionCode_injective (a a' : Action) (h : actionCode a = actionCode a') :
    a = a' := by
  cases a <;> cases a' <;> simp_all [actionCode]

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

/-- The cautious line down the WEST spur: buy safety with supply rather than
time, twice.  Nine actions, and it works on every board because it reads no
bit. -/
def cautiousWestLine : List Action :=
  [.shore, .descend, .lift, .shore, .descend, .lift, .ascend, .ascend, .extract]

/-- The same discipline down the EAST spur, taking the mouth relic and ONE east
relic.  Also nine, also board-independent — so the spur choice is a genuine
choice and not a right answer. -/
def cautiousEastLine : List Action :=
  [.shore, .descend, .lift, .shoreEast, .descendEast, .lift, .ascend, .ascend,
   .extract]

/-- ⚑ The line the second relic creates: leave the mouth relic on the deck,
shore both crossings, and lift the east spur TWICE.  Nine actions, board-
independent, and it never touches west — the east commitment is a complete
expedition of its own, which is what makes the junction a decision before any
bit is read. -/
def deepEastLine : List Action :=
  [.shore, .descend, .shoreEast, .descendEast, .lift, .lift, .ascend, .ascend,
   .extract]

/-- ⚑ The sweep: leave the mouth relic where it is, walk in blind, and take BOTH
spurs.  Nine actions again — the two extra crossings between spurs are paid for
by not shoring and not lifting at the mouth — and it reads all three bits. -/
def sweepLine : List Action :=
  [.descend, .descend, .lift, .ascend, .descendEast, .lift, .ascend, .ascend,
   .extract]

theorem every_line_is_the_whole_budget :
    cautiousWestLine.length = AIR ∧ cautiousEastLine.length = AIR ∧
      deepEastLine.length = AIR ∧ sweepLine.length = AIR := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- ⚑ **Every instance is winnable, down either spur.**  Both cautious lines bank
on all eight boards, so no draw is a dead mission and the spur choice is never
forced. -/
theorem every_board_can_be_banked :
    (∀ i : Fin 8, playsOutB (boardAt i) cautiousWestLine = true) ∧
    (∀ i : Fin 8, playsOutB (boardAt i) cautiousEastLine = true) := by
  refine ⟨?_, ?_⟩
  · native_decide
  · native_decide

/-- ⚑ **The east spur alone is an expedition.**  The deep-east line banks the
target on all eight boards without lifting the mouth relic or entering west.
There is no west twin of this line — one relic short — so the two branches of
the junction differ BEFORE any bit is revealed, in what committing to them can
win, not in what reaching them costs. -/
theorem the_second_relic_makes_east_bankable_alone :
    deepEastLine.length = AIR ∧
    (∀ i : Fin 8, playsOutB (boardAt i) deepEastLine = true) := by
  refine ⟨by decide, ?_⟩
  native_decide

/-- ⚑ **The budget binds on the cautious lines.** -/
theorem budget_binds_on_the_cautious_lines :
    cautiousWestLine.length = AIR ∧ cautiousEastLine.length = AIR ∧
      ∀ i : Fin 8, playsOutB (boardAt i) cautiousWestLine = true := by
  refine ⟨by decide, by decide, ?_⟩
  native_decide

/-- ⚑ **And on the sweep, from the other side.**  Visiting both spurs costs
exactly the same nine actions, and banks on exactly one board in eight — the
sound one.  Same budget, opposite wager. -/
theorem sweep_costs_the_budget_and_banks_on_one_board :
    sweepLine.length = AIR ∧
    playsOutB (boardAt 0) sweepLine = true ∧
    (∀ i : Fin 8, i ≠ 0 → playsOutB (boardAt i) sweepLine = false) := by
  refine ⟨by decide, by native_decide, ?_⟩
  native_decide

/-- ⚑ **The two budgets are incomparable.**  The cautious lines spend the whole
supply and no body; the sweep spends no supply and, on the board where it works,
no body either — but it wagers three hidden bits to do it.  Neither cost vector
dominates the other, and no action converts air into shoring or shoring into
air. -/
def lineCost (b : Board) (acts : List Action) : Option (Nat × Nat × Nat) :=
  match replayB b initialState acts with
  | none => none
  | some s => some (AIR - s.air, SHORING - s.shoring, s.damage)

theorem budgets_are_incomparable :
    lineCost (boardAt 0) cautiousWestLine = some (9, 2, 0) ∧
    lineCost (boardAt 7) cautiousWestLine = some (9, 2, 0) ∧
    lineCost (boardAt 0) sweepLine = some (9, 0, 0) ∧
    playsOutB (boardAt 7) sweepLine = false := by
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

/-- Every state reachable in at most `fuel` accepted actions. -/
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

/-- ⚑ **Every board offers an outcome-changing fork.** -/
theorem every_board_forks : ∀ i : Fin 8, 0 < forkCount (boardAt i) := by
  native_decide

/-- ⚑ **Every board can be lost.** -/
theorem every_board_can_be_lost : ∀ i : Fin 8, 0 < doomCount (boardAt i) := by
  native_decide

/-- The measured shape of the family, per board and summed.  These are the
numbers `scripts/poa-design-gate.py` must independently arrive at from the
emitted table; they are stated here so a disagreement is loud.  Before the
east spur's second relic the triple was 3905 / 1145 / 2059. -/
theorem family_shape_is_measured :
    familyTotal (fun b => (reachableStates b).length) = 4688 ∧
    familyTotal forkCount = 1360 ∧
    familyTotal doomCount = 2469 := by
  native_decide

/-- One board's census, as a comparable shape. -/
def boardShape (b : Board) : Nat × Nat × Nat :=
  ((reachableStates b).length, forkCount b, doomCount b)

/-- ⚑ **The mirror is broken.**  All eight draws are now distinct games: no two
boards share a (reachable, forks, doomed) shape.  Before the second relic a
board and its west/east reflection were the same game and the eight draws
collapsed to six shapes — 0.42 of a bit of the instance doing no work, the
gate's `the-family-collapses` finding.  This is the kernel-side statement whose
gate-side twin is `distinct_board_shapes = 8`. -/
theorem the_mirror_is_broken :
    ((List.finRange 8).map (fun i => boardShape (boardAt i))).Nodup := by
  native_decide

/-- The scout decision, named.  From the hatch on a flooded mouth, walking in
blind costs a point of damage that nothing in a descent restores; looking first
and shoring blind both cost a unit of air and no body. -/
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

/-- ⚑ **Extraction debt, and the deck's cut.**  Walk in blind on a flooded mouth,
take the mouth and west relics, and turn round: the second crossing of the same
flood is the second point of damage, capacity falls to one, and the deck keeps
the relic reached furthest for.  The run reaches the hatch holding one — with air
to spare and no way to use it. -/
def blindGrabLine : List Action :=
  [.descend, .lift, .descend, .lift, .ascend, .ascend]

theorem the_deck_keeps_what_you_could_not_carry :
    (match replayB (boardAt 4) initialState blindGrabLine with
      | none => false
      | some s =>
          decide (s.position = Node.hatch) && decide (s.damage = 2) &&
          decide (capacity s = 1) && decide (s.sling.count = 1) &&
          decide (0 < s.air) && doomedB s) = true := by
  native_decide

/-- The same six actions on a sound shaft come home with both. -/
theorem a_sound_shaft_keeps_both_relics :
    (match replayB (boardAt 0) initialState blindGrabLine with
      | none => false
      | some s =>
          decide (s.position = Node.hatch) && decide (s.damage = 0) &&
          decide (s.sling.count = 2) && reachableBankB s) = true := by
  native_decide

/-- The reachable state space of the whole family, for the emitter's benefit and
so the descriptor's size is a stated number rather than a surprise. -/
def familyStateCount : Nat :=
  (List.finRange 8).foldl (fun acc i => acc + (reachableWithin (boardAt i) AIR).length) 0

/-! ## The parametric table — the rules without the instance

A descriptor cannot carry the board.  What it carries instead is a table in
which every row that CONSULTS the board names BOTH of its successors, and every
other row names one.  `constBoard` supplies a fixed reading, and
`step_is_one_of_the_two_branches` is the fact that makes the two-successor row
honest: whatever the real board says, the real transition is one of the two the
row names. -/

def constBoard : Lore → Board
  | .flooded => { mouth := .flooded, west := .flooded, east := .flooded }
  | _ => { mouth := .sound, west := .sound, east := .sound }

/-- The transition under a fixed reading of whatever chamber this action would
consult.  It is `stepB` itself, not a copy of it. -/
def stepWith (reading : Lore) (s : State) (a : Action) : Option State :=
  stepB (constBoard reading) s a

theorem stepWith_eq_stepB (reading : Lore) (s : State) (a : Action) :
    stepWith reading s a = stepB (constBoard reading) s a := rfl

theorem constBoard_lore_sound (c : Chamber) :
    (constBoard Lore.sound).lore c = Lore.sound := by
  cases c <;> rfl

theorem constBoard_lore_flooded (c : Chamber) :
    (constBoard Lore.flooded).lore c = Lore.flooded := by
  cases c <;> rfl

/-- A board says exactly one of two things about a chamber.  This is the whole
of the hidden instance, one chamber at a time. -/
theorem board_lore_cases (b : Board) (c : Chamber) :
    b.lore c = Lore.sound ∨ b.lore c = Lore.flooded := by
  simp only [Board.lore]
  cases b.get c
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The board enters the transition at exactly one place — the lore of the
chamber an action reaches for — so every effect is one of two. -/
theorem transitionB_is_one_of_the_two (b : Board) (s : State) (a : Action) :
    transitionB b s a = transitionB (constBoard Lore.sound) s a ∨
    transitionB b s a = transitionB (constBoard Lore.flooded) s a := by
  cases a
  · -- survey: reads the chamber it reaches for
    cases htarget : Action.target Action.survey s.position with
    | none => exact Or.inl (by simp only [transitionB, htarget])
    | some c =>
        rcases board_lore_cases b c with hl | hl
        · exact Or.inl (by simp only [transitionB, htarget, hl, constBoard_lore_sound])
        · exact Or.inr (by simp only [transitionB, htarget, hl, constBoard_lore_flooded])
  · -- surveyEast: reads the chamber it reaches for
    cases htarget : Action.target Action.surveyEast s.position with
    | none => exact Or.inl (by simp only [transitionB, htarget])
    | some c =>
        rcases board_lore_cases b c with hl | hl
        · exact Or.inl (by simp only [transitionB, htarget, hl, constBoard_lore_sound])
        · exact Or.inr (by simp only [transitionB, htarget, hl, constBoard_lore_flooded])
  · exact Or.inl rfl   -- shore: the body never mentions the board
  · exact Or.inl rfl   -- shoreEast: the body never mentions the board
  · -- descend: reads the chamber it reaches for
    cases htarget : Action.target Action.descend s.position with
    | none => exact Or.inl (by simp only [transitionB, htarget])
    | some c =>
        rcases board_lore_cases b c with hl | hl
        · exact Or.inl (by simp only [transitionB, htarget, hl, constBoard_lore_sound])
        · exact Or.inr (by simp only [transitionB, htarget, hl, constBoard_lore_flooded])
  · -- descendEast: reads the chamber it reaches for
    cases htarget : Action.target Action.descendEast s.position with
    | none => exact Or.inl (by simp only [transitionB, htarget])
    | some c =>
        rcases board_lore_cases b c with hl | hl
        · exact Or.inl (by simp only [transitionB, htarget, hl, constBoard_lore_sound])
        · exact Or.inr (by simp only [transitionB, htarget, hl, constBoard_lore_flooded])
  · exact Or.inl rfl   -- lift: the body never mentions the board
  · exact Or.inl rfl   -- ascend: the body never mentions the board
  · exact Or.inl rfl   -- extract: the body never mentions the board

/-- ⚑ **The row is complete.**  For every board, every state and every action,
the real transition equals one of the two branches the emitted row names.  A
client that renders both branches has rendered every outcome that can occur, and
the descriptor has still not said which. -/
theorem step_is_one_of_the_two_branches (b : Board) (s : State) (a : Action) :
    stepB b s a = stepWith Lore.sound s a ∨
    stepB b s a = stepWith Lore.flooded s a := by
  by_cases hopen : openB s a
  · simp only [stepWith, stepB, hopen, ↓reduceIte]
    exact transitionB_is_one_of_the_two b s a
  · left
    simp only [stepWith, stepB, hopen, Bool.false_eq_true, ↓reduceIte]

/-- Whether an action is closed here does not depend on the instance: both
readings refuse together.  A row is therefore `refuse` for a reason the player
can see, never because of a bit they cannot. -/
theorem branches_agree_on_refusal (s : State) (a : Action) :
    (stepWith Lore.sound s a).isNone = (stepWith Lore.flooded s a).isNone := by
  simp only [stepWith, stepB]
  by_cases hopen : openB s a
  · simp only [hopen, ↓reduceIte]
    cases a <;> (try simp only [transitionB]) <;> (try split) <;> rfl
  · simp only [hopen, Bool.false_eq_true, ↓reduceIte]

/-- A row of the emitted table.  `refuse` carries a named reason and no
successor; `advance` is board-independent and carries one; `resolve` consults the
instance and carries both. -/
inductive Row where
  | refuse (reason : String)
  | advance (next : State)
  | resolve (onMatch onMismatch : State)
deriving DecidableEq

/-- Why an action is refused here.  The conjuncts are tested in the SAME order
`openB` and `openKindB` test them, so the reason a client renders is the first
thing that actually failed and not a plausible one. -/
def refusalReason (s : State) (a : Action) : String :=
  if s.banked then "run-banked"
  else if !reachableBankB s then "run-doomed"
  else if s.air = 0 then "no-air"
  else
    match a with
    | .survey | .surveyEast =>
        match a.target s.position with
        | none => "no-passage"
        | some _ => "already-read"
    | .shore | .shoreEast =>
        if s.shoring = 0 then "no-shoring"
        else
          match a.target s.position with
          | none => "no-passage"
          | some _ => "already-safe"
    | .descend | .descendEast => "no-passage"
    | .lift =>
        match s.position with
        | .hatch => "not-in-a-chamber"
        | .inside c =>
            if c.relicCount ≤ (s.deck.get c).relicsTaken then "chamber-emptied"
            else "over-capacity"
    | .ascend => "at-the-hatch"
    | .extract =>
        if s.position ≠ Node.hatch then "not-at-the-hatch" else "short-sling"

/-- The emitted row for one (state, action).  `advance` exactly when the two
readings agree, which is exactly when the action does not consult the board. -/
def rowFor (s : State) (a : Action) : Row :=
  match stepWith Lore.sound s a, stepWith Lore.flooded s a with
  | some m, some f => if m = f then .advance m else .resolve m f
  | _, _ => .refuse (refusalReason s a)

/-- A resolve row names two DIFFERENT states, so the gate's "the oracle bit is
not consulted and the row should be an accept" refusal cannot fire. -/
theorem resolve_rows_name_two_states (s : State) (a : Action) (m f : State)
    (h : rowFor s a = .resolve m f) : m ≠ f := by
  simp only [rowFor] at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · rename_i hne
      simp only [Row.resolve.injEq] at h
      obtain ⟨hm, hf⟩ := h
      subst hm; subst hf
      exact hne
  · exact absurd h (by simp)

/- ⚠ NOT LANDED, and named rather than quietly dropped.  The soundness
direction — `rowFor s a = .refuse r → ∀ b, stepB b s a = none`, i.e. a client
that greys an action out is not guessing — is TRUE and follows from
`branches_agree_on_refusal` plus `step_is_one_of_the_two_branches`, but the
proof kept foundering on reducing `rowFor`'s two-scrutinee match under a
hypothesis.  It is a tactic problem, not a mathematical one, and it wants
`rowFor` refactored to branch on `Option.isSome` first.  The gate's differential
independently rebuilds every refusal from the emitted view, so the property is
checked there in the meantime — but it is checked, not proved, and this comment
exists so the next reader does not assume otherwise. -/

/-! ### The board-independent closure

Both branches of every resolve row are followed, so the closure is the set of
knowledge states reachable on SOME board — which is exactly the state set a
descriptor that names both branches has to declare. -/

def rowSuccessors (s : State) (a : Action) : List State :=
  match rowFor s a with
  | .refuse _ => []
  | .advance n => [n]
  | .resolve m f => [m, f]

def parametricSuccessors (s : State) : List State :=
  allActions.flatMap (rowSuccessors s)

def parametricWithin : Nat → List State
  | 0 => [initialState]
  | fuel + 1 =>
      let prior := parametricWithin fuel
      (prior ++ prior.flatMap parametricSuccessors).eraseDups

def parametricStates : List State := parametricWithin AIR

def parametricRowCount : Nat := parametricStates.length * allActions.length

/-- ⚑ **The table is closed.**  Every successor any row names is a state the
descriptor declares, so a client can never be handed an id it does not have. -/
theorem parametric_closure_is_closed :
    parametricStates.all (fun s =>
      allActions.all (fun a =>
        (rowSuccessors s a).all (fun n => parametricStates.contains n))) = true := by
  native_decide

theorem parametric_states_nodup : parametricStates.eraseDups = parametricStates := by
  native_decide

theorem initial_state_is_declared : parametricStates.contains initialState = true := by
  native_decide

/-- The emitted shape, stated so the descriptor's size is a number a reader has
before they open the file.  Before the second relic: 1598 states, 14382 rows. -/
theorem parametric_shape_is_measured :
    parametricStates.length = 1924 ∧ allActions.length = 9 ∧
      parametricRowCount = 17316 := by
  refine ⟨by native_decide, by decide, by native_decide⟩

/-- `Sling.count` is unbounded as a TYPE — the counts are `Nat` — but capacity
is the wall the transition enforces: no declared state carries more than
`BASE_CAPACITY` relics.  This replaces the old `Sling.count_le_three`, which was
a fact about the type and is false of it now. -/
theorem declared_states_fit_the_sling :
    parametricStates.all (fun s => decide (s.sling.count ≤ BASE_CAPACITY)) = true := by
  native_decide

/-- ⚑ **The table really consults the instance.**  Some rows resolve, so the
gate's `no-oracle-row` FAIL — "every transition is deterministic, so the instance
cannot affect play" — cannot fire. -/
def resolveRowCount : Nat :=
  (parametricStates.flatMap (fun s =>
    allActions.filter (fun a => match rowFor s a with | .resolve _ _ => true | _ => false)))
  |>.length

theorem the_table_consults_the_instance : 0 < resolveRowCount := by
  native_decide

/-! ### Rendering names

Ids are semantic, not enumeration indices, so a re-emission that visits states in
a different order produces the same wire. -/

def Chamber.tag : Chamber → String
  | .mouth => "mouth"
  | .west => "west"
  | .east => "east"

def Node.tag : Node → String
  | .hatch => "hatch"
  | .inside c => c.tag

def Lore.tag : Lore → String
  | .dark => "dark"
  | .sound => "sound"
  | .flooded => "flooded"
  | .shored => "shored"

/-- One lowercase letter per reading, and `dark` is `d` rather than `?`.

⚠ A STATE ID IS AN IDENTIFIER AND HAS AN IDENTIFIER'S ALPHABET.  `?` (and the
`+` `slingTag` used to join with) are outside `[a-z0-9._:-]`, which is the
character class every POAG1 client checks a state id against before it will read
a table.  A descriptor whose ids carry them is one no client can load, and the
repair belongs HERE — widening the client's alphabet would weaken the check for
the four games that do not need it. -/
def Lore.code : Lore → String
  | .dark => "d"
  | .sound => "s"
  | .flooded => "f"
  | .shored => "x"

def Action.tag : Action → String
  | .survey => "survey"
  | .surveyEast => "survey-east"
  | .shore => "shore"
  | .shoreEast => "shore-east"
  | .descend => "descend"
  | .descendEast => "descend-east"
  | .lift => "lift"
  | .ascend => "ascend"
  | .extract => "extract"

def Action.label : Action → String
  | .survey => "Sound the passage below"
  | .surveyEast => "Sound the east spur"
  | .shore => "Shore the passage below"
  | .shoreEast => "Shore the east spur"
  | .descend => "Descend"
  | .descendEast => "Descend the east spur"
  | .lift => "Lift the relic"
  | .ascend => "Climb"
  | .extract => "Come through the hatch"

theorem action_tags_are_distinct :
    (allActions.map Action.tag).eraseDups = allActions.map Action.tag := by decide

private def slingTag (s : Sling) : String :=
  String.intercalate "." ((allChambers.filter (fun c => s.holds c)).map
    (fun c => c.tag ++ (if 2 ≤ s.get c then toString (s.get c) else "")))

def stateId (s : State) : String :=
  "dd:" ++ s.position.tag ++ ":" ++ toString s.air ++ ":" ++ toString s.shoring ++
  ":" ++ toString s.damage ++ ":" ++
  (allChambers.map (fun c => (s.deck.get c).lore.code)).foldl (· ++ ·) "" ++ ":" ++
  (allChambers.map (fun c => toString (s.deck.get c).relicsTaken)).foldl (· ++ ·) "" ++
  ":" ++ (if slingTag s.sling = "" then "-" else slingTag s.sling) ++
  ":" ++ (if s.banked then "banked" else "in")

/-- ⚑ **Ids separate states.**  Two declared states never share an id, so the
transition table's string references are unambiguous. -/
theorem state_ids_are_distinct :
    (parametricStates.map stateId).eraseDups.length = parametricStates.length := by
  native_decide

/-! ### The id alphabet, as a fact rather than a habit

`?` sat in `Lore.code` for as long as the game has existed and nothing was
measuring it, because nothing in Lean cares what a string looks like.  A POAG1
client does: it checks every state id, action id and refusal reason against
`^[a-z0-9][a-z0-9._:-]{0,95}$` before it will read a row, so a descriptor whose
ids fall outside that class is one no browser can load — a stop that shows up as
a total refusal in a browser and as nothing at all here.  So the class is stated,
and the states are held to it. -/

def isIdTailChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') ||
    c = '.' || c = '_' || c = ':' || c = '-'

def isIdHeadChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')

/-- `^[a-z0-9][a-z0-9._:-]{0,95}$`, the POAG1 identifier class. -/
def isPoag1Identifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => isIdHeadChar c && rest.all isIdTailChar && rest.length ≤ 95

/-- ⚑ **Every id a client is handed is an identifier.**  This is the pin that
`?` and `+` walked past; it is stated over the SAME `stateId` the descriptor
renders, so re-introducing either character goes red here. -/
theorem state_ids_are_identifiers :
    parametricStates.all (fun s => isPoag1Identifier (stateId s)) = true := by
  native_decide

theorem action_tags_are_identifiers :
    allActions.all (fun a => isPoag1Identifier a.tag) = true := by
  decide

/-- ⚠ The falsifier.  Without it `isPoag1Identifier` could be a function that
says `true` of everything, and both theorems above would be decoration.  These
are the two characters that were actually there. -/
theorem the_id_alphabet_refuses_the_old_codes :
    isPoag1Identifier "dd:hatch:9:2:0:???:000:-:in" = false ∧
    isPoag1Identifier "dd:mouth:5:2:0:sfd:100:mouth+west:in" = false := by
  decide

/-- What a client may render.  Everything the rules read is here, which is the
property the design gate's differential depends on: it rebuilds every verdict
from these fields alone and refuses on disagreement. -/
def solvedB (s : State) : Bool := s.banked

#assert_axioms stepWith_eq_stepB
#assert_axioms constBoard_lore_sound
#assert_axioms constBoard_lore_flooded
#assert_axioms board_lore_cases
#assert_axioms transitionB_is_one_of_the_two
#assert_axioms step_is_one_of_the_two_branches
#assert_axioms branches_agree_on_refusal
#assert_axioms resolve_rows_name_two_states
#assert_axioms action_tags_are_distinct
#assert_axioms action_tags_are_identifiers
#assert_axioms the_id_alphabet_refuses_the_old_codes

#assert_compiled parametric_closure_is_closed
#assert_compiled parametric_states_nodup
#assert_compiled initial_state_is_declared
#assert_compiled parametric_shape_is_measured
#assert_compiled the_table_consults_the_instance
#assert_compiled state_ids_are_distinct
#assert_compiled state_ids_are_identifiers

#assert_axioms allChambers_complete
#assert_axioms allNodes_complete
#assert_axioms mouth_is_a_junction
#assert_axioms only_the_mouth_forks
#assert_axioms spurs_are_leaves
#assert_axioms crossing_between_spurs_costs_two
#assert_axioms Deck.get_set_same
#assert_axioms boardTable_nodup
#assert_axioms boardAt_mem
#assert_axioms boardAt_injective
#assert_axioms draw_below_two_never_rejects
#assert_axioms asymmetry_is_prize_not_price
#assert_axioms the_east_spur_is_an_expedition_by_itself
#assert_axioms Config.slingRelics_length_le
#assert_axioms Sling.forfeit_is_deepest
#assert_axioms actionCode_injective
#assert_axioms Sling.forfeit_some_of_count
#assert_axioms allActions_complete
#assert_axioms Node.dist_self
#assert_axioms the_other_spur_costs_the_way_home
#assert_axioms takeDamage_capacity
#assert_axioms step_some_open
#assert_axioms step_some_live
#assert_axioms step_some_air
#assert_axioms step_some_kind
#assert_axioms step_eq_transition
#assert_axioms step_spends_exactly_one_air
#assert_axioms step_air_le_of_le
#assert_axioms step_turns_advance
#assert_axioms step_shoring_never_rises
#assert_axioms step_damage_never_falls
#assert_axioms step_capacity_never_rises
#assert_axioms not_open_refuses
#assert_axioms doomed_refuses_everything
#assert_axioms banked_refuses_everything
#assert_axioms airless_refuses_everything
#assert_axioms shoreless_refuses_shore
#assert_axioms surface_refuses_ascend
#assert_axioms only_the_junction_accepts_the_spur
#assert_axioms a_spur_refuses_going_deeper
#assert_axioms inside_refuses_extract
#assert_axioms short_sling_refuses_extract
#assert_axioms hatch_refuses_lift
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
#assert_axioms terminalOutput_canonical
#assert_axioms step_eq_stepB
#assert_axioms replay_eq_replayB
#assert_axioms judged_board_is_the_drawn_board
#assert_axioms judge_some_sound
#assert_axioms judge_receipt_binds_transcript
#assert_axioms judged_run_banked
#assert_axioms judged_run_within_budget
#assert_axioms every_line_is_the_whole_budget

#assert_compiled every_board_can_be_banked
#assert_compiled the_second_relic_makes_east_bankable_alone
#assert_compiled budget_binds_on_the_cautious_lines
#assert_compiled sweep_costs_the_budget_and_banks_on_one_board
#assert_compiled budgets_are_incomparable
#assert_compiled every_board_forks
#assert_compiled every_board_can_be_lost
#assert_compiled family_shape_is_measured
#assert_compiled the_mirror_is_broken
#assert_compiled declared_states_fit_the_sling
#assert_compiled walking_in_blind_costs_a_body
#assert_compiled the_deck_keeps_what_you_could_not_carry
#assert_compiled a_sound_shaft_keeps_both_relics

end Dregg2.Games.PathOfAngels.DeckDescent
