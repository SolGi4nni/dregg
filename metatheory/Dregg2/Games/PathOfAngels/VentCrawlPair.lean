/-
# Vent Crawl, two slings — one shaft, one tape, two people arguing about one rung

Substrate note: this is **Lean-authored game semantics**.  Nothing here is an AIR, a
constraint system or a gadget.  The browser and Rust dispatch what this module's
emitter renders; they carry no second copy of the rules.

## Why a second sling and not a second player

None of the seven games on the rack REQUIRES two people.  A second player is a spare
brain: they can advise, and nothing in any kernel notices whether they are there.
Vent Crawl is the one game whose arithmetic is already live — the best adaptive
policy strictly beats the best fixed-depth one, and every decision state is contested
by some risk posture — so the cheapest honest way to get a two-player game is not to
author an eighth game.  It is to put a second sling on the rope Vent already has.

**Shared shaft, shared tape, independent banking.**  That is the whole change.

## The coupling, and it is the only interesting design decision here

Two slings that do not touch is two solitaires on one screen.  The coupling that
makes it a game is the one the fiction already supplies:

⚑ **THE SHAFT FLOODS, NOT THE CRAWLER.**  A rung is one draw off one tape, and what
the draw is compared against is HOW MANY BODIES ENTER THE RUNG.  One crawler is the
ladder Vent already publishes; two crawlers is one more face in eight.

    floodBelow d .one = d - 1      -- exactly `VentCrawl.floodBelow`, unchanged
    floodBelow d .two = d          -- two on the rope

⚑ **AND A CRAWLER WHO BANKS IS OUT BEFORE THE RUNG IS ENTERED.**  Banking is safe —
it never drowns — and because the party is counted at the moment of entry, the
crawler who climbs out makes their partner's very next rung one face safer.  Both
directions of the coupling fall out of one rule.

So the questions the design has to answer, answered:

* **Does a shared descent mean shared hazard?**  Yes, and it is literally shared: one
  byte decides the rung for everyone standing on it.  Two crawlers who both crawl
  drown together or arrive together — `the_shaft_floods_not_the_crawler`.  There is no
  per-crawler luck inside a rung, which is what makes a neighbour's drowning news
  about the shaft rather than news about the neighbour.
* **Does banking early help or hurt the partner?**  It HELPS, and by a measured
  amount: the partner's next rung drops from `floodBelow d .two` to
  `floodBelow d .one`.  `leaving_lowers_the_partners_hazard` is the arithmetic and
  `every_rung_has_a_face_that_takes_a_pair_and_holds_one` is the behavioural form —
  at every rung in the shaft there is a tape byte that drowns a pair and holds a solo.
  This is the design's load-bearing choice.  Hurting the partner (a rope that gets
  more dangerous as it empties) pushes both crawlers to ride to the bottom together,
  which collapses back to one player with two slings.  Helping them makes SOMEBODY
  LEAVING the productive move, and who that somebody is, is an argument.
* **Cooperative or competitive?**  Cooperative-with-tension, and deliberately not a
  race.  Nobody gains from the other's loss: the crew haul is the SUM of the two
  slings and a drowning subtracts from it.  What is unequal is the OPTIMUM — the
  joint-optimal play is asymmetric, so the crew that plays well has to decide which
  of them takes the smaller share.  A zero-sum race would settle that by arithmetic
  and there would be nothing to say to each other.
* **What does each player see?**  Everything, and the same everything.  The vein is
  shared, the tape is shared, the sling is common while both are live, and
  `VentCrawl.the_carry_path_is_its_endpoint` already says the carry IS the posterior.
  So a disagreement is never "I know something you do not".  It is two people looking
  at the same six numbers and one of them has to go up.  Hiding half the shaft from
  each crawler would be a different game — a communication game — and it would also
  cost the property that makes Vent's table honest, because `consistentVeins` would
  stop being a fact about the state a client can render.

## ⚑ The bar, and it is exhibited rather than asserted

`check_the_two_crawlers_want_different_moves` says: at six of the fifteen joint
decision states, the optimal joint play is a SPLIT — one crawler banks while the other,
STANDING ON THE SAME RUNG WITH THE SAME SLING AND THE SAME POSTERIOR, crawls — and it
strictly beats both symmetric alternatives.  Two independent optimal solos cannot
produce that: they see identical information and face identical odds, so they make
identical moves.  Measured (exact backward induction over the belief state, scaled by
`SCALE` so no rational enters the kernel):

    optimal JOINT play                             8.1606
    both crawlers running the SOLO-optimal rule     5.7568     +41.8% for joint play
    best SYMMETRIC joint rule (never splits)        7.4531      +9.5% for joint play

The middle row is the bar as the brief stated it — "a distribution where the optimal
joint play differs from two independent optimal solos" — and the gap is 41.8%.  The
third row is the sharper version: even a pair allowed to optimise, so long as they
must move together, leaves 9.5% in the shaft.  ⚑ The whole 9.5% is the asymmetry.

## Single-player Vent is not broken, and that is a theorem

`the_lone_crawler_plays_single_player_vent` is a refinement: a pair state in which
one crawler has already left the shaft steps EXACTLY as `VentCrawl.transitionB` steps
the other.  The one-sling game was not re-implemented beside this one — it is this
transition restricted to a party of one, and `floodBelow · .one` is
`VentCrawl.floodBelow` by `rfl`.

## ⚠ The second sling is a WORSE DEAL than two solo runs, and that is not tuned

Two crawlers who each run the shaft alone bank `2 × 5.5833 = 11.1665` between them.
The same two on one rope bank `8.1606`.  **Sharing a shaft costs the crew 27% of
their expected salvage**, and it costs it for the reason the game works at all: the
extra face of hazard is the coupling, and the coupling is what makes leaving a move.

So a crawler offered BOTH modes for the same reward would never pick this one, and
the two-sling mode as specified is DOMINATED.  That is a live balance defect, it is
not fixed here, and it should not be fixed by weakening the hazard — the hazard is
the design.  It belongs on the REWARD side: a crew bonus on the shared haul, a bigger
shared mouth cache, or a pair that reads the seam a rung earlier than a solo can.
Each of those is a kernel constant and each needs its own solve before it is chosen,
which is why this module ships the mechanism measured and the tuning open rather than
picking a number here and calling the mode balanced.

## ⚠ What this module does NOT do

Named rather than smoothed over, because the pass is a DESIGN pass:

* **There is no two-player judge, receipt or admission.**  A judged pair run needs two
  player keys, two counters and two receipts bound to one tape, and `Judged`'s surface
  is single-player throughout.  `VentCrawl`'s judge is untouched and still correct for
  one sling.  This module carries the SEMANTICS and the MEASUREMENT; the judged
  surface is the next pass and it is real work, not a thin swap.
* **Nothing is emitted yet.**  No descriptor block, so `scripts/poa-design-gate.py`
  cannot see this game — the gate reads emitted descriptors and there is not one.
  The measurement below is therefore Lean-side only and is NOT gate-corroborated.
* **The heavy evaluations live in `VentCrawlPairFixtures.lean`**, following the
  decoupling every sibling module here already follows: the `check_* : Bool` bodies
  elaborate without running, and the `= true` pins are `native_decide` +
  `#assert_compiled` in the guards library.
-/
import Dregg2.Games.PathOfAngels.VentCrawl
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.VentCrawlPair

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.VentCrawl
  (Vein allVeins consistentVeins FloodTape DEPTH_CAP FACES MOUTH_SALVAGE)

set_option autoImplicit false

/-! ## The party, and the hazard it faces -/

/-- How many crawlers ENTER a rung.  ⚠ Not how many are in the run: a crawler who
banks is out of the shaft before the rung is entered, so they are not in the party
that faces it. -/
inductive Party where
  /-- One body on the rope.  This is the shaft `VentCrawl` publishes. -/
  | one
  /-- Two.  Heavier, slower, and one more face in eight. -/
  | two
deriving Repr, DecidableEq

def Party.size : Party → Nat
  | .one => 1
  | .two => 2

/-- Faces out of `FACES` that drown a party entering rung `rung`. -/
def floodBelow (rung : Nat) : Party → Nat
  | .one => VentCrawl.floodBelow rung
  | .two => rung

/-- ⚑ **THE SOLO LADDER IS THE OLD LADDER, BY `rfl`.**  A party of one faces exactly
the hazard `VentCrawl` already publishes, so single-player Vent is not a second
implementation that has to be kept in step — it is this one restricted. -/
theorem the_one_sling_hazard_is_the_published_hazard (rung : Nat) :
    floodBelow rung .one = VentCrawl.floodBelow rung := rfl

/-- The two ladders, measured side by side over the rungs a crawl can enter. -/
theorem the_two_ladders_are_measured :
    (List.range (DEPTH_CAP - 1)).map (fun i => (floodBelow (i + 2) .one,
                                               floodBelow (i + 2) .two))
      = [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)] := by decide

/-- ⚑ **LEAVING LOWERS THE PARTNER'S HAZARD.**  This is the whole coupling as
arithmetic: at every rung a crawl can enter, a party of one faces strictly fewer
drowning faces than a party of two.  A crawler who climbs out has made their
partner's next rung safer, and that is why "one of us should go up" is a move and
not a concession.

⚠ Stated for the rungs a crawl can ENTER (`2 ≤ rung`), which is every rung the
comparison is ever made at.  It is not true at rung 0, and a version quantified over
all of `Nat` would be false rather than general — `VentCrawl.floodBelow 0 = 0` because
`Nat` subtraction truncates, so the two ladders agree there. -/
theorem leaving_lowers_the_partners_hazard (rung : Nat) (h : 2 ≤ rung) :
    floodBelow rung .one < floodBelow rung .two := by
  show VentCrawl.floodBelow rung < rung
  show rung - 1 < rung
  omega

/-- ⚑ **AND THE SHARED TAPE IS WHAT MAKES THAT REAL.**  At every rung there is a face
of the die that drowns a pair and holds a single crawler — the same byte, read against
two different party sizes.  Without this the party count would be a number that never
changed an outcome. -/
theorem every_rung_has_a_face_that_takes_a_pair_and_holds_one :
    (List.range (DEPTH_CAP - 1)).all (fun i =>
      let rung := i + 2
      (List.range FACES).any (fun face =>
        decide (floodBelow rung .one ≤ face) && decide (face < floodBelow rung .two)))
      = true := by decide

/-- No rung is certain death for a pair either: the deepest is 6 in 8, so the bottom
of the shaft is a wager for two crawlers exactly as it is for one. -/
theorem no_rung_drowns_a_pair_for_certain :
    (List.range (DEPTH_CAP - 1)).all (fun i =>
      decide (floodBelow (i + 2) .two < FACES)) = true := by decide

/-! ## State -/

inductive Standing where
  /-- Still on the rope. -/
  | inShaft
  /-- Climbed out, sling kept. -/
  | banked
  /-- The rung gave way. -/
  | drowned
deriving Repr, DecidableEq

def Standing.tag : Standing → String
  | .inShaft => "in-shaft"
  | .banked => "banked"
  | .drowned => "drowned"

/-- One crawler.  `reached` is the deepest rung this crawler entered — a banker keeps
theirs, which is what pays their map. -/
structure Crawler where
  standing : Standing
  sling : Nat
  reached : Nat
deriving Repr, DecidableEq

def Crawler.live (c : Crawler) : Bool := decide (c.standing = Standing.inShaft)

/-- Both crawlers start at the mouth holding the mouth cache.  It is the same cache
on every vein, so the opening position still carries nothing about the day. -/
def atTheMouth : Crawler :=
  { standing := .inShaft, sling := MOUTH_SALVAGE, reached := 1 }

structure State where
  /-- The rung the live party stands on, or the last rung entered. -/
  depth : Nat
  a : Crawler
  b : Crawler
deriving Repr, DecidableEq

def initialState : State := { depth := 1, a := atTheMouth, b := atTheMouth }

/-- The run is over when nobody is on the rope. -/
def State.over (s : State) : Bool := !s.a.live && !s.b.live

/-- ⚑ The crew haul: the SUM of what came out.  A drowned sling contributes nothing,
which is why this is cooperative — neither crawler is ever paid for the other's
water. -/
def State.crewHaul (s : State) : Nat :=
  (match s.a.standing with | .banked => s.a.sling | _ => 0) +
  (match s.b.standing with | .banked => s.b.sling | _ => 0)

/-! ## The joint action

Both crawlers choose at once.  A crawler who has already left the shaft has no move,
and `a_departed_crawler_has_no_move` is the check that the transition really ignores
their entry rather than merely being called with a conventional value. -/

structure Joint where
  a : VentCrawl.Action
  b : VentCrawl.Action
deriving Repr, DecidableEq

def allJoints : List Joint :=
  [⟨.crawl, .crawl⟩, ⟨.crawl, .bank⟩, ⟨.bank, .crawl⟩, ⟨.bank, .bank⟩]

theorem allJoints_complete (j : Joint) : j ∈ allJoints := by
  obtain ⟨a, b⟩ := j
  cases a <;> cases b <;> simp [allJoints]

def Joint.tag (j : Joint) : String := j.a.tag ++ "/" ++ j.b.tag

/-- Whether this crawler ENTERS the next rung: they are on the rope and they said
crawl. -/
def entersB (c : Crawler) (act : VentCrawl.Action) : Bool :=
  c.live && decide (act = VentCrawl.Action.crawl)

/-- How many bodies enter the next rung. -/
def entrants (s : State) (j : Joint) : Nat :=
  (if entersB s.a j.a then 1 else 0) + (if entersB s.b j.b then 1 else 0)

def partyOf (n : Nat) : Party := if n ≤ 1 then .one else .two

theorem entrants_le_two (s : State) (j : Joint) : entrants s j ≤ 2 := by
  simp only [entrants]
  split <;> split <;> omega

/-! ## The transition

⚑ Read the ORDER, because it is the design: the bankers leave, THEN the party that is
left enters the rung, THEN the tape is consulted against the size of that party. -/

/-- What one rung does to one crawler.  A crawler off the rope is untouched; a banker
climbs out at the rung they were already standing on; a crawler either arrives one
rung deeper with more in the sling or loses all of it. -/
def resolve (v : Vein) (rung : Nat) (flooded : Bool) (c : Crawler)
    (act : VentCrawl.Action) : Crawler :=
  if c.live then
    match act with
    | .bank => { c with standing := .banked }
    | .crawl =>
        if flooded then { standing := .drowned, sling := 0, reached := rung }
        else { standing := .inShaft, sling := c.sling + v.yieldAt rung, reached := rung }
  else c

/-- ⚑ **BANKING IS SAFE.**  A crawler who says "I am going up" is out before the rung
is entered, so no tape and no party size can drown them.  This is what makes the
second sling a decision rather than a shared fate.

⚠ Stated for a crawler who is ON THE ROPE.  A crawler already off it keeps whatever
standing they had, so a version without `c.live` would be claiming that `resolve`
resurrects a drowned crawler rather than that banking is safe. -/
theorem a_crawler_who_banks_never_drowns (v : Vein) (rung : Nat) (flooded : Bool)
    (c : Crawler) (hl : c.live = true) :
    (resolve v rung flooded c VentCrawl.Action.bank).standing ≠ Standing.drowned := by
  simp [resolve, hl]

/-- A banker keeps the rung they were standing on, so their map is paid for the shaft
they actually saw and not for the one their partner went on to see. -/
theorem a_banker_keeps_their_own_rung (v : Vein) (rung : Nat) (flooded : Bool)
    (c : Crawler) : (resolve v rung flooded c VentCrawl.Action.bank).reached = c.reached := by
  simp only [resolve]
  split <;> rfl

def transition (v : Vein) (t : FloodTape) (s : State) (j : Joint) : State :=
  let n := entrants s j
  if n = 0 then
    { s with a := resolve v s.depth false s.a .bank
             b := resolve v s.depth false s.b .bank }
  else
    let rung := s.depth + 1
    let flooded := decide ((t.rung rung).val < floodBelow rung (partyOf n))
    { depth := rung
      a := resolve v rung flooded s.a j.a
      b := resolve v rung flooded s.b j.b }

/-- Openness: somebody is still on the rope, and nobody is being asked to crawl past
the bottom of the shaft. -/
def openB (s : State) (j : Joint) : Bool :=
  (s.a.live || s.b.live) &&
  (!(entersB s.a j.a || entersB s.b j.b) || decide (s.depth < DEPTH_CAP))

def stepB (v : Vein) (t : FloodTape) (s : State) (j : Joint) : Option State :=
  if openB s j then some (transition v t s j) else none

def replayB (v : Vein) (t : FloodTape) : State → List Joint → Option State
  | s, [] => some s
  | s, j :: js =>
      match stepB v t s j with
      | none => none
      | some s' => replayB v t s' js

/-! ### Reading the transition back out -/

/-- ⚑ **A DEPARTED CRAWLER HAS NO MOVE.**  Whatever intent is submitted for a crawler
who is off the rope, the transition does the same thing — so the four-element joint
action is honest about a run in which one crawler has already left. -/
theorem a_departed_crawler_has_no_move (v : Vein) (t : FloodTape) (s : State)
    (act act' : VentCrawl.Action) (jb : VentCrawl.Action) (h : s.a.live = false) :
    transition v t s ⟨act, jb⟩ = transition v t s ⟨act', jb⟩ := by
  have he : ∀ x, entersB s.a x = false := by
    intro x; simp [entersB, h]
  simp only [transition, entrants, he, resolve, h, if_false, Bool.false_eq_true]

/-- ⚑ **THE SHAFT FLOODS, NOT THE CRAWLER.**  Two crawlers who both enter a rung meet
the same byte against the same threshold, so they drown together or arrive together.
There is no per-crawler luck inside a rung. -/
theorem the_shaft_floods_not_the_crawler (v : Vein) (t : FloodTape) (s : State)
    (ha : s.a.live = true) (hb : s.b.live = true) :
    let s' := transition v t s ⟨.crawl, .crawl⟩
    (s'.a.standing = Standing.drowned) ↔ (s'.b.standing = Standing.drowned) := by
  simp only [transition, entrants, entersB, ha, hb, resolve]
  by_cases hf : (t.rung (s.depth + 1)).val < floodBelow (s.depth + 1) (partyOf 2) <;>
    simp [hf]

/-- A crawl is exactly one rung, for whoever took it. -/
theorem a_crawl_is_exactly_one_rung (v : Vein) (t : FloodTape) (s : State) (j : Joint)
    (h : 0 < entrants s j) : (transition v t s j).depth = s.depth + 1 := by
  simp only [transition]
  split
  · omega
  · rfl

/-- Nobody enters, nobody moves: a round in which both crawlers bank leaves the shaft
where it was. -/
theorem a_round_with_no_entrant_moves_no_rung (v : Vein) (t : FloodTape) (s : State)
    (j : Joint) (h : entrants s j = 0) : (transition v t s j).depth = s.depth := by
  simp only [transition, h]
  rfl

/-! ## The solo projection — single-player Vent, restricted rather than re-authored -/

def outcomeOf : Standing → VentCrawl.Outcome
  | .inShaft => .crawling
  | .banked => .banked
  | .drowned => .drowned

/-- One crawler, read as a single-player Vent Crawl state. -/
def soloOf (c : Crawler) : VentCrawl.State :=
  { depth := c.reached, carried := c.sling, outcome := outcomeOf c.standing }

/-- The pair state is well formed when every crawler still on the rope is standing on
the shaft's own rung.  A split freezes the leaver's `reached` and this is what says
the survivor's is still the live one. -/
def wellFormedB (s : State) : Bool :=
  (!s.a.live || decide (s.a.reached = s.depth)) &&
  (!s.b.live || decide (s.b.reached = s.depth))

theorem initialState_wellFormed : wellFormedB initialState = true := by decide

/-- ⚑ **THE SOLO PROJECTION.**  When one crawler has already left the shaft, the pair
transition does to the other EXACTLY what `VentCrawl.transitionB` does to them.  Not a
differential on cases — the two functions agree, for every vein, every tape, every
well-formed state and both verbs.  This is the sense in which one sling still works:
single-player Vent IS this game with a party of one, and there is no second copy of
the rules to keep in step. -/
theorem the_lone_crawler_plays_single_player_vent (v : Vein) (t : FloodTape) (s : State)
    (act : VentCrawl.Action) (hb : s.b.live = false) (ha : s.a.live = true)
    (hwf : s.a.reached = s.depth) :
    soloOf (transition v t s ⟨act, VentCrawl.Action.bank⟩).a
      = VentCrawl.transitionB v t (soloOf s.a) act := by
  have hbe : entersB s.b VentCrawl.Action.bank = false := by simp [entersB, hb]
  cases act with
  | bank =>
      have hae : entersB s.a VentCrawl.Action.bank = false := by simp [entersB]
      simp only [transition, entrants, hae, hbe, if_false, Bool.false_eq_true,
        reduceIte, resolve, ha, VentCrawl.transitionB, VentCrawl.bankSuccessor,
        soloOf, outcomeOf]
  | crawl =>
      have hae : entersB s.a VentCrawl.Action.crawl = true := by simp [entersB, ha]
      simp only [transition, entrants, hae, hbe, resolve, ha, soloOf, outcomeOf,
        floodBelow, partyOf, VentCrawl.transitionB, hwf]
      by_cases hf : (t.rung (s.depth + 1)).val < VentCrawl.floodBelow (s.depth + 1)
      · simp [hf, VentCrawl.floodSuccessor, hwf]
      · simp [hf, VentCrawl.haulSuccessor, hwf]

/-! ## The exact joint solve, in scaled `Nat`

Everything below is an EXACT backward induction over the belief state, scaled by
`SCALE` so that no rational and no float enters the kernel.  ⚑ `SCALE` is `2^24`
because the deepest denominator this induction can build is five rungs of `FACES = 8`
(`2^15`) times the belief sizes it averages over on the way down (`8·4·2·2·2 = 2^8`),
which is `2^23`; `check_the_scaled_induction_is_exact` is the pin that no division
below ever truncates, so these integers are the rational values and not roundings of
them. -/

abbrev SCALE : Nat := 16777216

/-- Faces out of `FACES` that a party entering `rung` survives. -/
def survivors (rung : Nat) (p : Party) : Nat := FACES - floodBelow rung p

/-- ⚑ Single-sling value at a belief state, scaled.  This is `VentCrawl`'s own game:
the ladder it consults is `floodBelow · .one`. -/
def soloValue : Nat → Nat → Nat → Nat
  | 0, _, carried => SCALE * carried
  | fuel + 1, depth, carried =>
      if DEPTH_CAP ≤ depth then SCALE * carried
      else
        let rung := depth + 1
        let cands := consistentVeins depth carried
        let tot := cands.foldl
          (fun acc v => acc + soloValue fuel rung (carried + v.yieldAt rung)) 0
        max (SCALE * carried) (survivors rung .one * tot / (FACES * cands.length))

/-- What one crawler is worth from here if they finish the shaft alone. -/
def soloAt (depth carried : Nat) : Nat := soloValue DEPTH_CAP depth carried

/-- Joint value: BOTH crawlers bank right here. -/
def bothBankValue (carried : Nat) : Nat := SCALE * (2 * carried)

/-- ⚑ Joint value of the SPLIT: one crawler banks (locking their sling, and out
before the rung), the other finishes the shaft ALONE — at solo odds, because the
party they enter the next rung with is a party of one. -/
def splitValue (depth carried : Nat) : Nat := SCALE * carried + soloAt depth carried

/-- ⚑ Joint value of BOTH crawling: a party of two enters the next rung against one
byte, so they arrive together or lose both slings together. -/
def pairValue : Nat → Nat → Nat → Nat
  | 0, _, carried => bothBankValue carried
  | fuel + 1, depth, carried =>
      if DEPTH_CAP ≤ depth then bothBankValue carried
      else
        let rung := depth + 1
        let cands := consistentVeins depth carried
        let tot := cands.foldl
          (fun acc v => acc + pairValue fuel rung (carried + v.yieldAt rung)) 0
        let crawl := survivors rung .two * tot / (FACES * cands.length)
        max (max (bothBankValue carried) crawl) (splitValue depth carried)

def pairAt (depth carried : Nat) : Nat := pairValue DEPTH_CAP depth carried

def bothCrawlValue (depth carried : Nat) : Nat :=
  if DEPTH_CAP ≤ depth then 0
  else
    let rung := depth + 1
    let cands := consistentVeins depth carried
    let tot := cands.foldl
      (fun acc v => acc + pairValue DEPTH_CAP rung (carried + v.yieldAt rung)) 0
    survivors rung .two * tot / (FACES * cands.length)

/-! ### The reachable joint decision states

A joint decision state is a rung above the bottom together with a sling, and by
`VentCrawl.the_carry_path_is_its_endpoint` that pair IS the posterior — there is
nothing the crawlers saw on the way down that it has forgotten. -/

def decisionsFrom : Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _ => []
  | fuel + 1, depth, carried =>
      if DEPTH_CAP ≤ depth then []
      else
        (depth, carried) :: (consistentVeins depth carried).flatMap
          (fun v => decisionsFrom fuel (depth + 1) (carried + v.yieldAt (depth + 1)))

def decisionStates : List (Nat × Nat) :=
  (decisionsFrom (DEPTH_CAP + 1) 1 MOUTH_SALVAGE).eraseDups

/-- The joint move optimal at a decision state. -/
inductive JointMove where
  | bothBank
  | bothCrawl
  | split
deriving Repr, DecidableEq

def JointMove.tag : JointMove → String
  | .bothBank => "both-bank"
  | .bothCrawl => "both-crawl"
  | .split => "split"

/-- ⚠ Ties go to the SYMMETRIC move.  A split reported on a tie would be a
disagreement manufactured by the tie-break rather than by the arithmetic, and the
whole claim below is that the arithmetic wants it. -/
def bestMove (depth carried : Nat) : JointMove :=
  let bank := bothBankValue carried
  let crawl := bothCrawlValue depth carried
  let split := splitValue depth carried
  if split > bank && split > crawl then .split
  else if crawl ≥ bank then .bothCrawl
  else .bothBank

def splitStates : List (Nat × Nat) :=
  decisionStates.filter (fun dc => bestMove dc.1 dc.2 == JointMove.split)

/-- Two crawlers who both run the single-sling optimal rule on the shared shaft.  It
is a SYMMETRIC policy, so it never splits — which is exactly why it is the right
stand-in for "two independent optimal solos". -/
def bothFollowSoloValue : Nat → Nat → Nat → Nat
  | 0, _, carried => bothBankValue carried
  | fuel + 1, depth, carried =>
      if DEPTH_CAP ≤ depth then bothBankValue carried
      else
        let rung := depth + 1
        let cands := consistentVeins depth carried
        if soloAt depth carried ≤ SCALE * carried then bothBankValue carried
        else
          let tot := cands.foldl
            (fun acc v => acc + bothFollowSoloValue fuel rung (carried + v.yieldAt rung)) 0
          survivors rung .two * tot / (FACES * cands.length)

/-- The best joint policy that never splits: both crawlers optimise, together. -/
def symmetricOptimum : Nat → Nat → Nat → Nat
  | 0, _, carried => bothBankValue carried
  | fuel + 1, depth, carried =>
      if DEPTH_CAP ≤ depth then bothBankValue carried
      else
        let rung := depth + 1
        let cands := consistentVeins depth carried
        let tot := cands.foldl
          (fun acc v => acc + symmetricOptimum fuel rung (carried + v.yieldAt rung)) 0
        max (bothBankValue carried) (survivors rung .two * tot / (FACES * cands.length))

/-! ### The pins

Statements here, evaluation in `VentCrawlPairFixtures.lean` — the same decoupling
every sibling module in this directory uses, so a regression reds the guards library
and not a proving target. -/

/-- ⚑ **No division in the induction above ever truncates**, so the scaled integers
are the exact rational values.  Without this every number below would be a rounding
whose direction nobody had checked, and a `max` over roundings is not an optimum.
(Pinned `= true` in `VentCrawlPairFixtures`.) -/
def check_the_scaled_induction_is_exact : Bool :=
  decisionStates.all (fun dc =>
    let depth := dc.1
    let carried := dc.2
    let rung := depth + 1
    let cands := consistentVeins depth carried
    let solos := cands.foldl
      (fun acc v => acc + soloValue DEPTH_CAP rung (carried + v.yieldAt rung)) 0
    let pairs := cands.foldl
      (fun acc v => acc + pairValue DEPTH_CAP rung (carried + v.yieldAt rung)) 0
    decide (survivors rung .one * solos % (FACES * cands.length) = 0) &&
    decide (survivors rung .two * pairs % (FACES * cands.length) = 0))

/-- The shape of the joint decision problem, measured: fifteen states, and the
posterior at each is what `VentCrawl` already says it is.
(Pinned `= true` in `VentCrawlPairFixtures`.) -/
def check_the_joint_decision_shape_is_measured : Bool :=
  decide (decisionStates.length = 15) &&
  decisionStates.all (fun dc => decide (0 < (consistentVeins dc.1 dc.2).length))

/-- ⚑⚑ **THE EXHIBITED DISAGREEMENT — the bar this whole module exists to clear.**

At each of these six states both crawlers stand on the SAME rung holding the SAME
sling with the SAME posterior, so two independent optimal solos would necessarily
make the SAME move.  Optimal joint play makes DIFFERENT ones: one banks, the other
crawls — and it strictly beats both symmetric alternatives at every one of them.

⚠ Stated over the states the induction FINDS, not over a hand-picked list, and with
ties broken toward the symmetric move, so neither the selection nor the tie-break can
manufacture the finding.
(Pinned `= true` in `VentCrawlPairFixtures`.) -/
def check_the_two_crawlers_want_different_moves : Bool :=
  decide (splitStates.length = 6) &&
  decide (splitStates = [(2, 4), (2, 5), (3, 9), (3, 10), (4, 18), (5, 38)]) &&
  splitStates.all (fun dc =>
    decide (bothBankValue dc.2 < splitValue dc.1 dc.2) &&
    decide (bothCrawlValue dc.1 dc.2 < splitValue dc.1 dc.2))

/-- ⚑ **AND THE DISAGREEMENT IS WORTH SOMETHING.**  The optimal joint play at the
mouth is worth `136912896 / 2^24 = 8.1606` slings; a pair in which both crawlers run
the SOLO-optimal rule — which is exactly "two independent optimal solos", the
comparison the bar names — banks `96583680 / 2^24 = 5.7568`.  That is +41.8%, and all
of it is the option to send one crawler up.
(Pinned `= true` in `VentCrawlPairFixtures`.) -/
def check_the_joint_optimum_beats_two_solos : Bool :=
  decide (pairAt 1 MOUTH_SALVAGE = 136912896) &&
  decide (bothFollowSoloValue DEPTH_CAP 1 MOUTH_SALVAGE = 96583680) &&
  decide (bothFollowSoloValue DEPTH_CAP 1 MOUTH_SALVAGE < pairAt 1 MOUTH_SALVAGE)

/-- ⚑ **THE SPLIT IS NOT AVAILABLE TO A PAIR THAT MUST MOVE TOGETHER.**  Even a pair
allowed to optimise, so long as both crawlers always make the same move, banks
125042688 / 2^24 = 7.4531 against the joint optimum's 8.1606 — so 9.5% of the shaft is
in the asymmetry alone and not in the coupling generally.
(Pinned `= true` in `VentCrawlPairFixtures`.) -/
def check_the_asymmetry_is_where_the_value_is : Bool :=
  decide (symmetricOptimum DEPTH_CAP 1 MOUTH_SALVAGE = 125042688) &&
  decide (symmetricOptimum DEPTH_CAP 1 MOUTH_SALVAGE < pairAt 1 MOUTH_SALVAGE)

/-- ⚑ **NEITHER SYMMETRIC MOVE IS DOMINATED EITHER.**  Both-bank is strictly right
somewhere and both-crawl is strictly right somewhere, so the second sling did not
collapse the game into "always split".  A client that offered only the split would be
hiding two moves that win.
(Pinned `= true` in `VentCrawlPairFixtures`.) -/
def check_every_joint_move_is_someones_best : Bool :=
  decisionStates.any (fun dc => bestMove dc.1 dc.2 == JointMove.bothBank) &&
  decisionStates.any (fun dc => bestMove dc.1 dc.2 == JointMove.bothCrawl) &&
  decisionStates.any (fun dc => bestMove dc.1 dc.2 == JointMove.split)

/-- ⚑ **THE FIRST CRAWL IS STILL MADE TOGETHER.**  At the mouth the joint optimum is
both-crawl, so the pair does not open by immediately sending someone home — the
argument starts at rung 2, after the shaft has said something.
(Pinned `= true` in `VentCrawlPairFixtures`.) -/
def check_the_pair_opens_together : Bool :=
  bestMove 1 MOUTH_SALVAGE == JointMove.bothCrawl

#assert_axioms the_one_sling_hazard_is_the_published_hazard
#assert_axioms the_two_ladders_are_measured
#assert_axioms leaving_lowers_the_partners_hazard
#assert_axioms every_rung_has_a_face_that_takes_a_pair_and_holds_one
#assert_axioms no_rung_drowns_a_pair_for_certain
#assert_axioms allJoints_complete
#assert_axioms entrants_le_two
#assert_axioms a_crawler_who_banks_never_drowns
#assert_axioms a_banker_keeps_their_own_rung
#assert_axioms a_departed_crawler_has_no_move
#assert_axioms the_shaft_floods_not_the_crawler
#assert_axioms a_crawl_is_exactly_one_rung
#assert_axioms a_round_with_no_entrant_moves_no_rung
#assert_axioms initialState_wellFormed
#assert_axioms the_lone_crawler_plays_single_player_vent

-- The measured-design pins (`native_decide` + `#assert_compiled`) live in
-- `VentCrawlPairFixtures.lean`, rooted in `PathOfAngelsGuards`.

end Dregg2.Games.PathOfAngels.VentCrawlPair
