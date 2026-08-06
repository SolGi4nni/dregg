/-
# CrewRelayExpedition — the shared crew vocabulary

⚑ 2026-08-06 — this module used to be a 1,381-line asynchronous signed relay
kernel: `Config`, `State`, `CanonicalRunAdmission`, `SeatCapability`,
`SignedTurn`, `transition`, `execute`, `replay`, and a canonical settlement
registry.  **All of it is deleted.**  Nothing in the tree ever called it.  Its
only external mentions were its own `CrewRelayExpeditionBoundary`, whose twenty
`fail_if_success` teeth asserted that its constructors were unreachable — a
module proving that another module could not be used, next to a runtime that
shipped.  `CrewFieldMission` is the surviving relay: it never called this one,
and reused exactly the leaf types below.

⚠ The name is now wrong.  What remains is a vocabulary, not an expedition.  The
rename is not done here because nine importers spell this namespace and six of
them belong to other lanes' files.

What survives is the vocabulary those importers actually consume: who a seat is,
what role it holds, and which eight commands a crew can play.

`.abort` and `.restart` went with the machine.  They were the deleted relay's
terminal and recovery moves; no surviving consumer can accept one, and their
presence forced `Command.role`/`Command.strategy` to be partial for branches
nothing could reach.  Both are now total.
-/
import Dregg2.Games.PathOfAngels.DeckExpedition
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.CrewRelayExpedition

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

structure SeatId where
  value : Nat
deriving Repr, DecidableEq

structure CredentialId where
  value : Nat
deriving Repr, DecidableEq

inductive CrewRole where
  | pathfinder
  | engineer
  | containment
  | quartermaster
deriving Repr, DecidableEq

/-- A singleton role grant.  There is no role-set field that a client can widen. -/
structure Seat where
  id : SeatId
  playerKey : Digest32
  credential : CredentialId
  role : CrewRole
  initialCounter : Nat
deriving DecidableEq

def seatById? : List Seat → SeatId → Option Seat
  | [], _ => none
  | seat :: seats, id => if seat.id = id then some seat else seatById? seats id

inductive Strategy where
  | survey
  | salvage
deriving Repr, DecidableEq

/-- Each role has one move in either strategy.  Constructors, rather than a
caller-owned role field, make the role surface finite and auditable. -/
inductive Command where
  | chartPressureRoute
  | markSalvageRoute
  | braceTransit
  | overdriveCargoLift
  | quietAnomaly
  | screenRecovery
  | bankSupplies
  | secureCache
deriving Repr, DecidableEq

/-- Total: every command names exactly one authoring role. -/
def Command.role : Command → CrewRole
  | .chartPressureRoute | .markSalvageRoute => .pathfinder
  | .braceTransit | .overdriveCargoLift => .engineer
  | .quietAnomaly | .screenRecovery => .containment
  | .bankSupplies | .secureCache => .quartermaster

/-- Total: every command commits the crew to exactly one strategy. -/
def Command.strategy : Command → Strategy
  | .chartPressureRoute | .braceTransit | .quietAnomaly | .bankSupplies => .survey
  | .markSalvageRoute | .overdriveCargoLift | .screenRecovery | .secureCache => .salvage

def Command.code : Command → Nat
  | .chartPressureRoute => 0
  | .markSalvageRoute => 1
  | .braceTransit => 2
  | .overdriveCargoLift => 3
  | .quietAnomaly => 4
  | .screenRecovery => 5
  | .bankSupplies => 6
  | .secureCache => 7

/-- Each `(role, strategy)` pair has exactly one command, so a seat's authored
role and the crew's chosen strategy determine its move.  This is what makes
`decide (command.role = seat.role)` a complete role check rather than a filter
over a wider space. -/
theorem command_is_determined_by_role_and_strategy (left right : Command)
    (role : left.role = right.role) (strategy : left.strategy = right.strategy) :
    left = right := by
  cases left <;> cases right <;> simp_all [Command.role, Command.strategy]

theorem command_code_injective (left right : Command) (code : left.code = right.code) :
    left = right := by
  cases left <;> cases right <;> simp_all [Command.code]

/-! ## Fixture roster

Four seats with distinct player keys, credentials and counter origins.  Used by
`CrewFieldMission` and by `CrewFieldMissionRuntime`'s activation fixtures. -/

def digestFilled (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

def fixtureSeat0 : Seat := ⟨⟨0⟩, digestFilled 10, ⟨10⟩, .pathfinder, 10⟩
def fixtureSeat1 : Seat := ⟨⟨1⟩, digestFilled 11, ⟨11⟩, .engineer, 20⟩
def fixtureSeat2 : Seat := ⟨⟨2⟩, digestFilled 12, ⟨12⟩, .containment, 30⟩
def fixtureSeat3 : Seat := ⟨⟨3⟩, digestFilled 13, ⟨13⟩, .quartermaster, 40⟩

def fixtureRoster : List Seat := [fixtureSeat0, fixtureSeat1, fixtureSeat2, fixtureSeat3]

theorem fixture_roster_seats_are_distinct_in_every_authorizing_field :
    (fixtureRoster.map Seat.id).Nodup ∧
    (fixtureRoster.map Seat.playerKey).Nodup ∧
    (fixtureRoster.map Seat.credential).Nodup ∧
    (fixtureRoster.map Seat.role).Nodup := by
  native_decide

#assert_axioms command_is_determined_by_role_and_strategy
#assert_axioms command_code_injective
#assert_compiled fixture_roster_seats_are_distinct_in_every_authorizing_field

end Dregg2.Games.PathOfAngels.CrewRelayExpedition
