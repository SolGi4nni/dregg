/-
# Finite POAG1 tables for Relay Repair and Salvage Lock

These declarations enumerate the duplicate-free legal-state closure of each
small game and the complete state x action transition table over that closure.
The web host dispatches these tables; it does not carry a second implementation
of either state machine.
-/
import Dregg2.Games.PathOfAngels.RelayRepair
import Dregg2.Games.PathOfAngels.SalvageLock
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.FiniteTables

open Dregg2.Games.PathOfAngels

/-! ## Generic finite closure -/

def expandStates {State Action : Type} [DecidableEq State]
    (step : State → Action → Option State) (actions : List Action)
    (states : List State) : List State :=
  (states ++ states.flatMap fun state => actions.filterMap (step state)).eraseDups

def stateClosure {State Action : Type} [DecidableEq State]
    (step : State → Action → Option State) (actions : List Action)
    (initial : State) : Nat → List State
  | 0 => [initial]
  | n + 1 => expandStates step actions (stateClosure step actions initial n)

/-! ## Relay Repair -/

def relayActions : List RelayRepair.Action :=
  [.alphaBeta, .alphaGamma, .betaDelta, .gammaDelta]

def relayActionId : RelayRepair.Action → String
  | .alphaBeta => "alpha-beta"
  | .alphaGamma => "alpha-gamma"
  | .betaDelta => "beta-delta"
  | .gammaDelta => "gamma-delta"

def relayActionLabel : RelayRepair.Action → String
  | .alphaBeta => "Install Alpha-Beta"
  | .alphaGamma => "Install Alpha-Gamma"
  | .betaDelta => "Install Beta-Delta"
  | .gammaDelta => "Install Gamma-Delta"

def relayActionFrom : RelayRepair.Action → String
  | .alphaBeta | .alphaGamma => "alpha"
  | .betaDelta => "beta"
  | .gammaDelta => "gamma"

def relayActionTo : RelayRepair.Action → String
  | .alphaBeta => "beta"
  | .alphaGamma => "gamma"
  | .betaDelta | .gammaDelta => "delta"

def relayPanelMask (panel : RelayRepair.Panel) : Nat :=
  (if panel.alphaBeta then 1 else 0) +
  (if panel.alphaGamma then 2 else 0) +
  (if panel.betaDelta then 4 else 0) +
  (if panel.gammaDelta then 8 else 0)

def relayStateId (state : RelayRepair.State) : String :=
  "relay:" ++ toString (relayPanelMask state.panel) ++ ":" ++
    toString state.spares ++ ":" ++ toString state.turns

def relayInstalledActionIds (panel : RelayRepair.Panel) : List String :=
  (relayActions.filter fun action => RelayRepair.installed panel action).map relayActionId

theorem relayActions_length : relayActions.length = 4 := rfl

theorem relayActions_complete (action : RelayRepair.Action) : action ∈ relayActions := by
  cases action <;> simp [relayActions]

/-- The source transition with its proof-only Config erased. -/
def relayStep (state : RelayRepair.State) (action : RelayRepair.Action) :
    Option RelayRepair.State :=
  if RelayRepair.openB state action then
    some {
      panel := RelayRepair.install state.panel action
      spares := state.spares - 1
      turns := state.turns + 1
    }
  else none

theorem relayStep_eq_source (cfg : RelayRepair.Config) (state : RelayRepair.State)
    (action : RelayRepair.Action) :
    relayStep state action = RelayRepair.step cfg state action := rfl

def relayStates : List RelayRepair.State :=
  stateClosure relayStep relayActions RelayRepair.initialState RelayRepair.MAX_TURNS

structure RelayTransition where
  state : RelayRepair.State
  action : RelayRepair.Action
  next : Option RelayRepair.State
deriving DecidableEq, Repr

def relayTransitions : List RelayTransition :=
  relayStates.flatMap fun state =>
    relayActions.map fun action => { state, action, next := relayStep state action }

def relayTableClosedB : Bool :=
  relayTransitions.all fun transition =>
    match transition.next with
    | none => true
    | some next => decide (next ∈ relayStates)

def relayStatesNodupB : Bool := relayStates.Nodup

def relayStateIdsUniqueB (stateId : RelayRepair.State → String) : Bool :=
  (relayStates.map stateId).Nodup

def relayRefusalReason (state : RelayRepair.State) (action : RelayRepair.Action) :
    Option String :=
  if RelayRepair.reachableB state.panel then some "solved"
  else if RelayRepair.MAX_TURNS ≤ state.turns then some "turn-limit"
  else if state.spares = 0 then some "no-spares"
  else if RelayRepair.installed state.panel action then some "already-installed"
  else none

def relayRefusalReasonsCompleteB : Bool :=
  relayTransitions.all fun transition =>
    match transition.next, relayRefusalReason transition.state transition.action with
    | some _, none => true
    | none, some _ => true
    | _, _ => false

theorem relayTransitions_length :
    relayTransitions.length = relayStates.length * relayActions.length := by
  simp [relayTransitions]

theorem relayTransition_spec (transition : RelayTransition)
    (h : transition ∈ relayTransitions) :
    transition.next = relayStep transition.state transition.action := by
  simp only [relayTransitions, List.mem_flatMap, List.mem_map] at h
  obtain ⟨state, _hstate, action, _haction, rfl⟩ := h
  rfl

theorem relayTable_closed : relayTableClosedB = true := by
  native_decide

theorem relayStates_nodup : relayStatesNodupB = true := by
  native_decide

theorem relayRefusalReasons_complete : relayRefusalReasonsCompleteB = true := by
  native_decide

theorem relayStateIds_unique : relayStateIdsUniqueB relayStateId = true := by
  native_decide

theorem relayStates_count : relayStates.length = 15 := by
  native_decide

theorem relayTransitions_count : relayTransitions.length = 60 := by
  native_decide

#assert_axioms relayActions_length
#assert_axioms relayActions_complete
#assert_axioms relayStep_eq_source
#assert_axioms relayTransitions_length
#assert_axioms relayTransition_spec
#assert_compiled relayTable_closed
#assert_compiled relayStates_nodup
#assert_compiled relayRefusalReasons_complete
#assert_compiled relayStateIds_unique
#assert_compiled relayStates_count
#assert_compiled relayTransitions_count

/-! ## Salvage Lock -/

def salvageActions : List SalvageLock.Action :=
  (List.finRange 6).map SalvageLock.Action.expose

def salvageActionId (action : SalvageLock.Action) : String :=
  "slot-" ++ toString (SalvageLock.actionSlot action).val

def salvageActionLabel (action : SalvageLock.Action) : String :=
  "Expose plate " ++ toString (SalvageLock.actionSlot action).val

def salvageGlyphLabel (glyph : Fin 3) : String :=
  "glyph-" ++ toString glyph.val

def salvageClearedMask (state : SalvageLock.State) : Nat :=
  SalvageLock.allSlots.foldl (fun mask slot =>
    if slot ∈ state.cleared then mask + 2 ^ slot.val else mask) 0

def salvageStateId (state : SalvageLock.State) : String :=
  let exposed := match state.exposed with
    | none => "none"
    | some slot => toString slot.val
  "salvage:" ++ toString (salvageClearedMask state) ++ ":" ++ exposed ++ ":" ++
    toString state.turns

def salvageClearedSlots (state : SalvageLock.State) : List (Fin 6) :=
  SalvageLock.allSlots.filter fun slot => decide (slot ∈ state.cleared)

theorem salvageActions_length : salvageActions.length = 6 := by
  simp [salvageActions]

theorem salvageActions_complete (action : SalvageLock.Action) : action ∈ salvageActions := by
  cases action with
  | expose slot => simp [salvageActions]

/-- Salvage's source transition parameterized only by the semantically relevant
seed; MissionSpec and reward proofs do not influence play. -/
def salvageStep (seed : Fin 3) (state : SalvageLock.State) :
    SalvageLock.Action → Option SalvageLock.State
  | .expose slot =>
      if SalvageLock.openB state slot then
        match state.exposed with
        | none => some { state with exposed := some slot, turns := state.turns + 1 }
        | some first =>
            let cleared :=
              if SalvageLock.glyphAt seed first = SalvageLock.glyphAt seed slot then
                insert slot (insert first state.cleared)
              else state.cleared
            some { cleared, exposed := none, turns := state.turns + 1 }
      else none

theorem salvageStep_eq_source (cfg : SalvageLock.Config) (state : SalvageLock.State)
    (action : SalvageLock.Action) :
    salvageStep cfg.seed state action = SalvageLock.step cfg state action := by
  cases action <;> rfl

def salvageStates (seed : Fin 3) : List SalvageLock.State :=
  stateClosure (salvageStep seed) salvageActions SalvageLock.initialState SalvageLock.MAX_TURNS

structure SalvageTransition where
  state : SalvageLock.State
  action : SalvageLock.Action
  next : Option SalvageLock.State
deriving DecidableEq

def salvageTransitions (seed : Fin 3) : List SalvageTransition :=
  (salvageStates seed).flatMap fun state =>
    salvageActions.map fun action => { state, action, next := salvageStep seed state action }

def salvageTableClosedB (seed : Fin 3) : Bool :=
  (salvageTransitions seed).all fun transition =>
    match transition.next with
    | none => true
    | some next => decide (next ∈ salvageStates seed)

def salvageStatesNodupB (seed : Fin 3) : Bool := (salvageStates seed).Nodup

def salvageStateIdsUniqueB (seed : Fin 3) (stateId : SalvageLock.State → String) : Bool :=
  ((salvageStates seed).map stateId).Nodup

def salvageRefusalReason (state : SalvageLock.State) (action : SalvageLock.Action) :
    Option String :=
  let slot := SalvageLock.actionSlot action
  if SalvageLock.solvedB state then some "solved"
  else if SalvageLock.MAX_TURNS ≤ state.turns then some "turn-limit"
  else if slot ∈ state.cleared then some "cleared-slot"
  else if state.exposed = some slot then some "already-exposed"
  else none

def salvageRefusalReasonsCompleteB (seed : Fin 3) : Bool :=
  (salvageTransitions seed).all fun transition =>
    match transition.next, salvageRefusalReason transition.state transition.action with
    | some _, none => true
    | none, some _ => true
    | _, _ => false

theorem salvageTransitions_length (seed : Fin 3) :
    (salvageTransitions seed).length = (salvageStates seed).length * salvageActions.length := by
  simp [salvageTransitions]

theorem salvageTransition_spec (seed : Fin 3) (transition : SalvageTransition)
    (h : transition ∈ salvageTransitions seed) :
    transition.next = salvageStep seed transition.state transition.action := by
  simp only [salvageTransitions, List.mem_flatMap, List.mem_map] at h
  obtain ⟨state, _hstate, action, _haction, rfl⟩ := h
  rfl

theorem salvageStates_nodup_seed_two : salvageStatesNodupB 2 = true := by
  native_decide

theorem salvageTable_closed_seed_two : salvageTableClosedB 2 = true := by
  native_decide

theorem salvageRefusalReasons_complete_seed_two :
    salvageRefusalReasonsCompleteB 2 = true := by
  native_decide

theorem salvageStateIds_unique_seed_two :
    salvageStateIdsUniqueB 2 salvageStateId = true := by
  native_decide

theorem salvageStates_count_seed_two : (salvageStates 2).length = 164 := by
  native_decide

theorem salvageTransitions_count_seed_two : (salvageTransitions 2).length = 984 := by
  native_decide

#assert_axioms salvageActions_length
#assert_axioms salvageActions_complete
#assert_axioms salvageStep_eq_source
#assert_axioms salvageTransitions_length
#assert_axioms salvageTransition_spec
#assert_compiled salvageStates_nodup_seed_two
#assert_compiled salvageTable_closed_seed_two
#assert_compiled salvageRefusalReasons_complete_seed_two
#assert_compiled salvageStateIds_unique_seed_two
#assert_compiled salvageStates_count_seed_two
#assert_compiled salvageTransitions_count_seed_two

end Dregg2.Games.PathOfAngels.FiniteTables
