/-
# Containment Inspection — compare two authored sensor sweeps

An inspection board is a finite list of authored hit regions.  Each region is an
explicit finite set of cells rather than an unverified image-space convention.
Accepted clicks either discover one fresh region or consume one false-positive
allowance.  Out-of-bounds clicks, exact repeated (reflexive) clicks, clicks inside
an already-discovered region, exhausted false-positive budgets, solved boards and
exhausted action budgets all refuse.

The contribution is derived from one mission-accepted reward by subtracting a
bounded score penalty for false positives.  `judge` is the only authoritative
world-transition surface and binds the complete accepted click transcript.
-/
import Dregg2.Games.PathOfAngels.Core

namespace Dregg2.Games.PathOfAngels.ContainmentInspection

open Dregg2.Games.PathOfAngels

/-- Two coordinates per click plus one length byte fit in a 32-byte transcript. -/
abbrev MAX_ACTIONS : Nat := 15

/-- Authored regions remain deliberately small enough for finite validation and UI review. -/
abbrev MAX_REGIONS : Nat := 15

structure Point where
  x : Nat
  y : Nat
deriving Repr, DecidableEq

def Point.inBounds (point : Point) (width height : Nat) : Bool :=
  decide (point.x < width ∧ point.y < height)

theorem Point.inBounds_eq_true_iff (point : Point) (width height : Nat) :
    point.inBounds width height = true ↔ point.x < width ∧ point.y < height := by
  simp [Point.inBounds]

structure RegionId where
  value : Nat
deriving Repr, DecidableEq

/-- A region is an exact finite population of clickable cells. -/
structure Region where
  id : RegionId
  cells : Finset Point
deriving DecidableEq

def Region.containsB (region : Region) (point : Point) : Bool :=
  decide (point ∈ region.cells)

theorem Region.containsB_eq_true_iff (region : Region) (point : Point) :
    region.containsB point = true ↔ point ∈ region.cells := by
  simp [Region.containsB]

/-- First-match lookup is deterministic.  `Config.regions_unambiguous` proves that
well-formed authored content never has a second distinct match. -/
def regionAtList? : List Region → Point → Option Region
  | [], _ => none
  | region :: regions, point =>
      if region.containsB point then some region else regionAtList? regions point

theorem regionAtList_some_mem_contains {regions : List Region} {point : Point}
    {region : Region} (h : regionAtList? regions point = some region) :
    region ∈ regions ∧ point ∈ region.cells := by
  induction regions with
  | nil => simp [regionAtList?] at h
  | cons head tail ih =>
      simp only [regionAtList?] at h
      split at h
      · rename_i hcontains
        have heq : head = region := by simpa using h
        subst region
        exact ⟨by simp, (Region.containsB_eq_true_iff head point).mp hcontains⟩
      · rename_i hcontains
        have htail := ih h
        exact ⟨by simp [htail.1], htail.2⟩

/-- Proof-carrying authored board plus the mission reward policy.  The content
compiler is expected to discharge these decidable obligations before activation. -/
structure Config where
  width : Nat
  height : Nat
  regions : List Region
  actionLimit : Nat
  falsePositiveLimit : Nat
  falsePositivePenalty : Nat
  mission : MissionSpec
  reward : Contribution
  width_positive : 0 < width
  height_positive : 0 < height
  width_byte_bounded : width ≤ 256
  height_byte_bounded : height ≤ 256
  regions_nonempty : regions ≠ []
  regions_bounded : regions.length ≤ MAX_REGIONS
  regions_fit_actions : regions.length ≤ actionLimit
  region_ids_nodup : (regions.map Region.id).Nodup
  region_cells_nonempty : ∀ region ∈ regions, region.cells.Nonempty
  region_cells_in_bounds : ∀ region ∈ regions, ∀ point ∈ region.cells,
    point.x < width ∧ point.y < height
  regions_unambiguous : ∀ {first second point},
    first ∈ regions → second ∈ regions → first.id ≠ second.id →
      ¬ (point ∈ first.cells ∧ point ∈ second.cells)
  action_limit_positive : 0 < actionLimit
  action_limit_bounded : actionLimit ≤ MAX_ACTIONS
  false_positive_limit_bounded : falsePositiveLimit ≤ actionLimit
  false_positive_penalty_bounded : falsePositivePenalty ≤ METRIC_LIMIT
  reward_accepted : mission.acceptsContribution reward = true

def regionAt? (cfg : Config) (point : Point) : Option Region :=
  regionAtList? cfg.regions point

theorem regionAt_some_mem_contains (cfg : Config) {point : Point} {region : Region}
    (h : regionAt? cfg point = some region) :
    region ∈ cfg.regions ∧ point ∈ region.cells :=
  regionAtList_some_mem_contains h

theorem distinct_authored_regions_cannot_share_click (cfg : Config)
    {first second : Region} {point : Point}
    (hfirst : first ∈ cfg.regions) (hsecond : second ∈ cfg.regions)
    (hid : first.id ≠ second.id) :
    ¬ (point ∈ first.cells ∧ point ∈ second.cells) :=
  cfg.regions_unambiguous hfirst hsecond hid

structure State where
  found : Finset RegionId
  clicked : Finset Point
  falsePositives : Nat
  turns : Nat
deriving DecidableEq

def initialState : State :=
  { found := ∅, clicked := ∅, falsePositives := 0, turns := 0 }

inductive Action where
  | click (point : Point)
deriving Repr, DecidableEq

/-- Completion is derived from the authored region IDs, never from a caller-owned counter. -/
def solvedB (cfg : Config) (state : State) : Bool :=
  cfg.regions.all (fun region => decide (region.id ∈ state.found))

def openB (cfg : Config) (state : State) : Bool :=
  !solvedB cfg state &&
  state.turns < cfg.actionLimit &&
  state.falsePositives ≤ cfg.falsePositiveLimit

/-- Every click has one explicit semantic classification.  Exact point repetition
is called reflexive even when the first click was a false positive; a different
point in a previously found region is a duplicate-region click. -/
inductive ClickDecision where
  | acceptHit (region : RegionId)
  | acceptFalsePositive
  | rejectOutOfBounds
  | rejectReflexive
  | rejectDuplicateRegion (region : RegionId)
  | rejectFalsePositiveBudget
deriving Repr, DecidableEq

def clickDecision (cfg : Config) (state : State) (point : Point) : ClickDecision :=
  if !point.inBounds cfg.width cfg.height then
    .rejectOutOfBounds
  else if decide (point ∈ state.clicked) then
    .rejectReflexive
  else
    match regionAt? cfg point with
    | some region =>
        if decide (region.id ∈ state.found) then
          .rejectDuplicateRegion region.id
        else
          .acceptHit region.id
    | none =>
        if state.falsePositives < cfg.falsePositiveLimit then
          .acceptFalsePositive
        else
          .rejectFalsePositiveBudget

/-- Refused decisions are fail-stop `none`, not accepted no-ops. -/
def step (cfg : Config) (state : State) : Action → Option State
  | .click point =>
      if openB cfg state then
        match clickDecision cfg state point with
        | .acceptHit region =>
            some {
              found := insert region state.found
              clicked := insert point state.clicked
              falsePositives := state.falsePositives
              turns := state.turns + 1
            }
        | .acceptFalsePositive =>
            some {
              found := state.found
              clicked := insert point state.clicked
              falsePositives := state.falsePositives + 1
              turns := state.turns + 1
            }
        | .rejectOutOfBounds => none
        | .rejectReflexive => none
        | .rejectDuplicateRegion _ => none
        | .rejectFalsePositiveBudget => none
      else
        none

/-- Replay refuses at the first refused click. -/
def replay (cfg : Config) : State → List Action → Option State
  | state, [] => some state
  | state, action :: actions =>
      match step cfg state action with
      | none => none
      | some state' => replay cfg state' actions

def remaining (cfg : Config) (state : State) : Nat :=
  cfg.actionLimit - state.turns

/-- False positives can reduce score but can never increase it or affect the
reward's other bounded fields.  Natural subtraction is deliberate: a penalty may
floor the score at zero, never wrap. -/
def penalizedScore (cfg : Config) (state : State) : Metric :=
  ⟨cfg.reward.score.val - state.falsePositives * cfg.falsePositivePenalty,
    lt_of_le_of_lt (Nat.sub_le _ _) cfg.reward.score.isLt⟩

def penalizedContribution (cfg : Config) (state : State) : Contribution :=
  { cfg.reward with score := penalizedScore cfg state }

theorem penalized_score_le_reward (cfg : Config) (state : State) :
    (penalizedContribution cfg state).score.val ≤ cfg.reward.score.val := by
  simp [penalizedContribution, penalizedScore]

theorem penalizedContribution_accepted (cfg : Config) (state : State) :
    cfg.mission.acceptsContribution (penalizedContribution cfg state) = true := by
  have hreward :=
    (MissionSpec.acceptsContribution_eq_true_iff cfg.mission cfg.reward).mp
      cfg.reward_accepted
  have hwithin :=
    (Contribution.within_eq_true_iff cfg.reward cfg.mission.budget).mp hreward.1
  apply (MissionSpec.acceptsContribution_eq_true_iff cfg.mission
    (penalizedContribution cfg state)).mpr
  constructor
  · apply (Contribution.within_eq_true_iff (penalizedContribution cfg state)
      cfg.mission.budget).mpr
    exact ⟨hwithin.1, hwithin.2.1, hwithin.2.2.1, hwithin.2.2.2.1,
      (penalized_score_le_reward cfg state).trans hwithin.2.2.2.2.1,
      hwithin.2.2.2.2.2⟩
  · exact hreward.2

private def terminalOutput (cfg : Config) (state : State) :
    Option (Contribution × ArtifactRef) :=
  if solvedB cfg state then
    some (penalizedContribution cfg state, cfg.mission.artifact)
  else
    none

def byte (n : Nat) : Fin 256 :=
  ⟨n % 256, Nat.mod_lt _ (by omega)⟩

def zeroPoint : Point := { x := 0, y := 0 }

def actionPoint : Action → Point
  | .click point => point

def pointAt (actions : List Action) (index : Nat) : Point :=
  match actions[index]? with
  | some action => actionPoint action
  | none => zeroPoint

/-- Accepted runs have at most fifteen actions, so byte zero binds the length and
bytes 1..30 bind every `(x,y)` pair.  Config bounds accepted coordinates to bytes. -/
def transcriptDigest (actions : List Action) : Digest32 where
  bytes := List.ofFn (fun index : Fin 32 =>
    if index.val = 0 then byte actions.length else
      let offset := index.val - 1
      let point := pointAt actions (offset / 2)
      if offset % 2 = 0 then byte point.x else byte point.y)
  length_eq := by simp

structure JudgeContext where
  actorRoot : Digest32
  playerKey : Digest32
  previousPlayerCounter : Nat

structure JudgedRun where
  finalState : State
  afterWorld : WorldState
  receipt : RunReceipt

/-- Fixed inspection judge: replay from genesis, require completion, derive the
penalized contribution, apply it atomically, and bind the exact accepted transcript. -/
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

/-! ## Transition and refusal theorems -/

theorem step_deterministic (cfg : Config) (state : State) (action : Action)
    {first second : State}
    (hfirst : step cfg state action = some first)
    (hsecond : step cfg state action = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem step_some_turns (cfg : Config) (state : State) (action : Action)
    {state' : State} (h : step cfg state action = some state') :
    state'.turns = state.turns + 1 := by
  cases action with
  | click point =>
      simp only [step] at h
      split at h
      · generalize hd : clickDecision cfg state point = decision at h
        cases decision <;> simp only [Option.some.injEq] at h <;> try contradiction
        · subst state'
          rfl
        · subst state'
          rfl
      · contradiction

theorem step_some_turn_bound (cfg : Config) (state : State) (action : Action)
    {state' : State} (h : step cfg state action = some state') :
    state'.turns ≤ cfg.actionLimit := by
  have hturn := step_some_turns cfg state action h
  cases action with
  | click point =>
      simp only [step] at h
      split at h
      · rename_i hopen
        have hlt : state.turns < cfg.actionLimit := by
          simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hopen
          exact hopen.1.2
        omega
      · contradiction

theorem remaining_strictly_decreases (cfg : Config) (state : State) (action : Action)
    {state' : State} (h : step cfg state action = some state') :
    remaining cfg state' < remaining cfg state := by
  have hturn := step_some_turns cfg state action h
  have hbound := step_some_turn_bound cfg state action h
  simp only [remaining]
  omega

theorem step_found_never_shrinks (cfg : Config) (state : State) (action : Action)
    {state' : State} (h : step cfg state action = some state') :
    state.found ⊆ state'.found := by
  cases action with
  | click point =>
      simp only [step] at h
      split at h
      · generalize hd : clickDecision cfg state point = decision at h
        cases decision <;> simp only [Option.some.injEq] at h <;> try contradiction
        · subst state'
          exact Finset.subset_insert _ _
        · subst state'
          exact Finset.Subset.rfl
      · contradiction

theorem clickDecision_acceptFalsePositive_implies_lt (cfg : Config) (state : State)
    (point : Point)
    (h : clickDecision cfg state point = .acceptFalsePositive) :
    state.falsePositives < cfg.falsePositiveLimit := by
  unfold clickDecision at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h
  · split at h <;> contradiction
  · split at h
    · assumption
    · contradiction

theorem step_some_false_positive_bound (cfg : Config) (state : State) (action : Action)
    {state' : State} (h : step cfg state action = some state') :
    state'.falsePositives ≤ cfg.falsePositiveLimit := by
  cases action with
  | click point =>
      simp only [step] at h
      split at h
      · rename_i hopen
        have hbefore : state.falsePositives ≤ cfg.falsePositiveLimit := by
          simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hopen
          exact hopen.2
        generalize hd : clickDecision cfg state point = decision at h
        cases decision with
        | acceptHit region =>
            simp only [Option.some.injEq] at h
            subst state'
            exact hbefore
        | acceptFalsePositive =>
            have hlt := clickDecision_acceptFalsePositive_implies_lt cfg state point hd
            simp only [Option.some.injEq] at h
            subst state'
            simp only
            omega
        | rejectOutOfBounds => contradiction
        | rejectReflexive => contradiction
        | rejectDuplicateRegion region => contradiction
        | rejectFalsePositiveBudget => contradiction
      · contradiction

theorem out_of_bounds_click_refused (cfg : Config) (state : State) (point : Point)
    (h : point.inBounds cfg.width cfg.height = false) :
    step cfg state (.click point) = none := by
  simp [step, clickDecision, h]

/-- Exact repetition is refused whether the original point was a hit or a miss. -/
theorem reflexive_click_refused (cfg : Config) (state : State) (point : Point)
    (h : point ∈ state.clicked) : step cfg state (.click point) = none := by
  by_cases hbounds : point.inBounds cfg.width cfg.height = true
  · simp [step, clickDecision, hbounds, h]
  · have hfalse : point.inBounds cfg.width cfg.height = false := by
      exact Bool.eq_false_of_not_eq_true hbounds
    exact out_of_bounds_click_refused cfg state point hfalse

/-- A different point inside an already-found authored region is also refused. -/
theorem duplicate_region_click_refused (cfg : Config) (state : State)
    (point : Point) (region : Region)
    (hbounds : point.inBounds cfg.width cfg.height = true)
    (hfreshPoint : point ∉ state.clicked)
    (hregion : regionAt? cfg point = some region)
    (hfound : region.id ∈ state.found) :
    step cfg state (.click point) = none := by
  simp [step, clickDecision, hbounds, hfreshPoint, hregion, hfound]

theorem false_positive_budget_click_refused (cfg : Config) (state : State)
    (point : Point)
    (hbounds : point.inBounds cfg.width cfg.height = true)
    (hfreshPoint : point ∉ state.clicked)
    (hregion : regionAt? cfg point = none)
    (hexhausted : cfg.falsePositiveLimit ≤ state.falsePositives) :
    step cfg state (.click point) = none := by
  simp [step, clickDecision, hbounds, hfreshPoint, hregion,
    Nat.not_lt.mpr hexhausted]

theorem solved_refuses (cfg : Config) (state : State) (action : Action)
    (h : solvedB cfg state = true) : step cfg state action = none := by
  cases action
  simp [step, openB, h]

theorem exhausted_refuses (cfg : Config) (state : State) (action : Action)
    (h : cfg.actionLimit ≤ state.turns) : step cfg state action = none := by
  cases action
  simp [step, openB, Nat.not_lt.mpr h]

theorem fresh_hit_records_region (cfg : Config) (state : State)
    (point : Point) (region : Region)
    (hopen : openB cfg state = true)
    (hbounds : point.inBounds cfg.width cfg.height = true)
    (hfreshPoint : point ∉ state.clicked)
    (hregion : regionAt? cfg point = some region)
    (hfreshRegion : region.id ∉ state.found) :
    step cfg state (.click point) = some {
      found := insert region.id state.found
      clicked := insert point state.clicked
      falsePositives := state.falsePositives
      turns := state.turns + 1
    } := by
  simp [step, clickDecision, hopen, hbounds, hfreshPoint, hregion, hfreshRegion]

theorem fresh_false_positive_is_counted (cfg : Config) (state : State)
    (point : Point)
    (hopen : openB cfg state = true)
    (hbounds : point.inBounds cfg.width cfg.height = true)
    (hfreshPoint : point ∉ state.clicked)
    (hregion : regionAt? cfg point = none)
    (hbudget : state.falsePositives < cfg.falsePositiveLimit) :
    step cfg state (.click point) = some {
      found := state.found
      clicked := insert point state.clicked
      falsePositives := state.falsePositives + 1
      turns := state.turns + 1
    } := by
  simp [step, clickDecision, hopen, hbounds, hfreshPoint, hregion, hbudget]

/-! ## Replay, terminality and judge theorems -/

theorem replay_append (cfg : Config) (state : State) (first second : List Action) :
    replay cfg state (first ++ second) =
      (replay cfg state first).bind (fun state' => replay cfg state' second) := by
  induction first generalizing state with
  | nil => rfl
  | cons action actions ih =>
      simp only [List.cons_append, replay]
      split <;> simp_all

theorem refused_prefix_refuses_replay (cfg : Config) (state : State)
    (action : Action) (actions : List Action)
    (h : step cfg state action = none) :
    replay cfg state (action :: actions) = none := by
  simp [replay, h]

theorem replay_some_turns (cfg : Config) (state : State) (actions : List Action)
    {state' : State} (h : replay cfg state actions = some state') :
    state'.turns = state.turns + actions.length := by
  induction actions generalizing state state' with
  | nil =>
      simp only [replay, Option.some.injEq] at h
      subst state'
      simp
  | cons action actions ih =>
      simp only [replay] at h
      split at h
      · contradiction
      · rename_i next hstep
        have htail := ih (state := next) h
        have hturn := step_some_turns cfg state action hstep
        simp only [List.length_cons]
        rw [htail, hturn]
        omega

theorem replay_some_turn_bound (cfg : Config) (state : State) (actions : List Action)
    {state' : State} (hstart : state.turns ≤ cfg.actionLimit)
    (h : replay cfg state actions = some state') :
    state'.turns ≤ cfg.actionLimit := by
  induction actions generalizing state state' with
  | nil =>
      simp only [replay, Option.some.injEq] at h
      subst state'
      exact hstart
  | cons action actions ih =>
      simp only [replay] at h
      split at h
      · contradiction
      · rename_i next hstep
        exact ih (state := next) (step_some_turn_bound cfg state action hstep) h

theorem replay_some_false_positive_bound (cfg : Config) (state : State)
    (actions : List Action) {state' : State}
    (hstart : state.falsePositives ≤ cfg.falsePositiveLimit)
    (h : replay cfg state actions = some state') :
    state'.falsePositives ≤ cfg.falsePositiveLimit := by
  induction actions generalizing state state' with
  | nil =>
      simp only [replay, Option.some.injEq] at h
      subst state'
      exact hstart
  | cons action actions ih =>
      simp only [replay] at h
      split at h
      · contradiction
      · rename_i next hstep
        exact ih (state := next) (step_some_false_positive_bound cfg state action hstep) h

theorem replay_initial_length_bounded (cfg : Config) (actions : List Action)
    {state : State} (h : replay cfg initialState actions = some state) :
    actions.length ≤ cfg.actionLimit := by
  have hturns := replay_some_turns cfg initialState actions h
  have hbound := replay_some_turn_bound cfg initialState actions (by simp [initialState]) h
  simp only [initialState] at hturns
  omega

theorem terminalOutput_none_before_solution (cfg : Config) (state : State)
    (h : solvedB cfg state = false) : terminalOutput cfg state = none := by
  simp [terminalOutput, h]

theorem terminalOutput_is_mission_accepted (cfg : Config) (state : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg state = some out) :
    cfg.mission.acceptsContribution out.1 = true := by
  simp only [terminalOutput] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst out
    exact penalizedContribution_accepted cfg state
  · contradiction

theorem terminalOutput_names_exact_beta_artifact (cfg : Config) (state : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg state = some out) :
    out.2 = cfg.mission.artifact := by
  simp only [terminalOutput] at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
  · contradiction

theorem terminalOutput_canonical (cfg : Config) (state : State)
    {contribution : Contribution} {artifact : ArtifactRef}
    (h : terminalOutput cfg state = some (contribution, artifact)) :
    terminalOutput cfg state = some (contribution, cfg.mission.artifact) := by
  have hart := terminalOutput_names_exact_beta_artifact cfg state h
  change artifact = cfg.mission.artifact at hart
  rw [hart] at h
  exact h

theorem judge_some_sound (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
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
    run.receipt.transcriptDigest = transcriptDigest actions := by
  exact (judge_some_sound cfg before ctx actions h).2.2.2.2

theorem judge_final_state_solved (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
    solvedB cfg run.finalState = true := by
  have hsound := judge_some_sound cfg before ctx actions h
  have hterminal := hsound.2.1
  simp only [terminalOutput] at hterminal
  split at hterminal
  · assumption
  · contradiction

theorem judge_action_count_bounded (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
    actions.length ≤ cfg.actionLimit :=
  replay_initial_length_bounded cfg actions (judge_some_sound cfg before ctx actions h).1

theorem judge_false_positives_bounded (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
    run.finalState.falsePositives ≤ cfg.falsePositiveLimit := by
  have hreplay := (judge_some_sound cfg before ctx actions h).1
  exact replay_some_false_positive_bound cfg initialState actions
    (by simp [initialState]) hreplay

/-! ## Named executable examples -/

def fixturePointA : Point := { x := 1, y := 1 }
def fixturePointAEdge : Point := { x := 1, y := 2 }
def fixturePointB : Point := { x := 3, y := 1 }
def fixtureMiss : Point := { x := 0, y := 0 }

def fixtureRegionA : Region :=
  { id := ⟨10⟩, cells := {fixturePointA, fixturePointAEdge} }

def fixtureRegionB : Region :=
  { id := ⟨20⟩, cells := {fixturePointB} }

def fixtureRegions : List Region := [fixtureRegionA, fixtureRegionB]

theorem fixture_click_finds_first_region :
    regionAtList? fixtureRegions fixturePointA = some fixtureRegionA := by
  decide

theorem fixture_edge_click_finds_same_region :
    regionAtList? fixtureRegions fixturePointAEdge = some fixtureRegionA := by
  decide

theorem fixture_click_finds_second_region :
    regionAtList? fixtureRegions fixturePointB = some fixtureRegionB := by
  decide

theorem fixture_miss_finds_no_region :
    regionAtList? fixtureRegions fixtureMiss = none := by
  decide

#assert_axioms Point.inBounds_eq_true_iff
#assert_axioms Region.containsB_eq_true_iff
#assert_axioms regionAtList_some_mem_contains
#assert_axioms regionAt_some_mem_contains
#assert_axioms distinct_authored_regions_cannot_share_click
#assert_axioms penalized_score_le_reward
#assert_axioms penalizedContribution_accepted
#assert_axioms step_deterministic
#assert_axioms step_some_turns
#assert_axioms step_some_turn_bound
#assert_axioms remaining_strictly_decreases
#assert_axioms step_found_never_shrinks
#assert_axioms clickDecision_acceptFalsePositive_implies_lt
#assert_axioms step_some_false_positive_bound
#assert_axioms out_of_bounds_click_refused
#assert_axioms reflexive_click_refused
#assert_axioms duplicate_region_click_refused
#assert_axioms false_positive_budget_click_refused
#assert_axioms solved_refuses
#assert_axioms exhausted_refuses
#assert_axioms fresh_hit_records_region
#assert_axioms fresh_false_positive_is_counted
#assert_axioms replay_append
#assert_axioms refused_prefix_refuses_replay
#assert_axioms replay_some_turns
#assert_axioms replay_some_turn_bound
#assert_axioms replay_some_false_positive_bound
#assert_axioms replay_initial_length_bounded
#assert_axioms terminalOutput_none_before_solution
#assert_axioms terminalOutput_is_mission_accepted
#assert_axioms terminalOutput_names_exact_beta_artifact
#assert_axioms terminalOutput_canonical
#assert_axioms judge_some_sound
#assert_axioms judge_receipt_binds_transcript
#assert_axioms judge_final_state_solved
#assert_axioms judge_action_count_bounded
#assert_axioms judge_false_positives_bounded
#assert_axioms fixture_click_finds_first_region
#assert_axioms fixture_edge_click_finds_same_region
#assert_axioms fixture_click_finds_second_region
#assert_axioms fixture_miss_finds_no_region

end Dregg2.Games.PathOfAngels.ContainmentInspection
