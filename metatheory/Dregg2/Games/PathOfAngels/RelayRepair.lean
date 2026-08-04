/-
# Relay Repair — restore a route through an abandoned ship relay

Four physical links form two possible source-to-sink routes.  Installing a link spends
one spare.  Duplicate work, exhausted inventories, solved panels, and overlong runs
refuse.  The canonical state stores the installed links; reachability is a projection,
so a drifting `solved` counter cannot exist.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.RelayRepair

open Dregg2.Games.PathOfAngels

abbrev MAX_TURNS : Nat := 4
abbrev INITIAL_SPARES : Nat := 4

inductive Link where
  | alphaBeta
  | alphaGamma
  | betaDelta
  | gammaDelta
deriving Repr, DecidableEq

/-- Installed topology is canonical; route availability is derived below. -/
structure Panel where
  alphaBeta : Bool
  alphaGamma : Bool
  betaDelta : Bool
  gammaDelta : Bool
deriving Repr, DecidableEq

def emptyPanel : Panel :=
  { alphaBeta := false, alphaGamma := false, betaDelta := false, gammaDelta := false }

def installed (p : Panel) : Link → Bool
  | .alphaBeta => p.alphaBeta
  | .alphaGamma => p.alphaGamma
  | .betaDelta => p.betaDelta
  | .gammaDelta => p.gammaDelta

def install (p : Panel) : Link → Panel
  | .alphaBeta => { p with alphaBeta := true }
  | .alphaGamma => { p with alphaGamma := true }
  | .betaDelta => { p with betaDelta := true }
  | .gammaDelta => { p with gammaDelta := true }

/-- Exactly the two finite source-to-sink paths in the relay graph. -/
def reachableB (p : Panel) : Bool :=
  (p.alphaBeta && p.betaDelta) || (p.alphaGamma && p.gammaDelta)

structure Config where
  mission : MissionSpec
  reward : Contribution
  reward_accepted : mission.acceptsContribution reward = true

structure State where
  panel  : Panel
  spares : Nat
  turns  : Nat
deriving Repr, DecidableEq

def initialState : State :=
  { panel := emptyPanel, spares := INITIAL_SPARES, turns := 0 }

abbrev Action := Link

def openB (s : State) (a : Action) : Bool :=
  !reachableB s.panel &&
  s.turns < MAX_TURNS &&
  0 < s.spares &&
  !installed s.panel a

def step (_cfg : Config) (s : State) (a : Action) : Option State :=
  if openB s a then
    some {
      panel := install s.panel a
      spares := s.spares - 1
      turns := s.turns + 1
    }
  else
    none

private def terminalOutput (cfg : Config) (s : State) : Option (Contribution × ArtifactRef) :=
  if reachableB s.panel then some (cfg.reward, cfg.mission.artifact) else none

def replay (cfg : Config) : State → List Action → Option State
  | s, [] => some s
  | s, a :: as =>
      match step cfg s a with
      | none => none
      | some s' => replay cfg s' as

def remaining (s : State) : Nat := MAX_TURNS - s.turns

def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by omega)⟩

def linkCode : Link → Nat
  | .alphaBeta => 0
  | .alphaGamma => 1
  | .betaDelta => 2
  | .gammaDelta => 3

def actionAt (actions : List Action) (i : Nat) : Nat :=
  match actions[i]? with
  | some a => linkCode a
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

theorem reachableB_iff_route (p : Panel) :
    reachableB p = true ↔
      (p.alphaBeta = true ∧ p.betaDelta = true) ∨
      (p.alphaGamma = true ∧ p.gammaDelta = true) := by
  simp [reachableB]

theorem step_deterministic (cfg : Config) (s : State) (a : Action) {s₁ s₂ : State}
    (h₁ : step cfg s a = some s₁) (h₂ : step cfg s a = some s₂) : s₁ = s₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem step_consumes_one_spare (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : s'.spares + 1 = s.spares := by
  simp only [step] at h
  split at h
  · rename_i hop
    have hpos : 0 < s.spares := by
      simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hop
      exact hop.1.2
    simp only [Option.some.injEq] at h
    subst s'
    simp only
    omega
  · contradiction

theorem step_never_underflows (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : s'.spares < s.spares := by
  have hc := step_consumes_one_spare cfg s a h
  omega

theorem step_some_turns (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : s'.turns = s.turns + 1 := by
  simp only [step] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst s'
    rfl
  · contradiction

theorem step_some_bound (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : s'.turns ≤ MAX_TURNS := by
  simp only [step] at h
  split at h
  · rename_i hop
    have hlt : s.turns < MAX_TURNS := by
      simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hop
      exact hop.1.1.2
    simp only [Option.some.injEq] at h
    subst s'
    simp only
    omega
  · contradiction

theorem remaining_strictly_decreases (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : remaining s' < remaining s := by
  have ht := step_some_turns cfg s a h
  have hb := step_some_bound cfg s a h
  simp only [remaining]
  omega

theorem duplicate_link_refused (cfg : Config) (s : State) (a : Action)
    (h : installed s.panel a = true) : step cfg s a = none := by
  simp [step, openB, h]

theorem solved_refuses (cfg : Config) (s : State) (a : Action)
    (h : reachableB s.panel = true) : step cfg s a = none := by
  simp [step, openB, h]

theorem no_spares_refuses (cfg : Config) (s : State) (a : Action)
    (h : s.spares = 0) : step cfg s a = none := by
  simp [step, openB, h]

theorem exhausted_refuses (cfg : Config) (s : State) (a : Action)
    (h : MAX_TURNS ≤ s.turns) : step cfg s a = none := by
  simp [step, openB, Nat.not_lt.mpr h]

/-- A concrete legal route witnesses that success is non-vacuous. -/
theorem alpha_beta_route_completes (cfg : Config) :
    ∃ s', replay cfg initialState [.alphaBeta, .betaDelta] = some s' ∧
      reachableB s'.panel = true := by
  refine ⟨{
    panel := { emptyPanel with alphaBeta := true, betaDelta := true }
    spares := 2
    turns := 2
  }, ?_, ?_⟩ <;> rfl

theorem terminalOutput_none_without_route (cfg : Config) (s : State)
    (h : reachableB s.panel = false) : terminalOutput cfg s = none := by
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
    run.receipt.transcriptDigest = transcriptDigest actions := by
  exact (judge_some_sound cfg before ctx actions h).2.2.2.2

theorem replay_append (cfg : Config) (s : State) (xs ys : List Action) :
    replay cfg s (xs ++ ys) = (replay cfg s xs).bind (fun s' => replay cfg s' ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, replay]
      split <;> simp_all

theorem refused_prefix_refuses_replay (cfg : Config) (s : State) (a : Action) (as : List Action)
    (h : step cfg s a = none) : replay cfg s (a :: as) = none := by
  simp [replay, h]

#assert_axioms reachableB_iff_route
#assert_axioms step_deterministic
#assert_axioms step_consumes_one_spare
#assert_axioms step_never_underflows
#assert_axioms step_some_turns
#assert_axioms step_some_bound
#assert_axioms remaining_strictly_decreases
#assert_axioms duplicate_link_refused
#assert_axioms solved_refuses
#assert_axioms no_spares_refuses
#assert_axioms exhausted_refuses
#assert_axioms alpha_beta_route_completes
#assert_axioms terminalOutput_none_without_route
#assert_axioms terminalOutput_is_mission_accepted
#assert_axioms terminalOutput_names_exact_beta_artifact
#assert_axioms terminalOutput_canonical
#assert_axioms judge_some_sound
#assert_axioms judge_receipt_binds_transcript
#assert_axioms replay_append
#assert_axioms refused_prefix_refuses_replay

end Dregg2.Games.PathOfAngels.RelayRepair
