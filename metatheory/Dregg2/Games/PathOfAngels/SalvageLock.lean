/-
# Salvage Lock — a deterministic paired-glyph hatch

Six sealed plates carry exactly two copies of each of three glyphs.  One plate may
remain exposed between actions; the second exposure either clears a matching pair or
closes both.  The type therefore makes an impossible "three exposed plates" state
unrepresentable.  All shared-world effects go through `judge` and Core's receipt.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.SalvageLock

open Dregg2.Games.PathOfAngels

abbrev MAX_TURNS : Nat := 12

def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by omega)⟩

/-- A three-way seed class is sufficient to rotate the paired board. -/
def glyphAt (seed : Fin 3) (slot : Fin 6) : Fin 3 :=
  ⟨(slot.val + seed.val) % 3, Nat.mod_lt _ (by omega)⟩

def seedFromRunSeed (runSeed : Digest32) : Fin 3 :=
  ⟨(runSeed.bytes.getD 0 0).val % 3, Nat.mod_lt _ (by omega)⟩

def allSlots : List (Fin 6) := [0, 1, 2, 3, 4, 5]

def glyphPopulation (seed : Fin 3) (glyph : Fin 3) : Nat :=
  (allSlots.filter (fun slot => glyphAt seed slot = glyph)).length

/-- Generated boards contain exactly two of each glyph, for every seed. -/
theorem glyph_population_two : ∀ seed glyph : Fin 3, glyphPopulation seed glyph = 2 := by
  decide

structure Config where
  seed : Fin 3
  mission : MissionSpec
  reward : Contribution
  reward_accepted : mission.acceptsContribution reward = true
  seed_eq : seed = seedFromRunSeed mission.runSeed

structure State where
  cleared : Finset (Fin 6)
  exposed : Option (Fin 6)
  turns : Nat
deriving DecidableEq

def initialState : State := { cleared := ∅, exposed := none, turns := 0 }

inductive Action where
  | expose (slot : Fin 6)
deriving Repr, DecidableEq

def solvedB (s : State) : Bool := s.cleared.card == 6

def openB (s : State) (slot : Fin 6) : Bool :=
  !solvedB s &&
  s.turns < MAX_TURNS &&
  decide (slot ∉ s.cleared) &&
  decide (s.exposed ≠ some slot)

def step (cfg : Config) (s : State) : Action → Option State
  | .expose slot =>
      if openB s slot then
        match s.exposed with
        | none => some { s with exposed := some slot, turns := s.turns + 1 }
        | some first =>
            let cleared :=
              if glyphAt cfg.seed first = glyphAt cfg.seed slot then
                insert slot (insert first s.cleared)
              else
                s.cleared
            some { cleared, exposed := none, turns := s.turns + 1 }
      else
        none

def replay (cfg : Config) : State → List Action → Option State
  | s, [] => some s
  | s, a :: as =>
      match step cfg s a with
      | none => none
      | some s' => replay cfg s' as

private def terminalOutput (cfg : Config) (s : State) : Option (Contribution × ArtifactRef) :=
  if solvedB s then some (cfg.reward, cfg.mission.artifact) else none

def actionSlot : Action → Fin 6
  | .expose slot => slot

def actionAt (actions : List Action) (i : Nat) : Nat :=
  match actions[i]? with
  | some a => (actionSlot a).val
  | none => 255

def transcriptDigest (actions : List Action) : Digest32 where
  bytes := List.ofFn (fun i : Fin 32 =>
    if i.val = 0 then byte actions.length else byte (actionAt actions (i.val - 1)))
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

def remaining (s : State) : Nat := MAX_TURNS - s.turns

def exposedCount (s : State) : Nat :=
  match s.exposed with
  | none => 0
  | some _ => 1

theorem exposed_population_le_one (s : State) : exposedCount s ≤ 1 := by
  cases h : s.exposed <;> simp [exposedCount, h]

theorem step_deterministic (cfg : Config) (s : State) (a : Action) {s₁ s₂ : State}
    (h₁ : step cfg s a = some s₁) (h₂ : step cfg s a = some s₂) : s₁ = s₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem step_some_turns (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : s'.turns = s.turns + 1 := by
  cases a with
  | expose slot =>
      simp only [step] at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst s'
          rfl
        · simp only [Option.some.injEq] at h
          subst s'
          rfl
      · contradiction

theorem step_some_bound (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : s'.turns ≤ MAX_TURNS := by
  have ht := step_some_turns cfg s a h
  cases a with
  | expose slot =>
    simp only [step] at h
    split at h
    · rename_i hop
      have hlt : s.turns < MAX_TURNS := by
        simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hop
        exact hop.1.1.2
      omega
    · contradiction

theorem remaining_strictly_decreases (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : remaining s' < remaining s := by
  have ht := step_some_turns cfg s a h
  have hb := step_some_bound cfg s a h
  simp only [remaining]
  omega

theorem cleared_never_shrinks (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : s.cleared ⊆ s'.cleared := by
  cases a with
  | expose slot =>
      simp only [step] at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst s'
          exact Finset.Subset.rfl
        · split at h
          · simp only [Option.some.injEq] at h
            subst s'
            exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
          · simp only [Option.some.injEq] at h
            subst s'
            exact Finset.Subset.rfl
      · contradiction

theorem matching_second_exposure_clears (cfg : Config) (s : State) (first slot : Fin 6)
    (hopen : openB s slot = true)
    (hexposed : s.exposed = some first)
    (hmatch : glyphAt cfg.seed first = glyphAt cfg.seed slot) :
    step cfg s (.expose slot) = some {
      cleared := insert slot (insert first s.cleared)
      exposed := none
      turns := s.turns + 1
    } := by
  simp [step, hopen, hexposed, hmatch]

theorem duplicate_exposure_refused (cfg : Config) (s : State) (slot : Fin 6)
    (h : s.exposed = some slot) : step cfg s (.expose slot) = none := by
  simp [step, openB, h]

theorem cleared_slot_refused (cfg : Config) (s : State) (slot : Fin 6)
    (h : slot ∈ s.cleared) : step cfg s (.expose slot) = none := by
  simp [step, openB, h]

theorem solved_refuses (cfg : Config) (s : State) (a : Action)
    (h : solvedB s = true) : step cfg s a = none := by
  cases a <;> simp [step, openB, h]

theorem exhausted_refuses (cfg : Config) (s : State) (a : Action)
    (h : MAX_TURNS ≤ s.turns) : step cfg s a = none := by
  cases a <;> simp [step, openB, Nat.not_lt.mpr h]

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

theorem judge_receipt_binds_seed (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    cfg.seed = seedFromRunSeed run.receipt.runSeed := by
  have hs := judge_some_sound cfg before ctx actions h
  rw [run.receipt.run_seed_matches, hs.2.2.2.1]
  exact cfg.seed_eq

theorem judge_receipt_binds_transcript (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    run.receipt.transcriptDigest = transcriptDigest actions := by
  exact (judge_some_sound cfg before ctx actions h).2.2.2.2

#assert_axioms glyph_population_two
#assert_axioms exposed_population_le_one
#assert_axioms step_deterministic
#assert_axioms step_some_turns
#assert_axioms step_some_bound
#assert_axioms remaining_strictly_decreases
#assert_axioms cleared_never_shrinks
#assert_axioms matching_second_exposure_clears
#assert_axioms duplicate_exposure_refused
#assert_axioms cleared_slot_refused
#assert_axioms solved_refuses
#assert_axioms exhausted_refuses
#assert_axioms replay_append
#assert_axioms refused_prefix_refuses_replay
#assert_axioms terminalOutput_is_mission_accepted
#assert_axioms terminalOutput_names_exact_beta_artifact
#assert_axioms terminalOutput_canonical
#assert_axioms judge_some_sound
#assert_axioms judge_receipt_binds_seed
#assert_axioms judge_receipt_binds_transcript

end Dregg2.Games.PathOfAngels.SalvageLock
