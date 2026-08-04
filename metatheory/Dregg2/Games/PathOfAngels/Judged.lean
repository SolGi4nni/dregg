/-
# Dregg2.Games.PathOfAngels.Judged — the closed registry of game judges.

`RunReceipt` is a useful checked world-transition envelope, but it is not evidence
that any particular game was replayed.  This module is the construction boundary:
each `JudgedRun` constructor carries equality to one fixed, executable game judge.
Canon accepts this type, never a caller-assembled generic receipt.
-/
import Dregg2.Games.PathOfAngels.SignalTriangulation
import Dregg2.Games.PathOfAngels.RelayRepair
import Dregg2.Games.PathOfAngels.SalvageLock

namespace Dregg2.Games.PathOfAngels

/-- Issued only after the authenticated catalog and descriptor identify this exact
closed Signal configuration.  The indices include its mission, reward, target, and
activation digest through `config`; no arbitrary public `Config` can supply it. -/
opaque SignalActivation
  (config : SignalTriangulation.Config) (activationDigest : Digest32) : Type

/-- Authenticated exact Relay configuration activation. -/
opaque RelayActivation
  (config : RelayRepair.Config) (activationDigest : Digest32) : Type

/-- Authenticated exact Salvage configuration activation. -/
opaque SalvageActivation
  (config : SalvageLock.Config) (activationDigest : Digest32) : Type

/-- Node-issued settlement authority for one exact player counter step.  The future
node adapter must authenticate the actor-root ↔ player-key binding and current
counter before it can issue this opaque token.  Pure game judges remain playable
without it; only conversion into Canon's settled `JudgedRun` requires it. -/
opaque PlayerRunAuthorization
  (mission : MissionSpec) (actorRoot playerKey : Digest32)
  (previousPlayerCounter : Nat) : Type

inductive JudgedRun where
  | signal
      (config : SignalTriangulation.Config)
      (activation : SignalActivation config config.mission.activationDigest)
      (before : WorldState)
      (context : SignalTriangulation.JudgeContext)
      (playerAuthorization : PlayerRunAuthorization config.mission context.actorRoot
        context.playerKey context.previousPlayerCounter)
      (actions : List SignalTriangulation.Action)
      (run : SignalTriangulation.JudgedRun)
      (judged : SignalTriangulation.judge config before context actions = some run)
  | relay
      (config : RelayRepair.Config)
      (activation : RelayActivation config config.mission.activationDigest)
      (before : WorldState)
      (context : RelayRepair.JudgeContext)
      (playerAuthorization : PlayerRunAuthorization config.mission context.actorRoot
        context.playerKey context.previousPlayerCounter)
      (actions : List RelayRepair.Action)
      (run : RelayRepair.JudgedRun)
      (judged : RelayRepair.judge config before context actions = some run)
  | salvage
      (config : SalvageLock.Config)
      (activation : SalvageActivation config config.mission.activationDigest)
      (before : WorldState)
      (context : SalvageLock.JudgeContext)
      (playerAuthorization : PlayerRunAuthorization config.mission context.actorRoot
        context.playerKey context.previousPlayerCounter)
      (actions : List SalvageLock.Action)
      (run : SalvageLock.JudgedRun)
      (judged : SalvageLock.judge config before context actions = some run)

def JudgedRun.receipt : JudgedRun → RunReceipt
  | .signal _ _ _ _ _ _ run _ => run.receipt
  | .relay _ _ _ _ _ _ run _ => run.receipt
  | .salvage _ _ _ _ _ _ run _ => run.receipt

/-- Every registry member still carries Core's checked world transition; the fixed
judge equality above is the additional evidence generic receipts lacked. -/
theorem JudgedRun.applied (run : JudgedRun) :
    applyContribution run.receipt.mission run.receipt.contribution
      run.receipt.preWorld = some run.receipt.postWorld := by
  cases run <;> exact RunReceipt.applied _

/-- Every judged run's counter is positive before it reaches canon. -/
theorem JudgedRun.player_counter_positive (run : JudgedRun) :
    0 < run.receipt.playerCounter :=
  run.receipt.player_counter_positive

#assert_axioms JudgedRun.applied
#assert_axioms JudgedRun.player_counter_positive

end Dregg2.Games.PathOfAngels
