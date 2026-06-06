/-
# Dregg2.Exec.TurnAdmission — compose the admission prologue with the gated call-forest executor.

`Admission.runTurn` is the fail-closed prologue (fee + nonce + replay + receipt-chain binding) that
dregg1 runs BEFORE the forest fold. `FullForestAuth.execFullForestG` is the production forest executor
with per-node credential+caveat gates. This module wires them together as the devnet-shaped entry:

    runGatedForestTurn ctx hdr pre forest = runTurn ctx hdr pre (execFullForestG · forest)

The prologue commits even when the gated forest body fails (`prologue_survives_failed_body`); an
inadmissible turn is rejected with no edit (`runTurn_inadmissible_rejects`).

ADDITIVE: imports `Admission` + `FullForestAuth`; edits none.
-/
import Dregg2.Exec.Admission
import Dregg2.Exec.FullForestAuth

namespace Dregg2.Exec.TurnAdmission

open Dregg2.Exec (balOf)
open Dregg2.Exec.Admission
open Dregg2.Exec.EffectTransfer (nonceOf)
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.FullForestAuth.Demo (DForest St Wt)

/-- Pin the Demo `Verifiable` instance (local in `Demo`, not visible here). -/
local instance turnAdmissionVerifiable : Dregg2.Laws.Verifiable St Wt where
  Verify _ _ := true

/-- **Devnet-shaped turn execution:** admission prologue ∘ gated call-forest body. -/
def runGatedForestTurn (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (forest : DForest) : Option RecChainedState :=
  runTurn ctx h s (fun s₁ => (execFullForestG s₁) forest)

theorem runGatedForestTurn_inadmissible_rejects (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (forest : DForest) (hbad : admissible ctx h s = false) :
    runGatedForestTurn ctx h s forest = none :=
  runTurn_inadmissible_rejects ctx h s (fun s₁ => execFullForestG s₁ forest) hbad

theorem runGatedForestTurn_failed_body_commits_prologue (ctx : AdmCtx) (h : TurnHdr)
    (s : RecChainedState) (forest : DForest)
    (hadm : admissible ctx h s = true)
    (hbody : execFullForestG (commitPrologue s h.agent h.fee) forest = none) :
    runGatedForestTurn ctx h s forest = some (commitPrologue s h.agent h.fee) := by
  unfold runGatedForestTurn
  exact runTurn_failed_body ctx h s (fun s₁ => execFullForestG s₁ forest) hadm hbody

theorem runGatedForestTurn_prologue_survives_failed_body (ctx : AdmCtx) (h : TurnHdr)
    (s : RecChainedState) (forest : DForest)
    (hadm : admissible ctx h s = true)
    (hbody : execFullForestG (commitPrologue s h.agent h.fee) forest = none) :
    ∃ s', runGatedForestTurn ctx h s forest = some s' ∧
      balOf (s'.kernel.cell h.agent) = balOf (s.kernel.cell h.agent) - h.fee ∧
      nonceOf (s'.kernel.cell h.agent) = nonceOf (s.kernel.cell h.agent) + 1 :=
  prologue_survives_failed_body ctx h s (fun s₁ => execFullForestG s₁ forest) hadm hbody

theorem runGatedForestTurn_committing_body (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState)
    (forest : DForest) (s' : RecChainedState)
    (hadm : admissible ctx h s = true)
    (hbody : execFullForestG (commitPrologue s h.agent h.fee) forest = some s') :
    runGatedForestTurn ctx h s forest = some s' := by
  unfold runGatedForestTurn
  exact prologue_then_commit ctx h s (fun s₁ => execFullForestG s₁ forest) s' hadm hbody

#assert_axioms runGatedForestTurn_inadmissible_rejects
#assert_axioms runGatedForestTurn_failed_body_commits_prologue
#assert_axioms runGatedForestTurn_prologue_survives_failed_body
#assert_axioms runGatedForestTurn_committing_body

end Dregg2.Exec.TurnAdmission