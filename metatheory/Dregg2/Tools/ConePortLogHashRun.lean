/-
# Dregg2.Tools.ConePortLogHashRun — the ConePort DRIVER for the `logHashInjective` LEVEL-2 cone,
with the measurement PINNED as a build-time tooth.

The 16 `logHashInjective` ENDPOINTS were cut over in place (`Circuit/LogCommitRegrounded` supplies the
total extractor and the S3 form; `Circuit/LogCommitCutoverCheck` holds their teeth). Their 48 direct
consumers were rewired through the ONE uniform bridge `LogCommitRegrounded.noLogColl_of_inj` — and this
module is the machine-checked answer to the question that decides the next wave: **is the rest of that
cone mechanical?**

⚑ EIGHT OF THE ORIGINAL 48 PINS ARE GONE FROM THIS LIST, and their absence is the campaign WORKING.
The four adversarial-witness EXTRACTORS and their log-forgery teeth
(`WitnessExtract{,Dual,3,5}.effect2*_extract{,_rejects_log_forge}`) were CUT OVER IN PLACE on 07-25 —
same names, same conclusions, `logHashInjective S.LH` replaced by the per-instance
`¬ LogColl S.LH (E.view.getLog post) (E.postLog pre args)` — so ConePort correctly no longer sees a
carrier at those names and a `.port` pin there would now FAIL. Their teeth moved to
`Circuit/LogCommitCutoverCheck` §7 (kernel-defeq statement pins + `#assert_not_depends_on` +
no-strength-lost), which is where a cut-over endpoint belongs; this module measures what is still
PORTABLE, not what is already ported. The 28 `WitnessExtractPerEffect` instantiations and the
`TurnEmit` mint pair went with them and were never pinned here (they are consumers of consumers).

MEASURED, 2026-07-25, on this tree: **48 PORTED / 48 eligible, 0 refusals, 0 unexplained.** Every port
is one bridge application (`sites=1, sideConds=1`), each one surgered on the ELABORATED term,
`Meta.check`ed, kernel-`addDecl`ed and delaboration-ROUND-TRIPPED before it counts. That is the whole
level-2 cone of the largest refuted floor in the tree, and it says the remaining 313 `logHashInjective`
carriers are a codemod problem, not 313 re-proofs.

The two pinned REFUSALS are `CircuitSoundness.turnDecodeChainLog_seam_log_derived` /
`_rejects_forged_log`, and they are the reason the number is 48 and not 50. When this measurement was
taken they carried the floor as a STRUCTURE FIELD (`TurnDecodeChainLog.hLog : logHashInjective LH`),
not as a telescope binder — the field-bundle class, where a field has no argument position to be
per-instance AT, so the port unit is the BUNDLE and not a mechanical rewrite.

⚑ **THAT BUNDLE WAS CUT OVER (2026-07-25).** `TurnDecodeChainLog.hLog` is DELETED; both theorems now
take `CircuitSoundness.NoLogSeamColl LH c.steps` — `¬ LogColl` at exactly the chain adjacencies the
deleted field was fed — and the bundle is re-inhabited at a deployed accumulator whose
`logHashInjective` is REFUTED (`Circuit/TurnDecodeChainLogBundleCutoverCheck`). Both pins therefore
STAY `.refuse "not a carrier"`, and now for the strongest possible reason: the floor is not merely
out of ConePort's reach at these names, it is gone from their types and out of their proof closure
(`#assert_not_depends_on`, 2743/2745 constants scanned). The tool says "not a carrier" and it is
right to; what changed is that the statement is now true of the deployed system.

⚑ WHAT THIS IS NOT: it is not a cutover, and the ports it builds live only in this module's
environment as the measurement's evidence — no successor theorem is added to the tree beside a
surviving vacuous original. That additive pattern is the exact sin the campaign exists to kill; the
in-place cutover of these 48 is the NEXT transaction, and this pin is its launchpad.

Any drift — a pinned-portable site that refuses, a pinned refusal that ports, a refusal for the wrong
REASON — is a BUILD ERROR, not a warning: the census may only get more true.
-/
import Dregg2.Tools.ConePort
import Dregg2.Circuit.LogCommitRegrounded
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Circuit.EffectInstances
import Dregg2.Circuit.EffectInstances2
import Dregg2.Circuit.EffectRefinement
import Dregg2.Circuit.Inst.attenuateA
import Dregg2.Circuit.Inst.balanceA
import Dregg2.Circuit.Inst.bridgeMintA
import Dregg2.Circuit.Inst.burnA
import Dregg2.Circuit.Inst.cellDestroyA
import Dregg2.Circuit.Inst.cellSealA
import Dregg2.Circuit.Inst.cellUnsealA
import Dregg2.Circuit.Inst.createCellA
import Dregg2.Circuit.Inst.createCellFromFactoryA
import Dregg2.Circuit.Inst.delegate
import Dregg2.Circuit.Inst.delegateAttenA
import Dregg2.Circuit.Inst.emitEventA
import Dregg2.Circuit.Inst.exerciseA
import Dregg2.Circuit.Inst.heapWriteA
import Dregg2.Circuit.Inst.incrementNonceA
import Dregg2.Circuit.Inst.introduceA
import Dregg2.Circuit.Inst.makeSovereignA
import Dregg2.Circuit.Inst.mintA
import Dregg2.Circuit.Inst.noteCreateA
import Dregg2.Circuit.Inst.noteSpendA
import Dregg2.Circuit.Inst.pipelinedSendA
import Dregg2.Circuit.Inst.receiptArchiveA
import Dregg2.Circuit.Inst.receiptArchiveLifecycleA
import Dregg2.Circuit.Inst.refreshDelegationA
import Dregg2.Circuit.Inst.refusalA
import Dregg2.Circuit.Inst.revoke
import Dregg2.Circuit.Inst.revokeDelegationA
import Dregg2.Circuit.Inst.revokeDelegationFullA
import Dregg2.Circuit.Inst.setPermissionsA
import Dregg2.Circuit.Inst.setProgramA
import Dregg2.Circuit.Inst.setVKA
import Dregg2.Circuit.Inst.spawnA
import Dregg2.Circuit.Inst.transfer
import Dregg2.Circuit.WitnessExtract
import Dregg2.Circuit.WitnessExtract3
import Dregg2.Circuit.WitnessExtract5
import Dregg2.Circuit.WitnessExtractDual
import Dregg2.Circuit.WitnessExtractV1

namespace Dregg2.Tools.ConePortLogHashRun

open Lean Elab Command Dregg2.Tools.ConePort

set_option autoImplicit false

/-- ⚑ THE ONE BRIDGE RULE. After the endpoint cutover every still-floored consumer's floor flows into
exactly one application of `noLogColl_of_inj`, so the whole level is portable with ONE `AppRule`
(the side condition passes through `noLogColl_self`) — never a per-theorem rule table. That uniformity
is the point of routing the cutover through a single bridge. -/
def bridgeRules : List AppRule :=
  [ { orig := `Dregg2.Circuit.LogCommitRegrounded.noLogColl_of_inj, arity := 4,
      floorIdxs := #[1],
      repl := `Dregg2.Circuit.LogCommitRegrounded.noLogColl_self,
      argMap := #[some 0, some 2, some 3, none], tag := "bridge-noLogColl" } ]

def cfg : PortConfig :=
  { floors := [ `Dregg2.Circuit.StateCommit.logHashInjective ]
  , rules := bridgeRules
  , genNamespace := `Dregg2.Circuit.LogHashPortedCone
  , forbidden := [ `Dregg2.Circuit.StateCommit.logHashInjective ] }

/-- Every direct consumer of a cut-over `logHashInjective` endpoint, with its pinned outcome. -/
def targets : List Target :=
  [ { decl := `Dregg2.Circuit.CircuitSoundness.turnDecodeChainLog_seam_log_derived,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Circuit.CircuitSoundness.turnDecodeChainLog_rejects_forged_log,
      expected := .refuse "not a carrier" }
  , { decl := `Dregg2.Circuit.EffectInstances.transferE_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.EffectInstances.setFieldE_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.EffectInstances2.mintE_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.EffectInstances2.noteSpendE_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.EffectRefinement.effect2_circuit_refines_apex, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.AttenuateA.attenuateA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.BalanceA.balanceA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.BridgeMintA.bridgeMintA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.BurnA.burnA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.CellDestroyA.cellDestroyA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.CellSealA.cellSealA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.CellUnsealA.cellUnsealA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.CreateCellA.createCellA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.CreateCellFromFactoryA.createCellFromFactoryA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.Delegate.delegate_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.DelegateAttenA.delegateAttenA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.EmitEventA.emitEventA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.ExerciseA.exerciseA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.HeapWriteA.heapWriteA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.IncrementNonceA.incrementNonceA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.IntroduceA.introduceA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.MakeSovereignA.makeSovereignA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.MintA.mintA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.NoteCreateA.noteCreateA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.NoteSpendA.noteSpendA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.PipelinedSendA.pipelinedSendA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.ReceiptArchiveA.receiptArchiveA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.ReceiptArchiveLifecycleA.receiptArchiveLifecycleA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.RefreshDelegationA.refreshDelegationA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.RefusalA.refusalA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.Revoke.revoke_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.RevokeDelegationA.revokeDelegationA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.RevokeDelegationFullA.revokeDelegationFull_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.SetPermissionsA.setPermissionsA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.SetProgramA.setProgramA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.SetVKA.setVKA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.SpawnA.spawnA_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.Inst.Transfer.transfer_full_sound, expected := .port }
  , { decl := `Dregg2.Circuit.WitnessExtractV1.effect_extract, expected := .port }
  , { decl := `Dregg2.Circuit.WitnessExtractV1.effect_extract_rejects_log_forge, expected := .port } ]

elab "#cone_port_log_run" : command => do
  liftTermElabM do
    let rep ← runCluster cfg targets
    logInfo m!"=== ConePort logHashInjective LEVEL-2 cone: ported={rep.ported.size} refused={rep.refusals.size} mismatches={rep.mismatches.size} ==="
    unless rep.mismatches.isEmpty do
      for m in rep.mismatches do logError m
      throwError "ConePort: the logHash cone moved under the pinned measurement — re-measure, understand WHY, then re-pin"

#cone_port_log_run

end Dregg2.Tools.ConePortLogHashRun
