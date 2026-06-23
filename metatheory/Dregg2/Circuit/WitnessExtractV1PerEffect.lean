/-
# Dregg2.Circuit.WitnessExtractV1PerEffect — per-effect ADVERSARIAL-witness extraction for the v1 effects.

`WitnessExtractV1.effect_extract` is the generic v1 (`EffectCommit`) adversarial-witness extractor: an
ARBITRARY satisfying assignment that is `PIBindsDigestsV1`-pinned (the verifier's public-input check binds
its eight digest wires `66..73` + the guard region to the committed values) forces the effect's `apex` —
no dead whole-trace `hEnc`, the adversary keeps the un-gated roots `64/65` and every `w ≥ 74`.

THIS module lifts that to every v1 effect that routes through the generic `effect_circuit_full_sound`
(its `EffectSpec` `*E`, its constant `*GuardDecodes`, and its `apex ↔ *Spec` bridge). For each:

  * `*_extract`            — arbitrary satisfying + PI-bound trace ⇒ the COMPLETE declarative spec. The
    hostile-witness closure: a satisfying witness FORCES the genuine kernel step.
  * `*_extract_rejects_*`  — ANTI-GHOST teeth: a claimed post that VIOLATES the apex (tampered non-`cell`
    field / live-bystander cell / wrong touched cell / forged log) has NO satisfying PI-bound witness.

Covered (the cap-write family + the field/audit/log effects): setPermissionsA, setVKA, setProgramA,
incrementNonceA, emitEventA, makeSovereignA, refusalA, receiptArchiveA, pipelinedSendA.

ADDITIVE: imports the per-effect `Inst/*` modules + `WitnessExtractV1`; edits none.
-/
import Dregg2.Circuit.WitnessExtractV1
import Dregg2.Circuit.Inst.setPermissionsA
import Dregg2.Circuit.Inst.setVKA
import Dregg2.Circuit.Inst.setProgramA
import Dregg2.Circuit.Inst.incrementNonceA
import Dregg2.Circuit.Inst.emitEventA
import Dregg2.Circuit.Inst.makeSovereignA
import Dregg2.Circuit.Inst.refusalA
import Dregg2.Circuit.Inst.receiptArchiveA
import Dregg2.Circuit.Inst.pipelinedSendA

namespace Dregg2.Circuit.WitnessExtractV1PerEffect

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit (CommitSurface satisfiedE)
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective cellLeafInjective
  RestHashIffFrame AccountsWF)
open Dregg2.Circuit.WitnessExtractV1 (PIBindsDigestsV1 effect_extract
  effect_extract_rejects_field_tamper effect_extract_rejects_third_cell
  effect_extract_rejects_wrong_touched effect_extract_rejects_log_forge)
open Dregg2.Exec (RecChainedState)

set_option autoImplicit false

/-! ## §1 — CAP-WRITE family: `setPermissionsA`, `setVKA`, `setProgramA` (a `cell` touched component). -/

/-- **`setPermissionsA_extract`** — adversarial extraction for `setPermissions`. -/
theorem setPermissionsA_extract
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.SetPermissionsA.SetPermissionsArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (a : Assignment)
    (hsat : satisfiedE S Inst.SetPermissionsA.setPermissionsE a)
    (hPI : PIBindsDigestsV1 S Inst.SetPermissionsA.setPermissionsE s args s' a) :
    Spec.CellStatePermissions.SetPermissionsSpec s args.actor args.cell args.p s' :=
  (Inst.SetPermissionsA.apex_iff_setPermissionsSpec s args s').mp
    (effect_extract S Inst.SetPermissionsA.setPermissionsE hN hL hRest hLog
      Inst.SetPermissionsA.setPermissionsGuardDecodes s args s' hwf hwf' a hsat hPI)

/-- **`setPermissionsA_extract_rejects_wrong_cell`** — a touched cell whose post value differs from the
spec's `expectedLeaf` has NO satisfying PI-bound witness. (Forged permissions rejected.) -/
theorem setPermissionsA_extract_rejects_wrong_cell
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (s : RecChainedState) (args : Inst.SetPermissionsA.SetPermissionsArgs) (s' : RecChainedState)
    (a : Assignment) {c₀ : Dregg2.Exec.CellId}
    (hPI : PIBindsDigestsV1 S Inst.SetPermissionsA.setPermissionsE s args s' a)
    (hc₀ : c₀ ∈ Inst.SetPermissionsA.setPermissionsE.touched s args)
    (htamper : (Inst.SetPermissionsA.setPermissionsE.view.toKernel s').cell c₀
      ≠ Inst.SetPermissionsA.setPermissionsE.expectedLeaf s args c₀) :
    ¬ satisfiedE S Inst.SetPermissionsA.setPermissionsE a :=
  effect_extract_rejects_wrong_touched S Inst.SetPermissionsA.setPermissionsE hN hL s args s' a
    hPI hc₀ htamper

/-- **`setVKA_extract`** — adversarial extraction for `setVK` (verification-key write). -/
theorem setVKA_extract
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.SetVKA.SetVKArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (a : Assignment)
    (hsat : satisfiedE S Inst.SetVKA.setVKE a)
    (hPI : PIBindsDigestsV1 S Inst.SetVKA.setVKE s args s' a) :
    Spec.CellStateVK.SetVKSpec s args.actor args.cell args.vk s' :=
  (Inst.SetVKA.apex_iff_setVKSpec s args s').mp
    (effect_extract S Inst.SetVKA.setVKE hN hL hRest hLog
      Inst.SetVKA.setVKGuardDecodes s args s' hwf hwf' a hsat hPI)

theorem setVKA_extract_rejects_wrong_cell
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (s : RecChainedState) (args : Inst.SetVKA.SetVKArgs) (s' : RecChainedState)
    (a : Assignment) {c₀ : Dregg2.Exec.CellId}
    (hPI : PIBindsDigestsV1 S Inst.SetVKA.setVKE s args s' a)
    (hc₀ : c₀ ∈ Inst.SetVKA.setVKE.touched s args)
    (htamper : (Inst.SetVKA.setVKE.view.toKernel s').cell c₀
      ≠ Inst.SetVKA.setVKE.expectedLeaf s args c₀) :
    ¬ satisfiedE S Inst.SetVKA.setVKE a :=
  effect_extract_rejects_wrong_touched S Inst.SetVKA.setVKE hN hL s args s' a hPI hc₀ htamper

/-- **`setProgramA_extract`** — adversarial extraction for `setProgram`. -/
theorem setProgramA_extract
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.SetProgramA.SetProgramArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (a : Assignment)
    (hsat : satisfiedE S Inst.SetProgramA.setProgramE a)
    (hPI : PIBindsDigestsV1 S Inst.SetProgramA.setProgramE s args s' a) :
    Spec.CellStateProgram.SetProgramSpec s args.actor args.cell args.prog s' :=
  (Inst.SetProgramA.apex_iff_setProgramSpec s args s').mp
    (effect_extract S Inst.SetProgramA.setProgramE hN hL hRest hLog
      Inst.SetProgramA.setProgramGuardDecodes s args s' hwf hwf' a hsat hPI)

theorem setProgramA_extract_rejects_wrong_cell
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (s : RecChainedState) (args : Inst.SetProgramA.SetProgramArgs) (s' : RecChainedState)
    (a : Assignment) {c₀ : Dregg2.Exec.CellId}
    (hPI : PIBindsDigestsV1 S Inst.SetProgramA.setProgramE s args s' a)
    (hc₀ : c₀ ∈ Inst.SetProgramA.setProgramE.touched s args)
    (htamper : (Inst.SetProgramA.setProgramE.view.toKernel s').cell c₀
      ≠ Inst.SetProgramA.setProgramE.expectedLeaf s args c₀) :
    ¬ satisfiedE S Inst.SetProgramA.setProgramE a :=
  effect_extract_rejects_wrong_touched S Inst.SetProgramA.setProgramE hN hL s args s' a hPI hc₀ htamper

/-! ## §2 — CELL-STATE field/audit/log effects: `incrementNonceA`, `emitEventA`, `makeSovereignA`,
`refusalA`, `receiptArchiveA`, `pipelinedSendA`. -/

/-- **`incrementNonceA_extract`** — adversarial extraction for `incrementNonce` (monotone nonce write). -/
theorem incrementNonceA_extract
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.IncrementNonceA.IncrementNonceArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (a : Assignment)
    (hsat : satisfiedE S Inst.IncrementNonceA.incrementNonceE a)
    (hPI : PIBindsDigestsV1 S Inst.IncrementNonceA.incrementNonceE s args s' a) :
    Spec.CellStateMonotone.IncrementNonceSpec s args.actor args.cell args.n s' :=
  (Inst.IncrementNonceA.apex_iff_incrementNonceSpec s args s').mp
    (effect_extract S Inst.IncrementNonceA.incrementNonceE hN hL hRest hLog
      Inst.IncrementNonceA.incrementNonceGuardDecodes s args s' hwf hwf' a hsat hPI)

theorem incrementNonceA_extract_rejects_wrong_cell
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (s : RecChainedState) (args : Inst.IncrementNonceA.IncrementNonceArgs) (s' : RecChainedState)
    (a : Assignment) {c₀ : Dregg2.Exec.CellId}
    (hPI : PIBindsDigestsV1 S Inst.IncrementNonceA.incrementNonceE s args s' a)
    (hc₀ : c₀ ∈ Inst.IncrementNonceA.incrementNonceE.touched s args)
    (htamper : (Inst.IncrementNonceA.incrementNonceE.view.toKernel s').cell c₀
      ≠ Inst.IncrementNonceA.incrementNonceE.expectedLeaf s args c₀) :
    ¬ satisfiedE S Inst.IncrementNonceA.incrementNonceE a :=
  effect_extract_rejects_wrong_touched S Inst.IncrementNonceA.incrementNonceE hN hL s args s' a
    hPI hc₀ htamper

/-- **`emitEventA_extract`** — adversarial extraction for `emitEvent` (the log-grow, T = ∅ effect). -/
theorem emitEventA_extract
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.EmitEventA.EmitEventArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (a : Assignment)
    (hsat : satisfiedE S Inst.EmitEventA.emitEventE a)
    (hPI : PIBindsDigestsV1 S Inst.EmitEventA.emitEventE s args s' a) :
    Spec.CellStateLog.EmitEventSpec s args.actor args.cell args.topic args.data s' :=
  (Inst.EmitEventA.apex_iff_emitEventSpec s args s').mp
    (effect_extract S Inst.EmitEventA.emitEventE hN hL hRest hLog
      Inst.EmitEventA.emitEventGuardDecodes s args s' hwf hwf' a hsat hPI)

/-- **`emitEventA_extract_rejects_log_forge`** — a claimed post-log differing from the spec-predicted
post-log has NO satisfying PI-bound witness (`logHashInjective`). The emitted event is PINNED. -/
theorem emitEventA_extract_rejects_log_forge
    (S : CommitSurface) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.EmitEventA.EmitEventArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigestsV1 S Inst.EmitEventA.emitEventE s args s' a)
    (htamper : Inst.EmitEventA.emitEventE.view.getLog s'
      ≠ Inst.EmitEventA.emitEventE.postLog s args) :
    ¬ satisfiedE S Inst.EmitEventA.emitEventE a :=
  effect_extract_rejects_log_forge S Inst.EmitEventA.emitEventE hLog s args s' a hPI htamper

/-- **`makeSovereignA_extract`** — adversarial extraction for `makeSovereign`. -/
theorem makeSovereignA_extract
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.MakeSovereignA.MakeSovereignArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (a : Assignment)
    (hsat : satisfiedE S Inst.MakeSovereignA.makeSovereignE a)
    (hPI : PIBindsDigestsV1 S Inst.MakeSovereignA.makeSovereignE s args s' a) :
    Spec.SovereignCommitment.MakeSovereignSpec s args.actor args.cell s' :=
  (Inst.MakeSovereignA.apex_iff_makeSovereignSpec s args s').mp
    (effect_extract S Inst.MakeSovereignA.makeSovereignE hN hL hRest hLog
      Inst.MakeSovereignA.makeSovereignGuardDecodes s args s' hwf hwf' a hsat hPI)

theorem makeSovereignA_extract_rejects_wrong_cell
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (s : RecChainedState) (args : Inst.MakeSovereignA.MakeSovereignArgs) (s' : RecChainedState)
    (a : Assignment) {c₀ : Dregg2.Exec.CellId}
    (hPI : PIBindsDigestsV1 S Inst.MakeSovereignA.makeSovereignE s args s' a)
    (hc₀ : c₀ ∈ Inst.MakeSovereignA.makeSovereignE.touched s args)
    (htamper : (Inst.MakeSovereignA.makeSovereignE.view.toKernel s').cell c₀
      ≠ Inst.MakeSovereignA.makeSovereignE.expectedLeaf s args c₀) :
    ¬ satisfiedE S Inst.MakeSovereignA.makeSovereignE a :=
  effect_extract_rejects_wrong_touched S Inst.MakeSovereignA.makeSovereignE hN hL s args s' a
    hPI hc₀ htamper

/-- **`refusalA_extract`** — adversarial extraction for `refusal` (the audit-record effect). -/
theorem refusalA_extract
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.RefusalA.RefusalArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (a : Assignment)
    (hsat : satisfiedE S Inst.RefusalA.refusalE a)
    (hPI : PIBindsDigestsV1 S Inst.RefusalA.refusalE s args s' a) :
    Spec.CellStateAudit.RefusalSpec s args.actor args.cell s' :=
  (Inst.RefusalA.apex_iff_refusalSpec s args s').mp
    (effect_extract S Inst.RefusalA.refusalE hN hL hRest hLog
      Inst.RefusalA.refusalGuardDecodes s args s' hwf hwf' a hsat hPI)

theorem refusalA_extract_rejects_log_forge
    (S : CommitSurface) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.RefusalA.RefusalArgs) (s' : RecChainedState) (a : Assignment)
    (hPI : PIBindsDigestsV1 S Inst.RefusalA.refusalE s args s' a)
    (htamper : Inst.RefusalA.refusalE.view.getLog s' ≠ Inst.RefusalA.refusalE.postLog s args) :
    ¬ satisfiedE S Inst.RefusalA.refusalE a :=
  effect_extract_rejects_log_forge S Inst.RefusalA.refusalE hLog s args s' a hPI htamper

/-- **`receiptArchiveA_extract`** — adversarial extraction for `receiptArchive`. -/
theorem receiptArchiveA_extract
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.ReceiptArchiveA.ReceiptArchiveArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (a : Assignment)
    (hsat : satisfiedE S Inst.ReceiptArchiveA.receiptArchiveE a)
    (hPI : PIBindsDigestsV1 S Inst.ReceiptArchiveA.receiptArchiveE s args s' a) :
    Spec.CellStateAudit.ReceiptArchiveSpec s args.actor args.cell s' :=
  (Inst.ReceiptArchiveA.apex_iff_ReceiptArchiveSpec s args s').mp
    (effect_extract S Inst.ReceiptArchiveA.receiptArchiveE hN hL hRest hLog
      Inst.ReceiptArchiveA.receiptArchiveGuardDecodes s args s' hwf hwf' a hsat hPI)

theorem receiptArchiveA_extract_rejects_log_forge
    (S : CommitSurface) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.ReceiptArchiveA.ReceiptArchiveArgs) (s' : RecChainedState)
    (a : Assignment)
    (hPI : PIBindsDigestsV1 S Inst.ReceiptArchiveA.receiptArchiveE s args s' a)
    (htamper : Inst.ReceiptArchiveA.receiptArchiveE.view.getLog s'
      ≠ Inst.ReceiptArchiveA.receiptArchiveE.postLog s args) :
    ¬ satisfiedE S Inst.ReceiptArchiveA.receiptArchiveE a :=
  effect_extract_rejects_log_forge S Inst.ReceiptArchiveA.receiptArchiveE hLog s args s' a hPI htamper

/-- **`pipelinedSendA_extract`** — adversarial extraction for `pipelinedSend`. -/
theorem pipelinedSendA_extract
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.PipelinedSendA.PipelinedSendArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (a : Assignment)
    (hsat : satisfiedE S Inst.PipelinedSendA.pipelinedSendE a)
    (hPI : PIBindsDigestsV1 S Inst.PipelinedSendA.pipelinedSendE s args s' a) :
    Spec.QueuePipelinedSend.PipelinedSendSpec s args.actor s' :=
  (Inst.PipelinedSendA.apex_iff_pipelinedSendSpec s args s').mp
    (effect_extract S Inst.PipelinedSendA.pipelinedSendE hN hL hRest hLog
      Inst.PipelinedSendA.pipelinedSendGuardDecodes s args s' hwf hwf' a hsat hPI)

theorem pipelinedSendA_extract_rejects_log_forge
    (S : CommitSurface) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.PipelinedSendA.PipelinedSendArgs) (s' : RecChainedState)
    (a : Assignment)
    (hPI : PIBindsDigestsV1 S Inst.PipelinedSendA.pipelinedSendE s args s' a)
    (htamper : Inst.PipelinedSendA.pipelinedSendE.view.getLog s'
      ≠ Inst.PipelinedSendA.pipelinedSendE.postLog s args) :
    ¬ satisfiedE S Inst.PipelinedSendA.pipelinedSendE a :=
  effect_extract_rejects_log_forge S Inst.PipelinedSendA.pipelinedSendE hLog s args s' a hPI htamper

/-! ## §3 — axiom-hygiene tripwires. -/

#assert_axioms setPermissionsA_extract
#assert_axioms setPermissionsA_extract_rejects_wrong_cell
#assert_axioms setVKA_extract
#assert_axioms setVKA_extract_rejects_wrong_cell
#assert_axioms setProgramA_extract
#assert_axioms setProgramA_extract_rejects_wrong_cell
#assert_axioms incrementNonceA_extract
#assert_axioms incrementNonceA_extract_rejects_wrong_cell
#assert_axioms emitEventA_extract
#assert_axioms emitEventA_extract_rejects_log_forge
#assert_axioms makeSovereignA_extract
#assert_axioms makeSovereignA_extract_rejects_wrong_cell
#assert_axioms refusalA_extract
#assert_axioms refusalA_extract_rejects_log_forge
#assert_axioms receiptArchiveA_extract
#assert_axioms receiptArchiveA_extract_rejects_log_forge
#assert_axioms pipelinedSendA_extract
#assert_axioms pipelinedSendA_extract_rejects_log_forge

end Dregg2.Circuit.WitnessExtractV1PerEffect
