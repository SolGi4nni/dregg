/-
# Dregg2.Circuit.ClosureAll — FAN OUT the closed-with-log rung to EVERY effect, then ASSEMBLE the
closed apex `lightclient_unfoolable_closed`.

`ClosureLog` landed THREE closed-with-log rungs (transfer / cellSeal / revoke), each discharging the
COMPLETE `<effect>Spec` (incl `.log`) from `StateDecodeLog` + the encode-minus-`logAdv` + the published
receipt-prepend, with the `.log` advance DERIVED through the realizable `logHashInjective` carrier (no
free `logAdv`). This module clones that template across the WHOLE effect cohort and assembles the result.

## §A — the generic closed-with-log rung (`closedLog_of_encode`)

The three `ClosureLog` rungs share one shape. We factor it into ONE generic combinator
`closedLog_of_encode`: given the kernel+log decode (`StateDecodeLog` over `S_live`), a `receipt : Turn`,
the published receipt-prepend (`pubLogPost = LH (receipt :: pre.log)`), a `logNeeds` function taking the
DERIVED advance `post.log = receipt :: pre.log` to a proof of `fullActionStep pre fa post` (the
per-effect rung applied to the reconstituted encode), and the tag identity `actionTag fa = e`, it
produces `kstepAll e pre post`. The `.log` advance is forced INSIDE `logHashInjective` (via
`logAdvance_forced`), never carried as a free `logAdv`. Every per-effect rung below is ONE LINE over
this combinator — the receipt is a parameter, so the rungs are uniform; the CORRECT receipt is pinned by
the `logNeeds` function's type (the encode's `logAdv` field IS `post.log = <that effect's receipt> ::
pre.log`, so only the genuine receipt yields a typeable `logNeeds`).

## §B — the per-effect closed-with-log rungs

One `<effect>_closedLog` per effect family with a landed `<effect>_descriptorRefines`
(`fullActionStep`-arm or `Spec`-arm). The cohort:

  transfer (0) · delegate (1) · revoke (2) · mint (3) · burn (4) · setField×8 (5) · emitEvent (6) ·
  incrementNonce (7) · setPermissions (8) · setVK (9) · introduce (10, =DelegateSpec) ·
  delegateAtten (11) · attenuate (12) · revokeDelegation (14, =RevokeSpec) · exercise (16) ·
  createCell (17) · createCellFromFactory (18) · spawn (19) · bridgeMint (20, =MintASpec) ·
  noteSpend (27) · noteCreate (28) · makeSovereign (38) · refusal (39) · receiptArchive (40) ·
  pipelinedSend (47) · cellSeal (52) · cellUnseal (53) · cellDestroy (54) · refreshDelegation (55) ·
  heapWrite (56).

transfer / cellSeal / revoke are RE-EXPORTED from `ClosureLog` (already landed there). The rest are
new, cloning the same template.

### The ONE structural holdout — `exercise` (tag 16)

`exercise` is the SOLE cohort member whose `<effect>Spec` (`ExerciseSpec`) has NO outer `.log`
receipt-prepend conjunct: the outer step is `innerFacetsAdmittedA = true ∧ exerciseGuard ∧ turnSpec
(exerciseHoldState …) inner`, and the log advance lives in the INNER fold's own per-step receipts, not
in an outer receipt the kernel-only surface would publish. So `exercise_closedLog` does NOT route through
`logAdvance_forced` (there is no outer receipt to force) — it goes straight through `closedBridge_of_step`
from `exerciseEncodes`. This is FAITHFUL: exercise's outer frame genuinely has no outer receipt; the log
is advanced by the inner turn, which is itself a fold of closed rungs. Named precisely, not folded into a
fake receipt-prepend.

## §C — the assembled closed apex

`hrefinesAllClosed` discharges `∀ e, EffectDecodeBridge S_live hash Rfix e` from a per-effect
`ClosedLogExtract` family (the named circuit-witness + log-floor extraction bundle: from a `Satisfied2`
witness of `Rfix e` decoding to `pre`/`post`, produce the `StateDecodeLog`, the receipt, the published
receipt-prepend, and the `logNeeds` encode-minus-log — i.e. the `WitnessDecodes`-class decode-extraction
the LEDGER-root commitment cannot certify, now carrying the log binding as the NAMED realizable
`logHashInjective` floor). `lightclient_unfoolable_closed` instantiates the apex at
`S_live`/`Rfix`/`kstepAll`/`hrefinesAllClosed`.

## The closed apex's EXACT carried floor set

`{StarkSound hash Rfix, Poseidon/Merkle CR carrier set (in S_live + Poseidon2SpongeCR),
logHashInjective LH (the log-CR floor), WitnessDecodes-class extraction (the per-effect
ClosedLogExtract — the circuit witness + the named log floor, NOT a per-effect EffectDecodeBridge
decode residual)}` — all REALIZABLE audited crypto primitives. No per-effect
`EffectDecodeBridge`/`LedgerSurfaceReadout`/decode residual remains beyond the circuit witness + the
four floors.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. All carriers (`StarkSound`,
`Poseidon2SpongeCR`, the `CommitSurface` CR fields, `logHashInjective`, the `ClosedLogExtract` family)
enter as Prop hypotheses/classes, never as axioms. No `sorry`, no `native_decide`, no `:= True`, no
fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.ClosureLog
import Dregg2.Circuit.RotatedKernelRefinementMintBurn
import Dregg2.Circuit.RotatedKernelRefinementMisc
import Dregg2.Circuit.RotatedKernelRefinementNotes
import Dregg2.Circuit.RotatedKernelRefinementNotesFresh
import Dregg2.Circuit.RotatedKernelRefinementExercise
import Dregg2.Circuit.RotatedKernelRefinementLifecycle
import Dregg2.Circuit.RotatedKernelRefinementPermsVK
import Dregg2.Circuit.RotatedKernelRefinementProgram
import Dregg2.Circuit.RotatedKernelRefinementIncNonce
import Dregg2.Circuit.RotatedKernelRefinementSetField
import Dregg2.Circuit.RotatedKernelRefinementAttenuate
import Dregg2.Circuit.RotatedKernelRefinementBirth

namespace Dregg2.Circuit.ClosureAll

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (logHashInjective compressInjective compressNInjective
  cellLeafInjective RestHashIffFrame)
open Dregg2.Circuit.ClosureSurface (S_live closedBridge_of_step)
open Dregg2.Circuit.ClosureLog (StateDecodeLog logAdvance_forced)
open Dregg2.Circuit.ActionDispatch (fullActionStep actionTag)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA)
open Dregg2.Authority (Auth)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (mintV3)
open Dregg2.Circuit.RotatedKernelRefinementMintBurn (burnV3)
open Dregg2.Circuit.Emit.EffectVmEmitSetField (slotName)

set_option autoImplicit false

/-! ## §A — the generic closed-with-log combinator.

`closedLog_of_encode` is the `ClosureLog` template factored out: derive the `.log` advance through the
realizable `logHashInjective` carrier, hand it to the per-effect `logNeeds` (the encode-minus-`logAdv`
applied), and bridge to `kstepAll`. Every per-effect rung is ONE line over this. The receipt is a
parameter; the genuine receipt is the only one for which `logNeeds` typechecks (the encode's `logAdv`
field IS `post.log = <receipt> :: pre.log`). -/

/-- **`closedLog_of_encode` — the generic closed-with-log rung.** From the kernel+log decode
(`StateDecodeLog` over `S_live`), a `receipt`, the published receipt-prepend, a `logNeeds` taking the
DERIVED advance to `fullActionStep pre fa post`, and `actionTag fa = e`, conclude `kstepAll e pre post`.
The `.log` advance is DERIVED via `logAdvance_forced` (inside `logHashInjective`), NOT carried. -/
theorem closedLog_of_encode
    {S : CommitSurface} {LH : List Turn → ℤ} {pc : PublishedCommit}
    {pubLogPre pubLogPost : ℤ} {pre post : RecChainedState} {e : EffectIdx}
    (fa : FullActionA) (receipt : Turn)
    (hdec : StateDecodeLog S LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (receipt :: pre.log))
    (htag : actionTag fa = e)
    (logNeeds : post.log = receipt :: pre.log → fullActionStep pre fa post) :
    kstepAll e pre post :=
  closedBridge_of_step fa hdec.toDecode htag (logNeeds (logAdvance_forced receipt hdec hpub))

/-! ## §B — the per-effect closed-with-log rungs.

Each takes the `S_live` kernel+log decode, the published receipt-prepend, and the per-effect
`logNeeds` (the landed `<effect>_descriptorRefines` applied to the encode reconstituted from the derived
advance). transfer / cellSeal / revoke are RE-EXPORTED from `ClosureLog`. -/

section PerEffect
variable {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
variable {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
variable {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
variable {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
variable {hRest : RestHashIffFrame RH}
variable {LH : List Turn → ℤ}

/-- The live commitment surface, with the section's CR carriers. -/
local notation "Slive" => S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest

/-! ### transfer / cellSeal / revoke — RE-EXPORTED from `ClosureLog`. -/

/-- transfer (tag 0) — re-exported. -/
theorem transfer_closedLog
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.RotatedKernelRefinement.transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (tr :: pre.log))
    (logNeeds : post.log = tr :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinement.rotatedEncodes hash minit mfin maddrs t pre post tr a) :
    kstepAll 0 pre post :=
  Dregg2.Circuit.ClosureLog.transfer_descriptorRefines_closedLog
    hash hside hsat pre post tr a pc pubLogPre pubLogPost hdec hpub logNeeds

/-- cellSeal (tag 52) — re-exported. -/
theorem cellSeal_closedLog
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementCellSeal.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementCellSeal.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN2)
    (pre post : RecChainedState) (actor cell : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementCellSeal.cellSealGenuineEncodes
        compressN2 pre post actor cell) :
    kstepAll 52 pre post :=
  Dregg2.Circuit.ClosureLog.cellSeal_descriptorRefines_closedLog
    compressN2 hN pre post actor cell pc pubLogPre pubLogPost hdec hpub logNeeds

/-- cellSeal (tag 52), CLASS A — re-exported. The seal is forced from the DEPLOYED `cellSealV3`
(`Satisfied2` + the chip/range `RotTableSide` + the realizable `CellSealTraceReadout`), NOT a modelled gate. -/
theorem cellSeal_closedLog_sat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellSealV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementCellSeal.CellSealTraceReadout
        hash minit mfin maddrs t pre post actor cell) :
    kstepAll 52 pre post :=
  Dregg2.Circuit.ClosureLog.cellSeal_descriptorRefines_closedLog_sat
    hash hside hsat pre post actor cell pc pubLogPre pubLogPost hdec hpub logNeeds

/-- revoke (tag 2) — re-exported. -/
theorem revoke_closedLog
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (pre post : RecChainedState) (holder tt : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes
        Scap pre post holder tt) :
    kstepAll 2 pre post :=
  Dregg2.Circuit.ClosureLog.revoke_descriptorRefines_closedLog
    Scap pre post holder tt pc pubLogPre pubLogPost hdec hpub logNeeds

/-! ### cap family — delegate (1) / attenuate (12) / delegateAtten (11) / refreshDelegation (55) /
introduce (10, =DelegateSpec) / revokeDelegation (14, =RevokeSpec). -/

/-- delegate (tag 1). -/
theorem delegate_closedLog
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (pre post : RecChainedState) (del rec tt : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt del :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt del :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes
        Scap pre post del rec tt) :
    kstepAll 1 pre post :=
  closedLog_of_encode (.delegate del rec tt)
    (Dregg2.Exec.TurnExecutorFull.authReceipt del) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.delegate del rec tt) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementCapFamily.delegate_descriptorRefines
        Scap pre post del rec tt (logNeeds hadv))

/-- introduce (tag 10) — refines `DelegateSpec` (same arm body). -/
theorem introduce_closedLog
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (pre post : RecChainedState) (intro rec tt : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt intro :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt intro :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes
        Scap pre post intro rec tt) :
    kstepAll 10 pre post :=
  closedLog_of_encode (.introduceA intro rec tt)
    (Dregg2.Exec.TurnExecutorFull.authReceipt intro) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.introduceA intro rec tt) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementCapFamily.delegate_descriptorRefines
        Scap pre post intro rec tt (logNeeds hadv))

/-- attenuate (tag 12) — cap-family exact rung. -/
theorem attenuate_closedLog
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt actor :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt actor :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementCapFamily.AttenuateCapsTreeEncodes
        Scap pre post actor idx keep) :
    kstepAll 12 pre post :=
  closedLog_of_encode (.attenuateA actor idx keep)
    (Dregg2.Exec.TurnExecutorFull.authReceipt actor) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.attenuateA actor idx keep) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementCapFamily.attenuate_descriptorRefines_exact
        Scap pre post actor idx keep (logNeeds hadv))

/-- delegateAtten (tag 11). -/
theorem delegateAtten_closedLog
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (pre post : RecChainedState) (del rec tt : CellId) (keep : List Auth)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt del :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt del :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateAttenCapsTreeEncodes
        Scap pre post del rec tt keep) :
    kstepAll 11 pre post :=
  closedLog_of_encode (.delegateAttenA del rec tt keep)
    (Dregg2.Exec.TurnExecutorFull.authReceipt del) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.delegateAttenA del rec tt keep) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementCapFamily.delegateAtten_descriptorRefines
        Scap pre post del rec tt keep (logNeeds hadv))

/-- revokeDelegation (tag 14) — refines `RevokeSpec` (same arm body). -/
theorem revokeDelegation_closedLog
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (pre post : RecChainedState) (holder tt : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes
        Scap pre post holder tt) :
    kstepAll 14 pre post :=
  closedLog_of_encode (.revokeDelegationA holder tt)
    (Dregg2.Exec.TurnExecutorFull.authReceipt holder) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.revokeDelegationA holder tt) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementCapFamily.revoke_descriptorRefines
        Scap pre post holder tt (logNeeds hadv))

/-- refreshDelegation (tag 55). -/
theorem refreshDelegation_closedLog
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (pre post : RecChainedState) (actor child : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementCapFamily.RefreshDelegationCapsTreeEncodes
        Scap pre post actor child) :
    kstepAll 55 pre post :=
  closedLog_of_encode (.refreshDelegationA actor child)
    (Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.refreshDelegationA actor child) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementCapFamily.refreshDelegation_descriptorRefines
        Scap pre post actor child (logNeeds hadv))

/-! ### lifecycle (compressN-style) — cellUnseal (53) / cellDestroy (54) / refusal (39) /
receiptArchive (40). -/

/-- cellUnseal (tag 53). -/
theorem cellUnseal_closedLog
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN2)
    (pre post : RecChainedState) (actor cell : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementLifecycle.cellUnsealEncodes
        compressN2 pre post actor cell) :
    kstepAll 53 pre post :=
  closedLog_of_encode (.cellUnsealA actor cell)
    (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.cellUnsealA actor cell) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementLifecycle.cellUnseal_descriptorRefines
        compressN2 hN pre post actor cell (logNeeds hadv))

/-- cellDestroy (tag 54). -/
theorem cellDestroy_closedLog
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN2)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementLifecycle.cellDestroyEncodes
        compressN2 pre post actor cell certHash) :
    kstepAll 54 pre post :=
  closedLog_of_encode (.cellDestroyA actor cell certHash)
    (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.cellDestroyA actor cell certHash) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementLifecycle.cellDestroy_descriptorRefines
        compressN2 hN pre post actor cell certHash (logNeeds hadv))

/-- refusal (tag 39). Receipt is the self-targeted row `{ actor, src:=cell, dst:=cell, amt:=0 }`. -/
theorem refusal_closedLog
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN2)
    (pre post : RecChainedState) (actor cell : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementLifecycle.auditEncodes
        compressN2 pre post actor cell Dregg2.Exec.TurnExecutorFull.refusalField) :
    kstepAll 39 pre post :=
  closedLog_of_encode (.refusalA actor cell)
    { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.refusalA actor cell) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementLifecycle.refusal_descriptorRefines
        compressN2 hN pre post actor cell (logNeeds hadv))

/-- receiptArchive (tag 40), CLASS A — forced from the DEPLOYED `receiptArchiveV3` disc gate (the
`lifecycle := Archived` side-table move). Mirrors `cellUnseal_closedLog_sat`/`refusal_closedLog_sat`:
the readout extracts the chip/range `RotTableSide`, the published receipt-prepend, and the
`ReceiptArchiveTraceReadout`-minus-log. Editing `receiptArchiveV3`'s disc gate turns this — and the
apex — RED. Receipt is `{ actor, src:=cell, dst:=cell, amt:=0 }`. -/
theorem receiptArchive_closedLog_sat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.receiptArchiveV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementLifecycle.ReceiptArchiveTraceReadout
        hash t pre post actor cell) :
    kstepAll 40 pre post :=
  closedLog_of_encode (.receiptArchiveA actor cell)
    { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.receiptArchiveA actor cell) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementLifecycle.receiptArchive_descriptorRefines_sat
        hash hside hsat pre post actor cell (logNeeds hadv))

/-! ### perms/vk/emit (compressN or value-forced) — setPermissions (8) / setVK (9) / emitEvent (6). -/

/-- setPermissions (tag 8). -/
theorem setPermissions_closedLog
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementPermsVK.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementPermsVK.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN2)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementPermsVK.setPermissionsEncodes
        compressN2 pre post actor cell p) :
    kstepAll 8 pre post :=
  closedLog_of_encode (.setPermissionsA actor cell p)
    { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.setPermissionsA actor cell p) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementPermsVK.setPermissions_descriptorRefines
        compressN2 hN pre post actor cell p (logNeeds hadv))

/-- setVK (tag 9). -/
theorem setVK_closedLog
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementPermsVK.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementPermsVK.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN2)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementPermsVK.setVKEncodes
        compressN2 pre post actor cell vk) :
    kstepAll 9 pre post :=
  closedLog_of_encode (.setVKA actor cell vk)
    { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.setVKA actor cell vk) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementPermsVK.setVK_descriptorRefines
        compressN2 hN pre post actor cell vk (logNeeds hadv))

/-- emitEvent (tag 6). Value-forced (no compressN). Receipt is `emitReceipt actor cell`. -/
theorem emitEvent_closedLog
    (pre post : RecChainedState) (actor cell : CellId) (topic data : Int)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.CellStateLog.emitReceipt actor cell :: pre.log))
    (logNeeds : post.log = Dregg2.Circuit.Spec.CellStateLog.emitReceipt actor cell :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementPermsVK.emitEventEncodes pre post actor cell) :
    kstepAll 6 pre post :=
  closedLog_of_encode (.emitEventA actor cell topic data)
    (Dregg2.Circuit.Spec.CellStateLog.emitReceipt actor cell) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.emitEventA actor cell topic data) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementPermsVK.emitEvent_descriptorRefines
        pre post actor cell topic data (logNeeds hadv))

/-! ### incrementNonce (7) — Satisfied2-style (rotated live descriptor). Receipt is the self-row. -/

/-- incrementNonce (tag 7). -/
theorem incrementNonce_closedLog
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.RotatedKernelRefinementIncNonce.incNonceV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (n : Int)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementIncNonce.rotatedEncodesIncNonce
        hash minit mfin maddrs t pre post actor cell n) :
    kstepAll 7 pre post :=
  closedLog_of_encode (.incrementNonceA actor cell n)
    { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.incrementNonceA actor cell n) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementIncNonce.incrementNonce_descriptorRefines
        hash hside hsat pre post actor cell n (logNeeds hadv))

/-! ### mint (3) / burn (4) / bridgeMint (20) — Satisfied2-style. -/

/-- mint (tag 3). Receipt is `mintReceipt actor cell a amt`. -/
theorem mint_closedLog
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      mintV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.SupplyCreation.mintReceipt actor cell a amt :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.SupplyCreation.mintReceipt actor cell a amt :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementMintBurn.rotatedEncodesMint
        hash minit mfin maddrs t pre post actor cell a amt) :
    kstepAll 3 pre post :=
  closedLog_of_encode (.mintA actor cell a amt)
    (Dregg2.Circuit.Spec.SupplyCreation.mintReceipt actor cell a amt) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.mintA actor cell a amt) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementMintBurn.mint_descriptorRefines
        hash hside hsat pre post actor cell a amt (logNeeds hadv))

/-- burn (tag 4). Receipt is `burnReceipt actor cell a amt`. -/
theorem burn_closedLog
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      burnV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.SupplyDestruction.burnReceipt actor cell a amt :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.SupplyDestruction.burnReceipt actor cell a amt :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementMintBurn.rotatedEncodesBurn
        hash minit mfin maddrs t pre post actor cell a amt) :
    kstepAll 4 pre post :=
  closedLog_of_encode (.burnA actor cell a amt)
    (Dregg2.Circuit.Spec.SupplyDestruction.burnReceipt actor cell a amt) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.burnA actor cell a amt) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementMintBurn.burn_descriptorRefines
        hash hside hsat pre post actor cell a amt (logNeeds hadv))

/-- bridgeMint (tag 20) — refines `MintASpec` (same arm body), via the mint descriptor. -/
theorem bridgeMint_closedLog
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      mintV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.SupplyCreation.mintReceipt actor cell a amt :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.SupplyCreation.mintReceipt actor cell a amt :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementMintBurn.rotatedEncodesMint
        hash minit mfin maddrs t pre post actor cell a amt) :
    kstepAll 20 pre post :=
  closedLog_of_encode (.bridgeMintA actor cell a amt)
    (Dregg2.Circuit.Spec.SupplyCreation.mintReceipt actor cell a amt) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.bridgeMintA actor cell a amt) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementMintBurn.bridgeMint_descriptorRefines
        hash hside hsat pre post actor cell a amt (logNeeds hadv))

/-! ### setField×8 (tag 5) — Satisfied2-style, slot-indexed. -/

/-- setField (tag 5), at slot `slot : Fin 8`. Receipt is the self-row. -/
theorem setField_closedLog (slot : Fin 8)
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      (Dregg2.Circuit.RotatedKernelRefinementSetField.setFieldV3 slot) minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (v : Int)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementSetField.rotatedEncodesSF
        slot hash minit mfin maddrs t pre post actor cell v) :
    kstepAll 5 pre post :=
  closedLog_of_encode
    (.setFieldA actor cell (slotName slot) v)
    { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv =>
      Dregg2.Circuit.RotatedKernelRefinementSetField.setField_descriptorRefines_fullActionStep
        slot hash hside hsat pre post actor cell v (logNeeds hadv))

/-! ### misc — makeSovereign (38) / setFieldDyn (5-alt) / pipelinedSend (47). -/

/-- makeSovereign (tag 38). Receipt is the self-row. -/
theorem makeSovereign_closedLog
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementMisc.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementMisc.FieldElem)
    (pre post : RecChainedState) (actor cell : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementMisc.makeSovereignEncodes
        compressN2 pre post actor cell) :
    kstepAll 38 pre post :=
  closedLog_of_encode (.makeSovereignA actor cell)
    { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.makeSovereignA actor cell) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementMisc.makeSovereign_descriptorRefines
        compressN2 pre post actor cell (logNeeds hadv))

/-- setFieldDyn (tag 5, dynamic-field route). Receipt is the self-row. -/
theorem setFieldDyn_closedLog
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementMisc.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementMisc.FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementMisc.setFieldDynEncodes
        compressN2 pre post actor cell f v) :
    kstepAll 5 pre post :=
  closedLog_of_encode (.setFieldA actor cell f v)
    { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.setFieldA actor cell f v) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementMisc.setFieldDyn_descriptorRefines
        compressN2 pre post actor cell f v (logNeeds hadv))

/-- pipelinedSend (tag 47). Receipt is `pipelinedSendReceipt actor`. -/
theorem pipelinedSend_closedLog
    (pre post : RecChainedState) (actor : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.QueuePipelinedSend.pipelinedSendReceipt actor :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.QueuePipelinedSend.pipelinedSendReceipt actor :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementMisc.pipelinedSendEncodes pre post actor) :
    kstepAll 47 pre post :=
  closedLog_of_encode (.pipelinedSendA actor)
    (Dregg2.Circuit.Spec.QueuePipelinedSend.pipelinedSendReceipt actor) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.pipelinedSendA actor) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementMisc.pipelinedSend_descriptorRefines
        pre post actor (logNeeds hadv))

/-! ### birth (compressN-style) — createCell (17) / createCellFromFactory (18) / spawn (19). -/

/-- createCell (tag 17). Receipt is `createReceipt actor newCell`. -/
theorem createCell_closedLog
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN2)
    (pre post : RecChainedState) (actor newCell : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementBirth.createCellGenuineEncodes
        compressN2 pre post actor newCell) :
    kstepAll 17 pre post :=
  closedLog_of_encode (.createCellA actor newCell)
    (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.createCellA actor newCell) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementBirth.createCell_descriptorRefines
        compressN2 hN pre post actor newCell (logNeeds hadv))

/-- createCellFromFactory (tag 18). Receipt is `factoryReceipt actor newCell`. -/
theorem createCellFromFactory_closedLog
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN2)
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementBirth.createFromFactoryGenuineEncodes
        compressN2 pre post actor newCell vk) :
    kstepAll 18 pre post :=
  closedLog_of_encode (.createCellFromFactoryA actor newCell vk)
    (Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.createCellFromFactoryA actor newCell vk) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementBirth.createCellFromFactory_descriptorRefines
        compressN2 hN pre post actor newCell vk (logNeeds hadv))

/-- spawn (tag 19). Receipt is `createReceipt actor child`. -/
theorem spawn_closedLog
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN2)
    (pre post : RecChainedState) (actor child target : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementBirth.spawnGenuineEncodes
        compressN2 pre post actor child target) :
    kstepAll 19 pre post :=
  closedLog_of_encode (.spawnA actor child target)
    (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.spawnA actor child target) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementBirth.spawn_descriptorRefines
        compressN2 hN pre post actor child target (logNeeds hadv))

/-! ### notes (compressN-style) — noteSpend (27) / noteCreate (28). -/

/-- noteSpend (tag 27). Receipt is `noteSpendReceipt actor`. -/
theorem noteSpend_closedLog
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementNotes.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementNotes.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN2)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementNotes.noteSpendGenuineEncodes
        compressN2 pre post nf actor spendProof) :
    kstepAll 27 pre post :=
  closedLog_of_encode (.noteSpendA nf actor spendProof)
    (Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.noteSpendA nf actor spendProof) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementNotes.noteSpend_descriptorRefines
        compressN2 hN pre post nf actor spendProof (logNeeds hadv))

/-- noteCreate (tag 28). Receipt is `noteCreateReceipt actor`. -/
theorem noteCreate_closedLog
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementNotes.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementNotes.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN2)
    (pre post : RecChainedState) (cm : Nat) (actor : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementNotes.noteCreateGenuineEncodes
        compressN2 pre post cm actor) :
    kstepAll 28 pre post :=
  closedLog_of_encode (.noteCreateA cm actor)
    (Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.noteCreateA cm actor) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementNotes.noteCreate_descriptorRefines
        compressN2 hN pre post cm actor (logNeeds hadv))

/-! ### heapWrite (56) — Satisfied2-style. Receipt is `{ actor, src:=target, dst:=target, amt:=0 }`. -/

/-- heapWrite (tag 56). -/
theorem heapWrite_closedLog
    (hash : List ℤ → ℤ)
    (pre post : RecChainedState) (actor target : CellId) (addr v newRoot : Int)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := target, dst := target, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log
        = { actor := actor, src := target, dst := target, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementExercise.heapWriteEncodes
        hash pre post actor target addr v newRoot) :
    kstepAll 56 pre post :=
  closedLog_of_encode (.heapWriteA actor target addr v newRoot)
    { actor := actor, src := target, dst := target, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.heapWriteA actor target addr v newRoot) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementExercise.heapWrite_descriptorRefines
        hash pre post actor target addr v newRoot (logNeeds hadv))

/-- heapWrite (tag 56), CLASS A — forced from the DEPLOYED `heapWriteV3` (`= Rfix 56` by `rfl`) via
`heapWrite_descriptorRefines_sat`: the new `heap_root` recompute is forced from the descriptor's own
`Satisfied2` (plus the chip/range `RotTableSide`) and the realizable `HeapWriteTraceReadout`-minus-log
(the register write / splice / guard / 14-field frame). Editing `heapWriteV3`'s recompute sites turns this —
and the apex — RED. -/
theorem heapWrite_closedLog_sat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.RotatedKernelRefinementExercise.heapWriteV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor target : CellId) (addr v newRoot : Int)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := target, dst := target, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log
        = { actor := actor, src := target, dst := target, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementExercise.HeapWriteTraceReadout
        hash t pre post actor target addr v newRoot) :
    kstepAll 56 pre post :=
  closedLog_of_encode (.heapWriteA actor target addr v newRoot)
    { actor := actor, src := target, dst := target, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.heapWriteA actor target addr v newRoot) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementExercise.heapWrite_descriptorRefines_sat
        hash hside hsat pre post actor target addr v newRoot (logNeeds hadv))

/-! ### exercise (16) — the structural holdout: NO outer `.log` receipt. Straight bridge, no
`logAdvance_forced` (the log advances in the INNER fold, faithfully — header §B). -/

/-- exercise (tag 16) — closed WITHOUT an outer receipt-prepend (`ExerciseSpec` has none). The
`StateDecodeLog` still pins the endpoints; the encode is bridged directly. The log advance lives in the
inner turn fold, not an outer receipt — so this rung does NOT consume `logHashInjective` (there is no
outer receipt to force), and it is NOT a residual: exercise's outer frame genuinely carries no receipt. -/
theorem exercise_closedLog
    (pre post : RecChainedState) (actor target : CellId) (inner : List FullActionA)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (henc : Dregg2.Circuit.RotatedKernelRefinementExercise.exerciseEncodes pre post actor target inner) :
    kstepAll 16 pre post :=
  closedBridge_of_step (.exerciseA actor target inner) hdec.toDecode rfl
    (by
      show fullActionStep pre (.exerciseA actor target inner) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementExercise.exercise_descriptorRefines
        pre post actor target inner henc)

/-! ### §B-sat — the CLASS-A (`Satisfied2`-forced) per-effect closed-with-log rungs.

Each mirrors its non-`_sat` sibling EXACTLY but routes the `fullActionStep` arm through the per-effect
`<e>_descriptorRefines_sat` — the Spec write is FORCED from a satisfying DEPLOYED `<e>V3` witness (plus
the chip/range `RotTableSide` where the family uses one) and the realizable `<E>TraceReadout` (the
`WitnessDecodes`-class seam), NOT the modelled-gate `<e>Encodes`. Editing the effect's `<e>V3` constraints
turns the rung — and the apex resting on it — RED. The `logNeeds` now yields the readout struct (whose
`logAdv` field is the derived advance), so the receipt-prepend rides `logAdvance_forced` exactly as before.
These are the rungs the genuine fanout (`ClosureFanoutGenuine`) consumes for guarantee A at the apex. -/

/-- revoke (tag 2), CLASS A — forced from `revokeCapabilityV3`. -/
theorem revoke_closedLog_sat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.revokeCapabilityV3 minit mfin maddrs t)
    (pre post : RecChainedState) (holder target : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapabilityTraceReadout
        hash minit mfin maddrs t pre post holder target) :
    kstepAll 2 pre post :=
  closedLog_of_encode (.revoke holder target)
    (Dregg2.Exec.TurnExecutorFull.authReceipt holder) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.revoke holder target) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementCapFamily.revokeCapability_descriptorRefines_sat
        hash hsat pre post holder target (logNeeds hadv))

/-- revokeCapability (tag 2 via `.revoke`), CLASS A — LIGHT-CLIENT routed from the WRITE-bearing
`revokeCapabilityWriteCapOpenV3` (`= Rfix` for the revokeCapability SDK route). The SINGLE descriptor the
light client verifies carries BOTH the cap-membership authority crown AND the cap-tree REMOVE: the wrapper's
`Satisfied2` strips through `capOpen_satisfied2_strips_to_base` to `revokeCapabilityV3`, whose
`revokeCapability_descriptorRefines_capOpenSat` forces `RevokeSpec` AND the cap-tree REMOVE in-circuit. This
closes the ROUTE-FORGE: the authority-only `revokeCapabilityCapOpenV3` (write:None) left the post-cap-root
host-trusted; THIS binds it. Editing `revokeCapabilityV3`'s `removeWriteOpRot` turns this RED. -/
theorem revokeCapability_closedLog_capOpenSat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.CapOpenEmit.revokeCapabilityWriteCapOpenV3 minit mfin maddrs t)
    (pre post : RecChainedState) (holder target : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapabilityTraceReadout
        hash minit mfin maddrs t pre post holder target) :
    kstepAll 2 pre post :=
  closedLog_of_encode (.revoke holder target)
    (Dregg2.Exec.TurnExecutorFull.authReceipt holder) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.revoke holder target) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementCapFamily.revokeCapability_descriptorRefines_capOpenSat
        hash hsat pre post holder target (logNeeds hadv))

/-! ### cap family CLASS A — delegate (1) / introduce (10) / delegateAtten (11) / revokeDelegation (14),
forced from the WRITE-FORCING cap-open WRAPPER (`Rfix tag` re-pointed to `…WriteCapOpenV3`). The wrapper's
`Satisfied2` strips through `capOpen_satisfied2_strips_to_base` to the base CLASS-A `_descriptorRefines_sat`,
which pins the post cap-root via the LIVE write op — guarantee A circuit-forced. The `logNeeds` yields the
`<Effect>CapsTreeEncodes` decode (whose `logAdv` field is the derived advance); the realizable
`<Effect>WriteAnchor` is the trace seam. -/

/-- delegate (tag 1), CLASS A — forced from `delegateWriteCapOpenV3` (`= Rfix 1`). -/
theorem delegate_closedLog_sat
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.CapOpenEmit.delegateWriteCapOpenV3 minit mfin maddrs t)
    (pre post : RecChainedState) (del rec tt : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt del :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt del :: pre.log →
      Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes
            Scap pre post del rec tt),
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateWriteAnchor
          Scap pre post del rec tt hash minit mfin maddrs t henc) :
    kstepAll 1 pre post :=
  closedLog_of_encode (.delegate del rec tt)
    (Dregg2.Exec.TurnExecutorFull.authReceipt del) hdec hpub rfl
    (fun hadv => by
      obtain ⟨henc, anc⟩ := logNeeds hadv
      show fullActionStep pre (.delegate del rec tt) post
      simp only [fullActionStep]
      exact (Dregg2.Circuit.RotatedKernelRefinementCapFamily.delegate_descriptorRefines_capOpenSat
        Scap pre post del rec tt hash minit mfin maddrs t hsat henc anc).1)

/-- introduce (tag 10), CLASS A — forced from `introduceWriteCapOpenV3` (`= Rfix 10`); routes to
`DelegateSpec`. -/
theorem introduce_closedLog_sat
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.CapOpenEmit.introduceWriteCapOpenV3 minit mfin maddrs t)
    (pre post : RecChainedState) (intro rec tt : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt intro :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt intro :: pre.log →
      Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes
            Scap pre post intro rec tt),
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.IntroduceWriteAnchor
          Scap pre post intro rec tt hash minit mfin maddrs t henc) :
    kstepAll 10 pre post :=
  closedLog_of_encode (.introduceA intro rec tt)
    (Dregg2.Exec.TurnExecutorFull.authReceipt intro) hdec hpub rfl
    (fun hadv => by
      obtain ⟨henc, anc⟩ := logNeeds hadv
      show fullActionStep pre (.introduceA intro rec tt) post
      simp only [fullActionStep]
      exact (Dregg2.Circuit.RotatedKernelRefinementCapFamily.introduce_descriptorRefines_capOpenSat
        Scap pre post intro rec tt hash minit mfin maddrs t hsat henc anc).1)

/-- delegateAtten (tag 11), CLASS A — forced from `delegateAttenWriteCapOpenV3` (`= Rfix 11`); the
insert + `granted ⊑ held` non-amp are FORCED. -/
theorem delegateAtten_closedLog_sat
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsub : t.tf (.custom Dregg2.Circuit.Emit.EffectVmEmitV2.SUBMASK_TID)
      = Dregg2.Circuit.Emit.EffectVmEmitV2.subsetTable Dregg2.Circuit.Emit.EffectVmEmitV2.MASK_BITS)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.CapOpenEmit.delegateAttenWriteCapOpenV3 minit mfin maddrs t)
    (pre post : RecChainedState) (del rec tt : CellId) (keep : List Auth)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt del :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt del :: pre.log →
      Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateAttenCapsTreeEncodes
            Scap pre post del rec tt keep),
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateAttenWriteAnchor
          Scap pre post del rec tt keep hash minit mfin maddrs t henc) :
    kstepAll 11 pre post :=
  closedLog_of_encode (.delegateAttenA del rec tt keep)
    (Dregg2.Exec.TurnExecutorFull.authReceipt del) hdec hpub rfl
    (fun hadv => by
      obtain ⟨henc, anc⟩ := logNeeds hadv
      show fullActionStep pre (.delegateAttenA del rec tt keep) post
      simp only [fullActionStep]
      exact (Dregg2.Circuit.RotatedKernelRefinementCapFamily.delegateAtten_descriptorRefines_capOpenSat
        Scap pre post del rec tt keep hash minit mfin maddrs t hsub hsat henc anc).1)

/-- revokeDelegation (tag 14), CLASS A — forced from `revokeDelegationWriteCapOpenV3` (`= Rfix 14`);
routes to `RevokeSpec`, the cap-tree REMOVE FORCED. -/
theorem revokeDelegation_closedLog_sat
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.CapOpenEmit.revokeDelegationWriteCapOpenV3 minit mfin maddrs t)
    (pre post : RecChainedState) (holder tt : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log →
      Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes
            Scap pre post holder tt),
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeDelegationWriteAnchor
          Scap pre post holder tt hash minit mfin maddrs t henc) :
    kstepAll 14 pre post :=
  closedLog_of_encode (.revokeDelegationA holder tt)
    (Dregg2.Exec.TurnExecutorFull.authReceipt holder) hdec hpub rfl
    (fun hadv => by
      obtain ⟨henc, anc⟩ := logNeeds hadv
      show fullActionStep pre (.revokeDelegationA holder tt) post
      simp only [fullActionStep]
      exact (Dregg2.Circuit.RotatedKernelRefinementCapFamily.revokeDelegation_descriptorRefines_capOpenSat
        Scap pre post holder tt hash minit mfin maddrs t hsat henc anc).1)

/-- revoke (tag 2), CLASS A — forced from `revokeDelegationWriteCapOpenV3` (`= Rfix 2`, the SAME
write-bearing descriptor tag 14 rides). `.revoke holder tt` lowers to the SHARED `RevokeSpec`/`removeEdgeCaps`
kernel step (`execFullA_revoke_iff_spec`), so the cap-tree REMOVE FORCED by `revokeDelegationWriteV3` (the
wrapper strips to it via `capOpen_satisfied2_strips_to_base`) discharges THIS arm exactly as it discharges
tag 14's. Editing `revokeDelegationWriteV3`'s `removeWriteOpRot` turns this — and the tag-2 apex — RED. -/
theorem revoke_closedLog_capOpenSat
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.CapOpenEmit.revokeDelegationWriteCapOpenV3 minit mfin maddrs t)
    (pre post : RecChainedState) (holder tt : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log →
      Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes
            Scap pre post holder tt),
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeDelegationWriteAnchor
          Scap pre post holder tt hash minit mfin maddrs t henc) :
    kstepAll 2 pre post :=
  closedLog_of_encode (.revoke holder tt)
    (Dregg2.Exec.TurnExecutorFull.authReceipt holder) hdec hpub rfl
    (fun hadv => by
      obtain ⟨henc, anc⟩ := logNeeds hadv
      show fullActionStep pre (.revoke holder tt) post
      simp only [fullActionStep]
      exact (Dregg2.Circuit.RotatedKernelRefinementCapFamily.revokeDelegation_descriptorRefines_capOpenSat
        Scap pre post holder tt hash minit mfin maddrs t hsat henc anc).1)

/-- refreshDelegation (tag 55), CLASS A — forced from `refreshDelegationWriteCapOpenV3` (`= Rfix 55`);
the DELEGATIONS-tree UPDATE-write is FORCED in-circuit (the `delegRoot_runtime_column_pending` supplied
digest is GONE). The cap-open wrapper strips to `refreshDelegationWriteV3` and applies
`refreshDelegation_descriptorRefines_sat`, forcing `RefreshDelegationSpec` AND the deleg-root write.
Editing the deleg-write descriptor turns this — and the apex — RED. -/
theorem refreshDelegation_closedLog_sat
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.CapOpenEmit.refreshDelegationWriteCapOpenV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor child : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log →
      Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RefreshDelegationCapsTreeEncodes
            Scap pre post actor child),
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.RefreshDelegationWriteAnchor
          Scap pre post actor child hash minit mfin maddrs t henc) :
    kstepAll 55 pre post :=
  closedLog_of_encode (.refreshDelegationA actor child)
    (Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child) hdec hpub rfl
    (fun hadv => by
      obtain ⟨henc, anc⟩ := logNeeds hadv
      show fullActionStep pre (.refreshDelegationA actor child) post
      simp only [fullActionStep]
      exact (Dregg2.Circuit.RotatedKernelRefinementCapFamily.refreshDelegation_descriptorRefines_capOpenSat
        Scap pre post actor child hash minit mfin maddrs t hsat henc anc).1)

/-- attenuate (tag 12), CLASS A — forced from the DEPLOYED `attenuateCapOpenEffV3` (`= Rfix 12`, base
`attenuateV3` — the MOVING write face, no `gCapPass` freeze). The cap-tree UPDATE-AT-KEY (the in-place
slot-narrow recompute of `cap_root`) is FORCED from `attenuateV3`'s `keepWriteOp` via
`attenuate_descriptorRefines_capOpenSat` (which strips the cap-open authority appendix + selector tooth to
`Satisfied2 attenuateV3` and applies `attenuateV3_non_amp`). The `hsub` carries the realizable submask
table the non-amp leg reads. The `logNeeds` yields the `AttenuateCapsTreeEncodes` decode + the realizable
`AttenuateWriteAnchor` trace seam. Editing `attenuateV3`'s write op turns this — and the apex — RED. -/
theorem attenuate_closedLog_sat
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsub : t.tf (.custom Dregg2.Circuit.Emit.EffectVmEmitV2.SUBMASK_TID)
      = Dregg2.Circuit.Emit.EffectVmEmitV2.subsetTable Dregg2.Circuit.Emit.EffectVmEmitV2.MASK_BITS)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.CapOpenEmit.attenuateCapOpenEffV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt actor :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt actor :: pre.log →
      Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.AttenuateCapsTreeEncodes
            Scap pre post actor idx keep),
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.AttenuateWriteAnchor
          Scap pre post actor idx keep hash minit mfin maddrs t henc) :
    kstepAll 12 pre post :=
  closedLog_of_encode (.attenuateA actor idx keep)
    (Dregg2.Exec.TurnExecutorFull.authReceipt actor) hdec hpub rfl
    (fun hadv => by
      obtain ⟨henc, anc⟩ := logNeeds hadv
      show fullActionStep pre (.attenuateA actor idx keep) post
      simp only [fullActionStep]
      exact (Dregg2.Circuit.RotatedKernelRefinementCapFamily.attenuate_descriptorRefines_capOpenSat
        Scap pre post actor idx keep hash minit mfin maddrs t hsub hsat henc anc).1)

/-- setPermissions (tag 8), CLASS A — forced from `setPermsV3`. -/
theorem setPermissions_closedLog_sat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.setPermsV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementPermsVK.SetPermsTraceReadout
        hash minit mfin maddrs t pre post actor cell p) :
    kstepAll 8 pre post :=
  closedLog_of_encode (.setPermissionsA actor cell p)
    { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.setPermissionsA actor cell p) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementPermsVK.setPermissions_descriptorRefines_sat
        hash hside hsat pre post actor cell p (logNeeds hadv))

/-- setVK (tag 9), CLASS A — forced from `setVKV3`. -/
theorem setVK_closedLog_sat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.setVKV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementPermsVK.SetVKTraceReadout
        hash minit mfin maddrs t pre post actor cell vk) :
    kstepAll 9 pre post :=
  closedLog_of_encode (.setVKA actor cell vk)
    { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.setVKA actor cell vk) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementPermsVK.setVK_descriptorRefines_sat
        hash hside hsat pre post actor cell vk (logNeeds hadv))

/-- setProgram (tag 13), CLASS A — forced from `setProgramV3` (the program record-pin, the program-digest
analog of setVK; carries `compressN`/`hN`/`RotTableSide` for the record-slot-root audit). -/
theorem setProgram_closedLog_sat
    (compressN : List ℤ → ℤ) (hN : compressNInjective compressN)
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.setProgramV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (prog : Int)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementProgram.SetProgramTraceReadout
        compressN hash t pre post actor cell prog) :
    kstepAll 13 pre post :=
  closedLog_of_encode (.setProgramA actor cell prog)
    { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.setProgramA actor cell prog) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementProgram.setProgram_descriptorRefines_sat
        compressN hN hash hside hsat pre post actor cell prog (logNeeds hadv))

/-- createCell (tag 17), CLASS A — forced from `createCellV3` (grow-gate, no `RotTableSide`). -/
theorem createCell_closedLog_sat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.createCellV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor newCell : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementBirth.CreateCellTraceReadout
        hash minit mfin maddrs t pre post actor newCell) :
    kstepAll 17 pre post :=
  closedLog_of_encode (.createCellA actor newCell)
    (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.createCellA actor newCell) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementBirth.createCell_descriptorRefines_sat
        hash hsat pre post actor newCell (logNeeds hadv))

/-- createCellFromFactory (tag 18), CLASS A — forced from `factoryV3`. -/
theorem createCellFromFactory_closedLog_sat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.factoryV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementBirth.CreateFromFactoryTraceReadout
        hash minit mfin maddrs t pre post actor newCell vk) :
    kstepAll 18 pre post :=
  closedLog_of_encode (.createCellFromFactoryA actor newCell vk)
    (Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.createCellFromFactoryA actor newCell vk) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementBirth.createCellFromFactory_descriptorRefines_sat
        hash hsat pre post actor newCell vk (logNeeds hadv))

/-- spawn (tag 19), CLASS A — forced from `spawnV3`. -/
theorem spawn_closedLog_sat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.spawnV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor child target : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementBirth.SpawnTraceReadout
        hash minit mfin maddrs t pre post actor child target) :
    kstepAll 19 pre post :=
  closedLog_of_encode (.spawnA actor child target)
    (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.spawnA actor child target) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementBirth.spawn_descriptorRefines_sat
        hash hsat pre post actor child target (logNeeds hadv))

/-- noteSpend (tag 27), CLASS A — forced from `noteSpendV3`. -/
theorem noteSpend_closedLog_sat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteSpendV3 minit mfin maddrs t)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementNotes.NoteSpendTraceReadout
        hash minit mfin maddrs t pre post nf actor spendProof) :
    kstepAll 27 pre post :=
  closedLog_of_encode (.noteSpendA nf actor spendProof)
    (Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.noteSpendA nf actor spendProof) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementNotes.noteSpend_descriptorRefines_sat
        hash hsat pre post nf actor spendProof (logNeeds hadv))

/-- noteCreate (tag 28), CLASS A — forced from `noteCreateV3`. -/
theorem noteCreate_closedLog_sat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteCreateV3 minit mfin maddrs t)
    (pre post : RecChainedState) (cm : Nat) (actor : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementNotes.NoteCreateTraceReadout
        hash minit mfin maddrs t pre post cm actor) :
    kstepAll 28 pre post :=
  closedLog_of_encode (.noteCreateA cm actor)
    (Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.noteCreateA cm actor) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementNotes.noteCreate_descriptorRefines_sat
        hash hsat pre post cm actor (logNeeds hadv))

/-- makeSovereign (tag 38), CLASS A — forced from `makeSovereignV3`. -/
theorem makeSovereign_closedLog_sat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.makeSovereignV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementMisc.MakeSovereignTraceReadout
        hash minit mfin maddrs t pre post actor cell) :
    kstepAll 38 pre post :=
  closedLog_of_encode (.makeSovereignA actor cell)
    { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.makeSovereignA actor cell) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementMisc.makeSovereign_descriptorRefines_sat
        hash hside hsat pre post actor cell (logNeeds hadv))

/-- refusal (tag 39), CLASS A — forced from `refusalV3`. -/
theorem refusal_closedLog_sat
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN2)
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.refusalV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log))
    (logNeeds : post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementLifecycle.RefusalTraceReadout
        compressN2 hash t pre post actor cell) :
    kstepAll 39 pre post :=
  closedLog_of_encode (.refusalA actor cell)
    { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.refusalA actor cell) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementLifecycle.refusal_descriptorRefines_sat
        compressN2 hN hash hside hsat pre post actor cell (logNeeds hadv))

/-- cellUnseal (tag 53), CLASS A — forced from `cellUnsealV3`. -/
theorem cellUnseal_closedLog_sat
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellUnsealV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementLifecycle.CellUnsealTraceReadout
        hash t pre post actor cell) :
    kstepAll 53 pre post :=
  closedLog_of_encode (.cellUnsealA actor cell)
    (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.cellUnsealA actor cell) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementLifecycle.cellUnseal_descriptorRefines_sat
        hash hside hsat pre post actor cell (logNeeds hadv))

/-- cellDestroy (tag 54), CLASS A — forced from `cellDestroyV3` (both the lifecycle + death-cert legs). -/
theorem cellDestroy_closedLog_sat
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN2)
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellDestroyV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementLifecycle.CellDestroyTraceReadout
        compressN2 hash t pre post actor cell certHash) :
    kstepAll 54 pre post :=
  closedLog_of_encode (.cellDestroyA actor cell certHash)
    (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell) hdec hpub rfl
    (fun hadv => by
      show fullActionStep pre (.cellDestroyA actor cell certHash) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementLifecycle.cellDestroy_descriptorRefines_sat
        compressN2 hN hash hside hsat pre post actor cell certHash (logNeeds hadv))

end PerEffect

/-! ## §C — the assembled closed apex.

`EffectDecodeBridge S hash Rfix e` (the apex's per-effect rung) unfolds to: `Poseidon2SpongeCR hash →
∀ minit mfin maddrs t pc pre post, Satisfied2 hash (Rfix e) … → StateDecode S pc pre post → kstepAll e
pre post`. The §B `*_closedLog` rungs produce `kstepAll e pre post` from `StateDecodeLog` (the kernel
decode PLUS the named realizable `logHashInjective LH` log-floor binding) + the witnessed
encode-minus-log + the published receipt. So discharging `EffectDecodeBridge` requires, per effect, a
bundle that turns the apex's `Satisfied2`-witness + `StateDecode` into exactly those three — the
`WitnessDecodes`-class circuit-witness extraction, now carrying the log binding as the NAMED
`logHashInjective` floor. We name that bundle `ClosedLogExtract`.

`ClosedLogExtract` is the HONEST residual: its content is the per-effect `Satisfied2 ⟹ encode`
extraction (the limb-level column reads the ledger-root commitment cannot certify — the circuit, supplied
by `StarkSound`) PLUS the realizable `logHashInjective` log-floor enrichment of the decode. It carries NO
per-effect `EffectDecodeBridge` decode residual beyond the circuit witness + the four floors; the §B
rungs are exactly what discharges `kstepAll` from it. -/

/-- **`ClosedLogExtract S LH hash R e` — the per-effect closed-with-log extraction bundle (NAMED).**
For any `Satisfied2` witness of `R e` whose published commitments `StateDecode`-decode to `pre`/`post`,
the bundle PRODUCES `kstepAll e pre post` — but with the decode ENRICHED to a `StateDecodeLog` over the
realizable `logHashInjective LH` floor (the log binding woven in as the named carrier, not a per-effect
residual). This is exactly the apex-shaped per-effect rung with the log floor `LH` made explicit: the
circuit-witness extraction (`StarkSound`-supplied) + the `logHashInjective` log-CR carrier. -/
def ClosedLogExtract (S : CommitSurface) (LH : List Turn → ℤ) (hash : List ℤ → ℤ) (R : Registry)
    (e : EffectIdx) : Prop :=
  Poseidon2SpongeCR hash →
  ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ) (pre post : RecChainedState),
    Dregg2.Circuit.DescriptorIR2.Satisfied2 hash (R e) minit mfin maddrs t →
    StateDecodeLog S LH pc pubLogPre pubLogPost pre post →
    kstepAll e pre post

/-- **`effectDecodeBridge_of_closedLogExtract` — `ClosedLogExtract` discharges `EffectDecodeBridge`,
given the log floor.** The apex's `EffectDecodeBridge` carries only a kernel `StateDecode`; the closed
extract needs the log-enriched `StateDecodeLog`. The bridge from one to the other is the NAMED realizable
`logHashInjective LH` floor plus the two published log commitments (the EffectCommit-surface `LH` field's
values) — supplied here as the `mkLog` enrichment hypothesis (a function building `StateDecodeLog` from
the bare `StateDecode`, witnessing exactly the realizable log-CR carrier binding). This is the log floor,
NOT new per-effect decode work. -/
theorem effectDecodeBridge_of_closedLogExtract
    {S : CommitSurface} {LH : List Turn → ℤ} {hash : List ℤ → ℤ} {R : Registry} {e : EffectIdx}
    (hext : ClosedLogExtract S LH hash R e)
    (mkLog : ∀ (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode S pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog S LH pc pubLogPre pubLogPost pre post) :
    EffectDecodeBridge S hash R e := by
  intro hCR minit mfin maddrs t pc pre post hsat hdec
  obtain ⟨pubLogPre, pubLogPost, hdecLog⟩ := mkLog pc pre post hdec
  exact hext hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog

/-! ### `hrefinesAllClosed`: the apex's `∀ e` per-effect family, from the closed-extract bundle. -/

/-- **`hrefinesAllClosed` — the apex's per-effect refinement family, DISCHARGED via the closed-with-log
extract.** From the per-effect `ClosedLogExtract` family (the circuit-witness extraction carrying the
`logHashInjective` log floor) and the realizable log-enrichment `mkLog` (the named `logHashInjective`
floor binding the published log commitments to `pre.log`/`post.log`), the apex's carried family
`∀ e, descriptorRefines S hash (Rfix e) (kstepAll e)`. The `.log` advance is now INSIDE the realizable
log-CR carrier for every effect — no per-effect `EffectDecodeBridge` decode residual remains beyond the
circuit witness + the four floors. -/
theorem hrefinesAllClosed
    (S : CommitSurface) (LH : List Turn → ℤ) (hash : List ℤ → ℤ)
    (hext : ∀ e, ClosedLogExtract S LH hash Rfix e)
    (mkLog : ∀ (e : EffectIdx) (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode S pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog S LH pc pubLogPre pubLogPost pre post) :
    ∀ e, descriptorRefines S hash (Rfix e) (kstepAll e) :=
  fun e => effectDecodeBridge_of_closedLogExtract (hext e) (mkLog e)

/-! ### `lightclient_unfoolable_closed`: the closed apex. -/

/-- **`lightclient_unfoolable_closed` — THE CLOSED CIRCUIT-SOUNDNESS APEX.** From a verifying batch
against `vkOfRegistry Rfix` + the FOUR realizable crypto floors —
  * `StarkSound hash Rfix` (the audited p3 batch-STARK extraction),
  * `Poseidon2SpongeCR hash` + the `CommitSurface` CR fields in `S` (the decode-faithfulness floor),
  * `WitnessDecodes hash Rfix S pi` (the witness→kernel-state existence rung),
  * the per-effect `ClosedLogExtract` family carrying `logHashInjective LH` (the log-CR floor) —
there EXIST decoded endpoints and a genuine FULL kernel+log transition `kstepAll pi.effect pre post`
whose endpoints commit to the published `(pi.pre, pi.post)`. The light client RAN NOTHING; every
per-effect `EffectDecodeBridge`/`LedgerSurfaceReadout`/decode residual is GONE — discharged to the four
realizable floors + the circuit witness. -/
theorem lightclient_unfoolable_closed
    (hash : List ℤ → ℤ) (S : CommitSurface) (LH : List Turn → ℤ)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash Rfix]
    (hext : ∀ e, ClosedLogExtract S LH hash Rfix e)
    (mkLog : ∀ (e : EffectIdx) (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode S pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog S LH pc pubLogPre pubLogPost pre post)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash Rfix S pi)
    (hacc : verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstepAll pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn :=
  lightclient_unfoolable hash S Rfix hCR kstepAll
    (hrefinesAllClosed S LH hash hext mkLog) pi π hwitdec hacc

/-! ### §C.1 — `ClosedLogExtract` is NON-VACUOUS: the transfer slot is dischargeable from the §B rung.

`ClosedLogExtract` is not a free assertion: each slot is exactly what its §B `*_closedLog` rung produces
from the witnessed encode. We demonstrate on the transfer slot (`Rfix 0 = transferV3` definitionally):
given the per-effect circuit extraction `Satisfied2 transferV3 → (RotTableSide ∧ rotatedEncodes-minus-log
∧ published-receipt)` — the genuine `WitnessDecodes`-class residual the ledger-root commitment cannot
certify, the CIRCUIT supplied by `StarkSound` — `transfer_closedLog` discharges `ClosedLogExtract … 0`.
The extractor's content is precisely the circuit witness + the realizable log floor (already inside
`StateDecodeLog`), no per-effect `EffectDecodeBridge` decode residual beyond it. -/

/-- **`closedLogExtract_transfer` — the transfer slot of `ClosedLogExtract`, PROVED from
`transfer_closedLog`.** The carried `extract` is the genuine per-effect circuit extraction (from the
`Satisfied2 transferV3` witness, recover the table side-condition, the receipt `tr`/asset `a`, the
published receipt-prepend, and the encode-minus-log) — the `WitnessDecodes`-class residual the
`StarkSound` circuit supplies. This witnesses that `ClosedLogExtract` is NON-VACUOUS: it is exactly the
§B rung over the circuit witness + the `logHashInjective` log floor. -/
theorem closedLogExtract_transfer
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ} (hash : List ℤ → ℤ)
    (extract : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
      (t : Dregg2.Circuit.DescriptorIR2.VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
        Dregg2.Circuit.RotatedKernelRefinement.transferV3 minit mfin maddrs t →
      -- the genuine circuit extraction: the receipt `tr`/asset `a`, the table side-condition, the
      -- published receipt-prepend, and the encode-minus-log (a `Type`, so carried by `PSigma`).
      Σ' (tr : Turn) (_a : AssetId) (permOut : List ℤ → List ℤ),
        Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
        PLift (pubLogPost = LH (tr :: pre.log)) ×'
        (post.log = tr :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinement.rotatedEncodes hash minit mfin maddrs t
            pre post tr _a)) :
    ClosedLogExtract
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash Rfix 0 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  -- `Rfix 0` is `transferV3` definitionally (registry position 0).
  have hsat' : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.RotatedKernelRefinement.transferV3 minit mfin maddrs t := hsat
  obtain ⟨tr, a, permOut, hside, hpub, logNeeds⟩ := extract minit mfin maddrs t pubLogPost pre post hsat'
  exact transfer_closedLog hash hside hsat' pre post tr a pc pubLogPre pubLogPost hdecLog
    hpub.down logNeeds

/-! ## §D — axiom hygiene. -/

#assert_axioms closedLog_of_encode
#assert_axioms ClosedLogExtract
#assert_axioms effectDecodeBridge_of_closedLogExtract
#assert_axioms closedLogExtract_transfer
#assert_axioms hrefinesAllClosed
#assert_axioms lightclient_unfoolable_closed

end Dregg2.Circuit.ClosureAll
