/-
# Dregg2.Circuit.EffectRefinementBatch2 — Wave-3 circuit ⊑ spec for remaining Inst effects.

Extends `EffectRefinement.lean` with `*CircuitStep` + `*_circuit_refines_spec` for batch-2
`FullActionA` arms that have Inst `*_full_sound`. Composed into `TurnEffectRefinement` dispatch.
-/
import Dregg2.Circuit.EffectRefinement
import Dregg2.Circuit.EffectCommit3
import Dregg2.Circuit.EffectCommit5
import Dregg2.Exec.RecordKernel
import Dregg2.Circuit.Inst.emitEventA
import Dregg2.Circuit.Inst.incrementNonceA
import Dregg2.Circuit.Inst.setPermissionsA
import Dregg2.Circuit.Inst.setVKA
import Dregg2.Circuit.Inst.setProgramA
import Dregg2.Circuit.Inst.delegateAttenA
import Dregg2.Circuit.Inst.attenuateA
import Dregg2.Circuit.Inst.createCellFromFactoryA
import Dregg2.Circuit.Inst.makeSovereignA
import Dregg2.Circuit.Inst.refusalA
import Dregg2.Circuit.Inst.receiptArchiveA
import Dregg2.Circuit.Inst.receiptArchiveLifecycleA
import Dregg2.Circuit.Inst.pipelinedSendA
import Dregg2.Circuit.Inst.cellSealA
import Dregg2.Circuit.Inst.cellUnsealA
import Dregg2.Circuit.Inst.cellDestroyA
import Dregg2.Circuit.Inst.heapWriteA
import Dregg2.Circuit.Inst.refreshDelegationA

namespace Dregg2.Circuit.EffectRefinementBatch2

open Dregg2.Authority
open Dregg2.Exec
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (CommitSurface encodeE satisfiedE)
open Dregg2.Circuit.EffectRefinement (effect2CircuitStep)
open Dregg2.Circuit.EffectCommit2 (Surface2 encodeE2 satisfiedE2)
open Dregg2.Circuit.EffectCommit2Dual (encodeE2Dual satisfiedE2Dual)
open Dregg2.Circuit.EffectCommit3 (encodeE2Triple satisfiedE2Triple)
open Dregg2.Circuit.EffectCommit5 (encodeE2Quint satisfiedE2Quint)
open Dregg2.Circuit.BornEmptyCommit (BornEmptyAuthorityTables bornEmptyAuthority_post_iff)
open Dregg2.Circuit.Inst.CreateCellFromFactoryA
  (RestIffNoFactoryTouched createFromFactoryE createCellFromFactoryA_full_sound)
open Dregg2.Circuit.ListCommit (listLeafInjective)

open Dregg2.Circuit.Inst.EmitEventA
open Dregg2.Circuit.Inst.IncrementNonceA
open Dregg2.Circuit.Inst.SetPermissionsA
open Dregg2.Circuit.Inst.SetVKA
open Dregg2.Circuit.Inst.DelegateAttenA
open Dregg2.Circuit.Inst.AttenuateA
open Dregg2.Circuit.Inst.CreateCellFromFactoryA
open Dregg2.Circuit.Inst.MakeSovereignA
open Dregg2.Circuit.Inst.RefusalA
open Dregg2.Circuit.Inst.ReceiptArchiveA
open Dregg2.Circuit.Inst.PipelinedSendA
open Dregg2.Circuit.Inst.CellSealA
open Dregg2.Circuit.Inst.CellUnsealA
open Dregg2.Circuit.Inst.CellDestroyA
open Dregg2.Circuit.Inst.HeapWriteA
open Dregg2.Circuit.Inst.RefreshDelegationA
open Dregg2.Circuit.Spec.CellStateLog (EmitEventSpec)
open Dregg2.Circuit.Spec.CellStateMonotone (IncrementNonceSpec)
open Dregg2.Circuit.Spec.CellStatePermissions (SetPermissionsSpec)
open Dregg2.Circuit.Spec.CellStateVK (SetVKSpec)
open Dregg2.Circuit.Spec.AuthorityAttenuation (AttenuateSpec DelegateAttenSpec)
open Dregg2.Circuit.Spec.FactoryCreation (CreateFromFactorySpec)
open Dregg2.Circuit.Spec.SovereignCommitment (MakeSovereignSpec)
open Dregg2.Circuit.Spec.CellStateAudit (RefusalSpec ReceiptArchiveSpec ReceiptArchiveLifecycleSpec)
open Dregg2.Circuit.Spec.QueuePipelinedSend (PipelinedSendSpec)
open Dregg2.Circuit.Spec.CellLifecycle (CellSealSpec CellUnsealSpec CellDestroySpec)
open Dregg2.Circuit.Spec.RefreshDelegation (RefreshDelegationSpec RefreshDelegationFullSpec refreshEpochAtMap)
open Dregg2.Circuit.ActionDispatch (fullActionStep)

/-! ## §0 — factory circuit-spec bridge. -/

theorem CreateFromFactoryCircuitSpec_implies_CreateFromFactorySpec (st : RecChainedState)
    (actor newCell : CellId) (vk : Int) (st' : RecChainedState)
    (h : CreateFromFactoryCircuitSpec st actor newCell vk st') :
    CreateFromFactorySpec st actor newCell vk st' := by
  obtain ⟨e, hadmit, hacc, hbal, hcell, hsc, hauth, hlog, hNull, hRev, hCom, hFac, hDE, hDEA⟩ := h
  have ⟨hcaps, hlif, hdc, hdel, hdgs⟩ :=
    (bornEmptyAuthority_post_iff st.kernel newCell st'.kernel).mp hauth
  exact ⟨e, hadmit, hacc, hbal, hcell, hsc, hlog, hcaps, hlif, hdc, hdel, hdgs, hNull, hRev, hCom,
    hFac, hDE, hDEA⟩

/-! ## §1 — v1 CommitSurface effects. -/

def emitEventCircuitStep (CS : CommitSurface) (s : RecChainedState) (args : EmitEventArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE CS emitEventE (encodeE CS emitEventE s args s')

theorem emitEvent_circuit_refines_spec (CS : CommitSurface)
    (hN : compressNInjective CS.compressN) (hL : cellLeafInjective CS.CH)
    (hRest : RestHashIffFrame CS.RH) (hLog : logHashInjective CS.LH)
    (s : RecChainedState) (args : EmitEventArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : emitEventCircuitStep CS s args s') :
    EmitEventSpec s args.actor args.cell args.topic args.data s' :=
  emitEventA_full_sound CS hN hL hRest hLog s args s' hwf hwf' h

def incrementNonceCircuitStep (CS : CommitSurface) (s : RecChainedState) (args : IncrementNonceArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE CS incrementNonceE (encodeE CS incrementNonceE s args s')

theorem incrementNonce_circuit_refines_spec (CS : CommitSurface)
    (hN : compressNInjective CS.compressN) (hL : cellLeafInjective CS.CH)
    (hRest : RestHashIffFrame CS.RH) (hLog : logHashInjective CS.LH)
    (s : RecChainedState) (args : IncrementNonceArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : incrementNonceCircuitStep CS s args s') :
    IncrementNonceSpec s args.actor args.cell args.n s' :=
  incrementNonceA_full_sound CS hN hL hRest hLog s args s' hwf hwf' h

def setPermissionsCircuitStep (CS : CommitSurface) (s : RecChainedState) (args : SetPermissionsArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE CS setPermissionsE (encodeE CS setPermissionsE s args s')

theorem setPermissions_circuit_refines_spec (CS : CommitSurface)
    (hN : compressNInjective CS.compressN) (hL : cellLeafInjective CS.CH)
    (hRest : RestHashIffFrame CS.RH) (hLog : logHashInjective CS.LH)
    (s : RecChainedState) (args : SetPermissionsArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : setPermissionsCircuitStep CS s args s') :
    SetPermissionsSpec s args.actor args.cell args.p s' :=
  setPermissionsA_full_sound CS hN hL hRest hLog s args s' hwf hwf' h

def setVKCircuitStep (CS : CommitSurface) (s : RecChainedState) (args : SetVKArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE CS setVKE (encodeE CS setVKE s args s')

theorem setVK_circuit_refines_spec (CS : CommitSurface)
    (hN : compressNInjective CS.compressN) (hL : cellLeafInjective CS.CH)
    (hRest : RestHashIffFrame CS.RH) (hLog : logHashInjective CS.LH)
    (s : RecChainedState) (args : SetVKArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : setVKCircuitStep CS s args s') :
    SetVKSpec s args.actor args.cell args.vk s' :=
  setVKA_full_sound CS hN hL hRest hLog s args s' hwf hwf' h

def setProgramCircuitStep (CS : CommitSurface) (s : RecChainedState)
    (args : Dregg2.Circuit.Inst.SetProgramA.SetProgramArgs) (s' : RecChainedState) : Prop :=
  satisfiedE CS Dregg2.Circuit.Inst.SetProgramA.setProgramE
    (encodeE CS Dregg2.Circuit.Inst.SetProgramA.setProgramE s args s')

theorem setProgram_circuit_refines_spec (CS : CommitSurface)
    (hN : compressNInjective CS.compressN) (hL : cellLeafInjective CS.CH)
    (hRest : RestHashIffFrame CS.RH) (hLog : logHashInjective CS.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.SetProgramA.SetProgramArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : setProgramCircuitStep CS s args s') :
    Dregg2.Circuit.Spec.CellStateProgram.SetProgramSpec s args.actor args.cell args.prog s' :=
  Dregg2.Circuit.Inst.SetProgramA.setProgramA_full_sound CS hN hL hRest hLog s args s' hwf hwf' h

def makeSovereignCircuitStep (CS : CommitSurface) (s : RecChainedState) (args : MakeSovereignArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE CS makeSovereignE (encodeE CS makeSovereignE s args s')

theorem makeSovereign_circuit_refines_spec (CS : CommitSurface)
    (hN : compressNInjective CS.compressN) (hL : cellLeafInjective CS.CH)
    (hRest : RestHashIffFrame CS.RH) (hLog : logHashInjective CS.LH)
    (s : RecChainedState) (args : MakeSovereignArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : makeSovereignCircuitStep CS s args s') :
    MakeSovereignSpec s args.actor args.cell s' :=
  makeSovereignA_full_sound CS hN hL hRest hLog s args s' hwf hwf' h

def refusalCircuitStep (CS : CommitSurface) (s : RecChainedState) (args : RefusalArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE CS refusalE (encodeE CS refusalE s args s')

theorem refusal_circuit_refines_spec (CS : CommitSurface)
    (hN : compressNInjective CS.compressN) (hL : cellLeafInjective CS.CH)
    (hRest : RestHashIffFrame CS.RH) (hLog : logHashInjective CS.LH)
    (s : RecChainedState) (args : RefusalArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : refusalCircuitStep CS s args s') :
    RefusalSpec s args.actor args.cell s' :=
  refusalA_full_sound CS hN hL hRest hLog s args s' hwf hwf' h

def receiptArchiveCircuitStep (CS : CommitSurface) (s : RecChainedState) (args : ReceiptArchiveArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE CS receiptArchiveE (encodeE CS receiptArchiveE s args s')

theorem receiptArchive_circuit_refines_spec (CS : CommitSurface)
    (hN : compressNInjective CS.compressN) (hL : cellLeafInjective CS.CH)
    (hRest : RestHashIffFrame CS.RH) (hLog : logHashInjective CS.LH)
    (s : RecChainedState) (args : ReceiptArchiveArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : receiptArchiveCircuitStep CS s args s') :
    ReceiptArchiveSpec s args.actor args.cell s' :=
  receiptArchiveA_full_sound CS hN hL hRest hLog s args s' hwf hwf' h

/-- The DEPLOYED receipt-archive v2 circuit step — the Surface2 LIFECYCLE side-table archive circuit
(`receiptArchiveLifecycleE`, the `cellSealE` analog), distinct from the superseded record-slot
`receiptArchiveCircuitStep`. -/
def receiptArchiveLifecycleCircuitStep (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.ReceiptArchiveLifecycleA.ReceiptArchiveArgs)
    (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (Dregg2.Circuit.Inst.ReceiptArchiveLifecycleA.receiptArchiveLifecycleE DLife hDLife)
    s args s'

/-- **The DEPLOYED receipt-archive v2 refinement** — the Surface2 archive circuit forces
`ReceiptArchiveLifecycleSpec` (the `lifecycle := Archived` side-table move). The deployed-semantics
analog of `cellSeal_circuit_refines_spec`. -/
theorem receiptArchiveLifecycle_circuit_refines_spec (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife)
    (hRest : Dregg2.Circuit.Inst.ReceiptArchiveLifecycleA.RestIffNoLifecycle S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.ReceiptArchiveLifecycleA.ReceiptArchiveArgs)
    (s' : RecChainedState)
    (h : receiptArchiveLifecycleCircuitStep S DLife hDLife s args s') :
    ReceiptArchiveLifecycleSpec s args.actor args.cell s' :=
  Dregg2.Circuit.Inst.ReceiptArchiveLifecycleA.receiptArchiveLifecycleA_full_sound
    S DLife hDLife hRest hLog s args s' h

def pipelinedSendCircuitStep (CS : CommitSurface) (s : RecChainedState) (args : PipelinedSendArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE CS pipelinedSendE (encodeE CS pipelinedSendE s args s')

theorem pipelinedSend_circuit_refines_spec (CS : CommitSurface)
    (hN : compressNInjective CS.compressN) (hL : cellLeafInjective CS.CH)
    (hRest : RestHashIffFrame CS.RH) (hLog : logHashInjective CS.LH)
    (s : RecChainedState) (args : PipelinedSendArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : pipelinedSendCircuitStep CS s args s') :
    PipelinedSendSpec s args.actor s' :=
  pipelinedSendA_full_sound CS hN hL hRest hLog s args s' hwf hwf' h

/-! ## §2 — v2 single-component effects. -/

def delegateAttenCircuitStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (delegateAttenE D hD) s args s'

theorem delegateAtten_circuit_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState)
    (h : delegateAttenCircuitStep S D hD s args s') :
    DelegateAttenSpec s args.del args.recv args.t args.keep s' :=
  delegateAttenA_full_sound S D hD hRest hLog s args s' h

def attenuateCircuitStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : AttenuateArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (attenuateE D hD) s args s'

theorem attenuate_circuit_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.AttenuateA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AttenuateArgs) (s' : RecChainedState)
    (h : attenuateCircuitStep S D hD s args s') :
    AttenuateSpec s args.actor args.idx args.keep s' :=
  attenuateA_full_sound S D hD hRest hLog s args s' h

def cellSealCircuitStep (S : Surface2) (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (s : RecChainedState) (args : CellSealArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (cellSealE DLife hDLife) s args s'

theorem cellSeal_circuit_refines_spec (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife)
    (hRest : Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellSealArgs) (s' : RecChainedState)
    (h : cellSealCircuitStep S DLife hDLife s args s') :
    CellSealSpec s args.actor args.cell s' :=
  cellSealA_full_sound S DLife hDLife hRest hLog s args s' h

def cellUnsealCircuitStep (S : Surface2) (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (s : RecChainedState) (args : CellUnsealArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (cellUnsealE DLife hDLife) s args s'

theorem cellUnseal_circuit_refines_spec (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife)
    (hRest : Dregg2.Circuit.Inst.CellUnsealA.RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellUnsealArgs) (s' : RecChainedState)
    (h : cellUnsealCircuitStep S DLife hDLife s args s') :
    CellUnsealSpec s args.actor args.cell s' :=
  cellUnsealA_full_sound S DLife hDLife hRest hLog s args s' h

def refreshDelegationCircuitStep (S : Surface2) (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDDgs : Function.Injective DDgs) (s : RecChainedState) (args : RefreshDelegationArgs)
    (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (refreshDelegationE DDgs hDDgs) s args s'

/-- **Deployed refresh circuit ⟹ STRENGTHENED `RefreshDelegationFullSpec`.** The deployed
`refreshDelegationE` func-descriptor now binds a PRODUCT component `(delegations, delegationEpochAt)`, so it
FORCES the freshness-restore stamp (no residual): the child's epoch tag is bound to the parent's current
epoch read off the same before-kernel. -/
theorem refreshDelegation_circuit_refines_spec (S : Surface2)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDDgs : Function.Injective DDgs) (hRest : RestIffNoDelegations S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState)
    (h : refreshDelegationCircuitStep S DDgs hDDgs s args s') :
    RefreshDelegationFullSpec s args.actor args.child s' :=
  refreshDelegationA_full_sound S DDgs hDDgs hRest hLog s args s' h

/-- **`RefreshEpochStampResidual` — CLOSED (NOT an open residual). SUPERSEDED by the deployed refresh
descriptor's PRODUCT component** (`(delegations, delegationEpochAt)` bound to
`(refreshDelegationsMap, refreshEpochAtMap)`): the freshness-restore epoch-stamp is PROVEN-FORCED there, and
the conjunct was DROPPED from the refresh bridges. This `def` survives ONLY as documentation of the forced
proposition (`delegationEpochAt = refreshEpochAtMap`, re-stamping the child's tag to the parent's CURRENT
epoch); `refreshDelegation_circuit_refines_spec` PROVES it directly out of the descriptor. Nothing reads it. -/
def RefreshEpochStampResidual (s : RecChainedState) (child : CellId) (s' : RecChainedState) : Prop :=
  s'.kernel.delegationEpochAt = refreshEpochAtMap s.kernel child

/-- **`refreshDelegationFullCircuitStep`** — the deployed `refreshDelegationCircuitStep`, which now ALONE
forces the freshness-restore stamp (the product component). The FAITHFUL circuit-side relation for
`.refreshDelegationA` is the deployed step itself. -/
def refreshDelegationFullCircuitStep (S : Surface2)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDDgs : Function.Injective DDgs) (s : RecChainedState) (args : RefreshDelegationArgs)
    (s' : RecChainedState) : Prop :=
  refreshDelegationCircuitStep S DDgs hDDgs s args s'

/-- **`refreshDelegation_full_circuit_refines_spec` — the FAITHFUL refinement.** The deployed product
descriptor FORCES `RefreshDelegationFullSpec` directly (the child re-syncs FRESH — the stamp is gate-forced,
no residual). A refresh that skips the stamp violates the product component's `postClause` and is UNSAT. -/
theorem refreshDelegation_full_circuit_refines_spec (S : Surface2)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDDgs : Function.Injective DDgs) (hRest : RestIffNoDelegations S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState)
    (h : refreshDelegationFullCircuitStep S DDgs hDDgs s args s') :
    RefreshDelegationFullSpec s args.actor args.child s' :=
  refreshDelegation_circuit_refines_spec S DDgs hDDgs hRest hLog s args s' h

/-- **`refreshDelegation_full_sat_rejects_stale_stamp`** — THE FORGED-FRESHNESS REJECTION (deployed
mutation-confirm, abstract layer). A claimed refresh post-state whose `delegationEpochAt` is NOT the
parent-epoch re-stamp (`refreshEpochAtMap` — e.g. the child left STALE at its old tag) violates the product
component's `postClause` and has NO satisfying witness on the encoded triple: the descriptor REJECTS a
forged-freshness refresh. -/
theorem refreshDelegation_full_sat_rejects_stale_stamp (S : Surface2)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoDelegations S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState)
    (hstale : s'.kernel.delegationEpochAt ≠ refreshEpochAtMap s.kernel args.child) :
    ¬ refreshDelegationCircuitStep S DDgs hDDgs s args s' := by
  intro h
  have hspec := refreshDelegation_circuit_refines_spec S DDgs hDDgs hRest hLog s args s' h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hstamp, _⟩ := hspec
  exact hstale hstamp

/-! ## §3 — dual-component effects. -/

def cellDestroyCircuitStep (S : Surface2) (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (s : RecChainedState) (args : CellDestroyArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Dual S (cellDestroyE DLife hDLife DDC hDDC)
    (encodeE2Dual S (cellDestroyE DLife hDLife DDC hDDC) s args s')

theorem cellDestroy_circuit_refines_spec (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife) (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (hRest : RestIffNoLifecycleDeathCert S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellDestroyArgs) (s' : RecChainedState)
    (h : cellDestroyCircuitStep S DLife hDLife DDC hDDC s args s') :
    CellDestroySpec s args.actor args.cell args.certHash s' :=
  cellDestroyA_full_sound S DLife hDLife DDC hDDC hRest hLog s args s' h

/-- THE ROTATION: the heap write's v2-dual circuit step (`cell` register write + `heaps` splice). -/
def heapWriteCircuitStep (S : Surface2)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DHeaps : (CellId → Dregg2.Substrate.Heap.FeltHeap) → ℤ) (hDHeaps : Function.Injective DHeaps)
    (s : RecChainedState) (args : HeapWriteArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Dual S (heapWriteE DCell hDCell DHeaps hDHeaps)
    (encodeE2Dual S (heapWriteE DCell hDCell DHeaps hDHeaps) s args s')

theorem heapWrite_circuit_refines_spec (S : Surface2)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DHeaps : (CellId → Dregg2.Substrate.Heap.FeltHeap) → ℤ) (hDHeaps : Function.Injective DHeaps)
    (hRest : RestIffNoCellHeaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : HeapWriteArgs) (s' : RecChainedState)
    (h : heapWriteCircuitStep S DCell hDCell DHeaps hDHeaps s args s') :
    Dregg2.Circuit.Spec.HeapWrite.HeapWriteSpec s args.actor args.target args.addr args.value
      args.newRoot s' :=
  heapWriteA_full_sound S DCell hDCell DHeaps hDHeaps hRest hLog s args s' h

/-! ## §4 — triple-component effects. -/

-- (F2a) the queueDequeue/queueAtomicTx triple-component circuit steps DELETED with the queue family.

/-! ## §5 — quint-component effect (factory create). -/

def createCellFromFactoryCircuitStep (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (s : RecChainedState) (args : CreateFromFactoryArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Quint S
    (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
    (encodeE2Quint S
      (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth) s args s')

theorem createCellFromFactory_circuit_refines_spec (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (hRest : RestIffNoFactoryTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateFromFactoryArgs) (s' : RecChainedState)
    (h : createCellFromFactoryCircuitStep S LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth
      s args s') :
    CreateFromFactorySpec s args.actor args.newCell args.vk s' := by
  exact CreateFromFactoryCircuitSpec_implies_CreateFromFactorySpec s args.actor args.newCell args.vk s'
    (createCellFromFactoryA_full_sound S LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth
      hRest hLog s args s' h)

end Dregg2.Circuit.EffectRefinementBatch2