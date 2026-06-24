/-
# Dregg2.Verify.LoadBearingAuditBroad — BROAD measurement sweep of the authority/Spec layer.

Runs the `@[load_bearing]` linter (`#load_bearing_audit_report`) across the WHOLE per-effect
`Circuit/Spec/*` full-state spec family, the `Spec/FunctionalRefinement` `*Gate`/`*Spec` family,
the `Spec.execGraph` refinement abstraction + its siblings, and the Exec attestation invariants
(`fullActionInvA` / `gatedActionInvG`). The deliverable is the MEASURED scope table: which specs
are independent + non-vacuous vs which collapse to the gate.

CALIBRATION (must come out as stated):
  * `Dregg2.Spec.execGraph` — check #2 MUST FAIL (defeq to its `.any` gate copy).
  * `gateCopyBurnSpec` (in AuditKey) — check #1 MUST FAIL (names recCBurnAsset).
-/
import Dregg2.Verify.LoadBearingLint
-- the per-effect full-state specs:
import Dregg2.Circuit.Spec.supplydestruction
import Dregg2.Circuit.Spec.supplycreation
import Dregg2.Circuit.Spec.bridgeinboundmint
import Dregg2.Circuit.Spec.cellstatefield
import Dregg2.Circuit.Spec.cellstatevk
import Dregg2.Circuit.Spec.cellstateprogram
import Dregg2.Circuit.Spec.cellstatepermissions
import Dregg2.Circuit.Spec.cellstatemonotone
import Dregg2.Circuit.Spec.cellstatelog
import Dregg2.Circuit.Spec.cellstateaudit
import Dregg2.Circuit.Spec.celllifecycle
import Dregg2.Circuit.Spec.sovereigncommitment
import Dregg2.Circuit.Spec.heapwrite
import Dregg2.Circuit.Spec.balancemovement
import Dregg2.Circuit.Spec.authorityunattenuated
import Dregg2.Circuit.Spec.authorityattenuation
import Dregg2.Circuit.Spec.authorityrevocation
import Dregg2.Circuit.Spec.refreshdelegation
import Dregg2.Circuit.Spec.accountgrowth
import Dregg2.Circuit.Spec.factorycreation
import Dregg2.Circuit.Spec.notecommitment
import Dregg2.Circuit.Spec.notenullifier
import Dregg2.Circuit.Spec.queuepipelinedsend
-- the FunctionalRefinement gate/spec family:
import Dregg2.Spec.FunctionalRefinement
-- the execGraph refinement abstraction + the Exec attestation invariants:
import Dregg2.Spec.ExecRefinement
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.FullForestAuth

open Dregg2.Verify.LoadBearingLint

namespace Dregg2.Verify.LoadBearingAuditBroad

/-! ## The calibration gate copy (same as AuditKey §0): the `authorizedB.any` body that
`execGraph` is defeq to. -/
def execGraphGate (caps : Dregg2.Authority.Caps) :
    Dregg2.Spec.Graph Dregg2.Authority.Label Dregg2.Spec.ExecRights :=
  fun h c =>
    (caps h).any (fun cap =>
      (cap == Dregg2.Authority.Cap.node c.target) ||
      (match cap with
       | .endpoint t rights => (t == c.target) && rights.contains Dregg2.Authority.Auth.write
       | _ => false)) = true

/-! ===========================================================================
## §1 — the per-effect full-state `*Spec`/`*Guard` family (Circuit/Spec/*).
Boundary [1] + non-vacuity [3] bite for ALL; defeq [2] is `n/a` (the gate is an
`Option`-returning step of a different TYPE than the `Prop` spec, so a defeq pairing is
not meaningful — boundary is the operative independence check here). The witnesses are the
`_rejects_*` / `_root_pinned` rejection teeth (a vacuous accept-all spec cannot carry one).
=========================================================================== -/

-- SUPPLY-DESTRUCTION
#load_bearing_audit_report Dregg2.Circuit.Spec.SupplyDestruction.BurnGuard
  nonvacuous := Dregg2.Circuit.Spec.SupplyDestruction.burnA_rejects_destroyed_issuer
#load_bearing_audit_report Dregg2.Circuit.Spec.SupplyDestruction.BurnSpec
  nonvacuous := Dregg2.Circuit.Spec.SupplyDestruction.burnA_rejects_destroyed_issuer

-- SUPPLY-CREATION
#load_bearing_audit_report Dregg2.Circuit.Spec.SupplyCreation.mintAdmit
  nonvacuous := Dregg2.Circuit.Spec.SupplyCreation.mintA_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.SupplyCreation.MintASpec
  nonvacuous := Dregg2.Circuit.Spec.SupplyCreation.mintA_rejects_unauthorized

-- BRIDGE INBOUND MINT
#load_bearing_audit_report Dregg2.Circuit.Spec.BridgeInboundMint.inboundMintAdmit
  nonvacuous := Dregg2.Circuit.Spec.BridgeInboundMint.bridgeMint_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.BridgeInboundMint.InboundMintSpec
  nonvacuous := Dregg2.Circuit.Spec.BridgeInboundMint.bridgeMint_rejects_unauthorized

-- CELL-STATE-FIELD
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateField.SetFieldGuard
  nonvacuous := Dregg2.Circuit.Spec.CellStateField.setFieldSpec_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateField.SetFieldSpec
  nonvacuous := Dregg2.Circuit.Spec.CellStateField.setFieldSpec_rejects_unauthorized

-- CELL-STATE-VK
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateVK.setVKGuard
  nonvacuous := Dregg2.Circuit.Spec.CellStateVK.setVK_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateVK.SetVKSpec
  nonvacuous := Dregg2.Circuit.Spec.CellStateVK.setVK_rejects_unauthorized

-- CELL-STATE-PROGRAM
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateProgram.setProgramGuard
  nonvacuous := Dregg2.Circuit.Spec.CellStateProgram.setProgram_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateProgram.SetProgramSpec
  nonvacuous := Dregg2.Circuit.Spec.CellStateProgram.setProgram_rejects_unauthorized

-- CELL-STATE-PERMISSIONS
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStatePermissions.setPermsGuard
  nonvacuous := Dregg2.Circuit.Spec.CellStatePermissions.setPermissions_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStatePermissions.SetPermissionsSpec
  nonvacuous := Dregg2.Circuit.Spec.CellStatePermissions.setPermissions_rejects_unauthorized

-- CELL-STATE-MONOTONE (incrementNonce)
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateMonotone.incNonceGuard
  nonvacuous := Dregg2.Circuit.Spec.CellStateMonotone.incrementNonce_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateMonotone.IncrementNonceSpec
  nonvacuous := Dregg2.Circuit.Spec.CellStateMonotone.incrementNonce_rejects_unauthorized

-- CELL-STATE-LOG (emitEvent)
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateLog.emitGuard
  nonvacuous := Dregg2.Circuit.Spec.CellStateLog.execFullA_emitEvent_rejects_dead
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateLog.EmitEventSpec
  nonvacuous := Dregg2.Circuit.Spec.CellStateLog.execFullA_emitEvent_rejects_dead

-- CELL-STATE-AUDIT (refusal / receiptArchive)
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateAudit.auditGuard
  nonvacuous := Dregg2.Circuit.Spec.CellStateAudit.refusalA_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateAudit.RefusalSpec
  nonvacuous := Dregg2.Circuit.Spec.CellStateAudit.refusalA_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.CellStateAudit.ReceiptArchiveSpec
  nonvacuous := Dregg2.Circuit.Spec.CellStateAudit.receiptArchiveA_rejects_unauthorized

-- CELL-LIFECYCLE (seal / unseal / destroy)
#load_bearing_audit_report Dregg2.Circuit.Spec.CellLifecycle.CellSealGuard
  nonvacuous := Dregg2.Circuit.Spec.CellLifecycle.cellSeal_iff_spec
#load_bearing_audit_report Dregg2.Circuit.Spec.CellLifecycle.CellSealSpec
  nonvacuous := Dregg2.Circuit.Spec.CellLifecycle.cellSeal_iff_spec
#load_bearing_audit_report Dregg2.Circuit.Spec.CellLifecycle.CellDestroyGuard
  nonvacuous := Dregg2.Circuit.Spec.CellLifecycle.cellDestroy_iff_spec
#load_bearing_audit_report Dregg2.Circuit.Spec.CellLifecycle.CellDestroySpec
  nonvacuous := Dregg2.Circuit.Spec.CellLifecycle.cellDestroy_iff_spec

-- SOVEREIGN-COMMITMENT
#load_bearing_audit_report Dregg2.Circuit.Spec.SovereignCommitment.MakeSovereignGuard
  nonvacuous := Dregg2.Circuit.Spec.SovereignCommitment.makeSovereignSpec_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.SovereignCommitment.MakeSovereignSpec
  nonvacuous := Dregg2.Circuit.Spec.SovereignCommitment.makeSovereignSpec_rejects_unauthorized

-- HEAP-WRITE
#load_bearing_audit_report Dregg2.Circuit.Spec.HeapWrite.HeapWriteSpec
  nonvacuous := Dregg2.Circuit.Spec.HeapWrite.heapWriteSpec_root_pinned

-- BALANCE-MOVEMENT
#load_bearing_audit_report Dregg2.Circuit.Spec.BalanceMovement.BalanceMovementSpec
  nonvacuous := Dregg2.Circuit.Spec.BalanceMovement.balanceMovement_rejects_unauthorized

-- AUTHORITY-UNATTENUATED (delegate / introduce)
#load_bearing_audit_report Dregg2.Circuit.Spec.AuthorityUnattenuated.delegateGuard
  nonvacuous := Dregg2.Circuit.Spec.AuthorityUnattenuated.delegate_rejects_unconnected
#load_bearing_audit_report Dregg2.Circuit.Spec.AuthorityUnattenuated.DelegateSpec
  nonvacuous := Dregg2.Circuit.Spec.AuthorityUnattenuated.delegate_rejects_unconnected

-- AUTHORITY-ATTENUATION (delegateAtten / attenuate)
#load_bearing_audit_report Dregg2.Circuit.Spec.AuthorityAttenuation.DelegateAttenGuard
  nonvacuous := Dregg2.Circuit.Spec.AuthorityAttenuation.delegateAtten_rejects_ungrounded
#load_bearing_audit_report Dregg2.Circuit.Spec.AuthorityAttenuation.DelegateAttenSpec
  nonvacuous := Dregg2.Circuit.Spec.AuthorityAttenuation.delegateAtten_rejects_ungrounded
#load_bearing_audit_report Dregg2.Circuit.Spec.AuthorityAttenuation.AttenuateSpec
  nonvacuous := Dregg2.Circuit.Spec.AuthorityAttenuation.delegateAtten_rejects_ungrounded

-- AUTHORITY-REVOCATION (revoke / revokeDelegation)
#load_bearing_audit_report Dregg2.Circuit.Spec.AuthorityRevocation.RevokeSpec
  nonvacuous := Dregg2.Circuit.Spec.AuthorityRevocation.recCRevoke_iff_spec
#load_bearing_audit_report Dregg2.Circuit.Spec.AuthorityRevocation.RevokeDelegationFullSpec
  nonvacuous := Dregg2.Circuit.Spec.AuthorityRevocation.recCRevokeDelegationFull_iff_spec

-- REFRESH-DELEGATION
#load_bearing_audit_report Dregg2.Circuit.Spec.RefreshDelegation.RefreshDelegationGuard
  nonvacuous := Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegation_iff_spec
#load_bearing_audit_report Dregg2.Circuit.Spec.RefreshDelegation.RefreshDelegationFullSpec
  nonvacuous := Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegation_iff_spec

-- ACCOUNT-GROWTH (createCell / spawn)
#load_bearing_audit_report Dregg2.Circuit.Spec.AccountGrowth.createCellAdmit
  nonvacuous := Dregg2.Circuit.Spec.AccountGrowth.createCellA_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.AccountGrowth.CreateCellSpec
  nonvacuous := Dregg2.Circuit.Spec.AccountGrowth.createCellA_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.AccountGrowth.spawnAdmit
  nonvacuous := Dregg2.Circuit.Spec.AccountGrowth.spawnA_rejects_unauthorized_child
#load_bearing_audit_report Dregg2.Circuit.Spec.AccountGrowth.SpawnFullSpec
  nonvacuous := Dregg2.Circuit.Spec.AccountGrowth.spawnA_rejects_unauthorized_child

-- FACTORY-CREATION
#load_bearing_audit_report Dregg2.Circuit.Spec.FactoryCreation.factoryAdmit
  nonvacuous := Dregg2.Circuit.Spec.FactoryCreation.createFromFactoryA_rejects_unauthorized
#load_bearing_audit_report Dregg2.Circuit.Spec.FactoryCreation.CreateFromFactorySpec
  nonvacuous := Dregg2.Circuit.Spec.FactoryCreation.createFromFactoryA_rejects_unauthorized

-- NOTE-COMMITMENT / NOTE-NULLIFIER
#load_bearing_audit_report Dregg2.Circuit.Spec.NoteCommitment.NoteCreateASpec
  nonvacuous := Dregg2.Circuit.Spec.NoteCommitment.noteCreateChainA_iff_spec
#load_bearing_audit_report Dregg2.Circuit.Spec.NoteNullifier.noteSpendGuard
  nonvacuous := Dregg2.Circuit.Spec.NoteNullifier.execFullA_noteSpend_rejects_double
#load_bearing_audit_report Dregg2.Circuit.Spec.NoteNullifier.NoteSpendSpec
  nonvacuous := Dregg2.Circuit.Spec.NoteNullifier.execFullA_noteSpend_rejects_double

-- QUEUE / PIPELINED SEND
#load_bearing_audit_report Dregg2.Circuit.Spec.QueuePipelinedSend.PipelinedSendSpec
  nonvacuous := Dregg2.Circuit.Spec.QueuePipelinedSend.execFullA_pipelinedSend_iff_spec

/-! ===========================================================================
## §2 — the FunctionalRefinement `*Gate`/`*Spec` family.
=========================================================================== -/

#load_bearing_audit_report Dregg2.Spec.FunctionalRefinement.mintGate
  nonvacuous := Dregg2.Spec.FunctionalRefinement.mint_triangle
#load_bearing_audit_report Dregg2.Spec.FunctionalRefinement.burnGate
  nonvacuous := Dregg2.Spec.FunctionalRefinement.burn_triangle
#load_bearing_audit_report Dregg2.Spec.FunctionalRefinement.stateWriteGate
  nonvacuous := Dregg2.Spec.FunctionalRefinement.mint_triangle
#load_bearing_audit_report Dregg2.Spec.FunctionalRefinement.makeSovereignGate
  nonvacuous := Dregg2.Spec.FunctionalRefinement.mint_triangle
#load_bearing_audit_report Dregg2.Spec.FunctionalRefinement.cellDestroyGate
  nonvacuous := Dregg2.Spec.FunctionalRefinement.mint_triangle
#load_bearing_audit_report Dregg2.Spec.FunctionalRefinement.refreshDelegationGate
  nonvacuous := Dregg2.Spec.FunctionalRefinement.mint_triangle
#load_bearing_audit_report Dregg2.Spec.FunctionalRefinement.createCellGate
  nonvacuous := Dregg2.Spec.FunctionalRefinement.mint_triangle

/-! ===========================================================================
## §3 — the execGraph refinement layer + the Exec attestation invariants.
The CALIBRATION + the sibling-collapse hunt. `execGraph` MUST FAIL #2 (defeq to gate copy).
`fullActionInvA` / `gatedActionInvG` back guarantee C-c1 — check whether the `execGraph`
collapse propagates into them (boundary [1] only catches executor STEP gates, not the
Spec-side `execGraph` `.any` copy, so this is reported in prose; the defeq pairing is run on
`execGraph` itself, the source).
=========================================================================== -/

-- CALIBRATION: execGraph — MUST FAIL #2 (defeq to its own `.any` gate copy). It is no longer the
-- abstract refinement TARGET (the inheritors below now ride `authConnects`); it survives ONLY as the
-- genuine graph-CHANGE carrier (`addEdge`/`removeEdge`), where the defeq is harmless.
#load_bearing_audit_report Dregg2.Spec.execGraph
  gate := Dregg2.Verify.LoadBearingAuditBroad.execGraphGate

-- THE SEVERED SPEC: `authConnects` — the INDEPENDENT authority-connectivity reference the C-c1
-- authority-graph legs now attest against. MUST PASS: [1] independent (no step gate, only the pure
-- `confersEdgeTo`-shape over the cap-table), [2] NOT defeq to the gate copy (the `∃ … ∧ …` Prop vs
-- the `.any … = true` Bool fold), [3] non-vacuous (`authConnects_nonvacuous` — accepts a held cap,
-- refutes an empty slot).
#load_bearing_audit_report Dregg2.Spec.authConnects
  gate := Dregg2.Verify.LoadBearingAuditBroad.execGraphGate
  nonvacuous := Dregg2.Spec.authConnects_nonvacuous

-- the refinement abstraction-function relation (now over `authConnects`, with a non-vacuity witness):
#load_bearing_audit_report Dregg2.Spec.Refines
  nonvacuous := Dregg2.Spec.authConnects_nonvacuous
#load_bearing_audit_report Dregg2.Spec.absOf
  nonvacuous := Dregg2.Spec.authConnects_nonvacuous

-- the Exec attestation invariants (guarantee C-c1): boundary + non-vacuity.
#load_bearing_audit_report Dregg2.Exec.TurnExecutorFull.fullActionInvA
#load_bearing_audit_report Dregg2.Exec.FullForestAuth.gatedActionInvG

end Dregg2.Verify.LoadBearingAuditBroad
