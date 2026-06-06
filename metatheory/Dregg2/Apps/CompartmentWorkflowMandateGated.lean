/-
# Dregg2.Apps.CompartmentWorkflowMandateGated — compartment workflow mandate on `execFullForestG` / `trajG`.

Phase B: monitor `refreshDelegation` re-up teeth (parent c-list snapshot), strengthened clearance
predicates on the gated path, and `cwm_safety_forever` wired through Hatchery `composeContracts`.
-/
import Dregg2.Exec.GatedForestCfg
import Dregg2.Exec.CellExecutor
import Dregg2.Exec.CellReal
import Dregg2.Authority.Positional
import Dregg2.Apps.CompartmentWorkflowMandate
import Dregg2.Verify.Catalog
import Dregg2.Verify.Contract

namespace Dregg2.Apps.CompartmentWorkflowMandateGated

open Dregg2.Exec
open Dregg2.Exec (cellObsA trajG SchedG)
open Dregg2.Apps.CompartmentWorkflowMandate
open Dregg2.Verify (gateRevoked asset_conserved_forever_production assetConserved composeContracts)
open Dregg2.Verify.Production (Contract Sched liftFromKernelForest)

abbrev KFContract := Dregg2.Verify.KernelForest.Contract
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated
open Dregg2.Authority (Cap)

abbrev cwmActor : CellId := mandateActor
abbrev cwmMonitorCell : CellId := 1
abbrev cwmEmitTopic : Int := 7

def cwmAdvanceNode (cred : Authorization Dg Pf) (target : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA cwmActor mandateCell stepCursorSlot target, [] ⟩

def cwmPhaseNode (cred : Authorization Dg Pf) (cur : Nat) : DForest :=
  cwmAdvanceNode cred (cur + 1)

def cwmEmitNode (cred : Authorization Dg Pf) (data : Int) : DForest :=
  ⟨ mkAuth cred [], .emitEventA cwmActor mandateCell cwmEmitTopic data, [] ⟩

/-- Monitor refresh: self-only `refreshDelegationA` snapshots the parent's CURRENT c-list. -/
def cwmRefreshNode (cred : Authorization Dg Pf) : DForest :=
  ⟨ mkAuth cred [], .refreshDelegationA cwmMonitorCell cwmMonitorCell, [] ⟩

theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

theorem execFullForestG_advanceNode (s : RecChainedState) (cred : Authorization Dg Pf) (target : Int) :
    execFullForestG s (cwmAdvanceNode cred target)
      = (if gateOK (mkAuth cred []) s = true
         then stateStepGuarded s stepCursorSlot cwmActor mandateCell target
         else none) := by
  rw [cwmAdvanceNode, execFullForestG_leaf, execFullAGated]
  rfl

theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK; rw [hcred]; simp

theorem cwm_forged_rejected (s : RecChainedState) (target : Int) :
    execFullForestG s (cwmAdvanceNode forgedCred target) = none := by
  rw [cwmAdvanceNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.setFieldA cwmActor mandateCell stepCursorSlot target) [] (gateOK_forged_false s)

theorem cwm_forged_emit_rejected (s : RecChainedState) (data : Int) :
    execFullForestG s (cwmEmitNode forgedCred data) = none := by
  rw [cwmEmitNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.emitEventA cwmActor mandateCell cwmEmitTopic data) [] (gateOK_forged_false s)

theorem cwm_revoked_rejected (s : RecChainedState) (cred : Authorization Dg Pf) (target : Int)
    (hrev : s.kernel.revoked.contains (mkAuth cred []).credNul = true) :
    execFullForestG s (cwmAdvanceNode cred target) = none := by
  rw [cwmAdvanceNode]
  exact execFullForestG_unauthorized_fails s (mkAuth cred [])
    (.setFieldA cwmActor mandateCell stepCursorSlot target) [] (gateOK_revoked_fails (mkAuth cred []) s hrev)

theorem cwm_revoked_emit_rejected (s : RecChainedState) (cred : Authorization Dg Pf) (data : Int)
    (hrev : s.kernel.revoked.contains (mkAuth cred []).credNul = true) :
    execFullForestG s (cwmEmitNode cred data) = none := by
  rw [cwmEmitNode]
  exact execFullForestG_unauthorized_fails s (mkAuth cred [])
    (.emitEventA cwmActor mandateCell cwmEmitTopic data) [] (gateOK_revoked_fails (mkAuth cred []) s hrev)

theorem cwm_illegal_dag_rejected_gated (s : RecChainedState) (target : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hseq : caveatsAdmit s.kernel stepCursorSlot cwmActor mandateCell target = false) :
    execFullForestG s (cwmAdvanceNode goodCred target) = none := by
  rw [execFullForestG_advanceNode, if_pos hgate]
  exact stateStepGuarded_caveat_violation_fails s stepCursorSlot cwmActor mandateCell target hseq

/-- **`cwm_clearance_violation_rejected_gated` (PROVED)** — insufficient clearance at the current
cursor is rejected at the predicate layer (`cwmAdvanceM`), independent of the executor gate. -/
theorem cwm_clearance_violation_rejected_gated (s : CwmRuntime)
    (hadm : stepAdmissible charterMandate3 s.cursor (completedOf s.cursor) = true)
    (hcl : stepClearanceOK charterMandate3 s.cursor = false)
    (hlen : s.cursor < charterMandate3.steps.length) :
    cwmAdvanceM charterMandate3 s = none :=
  cwm_clearance_violation_rejected charterMandate3 s hadm hcl hlen

theorem execFullForestG_refreshNode (s : RecChainedState) (cred : Authorization Dg Pf) :
    execFullForestG s (cwmRefreshNode cred) =
      execFullAGated s (mkAuth cred []) (.refreshDelegationA cwmMonitorCell cwmMonitorCell) := by
  rw [cwmRefreshNode, execFullForestG_leaf]

theorem cwm_refresh_forged_rejected (s : RecChainedState) :
    execFullForestG s (cwmRefreshNode forgedCred) = none := by
  rw [cwmRefreshNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.refreshDelegationA cwmMonitorCell cwmMonitorCell) [] (gateOK_forged_false s)

theorem cwm_refresh_revoked_rejected (s : RecChainedState) (cred : Authorization Dg Pf)
    (hrev : s.kernel.revoked.contains (mkAuth cred []).credNul = true) :
    execFullForestG s (cwmRefreshNode cred) = none := by
  rw [cwmRefreshNode]
  exact execFullForestG_unauthorized_fails s (mkAuth cred [])
    (.refreshDelegationA cwmMonitorCell cwmMonitorCell) [] (gateOK_revoked_fails (mkAuth cred []) s hrev)

theorem cwm_refresh_no_parent_rejected (s : RecChainedState)
    (h : s.kernel.delegate cwmMonitorCell = none) :
    execFullForestG s (cwmRefreshNode goodCred) = none := by
  rw [execFullForestG_refreshNode, execFullAGated]
  by_cases hg : gateOK (mkAuth goodCred []) s = true
  · rw [if_pos hg]
    simpa [execFullA] using refreshDelegationChainA_noParent_rejects s cwmMonitorCell cwmMonitorCell h
  · rw [if_neg (by simp [hg])]

theorem cwm_refresh_snapshots_parent {s s' : RecChainedState} (p : CellId)
    (_hgate : gateOK (mkAuth goodCred []) s = true)
    (hp : s.kernel.delegate cwmMonitorCell = some p)
    (h : execFullForestG s (cwmRefreshNode goodCred) = some s') :
    s'.kernel.delegations cwmMonitorCell = s.kernel.caps p := by
  rw [execFullForestG_refreshNode, execFullAGated] at h
  rcases (execFullAGated_some_iff s s' (mkAuth goodCred [])
    (.refreshDelegationA cwmMonitorCell cwmMonitorCell)).mp h with ⟨_, hfa⟩
  exact refreshDelegationChainA_snapshots_parent (by simpa only [execFullA] using hfa) hp

theorem cwmRefreshNode_delta_zero (cred : Authorization Dg Pf) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (cwmRefreshNode cred)).map Prod.snd) b = 0 := by
  simp [cwmRefreshNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem cwm_refresh_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (b : AssetId)
    (h : execFullForestG s (cwmRefreshNode cred) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (cwmRefreshNode cred) b h
    (cwmRefreshNode_delta_zero cred b)

theorem cwmAdvanceNode_delta_zero (cred : Authorization Dg Pf) (target : Int) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (cwmAdvanceNode cred target)).map Prod.snd) b = 0 := by
  simp [cwmAdvanceNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem cwmEmitNode_delta_zero (cred : Authorization Dg Pf) (data : Int) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (cwmEmitNode cred data)).map Prod.snd) b = 0 := by
  simp [cwmEmitNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem cwm_op_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (target : Int) (b : AssetId)
    (h : execFullForestG s (cwmAdvanceNode cred target) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (cwmAdvanceNode cred target) b h
    (cwmAdvanceNode_delta_zero cred target b)

theorem cwm_emit_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (data : Int) (b : AssetId)
    (h : execFullForestG s (cwmEmitNode cred data) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (cwmEmitNode cred data) b h
    (cwmEmitNode_delta_zero cred data b)

theorem cwm_pay_conserved_forever (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) payAsset = cellObsA s0 payAsset :=
  asset_conserved_forever_production s0 payAsset sched

theorem cwm_revoked_rejected_forever (s : RecChainedState) (cred : Authorization Dg Pf) (target : Int)
    (hinit : (mkAuth cred []).credNul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, execFullForestG (trajG s sched n) (cwmAdvanceNode cred target) = none := by
  intro n
  exact cwm_revoked_rejected (trajG s sched n) cred target
    (List.contains_iff_mem.mpr ((gateRevoked (mkAuth cred []).credNul).forever hinit sched n))

noncomputable def cwmStepLegalContractKF : KFContract where
  Inv s := cwmWF s.kernel
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]; unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | none => simp only [Option.getD_none]; exact h
    | some a' => simp only [Option.getD_some]; exact cwmWF_traj_carries a a' cf.1 hc h
  shape := .other

noncomputable def cwmCompartmentContractKF (comp : Int) : KFContract where
  Inv s := cwmInCompartment s.kernel comp
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]; unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | none => simp only [Option.getD_none]; exact h
    | some a' => simp only [Option.getD_some]; exact cwmCompartment_traj_carries a a' cf.1 comp hc h
  shape := .membership

noncomputable def cwmStepLegalContract : Contract := liftFromKernelForest cwmStepLegalContractKF
noncomputable def cwmCompartmentContract (comp : Int) : Contract := liftFromKernelForest (cwmCompartmentContractKF comp)

noncomputable def cwmPayConserved (s0 : RecChainedState) : Contract := assetConserved s0 payAsset
noncomputable def cwmRevokedDead (nul : Nat) : Contract := gateRevoked nul

noncomputable def cwmSafetyContract (s0 : RecChainedState) (nul : Nat) (comp : Int) : Contract :=
  composeContracts
    (composeContracts (composeContracts cwmStepLegalContract (cwmPayConserved s0)) (cwmRevokedDead nul))
    (cwmCompartmentContract comp)

theorem cwm_safety_forever (s0 : RecChainedState) (nul : Nat) (comp : Int) (s : RecChainedState)
    (hstep : cwmWF s.kernel) (hpay : cellObsA s payAsset = cellObsA s0 payAsset)
    (hrev : nul ∈ s.kernel.revoked) (hcomp : cwmInCompartment s.kernel comp) (sched : SchedG) :
    ∀ n,
      cwmWF (trajG s sched n).kernel ∧
        cellObsA (trajG s sched n) payAsset = cellObsA s0 payAsset ∧
          nul ∈ (trajG s sched n).kernel.revoked ∧
            cwmInCompartment (trajG s sched n).kernel comp := by
  intro n
  have h := (cwmSafetyContract s0 nul comp).forever
    (And.intro (And.intro (And.intro hstep hpay) hrev) hcomp) sched n
  rcases h with ⟨⟨⟨hstep', hpay'⟩, hrev'⟩, hcomp'⟩
  exact And.intro hstep' (And.intro hpay' (And.intro hrev' hcomp'))

def cwmG0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c =>
          if c = mandateCell then
            .record [("balance", .int 100), (stepCursorSlot, .int 0),
                     (commitmentAnchorSlot, .int cwmCompartmentTag)]
          else .record [("balance", .int 0)]
        caps := fun c => if c = cwmActor then [Cap.node cwmMonitorCell, Cap.node 2] else []
        delegate := fun c => if c = cwmMonitorCell then some cwmActor else none
        delegations := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0) else 0
        slotCaveats := fun c => if c = mandateCell then mandateCaveats else [] }
    log := [] }

def cwmGReviewed : Option RecChainedState :=
  execFullForestG cwmG0 (cwmPhaseNode goodCred 0)

def cwmGRedacted : Option RecChainedState :=
  cwmGReviewed.bind (fun s => execFullForestG s (cwmPhaseNode goodCred 1))

def cwmGSigned : Option RecChainedState :=
  cwmGRedacted.bind (fun s => execFullForestG s (cwmPhaseNode goodCred 2))

#guard (gateOK (mkAuth goodCred []) cwmG0)
#guard (caveatsAdmit cwmG0.kernel stepCursorSlot cwmActor mandateCell 1)
#guard ((execFullForestG cwmG0 (cwmPhaseNode goodCred 0)).isSome)
#guard (caveatsAdmit cwmG0.kernel stepCursorSlot cwmActor mandateCell 2) == false
#guard ((execFullForestG cwmG0 (cwmAdvanceNode goodCred 2)).isSome) == false
#guard ((execFullForestG cwmG0 (cwmAdvanceNode forgedCred 1)).isSome) == false
#guard ((execFullForestG ({ cwmG0 with kernel := { cwmG0.kernel with revoked := [(mkAuth goodCred []).credNul] } })
          (cwmAdvanceNode goodCred 1)).isSome) == false
#guard (cwmAdvanceM clerkMandate3 { cursor := 1, anchor := 42 }).isSome == false
#guard ((execFullForestG cwmG0 (cwmEmitNode goodCred 99)).isSome)
#guard (cwmCursorBound cwmG0.kernel)
#guard (cwmAnchorIs cwmG0.kernel cwmCompartmentTag)
#guard (cwmGReviewed.map (fun s => fieldOf stepCursorSlot (s.kernel.cell mandateCell))) == some 1
#guard (cwmGRedacted.map (fun s => fieldOf stepCursorSlot (s.kernel.cell mandateCell))) == some 2
#guard (cwmGSigned.map (fun s => fieldOf stepCursorSlot (s.kernel.cell mandateCell))) == some 3
#guard (cwmGSigned.map (fun s => fieldOf commitmentAnchorSlot (s.kernel.cell mandateCell))) == some cwmCompartmentTag
#guard ((cwmGSigned.map (fun s => recTotalAssetWithEscrow s.kernel payAsset)).getD 0) == 100
#guard (cwmClearanceOK cwmG0.kernel)
#guard (cwmWFStrong cwmG0.kernel)
#guard (cwmInCompartmentStrong cwmG0.kernel cwmCompartmentTag)
#guard ((execFullForestG cwmG0 (cwmRefreshNode goodCred)).isSome)
#guard ((execFullForestG cwmG0 (cwmRefreshNode goodCred)).map
        (fun s => (s.kernel.delegations cwmMonitorCell).length)) == some 2
#guard ((execFullForestG cwmG0 (cwmRefreshNode forgedCred)).isSome) == false
#guard ((execFullForestG ({ cwmG0 with kernel := { cwmG0.kernel with delegate := fun _ => none } })
          (cwmRefreshNode goodCred)).isSome) == false
#guard (cwmAdvanceM clerkMandate3 { cursor := 1, anchor := 42 }).isSome == false

#assert_axioms execFullForestG_leaf
#assert_axioms cwm_forged_rejected
#assert_axioms cwm_revoked_rejected
#assert_axioms cwm_illegal_dag_rejected_gated
#assert_axioms cwm_op_conserves
#assert_axioms cwm_pay_conserved_forever
#assert_axioms cwm_revoked_rejected_forever
#assert_axioms cwm_clearance_violation_rejected_gated
#assert_axioms execFullForestG_refreshNode
#assert_axioms cwm_refresh_forged_rejected
#assert_axioms cwm_refresh_revoked_rejected
#assert_axioms cwm_refresh_no_parent_rejected
#assert_axioms cwm_refresh_snapshots_parent
#assert_axioms cwm_refresh_conserves
#assert_axioms cwmSafetyContract
#assert_axioms cwm_safety_forever

end Dregg2.Apps.CompartmentWorkflowMandateGated