/-
# Dregg2.Apps.StorageGatewayMandateGated — storage gateway mandate on `execFullForestG` / `trajG`.
-/
import Dregg2.Exec.GatedForestCfg
import Dregg2.Exec.CellExecutor
import Dregg2.Exec.CellReal
import Dregg2.Apps.StorageGatewayMandate
import Dregg2.Verify.Catalog
import Dregg2.Verify.Contract

namespace Dregg2.Apps.StorageGatewayMandateGated

open Dregg2.Exec
open Dregg2.Exec (cellObsA trajG SchedG)
open Dregg2.Apps.StorageGatewayMandate
open Dregg2.Verify (gateRevoked asset_conserved_forever_production assetConserved composeContracts)
open Dregg2.Verify.Production (Contract Sched liftFromKernelForest)

abbrev KFContract := Dregg2.Verify.KernelForest.Contract
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.StarbridgeGated

abbrev sgmActor : CellId := mandateActor

def sgmSetKeyNode (cred : Authorization Dg Pf) (key : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA sgmActor mandateCell objectKeySlot key, [] ⟩

def sgmSetOpNode (cred : Authorization Dg Pf) (op : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA sgmActor mandateCell lastOpSlot op, [] ⟩

def sgmDebitVolumeNode (cred : Authorization Dg Pf) (newSpent : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA sgmActor mandateCell volumeSpentSlot newSpent, [] ⟩

def sgmEmitNode (cred : Authorization Dg Pf) (blobHash : Int) : DForest :=
  ⟨ mkAuth cred [], .emitEventA sgmActor mandateCell sgmEmitTopic blobHash, [] ⟩

/-- Gated PUT turn: set object key + op, emit blob hash. -/
def sgmPutNode (cred : Authorization Dg Pf) (key op blobHash : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA sgmActor mandateCell objectKeySlot key
  , [ { holder := sgmActor, keep := [], parentCap := .endpoint sgmActor []
      , sub := ⟨ mkAuth cred [], .setFieldA sgmActor mandateCell lastOpSlot op
              , [ { holder := sgmActor, keep := [], parentCap := .endpoint sgmActor []
                  , sub := ⟨ mkAuth cred [], .emitEventA sgmActor mandateCell sgmEmitTopic blobHash, [] ⟩ } ] ⟩ } ] ⟩

theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK; rw [hcred]; simp

theorem sgm_forged_rejected (s : RecChainedState) (key : Int) :
    execFullForestG s (sgmSetKeyNode forgedCred key) = none := by
  rw [sgmSetKeyNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.setFieldA sgmActor mandateCell objectKeySlot key) [] (gateOK_forged_false s)

theorem sgm_forged_put_rejected (s : RecChainedState) (key op blobHash : Int) :
    execFullForestG s (sgmPutNode forgedCred key op blobHash) = none := by
  rw [sgmPutNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.setFieldA sgmActor mandateCell objectKeySlot key) [] (gateOK_forged_false s)

theorem sgm_revoked_rejected (s : RecChainedState) (cred : Authorization Dg Pf) (key : Int)
    (hrev : s.kernel.revoked.contains (mkAuth cred []).credNul = true) :
    execFullForestG s (sgmSetKeyNode cred key) = none := by
  rw [sgmSetKeyNode]
  exact execFullForestG_unauthorized_fails s (mkAuth cred [])
    (.setFieldA sgmActor mandateCell objectKeySlot key) [] (gateOK_revoked_fails (mkAuth cred []) s hrev)

theorem sgm_over_debit_rejected_gated (s : RecChainedState) (newSpent : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hbound : caveatsAdmit s.kernel volumeSpentSlot sgmActor mandateCell newSpent = false) :
    execFullForestG s (sgmDebitVolumeNode goodCred newSpent) = none := by
  rw [sgmDebitVolumeNode, execFullForestG_leaf, execFullAGated, if_pos hgate]
  exact stateStepGuarded_caveat_violation_fails s volumeSpentSlot sgmActor mandateCell newSpent hbound

/-! ### §commit-iff — the gated executor COMMITS a `last_op` write IFF `sgmAdmitM`'s op-leg admits.

The output-side value frame for the op leg: on a mandate cell carrying `mandateCaveats`, with valid
prior op code, the GATED executor commits a `last_op := op` write IFF the gate passes AND the op is
admitted by `sgmAdmitM`'s op-allowlist ∧ GET-clearance leg. The negative tooth
(`sgm_guest_get_rejected`) exhibits a concrete guest (no-clearance) state where a GET write is
rejected by the executor. -/

theorem execFullForestG_setOpNode (s : RecChainedState) (cred : Authorization Dg Pf) (op : Int) :
    execFullForestG s (sgmSetOpNode cred op)
      = (if gateOK (mkAuth cred []) s = true
         then stateStepGuarded s lastOpSlot sgmActor mandateCell op
         else none) := by
  rw [sgmSetOpNode, execFullForestG_leaf, execFullAGated]
  rfl

/-- **`sgm_commit_iff_op_admit_gated` — PROVED (output-side COMMIT-IFF-ADMIT, op leg).** On a mandate
cell carrying the op admit-table, with the credential gate (`hg`) and the executor's authority/liveness
gate (`hauth`) passing, the gated executor COMMITS a `last_op := op.toInt` write IFF `sgmAdmitM`'s op
leg admits `op`. Pins that the ONLY committable ops are the admitted ones. -/
theorem sgm_commit_iff_op_admit_gated (s : RecChainedState)
    (hprog : s.kernel.slotCaveats mandateCell = mandateCaveats) (op : StorageOp)
    (hold : fieldOf lastOpSlot (s.kernel.cell mandateCell) ∈ [(-1 : Int), 0, 1, 2])
    (hg : gateOK (mkAuth goodCred []) s = true)
    (hauth : stateAuthB s.kernel.caps sgmActor mandateCell = true ∧ mandateCell ∈ s.kernel.accounts
              ∧ cellLive s.kernel mandateCell = true) :
    (∃ s', execFullForestG s (sgmSetOpNode goodCred op.toInt) = some s')
      ↔ sgmOpAdmitted demoMandate op = true := by
  rw [execFullForestG_setOpNode, if_pos hg]
  constructor
  · rintro ⟨s', hs'⟩
    have hadm := stateStepGuarded_admits hs'
    exact (sgm_commit_iff_op_admit s.kernel hprog sgmActor op hold).mp hadm
  · intro hadm
    have hcav : caveatsAdmit s.kernel lastOpSlot sgmActor mandateCell op.toInt = true :=
      (sgm_commit_iff_op_admit s.kernel hprog sgmActor op hold).mpr hadm
    refine ⟨{ kernel := writeField s.kernel lastOpSlot mandateCell (.int op.toInt),
              log := { actor := sgmActor, src := mandateCell, dst := mandateCell, amt := 0 } :: s.log }, ?_⟩
    unfold stateStepGuarded
    rw [if_pos hcav]
    unfold stateStep
    rw [if_pos hauth]

/-! ### §negative-tooth — a GUEST writing op GET (no clearance) is rejected by the EXECUTOR. -/

/-- Guest-clearance program: the op admit-table built from `guestMandate` (no GET clearance) — admits
PUT/LIST but NOT GET. -/
def guestCaveats : List SlotCaveat :=
  [ .immutable commitmentAnchorSlot
  , .monotonic volumeSpentSlot
  , .boundedBy volumeSpentSlot 0 (demoMandate.volumeBudget.ceiling : Int)
  , .admitTable lastOpSlot (sgmOpAdmitTable guestMandate) ]

/-- Genesis cell carrying the GUEST (no-GET-clearance) op program. -/
def guestSgmG0 : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun c =>
          if c = mandateCell then
            .record [("balance", .int 0), (objectKeySlot, .int 0), (lastOpSlot, .int (-1)),
                     (volumeSpentSlot, .int 0), (commitmentAnchorSlot, .int demoMandate.anchor)]
          else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0) else 0
        slotCaveats := fun c => if c = mandateCell then guestCaveats else [] }
    log := [] }

/-- **`sgm_guest_get_rejected` — PROVED (THE NEGATIVE TOOTH).** A guest lacking GET clearance CANNOT
record a GET op (`last_op := 0`): the executor returns `none`, because `(_, 0)` is NOT in the guest's
op admit-table. This is exactly the request `sgmAdmitM guestMandate _ {op := GET}` rejects — now
ENFORCED BY THE EXECUTOR (where no prior caveat could express clearance). -/
theorem sgm_guest_get_rejected :
    execFullForestG guestSgmG0 (sgmSetOpNode goodCred (StorageOp.GET.toInt)) = none := by
  rw [execFullForestG_setOpNode]
  by_cases hg : gateOK (mkAuth goodCred []) guestSgmG0 = true
  · rw [if_pos hg]
    have hcav : caveatsAdmit guestSgmG0.kernel lastOpSlot sgmActor mandateCell (StorageOp.GET.toInt) = false := by decide
    exact stateStepGuarded_caveat_violation_fails guestSgmG0 lastOpSlot sgmActor mandateCell (StorageOp.GET.toInt) hcav
  · rw [if_neg (by simp [hg])]

theorem sgmSetKeyNode_delta_zero (cred : Authorization Dg Pf) (key : Int) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (sgmSetKeyNode cred key)).map Prod.snd) b = 0 := by
  simp [sgmSetKeyNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem sgmEmitNode_delta_zero (cred : Authorization Dg Pf) (blobHash : Int) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (sgmEmitNode cred blobHash)).map Prod.snd) b = 0 := by
  simp [sgmEmitNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem sgm_op_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (key : Int) (b : AssetId)
    (h : execFullForestG s (sgmSetKeyNode cred key) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (sgmSetKeyNode cred key) b h
    (sgmSetKeyNode_delta_zero cred key b)

theorem sgm_emit_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (blobHash : Int) (b : AssetId)
    (h : execFullForestG s (sgmEmitNode cred blobHash) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (sgmEmitNode cred blobHash) b h
    (sgmEmitNode_delta_zero cred blobHash b)

theorem sgm_pay_conserved_forever (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) payAsset = cellObsA s0 payAsset :=
  asset_conserved_forever_production s0 payAsset sched

theorem sgm_revoked_rejected_forever (s : RecChainedState) (cred : Authorization Dg Pf) (key : Int)
    (hinit : (mkAuth cred []).credNul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, execFullForestG (trajG s sched n) (sgmSetKeyNode cred key) = none := by
  intro n
  exact sgm_revoked_rejected (trajG s sched n) cred key
    (List.contains_iff_mem.mpr ((gateRevoked (mkAuth cred []).credNul).forever hinit sched n))

noncomputable def sgmStepLegalContractKF : KFContract where
  Inv s := sgmWF s.kernel
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]; unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | none => simp only [Option.getD_none]; exact h
    | some a' => simp only [Option.getD_some]; exact sgmWF_traj_carries a a' cf.1 hc h
  shape := .other

noncomputable def sgmBucketContractKF (bucket : Int) : KFContract where
  Inv s := sgmInBucket s.kernel bucket
  step_ob a cf h := by
    rw [CellExecutor.kernelForest_next_eq]; unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | none => simp only [Option.getD_none]; exact h
    | some a' => simp only [Option.getD_some]; exact sgmBucket_traj_carries a a' cf.1 bucket hc h
  shape := .membership

noncomputable def sgmStepLegalContract : Contract := liftFromKernelForest sgmStepLegalContractKF
noncomputable def sgmBucketContract (bucket : Int) : Contract := liftFromKernelForest (sgmBucketContractKF bucket)

noncomputable def sgmPayConserved (s0 : RecChainedState) : Contract := assetConserved s0 payAsset
noncomputable def sgmRevokedDead (nul : Nat) : Contract := gateRevoked nul

noncomputable def sgmSafetyContract (s0 : RecChainedState) (nul : Nat) (bucket : Int) : Contract :=
  composeContracts
    (composeContracts (composeContracts sgmStepLegalContract (sgmPayConserved s0)) (sgmRevokedDead nul))
    (sgmBucketContract bucket)

theorem sgm_safety_forever (s0 : RecChainedState) (nul : Nat) (bucket : Int) (s : RecChainedState)
    (hstep : sgmWF s.kernel) (hpay : cellObsA s payAsset = cellObsA s0 payAsset)
    (hrev : nul ∈ s.kernel.revoked) (hbucket : sgmInBucket s.kernel bucket) (sched : SchedG) :
    ∀ n,
      sgmWF (trajG s sched n).kernel ∧
        cellObsA (trajG s sched n) payAsset = cellObsA s0 payAsset ∧
          nul ∈ (trajG s sched n).kernel.revoked ∧
            sgmInBucket (trajG s sched n).kernel bucket := by
  intro n
  have h := (sgmSafetyContract s0 nul bucket).forever
    (And.intro (And.intro (And.intro hstep hpay) hrev) hbucket) sched n
  rcases h with ⟨⟨⟨hstep', hpay'⟩, hrev'⟩, hbucket'⟩
  exact And.intro hstep' (And.intro hpay' (And.intro hrev' hbucket'))

def sgmG0 : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun c =>
          if c = mandateCell then
            .record [("balance", .int 0), (objectKeySlot, .int 0), (lastOpSlot, .int (-1)),
                     (volumeSpentSlot, .int 0), (commitmentAnchorSlot, .int demoMandate.anchor)]
          else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0) else 0
        slotCaveats := fun c => if c = mandateCell then mandateCaveats else [] }
    log := [] }

def sgmGPutKey : Option RecChainedState :=
  execFullForestG sgmG0 (sgmSetKeyNode goodCred demoKeyCode)

def sgmGPutOp : Option RecChainedState :=
  sgmGPutKey.bind (fun s => execFullForestG s (sgmSetOpNode goodCred (StorageOp.PUT.toInt)))

def sgmGPutEmit : Option RecChainedState :=
  sgmGPutOp.bind (fun s => execFullForestG s (sgmEmitNode goodCred demoBlobHash))

#guard (gateOK (mkAuth goodCred []) sgmG0)
#guard (sgmAdmitM demoMandate (SgmRuntime.init demoMandate) demoPutReq).isSome
#guard (sgmAdmitM demoMandate (SgmRuntime.init demoMandate) demoBadPutReq).isSome == false
#guard (sgmAdmitM guestMandate (SgmRuntime.init guestMandate) demoGetReq).isSome == false
#guard (caveatsAdmit sgmG0.kernel volumeSpentSlot sgmActor mandateCell 11) == false
#guard ((execFullForestG sgmG0 (sgmDebitVolumeNode goodCred 11)).isSome) == false
#guard ((execFullForestG sgmG0 (sgmSetKeyNode forgedCred demoKeyCode)).isSome) == false
#guard ((execFullForestG ({ sgmG0 with kernel := { sgmG0.kernel with revoked := [(mkAuth goodCred []).credNul] } })
          (sgmSetKeyNode goodCred demoKeyCode)).isSome) == false
#guard (sgmGPutKey.map (fun s => fieldOf objectKeySlot (s.kernel.cell mandateCell))) == some demoKeyCode
#guard (sgmGPutOp.map (fun s => fieldOf lastOpSlot (s.kernel.cell mandateCell))) == some 1
#guard (sgmGPutEmit.isSome)
#guard (sgmVolumeBound sgmG0.kernel)
#guard (sgmAnchorIs sgmG0.kernel (demoMandate.anchor : Int))
#guard ((sgmGPutEmit.map (fun s => recTotalAssetWithEscrow s.kernel payAsset)).getD 0) == 100

-- COMMIT-IFF-ADMIT negative tooth: a guest lacking GET clearance cannot record a GET op — the
-- EXECUTOR rejects the `last_op := 0` write (where no prior caveat could express clearance).
#guard ((execFullForestG guestSgmG0 (sgmSetOpNode goodCred (StorageOp.GET.toInt))).isSome) == false
#guard (caveatsAdmit guestSgmG0.kernel lastOpSlot sgmActor mandateCell (StorageOp.GET.toInt)) == false
-- the demo (writer-clearance) cell DOES admit the GET op
#guard (caveatsAdmit sgmG0.kernel lastOpSlot sgmActor mandateCell (StorageOp.GET.toInt)) == true
#guard (sgmOpAdmitted demoMandate StorageOp.GET) == true
#guard (sgmOpAdmitted guestMandate StorageOp.GET) == false
#guard (sgmOpAdmitted demoMandate StorageOp.PUT) == true

#assert_axioms execFullForestG_setOpNode
#assert_axioms sgm_commit_iff_op_admit_gated
#assert_axioms sgm_guest_get_rejected
#assert_axioms execFullForestG_leaf
#assert_axioms sgm_forged_rejected
#assert_axioms sgm_revoked_rejected
#assert_axioms sgm_over_debit_rejected_gated
#assert_axioms sgm_op_conserves
#assert_axioms sgm_pay_conserved_forever
#assert_axioms sgm_revoked_rejected_forever
#assert_axioms sgmSafetyContract
#assert_axioms sgm_safety_forever

end Dregg2.Apps.StorageGatewayMandateGated