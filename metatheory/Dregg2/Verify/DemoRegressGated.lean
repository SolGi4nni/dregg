/-
# Dregg2.Verify.DemoRegressGated — H4 gate on the production executor (`trajG`).

Mirrors `Verify/Regression.lean` for `CellExecutor.production`: the six shipped crowns reproduced
on `trajG` with bidirectional defeq witnesses against the named production theorems and the
Hatchery toolkit (catalog macros + tactics). Kernel regression (`Regression.lean`) pins `trajA`;
this module pins `trajG` — the executor customers run.
-/
import Dregg2.Verify.Catalog
import Dregg2.Verify.Tactics
import Dregg2.Apps.NameService
import Dregg2.Apps.Subscription
import Dregg2.Apps.ComputeExchangeGated
import Dregg2.Apps.CompartmentWorkflowMandateGated
import Dregg2.Apps.StorageGatewayMandateGated
import Dregg2.Verify.AppComposition

namespace Dregg2.Verify

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (fma0)
open Dregg2.Exec.FullForest
open Dregg2.Exec (AlwaysG)
open KernelForest (Contract Sched)
open Production (Contract Sched liftFromKernelForest)

/-! ## §1 — Identity: catalog + tactics + contract agree on `trajG`. -/

theorem identity_revoked_foreverG_via_catalog (credNul : Nat) (s : RecChainedState)
    (hinit : credNul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, credNul ∈ (trajG s sched n).kernel.revoked :=
  (liftFromKernelForest (monotone_registry% revoked credNul)).forever hinit sched

example (credNul : Nat) (s : RecChainedState) (hinit : credNul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, credNul ∈ (trajG s sched n).kernel.revoked :=
  identity_revoked_foreverG_via_catalog credNul s hinit sched

example (credNul : Nat) (s : RecChainedState) (hinit : credNul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, credNul ∈ (trajG s sched n).kernel.revoked :=
  Production.identity_revoked_forever_via_tactics credNul s hinit sched

example (credNul : Nat) (s : RecChainedState) (hinit : credNul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, credNul ∈ (trajG s sched n).kernel.revoked :=
  identity_revoked_forever_production credNul s hinit sched

theorem identity_revoked_alwaysG_via_catalog (credNul : Nat) (s : RecChainedState)
    (hinit : credNul ∈ s.kernel.revoked) (sched : SchedG) :
    AlwaysG (fun s' => credNul ∈ s'.kernel.revoked) s sched :=
  Production.always (liftFromKernelForest (monotone_registry% revoked credNul)) hinit sched

/-! ## §2 — Nullifier headline: `monotone_registry% nullifiers` on `trajG`. -/

theorem spent_note_never_respentG_via_catalog (nf : Nat) (s : RecChainedState)
    (hinit : nf ∈ s.kernel.nullifiers) (sched : SchedG) :
    ∀ n, nf ∈ (trajG s sched n).kernel.nullifiers :=
  (liftFromKernelForest (monotone_registry% nullifiers nf)).forever hinit sched

example (nf : Nat) (s : RecChainedState) (hinit : nf ∈ s.kernel.nullifiers) (sched : SchedG) :
    ∀ n, nf ∈ (trajG s sched n).kernel.nullifiers :=
  spent_note_never_respentG_via_catalog nf s hinit sched

example (nf : Nat) (s : RecChainedState) (hinit : nf ∈ s.kernel.nullifiers) (sched : SchedG) :
    ∀ n, nf ∈ (trajG s sched n).kernel.nullifiers :=
  spent_note_never_respent_production nf s hinit sched

/-! ## §3 — `⊆`-shaped nullifier / commitment crowns on `trajG`. -/

theorem no_double_spendG_via_contract (nul0 : List Nat) (s : RecChainedState)
    (hinit : nul0 ⊆ s.kernel.nullifiers) (sched : SchedG) :
    ∀ n, nul0 ⊆ (trajG s sched n).kernel.nullifiers :=
  (subsetNullifiersContract nul0).forever hinit sched

example (nul0 : List Nat) (s : RecChainedState) (hinit : nul0 ⊆ s.kernel.nullifiers) (sched : SchedG) :
    ∀ n, nul0 ⊆ (trajG s sched n).kernel.nullifiers :=
  no_double_spendG_via_contract nul0 s hinit sched

example (nul0 : List Nat) (s : RecChainedState) (hinit : nul0 ⊆ s.kernel.nullifiers) (sched : SchedG) :
    ∀ n, nul0 ⊆ (trajG s sched n).kernel.nullifiers :=
  no_double_spend_production nul0 s hinit sched

theorem commitments_persistG_via_contract (com0 : List Nat) (s : RecChainedState)
    (hinit : com0 ⊆ s.kernel.commitments) (sched : SchedG) :
    ∀ n, com0 ⊆ (trajG s sched n).kernel.commitments :=
  (subsetCommitmentsContract com0).forever hinit sched

example (com0 : List Nat) (s : RecChainedState) (hinit : com0 ⊆ s.kernel.commitments) (sched : SchedG) :
    ∀ n, com0 ⊆ (trajG s sched n).kernel.commitments :=
  commitments_persistG_via_contract com0 s hinit sched

example (com0 : List Nat) (s : RecChainedState) (hinit : com0 ⊆ s.kernel.commitments) (sched : SchedG) :
    ∀ n, com0 ⊆ (trajG s sched n).kernel.commitments :=
  commitments_persist_production com0 s hinit sched

/-! ## §4 — NameService on `trajG`. -/

theorem nameservice_registration_foreverG_via_contract (s : RecChainedState)
    (name owner : Dregg2.Apps.NameService.Name)
    (hinit : Dregg2.Apps.NameService.isRegistered s name owner = true) (sched : SchedG) :
    ∀ n, Dregg2.Apps.NameService.isRegistered (trajG s sched n) name owner = true :=
  (nameRegisteredContract name owner).forever hinit sched

example (s : RecChainedState) (name owner : Dregg2.Apps.NameService.Name)
    (hinit : Dregg2.Apps.NameService.isRegistered s name owner = true) (sched : SchedG) :
    ∀ n, Dregg2.Apps.NameService.isRegistered (trajG s sched n) name owner = true :=
  nameservice_registration_foreverG_via_contract s name owner hinit sched

example (s : RecChainedState) (name owner : Dregg2.Apps.NameService.Name)
    (hinit : Dregg2.Apps.NameService.isRegistered s name owner = true) (sched : SchedG) :
    ∀ n, Dregg2.Apps.NameService.isRegistered (trajG s sched n) name owner = true :=
  nameservice_registration_forever_production s name owner hinit sched

/-! ## §5 — Subscription on `trajG`.

F2b: the `subWF` queue-capacity crown moved to the factory story (`Apps/QueueFactory.lean`)
with the kernel queue side-table's deletion; the gated subscription app's surviving production
crowns are in `Apps/SubscriptionGated.lean` (`sub_pay_conserved_forever` et al). -/

/-! ## §5b — ComputeExchange: payment conservation on `trajG`. -/

theorem cx_pay_conserved_foreverG_via_contract (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) Dregg2.Apps.ComputeExchangeGated.payAsset = cellObsA s0 Dregg2.Apps.ComputeExchangeGated.payAsset :=
  asset_conserved_forever_production s0 Dregg2.Apps.ComputeExchangeGated.payAsset sched

example (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) Dregg2.Apps.ComputeExchangeGated.payAsset = cellObsA s0 Dregg2.Apps.ComputeExchangeGated.payAsset :=
  cx_pay_conserved_foreverG_via_contract s0 sched

example (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) Dregg2.Apps.ComputeExchangeGated.payAsset = cellObsA s0 Dregg2.Apps.ComputeExchangeGated.payAsset :=
  Dregg2.Apps.ComputeExchangeGated.cx_pay_conserved_forever s0 sched

/-! ## §5c — CompartmentWorkflowMandate (CWM): payment conservation on `trajG`. -/

theorem cwm_pay_conserved_foreverG_via_contract (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
      cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset :=
  asset_conserved_forever_production s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset sched

example (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
      cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset :=
  cwm_pay_conserved_foreverG_via_contract s0 sched

example (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
      cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset :=
  Dregg2.Apps.CompartmentWorkflowMandateGated.cwm_pay_conserved_forever s0 sched

/-! ## §5d — CompartmentWorkflowMandate: `cwm_safety_forever` on `trajG`. -/

theorem cwm_safety_foreverG_via_contract (s0 : RecChainedState) (nul : Nat) (comp : Int)
    (s : RecChainedState) (hstep : Dregg2.Apps.CompartmentWorkflowMandate.cwmWF s.kernel)
    (hpay : cellObsA s Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
            cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset)
    (hrev : nul ∈ s.kernel.revoked)
    (hcomp : Dregg2.Apps.CompartmentWorkflowMandate.cwmInCompartment s.kernel comp) (sched : SchedG)
    (hsafe : Dregg2.Apps.CompartmentWorkflowMandateGated.SchedAnchorSafe sched) :
    ∀ n,
      Dregg2.Apps.CompartmentWorkflowMandate.cwmWF (trajG s sched n).kernel ∧
        cellObsA (trajG s sched n) Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
          cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset ∧
            nul ∈ (trajG s sched n).kernel.revoked ∧
              Dregg2.Apps.CompartmentWorkflowMandate.cwmInCompartment (trajG s sched n).kernel comp :=
  Dregg2.Apps.CompartmentWorkflowMandateGated.cwm_safety_forever s0 nul comp s hstep hpay hrev hcomp sched hsafe

example (s0 : RecChainedState) (nul : Nat) (comp : Int) (s : RecChainedState)
    (hstep : Dregg2.Apps.CompartmentWorkflowMandate.cwmWF s.kernel)
    (hpay : cellObsA s Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
            cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset)
    (hrev : nul ∈ s.kernel.revoked)
    (hcomp : Dregg2.Apps.CompartmentWorkflowMandate.cwmInCompartment s.kernel comp)
    (sched : SchedG) (hsafe : Dregg2.Apps.CompartmentWorkflowMandateGated.SchedAnchorSafe sched) :
    ∀ n,
      Dregg2.Apps.CompartmentWorkflowMandate.cwmWF (trajG s sched n).kernel ∧
        cellObsA (trajG s sched n) Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
          cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset ∧
            nul ∈ (trajG s sched n).kernel.revoked ∧
              Dregg2.Apps.CompartmentWorkflowMandate.cwmInCompartment (trajG s sched n).kernel comp :=
  cwm_safety_foreverG_via_contract s0 nul comp s hstep hpay hrev hcomp sched hsafe

example (s0 : RecChainedState) (nul : Nat) (comp : Int) (s : RecChainedState)
    (hstep : Dregg2.Apps.CompartmentWorkflowMandate.cwmWF s.kernel)
    (hpay : cellObsA s Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
            cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset)
    (hrev : nul ∈ s.kernel.revoked)
    (hcomp : Dregg2.Apps.CompartmentWorkflowMandate.cwmInCompartment s.kernel comp)
    (sched : SchedG) (hsafe : Dregg2.Apps.CompartmentWorkflowMandateGated.SchedAnchorSafe sched) :
    ∀ n,
      Dregg2.Apps.CompartmentWorkflowMandate.cwmWF (trajG s sched n).kernel ∧
        cellObsA (trajG s sched n) Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
          cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset ∧
            nul ∈ (trajG s sched n).kernel.revoked ∧
              Dregg2.Apps.CompartmentWorkflowMandate.cwmInCompartment (trajG s sched n).kernel comp :=
  Dregg2.Apps.CompartmentWorkflowMandateGated.cwm_safety_forever s0 nul comp s hstep hpay hrev hcomp sched hsafe

/-! ## §5e — StorageGatewayMandate: `sgm_safety_forever` on `trajG`. -/

theorem sgm_safety_foreverG_via_contract (s0 : RecChainedState) (nul : Nat) (bucket : Int)
    (s : RecChainedState)
    (hstep : Dregg2.Apps.StorageGatewayMandate.sgmWF s.kernel)
    (hpay : cellObsA s Dregg2.Apps.StorageGatewayMandate.payAsset = cellObsA s0 Dregg2.Apps.StorageGatewayMandate.payAsset)
    (hrev : nul ∈ s.kernel.revoked)
    (hbucket : Dregg2.Apps.StorageGatewayMandate.sgmInBucket s.kernel bucket) (sched : SchedG)
    (hsafe : Dregg2.Apps.StorageGatewayMandateGated.SchedAnchorSafe sched) :
    ∀ n,
      Dregg2.Apps.StorageGatewayMandate.sgmWF (trajG s sched n).kernel ∧
        cellObsA (trajG s sched n) Dregg2.Apps.StorageGatewayMandate.payAsset =
          cellObsA s0 Dregg2.Apps.StorageGatewayMandate.payAsset ∧
            nul ∈ (trajG s sched n).kernel.revoked ∧
              Dregg2.Apps.StorageGatewayMandate.sgmInBucket (trajG s sched n).kernel bucket :=
  Dregg2.Apps.StorageGatewayMandateGated.sgm_safety_forever s0 nul bucket s hstep hpay hrev hbucket sched hsafe

example (s0 : RecChainedState) (nul : Nat) (bucket : Int) (s : RecChainedState)
    (hstep : Dregg2.Apps.StorageGatewayMandate.sgmWF s.kernel)
    (hpay : cellObsA s Dregg2.Apps.StorageGatewayMandate.payAsset = cellObsA s0 Dregg2.Apps.StorageGatewayMandate.payAsset)
    (hrev : nul ∈ s.kernel.revoked)
    (hbucket : Dregg2.Apps.StorageGatewayMandate.sgmInBucket s.kernel bucket) (sched : SchedG)
    (hsafe : Dregg2.Apps.StorageGatewayMandateGated.SchedAnchorSafe sched) :
    ∀ n,
      Dregg2.Apps.StorageGatewayMandate.sgmWF (trajG s sched n).kernel ∧
        cellObsA (trajG s sched n) Dregg2.Apps.StorageGatewayMandate.payAsset =
          cellObsA s0 Dregg2.Apps.StorageGatewayMandate.payAsset ∧
            nul ∈ (trajG s sched n).kernel.revoked ∧
              Dregg2.Apps.StorageGatewayMandate.sgmInBucket (trajG s sched n).kernel bucket :=
  sgm_safety_foreverG_via_contract s0 nul bucket s hstep hpay hrev hbucket sched hsafe

/-! ## §5f — Cross-app composition: `agent_mandate_safety_forever` on `trajG`. -/

theorem agent_mandate_safety_foreverG_via_contract (s0 : RecChainedState) (nul : Nat) (comp bucket : Int)
    (s : RecChainedState)
    (hcwm : Dregg2.Apps.CompartmentWorkflowMandate.cwmWF s.kernel)
    (hcwmPay : cellObsA s Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
               cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset)
    (hcwmComp : Dregg2.Apps.CompartmentWorkflowMandate.cwmInCompartment s.kernel comp)
    (hsgm : Dregg2.Apps.StorageGatewayMandate.sgmWF s.kernel)
    (hsgmPay : cellObsA s Dregg2.Apps.StorageGatewayMandate.payAsset =
               cellObsA s0 Dregg2.Apps.StorageGatewayMandate.payAsset)
    (hsgmBucket : Dregg2.Apps.StorageGatewayMandate.sgmInBucket s.kernel bucket)
    (hrev : nul ∈ s.kernel.revoked) (sched : SchedG) (hsafe : DualSchedAnchorSafe sched) :
    ∀ n,
      Dregg2.Apps.CompartmentWorkflowMandate.cwmWF (trajG s sched n).kernel ∧
        cellObsA (trajG s sched n) Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
          cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset ∧
            nul ∈ (trajG s sched n).kernel.revoked ∧
              Dregg2.Apps.CompartmentWorkflowMandate.cwmInCompartment (trajG s sched n).kernel comp ∧
                Dregg2.Apps.StorageGatewayMandate.sgmWF (trajG s sched n).kernel ∧
                  Dregg2.Apps.StorageGatewayMandate.sgmInBucket (trajG s sched n).kernel bucket :=
  agent_mandate_safety_forever s0 nul comp bucket s hcwm hcwmPay hcwmComp hsgm hsgmPay hsgmBucket hrev sched hsafe

example (s0 : RecChainedState) (nul : Nat) (comp bucket : Int) (s : RecChainedState)
    (hcwm : Dregg2.Apps.CompartmentWorkflowMandate.cwmWF s.kernel)
    (hcwmPay : cellObsA s Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
               cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset)
    (hcwmComp : Dregg2.Apps.CompartmentWorkflowMandate.cwmInCompartment s.kernel comp)
    (hsgm : Dregg2.Apps.StorageGatewayMandate.sgmWF s.kernel)
    (hsgmPay : cellObsA s Dregg2.Apps.StorageGatewayMandate.payAsset =
               cellObsA s0 Dregg2.Apps.StorageGatewayMandate.payAsset)
    (hsgmBucket : Dregg2.Apps.StorageGatewayMandate.sgmInBucket s.kernel bucket)
    (hrev : nul ∈ s.kernel.revoked) (sched : SchedG) (hsafe : DualSchedAnchorSafe sched) :
    ∀ n,
      Dregg2.Apps.CompartmentWorkflowMandate.cwmWF (trajG s sched n).kernel ∧
        cellObsA (trajG s sched n) Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
          cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset ∧
            nul ∈ (trajG s sched n).kernel.revoked ∧
              Dregg2.Apps.CompartmentWorkflowMandate.cwmInCompartment (trajG s sched n).kernel comp ∧
                Dregg2.Apps.StorageGatewayMandate.sgmWF (trajG s sched n).kernel ∧
                  Dregg2.Apps.StorageGatewayMandate.sgmInBucket (trajG s sched n).kernel bucket :=
  agent_mandate_safety_foreverG_via_contract s0 nul comp bucket s hcwm hcwmPay hcwmComp hsgm hsgmPay
    hsgmBucket hrev sched hsafe

/-! ## §6 — Log monotonicity: tactics + contract on `trajG`. -/

theorem logMono_foreverG_via_tactics (s : RecChainedState) (sched : SchedG) :
    ∀ n, s.log.length ≤ (trajG s sched n).log.length :=
  Production.logMono_via_tactics s sched

example (s : RecChainedState) (sched : SchedG) :
    ∀ n, s.log.length ≤ (trajG s sched n).log.length :=
  logMono_foreverG_via_tactics s sched

example (s : RecChainedState) (sched : SchedG) :
    ∀ n, s.log.length ≤ (trajG s sched n).log.length :=
  (logAppendOnly s).forever (le_refl _) sched

example (s : RecChainedState) (sched : SchedG) :
    ∀ n, s.log.length ≤ (trajG s sched n).log.length :=
  log_mono_forever_production s sched

/-! ## §7 — Non-vacuity guards (production path). -/

#guard (Dregg2.Apps.Identity.fmaRevoked.kernel.revoked.contains 42)
#guard (Dregg2.Apps.Identity.fmaRevoked.kernel.revoked.contains 99 == false)
#guard ((execFullForestA fma0 Dregg2.Exec.spendCF).map
          (fun s' => s'.kernel.nullifiers.contains 77) == some true)
#guard (Dregg2.Apps.NameService.isRegistered fma0
          Dregg2.Apps.NameService.aliceName Dregg2.Apps.NameService.aliceOwner == false)
#guard (Dregg2.Apps.NameService.afterRegister.map
          (fun s => Dregg2.Apps.NameService.isRegistered s
            Dregg2.Apps.NameService.aliceName Dregg2.Apps.NameService.aliceOwner) == some true)
#guard (SafetyShape.membership == SafetyShape.membership)
#guard (SafetyShape.other == SafetyShape.other)

/-! ## §8 — Axiom hygiene. -/

#assert_axioms identity_revoked_foreverG_via_catalog
#assert_axioms identity_revoked_alwaysG_via_catalog
#assert_axioms spent_note_never_respentG_via_catalog
#assert_axioms no_double_spendG_via_contract
#assert_axioms commitments_persistG_via_contract
#assert_axioms nameservice_registration_foreverG_via_contract
#assert_axioms cx_pay_conserved_foreverG_via_contract
#assert_axioms cwm_pay_conserved_foreverG_via_contract
#assert_axioms cwm_safety_foreverG_via_contract
#assert_axioms sgm_safety_foreverG_via_contract
#assert_axioms agent_mandate_safety_foreverG_via_contract
#assert_axioms logMono_foreverG_via_tactics

end Dregg2.Verify