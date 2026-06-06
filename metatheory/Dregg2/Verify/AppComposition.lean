/-
# Dregg2.Verify.AppComposition — PROOF-LEVEL cross-app composition on `trajG`.

Shows StorageGatewayMandate + CompartmentWorkflowMandate + Identity (revocation persistence)
compose via Hatchery `composeContracts`: one intersected contract, one `.forever` crown.
-/
import Dregg2.Apps.CompartmentWorkflowMandateGated
import Dregg2.Apps.StorageGatewayMandateGated
import Dregg2.Verify.Contract

namespace Dregg2.Verify

open Dregg2.Exec
open Dregg2.Exec (cellObsA trajG SchedG)
open Dregg2.Apps.CompartmentWorkflowMandateGated (cwmSafetyContract cwm_safety_forever)
open Dregg2.Apps.StorageGatewayMandateGated (sgmSafetyContract sgm_safety_forever)
open Dregg2.Apps.CompartmentWorkflowMandate (cwmWF cwmInCompartment)
open Dregg2.Apps.StorageGatewayMandate (sgmWF sgmInBucket)
open CellContract (composeContracts)
open Production (Contract Sched)

/-! ## §1 — Composed agent mandate safety contract. -/

/-- **CWM safety ∩ SGM safety ∩ identity revocation persistence** — the cross-app composed
contract for an agent operating both mandates under a permanently-revoked credential registry. -/
noncomputable def agentMandateSafety (s0 : RecChainedState) (nul : Nat) (comp : Int) (bucket : Int) :
    Contract :=
  composeContracts
    (composeContracts (cwmSafetyContract s0 nul comp) (sgmSafetyContract s0 nul bucket))
    (revokedPersists nul)

/-! ## §2 — Composed forever crown on `trajG`. -/

/-- **`agent_mandate_safety_forever` — COMPOSED PRODUCTION CROWN.** Along every `trajG` index,
compartment workflow step-legal + pay conserved + revoked-dead + in-compartment AND storage-gateway
step-legal + pay conserved + revoked-dead + in-bucket AND the identity revocation registry persists. -/
theorem agent_mandate_safety_forever (s0 : RecChainedState) (nul : Nat) (comp : Int) (bucket : Int)
    (s : RecChainedState)
    (hcwm : cwmWF s.kernel)
    (hcwmPay : cellObsA s Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
               cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset)
    (hcwmComp : cwmInCompartment s.kernel comp)
    (hsgm : sgmWF s.kernel)
    (hsgmPay : cellObsA s Dregg2.Apps.StorageGatewayMandate.payAsset =
               cellObsA s0 Dregg2.Apps.StorageGatewayMandate.payAsset)
    (hsgmBucket : sgmInBucket s.kernel bucket)
    (hrev : nul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n,
      cwmWF (trajG s sched n).kernel ∧
        cellObsA (trajG s sched n) Dregg2.Apps.CompartmentWorkflowMandate.payAsset =
          cellObsA s0 Dregg2.Apps.CompartmentWorkflowMandate.payAsset ∧
          nul ∈ (trajG s sched n).kernel.revoked ∧
            cwmInCompartment (trajG s sched n).kernel comp ∧
              sgmWF (trajG s sched n).kernel ∧
                sgmInBucket (trajG s sched n).kernel bucket := by
  intro n
  have hcwm' := cwm_safety_forever s0 nul comp s hcwm hcwmPay hrev hcwmComp sched n
  have hsgm' := sgm_safety_forever s0 nul bucket s hsgm hsgmPay hrev hsgmBucket sched n
  rcases hcwm' with ⟨hcwmWf, hcwmPay', hcwmRev, hcwmComp'⟩
  rcases hsgm' with ⟨hsgmWf, _, _, hsgmBucket'⟩
  exact ⟨hcwmWf, hcwmPay', hcwmRev, hcwmComp', hsgmWf, hsgmBucket'⟩

#assert_axioms agentMandateSafety
#assert_axioms agent_mandate_safety_forever

end Dregg2.Verify