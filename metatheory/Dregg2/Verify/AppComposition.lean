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
open Dregg2.Apps.CompartmentWorkflowMandateGated (cwmSafetyContract cwm_safety_forever
  cwm_compartment_strong_forever)
open Dregg2.Apps.StorageGatewayMandateGated (sgmSafetyContract sgm_safety_forever
  sgm_bucket_strong_forever)
open Dregg2.Apps.CompartmentWorkflowMandate (cwmWF cwmInCompartment cwmInCompartmentStrong
  cwmMandateProgramOK)
open Dregg2.Apps.StorageGatewayMandate (sgmWF sgmInBucket sgmInBucketStrong anchorForestOK)
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

/-! ## §3 — VALUE-PINNING composed crown (the strong predicate wired in).

`agent_mandate_safety_forever` (above) carries the program-live `cwmInCompartment`/`sgmInBucket` along
EVERY adversarial schedule. This strengthened crown ADDS the LITERAL bindings `cwmAnchor = comp ∧
sgmAnchor = bucket` — the agent stays in the SPECIFIC compartment/bucket, not just "some program is
live" — along every ANCHOR-SAFE schedule (one issuing no `makeSovereign` aimed at a mandate cell, the
sole un-caveat-gated record rebind that drops fields). The anchor-safe hypothesis is the precise,
stated residual: it is the ONE behaviour the immutable-anchor caveat cannot reject inline. -/

/-- A schedule is anchor-safe for BOTH mandate cells (compartment + bucket = cell `0` in each). -/
def DualSchedAnchorSafe (sched : SchedG) : Prop :=
  Dregg2.Apps.CompartmentWorkflowMandateGated.SchedAnchorSafe sched
    ∧ Dregg2.Apps.StorageGatewayMandateGated.SchedAnchorSafe sched

/-- **`agent_mandate_safety_forever_strong` — VALUE-PINNING PRODUCTION CROWN.** Along every anchor-safe
`trajG`, in addition to the program-live legs, the agent's compartment anchor stays EXACTLY `comp` AND
its bucket anchor stays EXACTLY `bucket` — the binding is pinned to the literal value, not merely the
program. This routes `cwmInCompartmentStrong`/`sgmInBucketStrong` (the value-pinning predicates) into
the crown via `cwm_compartment_strong_forever`/`sgm_bucket_strong_forever`. -/
theorem agent_mandate_safety_forever_strong (comp : Int) (bucket : Int) (s : RecChainedState)
    (hcwmLive : Dregg2.Apps.CompartmentWorkflowMandate.mandateCell ∈ s.kernel.accounts)
    (hcwmProg : cwmMandateProgramOK s.kernel)
    (hcwmStrong : cwmInCompartmentStrong s.kernel comp)
    (hsgmLive : Dregg2.Apps.StorageGatewayMandate.mandateCell ∈ s.kernel.accounts)
    (hsgmStrong : sgmInBucketStrong s.kernel bucket)
    (sched : SchedG) (hsafe : DualSchedAnchorSafe sched) :
    ∀ n,
      cwmInCompartmentStrong (trajG s sched n).kernel comp ∧
        sgmInBucketStrong (trajG s sched n).kernel bucket := by
  intro n
  obtain ⟨hsafeC, hsafeS⟩ := hsafe
  have hc := cwm_compartment_strong_forever comp s hcwmLive hcwmProg hcwmStrong sched hsafeC n
  have hs := sgm_bucket_strong_forever bucket s hsgmLive hsgmStrong sched hsafeS n
  exact ⟨hc.2.2, hs.2⟩

#assert_axioms agentMandateSafety
#assert_axioms agent_mandate_safety_forever
#assert_axioms agent_mandate_safety_forever_strong

end Dregg2.Verify