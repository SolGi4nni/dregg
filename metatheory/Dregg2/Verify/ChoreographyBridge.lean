/-
# Dregg2.Verify.ChoreographyBridge — blue/red choreography ↔ Hatchery contracts.

* **Blue** (I-confluent) interactions commit per-cell; their invariants are `CellContract.forever`
  safety crowns (`Spec.Choreography.blue_needs_no_hyperedge`).
* **Red** (coupled) interactions project to `Hyperedge` atomic commits
  (`Spec.Choreography.red_projects_to_hyperedge`).
-/
import Dregg2.Verify.Contract
import Dregg2.Spec.Choreography

namespace Dregg2.Verify

open Dregg2.Spec
open Dregg2.Exec
open Production

/-- Blue choreography safety on production trajectories — the identity revocation instance. -/
theorem identity_blue_forever (s : RecChainedState) (h : 42 ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, 42 ∈ (trajG s sched n).kernel.revoked :=
  (revokedPersists 42).forever h sched

#assert_axioms identity_blue_forever

end Dregg2.Verify