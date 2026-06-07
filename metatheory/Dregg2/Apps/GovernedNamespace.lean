/-
# Dregg2.Apps.GovernedNamespace — governed namespace as a verified cell-program (constitutional slot caveats).

`starbridge-apps/governed-namespace/src/lib.rs` is a governance-bound atomic route-table swap on a
sovereign cell: committee threshold signatures gate who may write, and per-slot caveats enforce the
constitution on every `SetField`. This module is the **ungated cell-program dual** of
`GovernedNamespaceGated` — the SAME domain ops run through the shipped credential-blind executor
`execFullForestA`, with load-bearing guarantees enforced by `stateStepGuarded` reading the cell's
factory-installed `slotCaveats`.

Headline guarantees (kernel-native, no §8 credential leg):

  * **CONSTITUTIONAL CAVEATS** — committee root and threshold are `Immutable`; version is
    `MonotonicSequence` (+1 only); dispute window is `Monotonic` (no shrink). Violations fail-closed.
  * **CONSERVATION** — every committed governed write is balance-neutral (`SetField` Δ = 0).
  * **NON-VACUITY** — concrete `gn0` state with `#guard` witnesses mirroring the gated app.

Templates: `Apps/GovernedNamespaceGated.lean` (domain + caveats), `Apps/NameService.lean` (cell-program
shape).
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.FullForest

namespace Dregg2.Apps.GovernedNamespace

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState (stateStepGuarded caveatsAdmit fieldOf
  stateStepGuarded_caveat_violation_fails)

/-! ## §1 — The governed-namespace DOMAIN (cell, slots, constitutional caveats). -/

abbrev nsCell : CellId := 0
abbrev nsActor : CellId := 0

abbrev routeTableRootSlot : FieldName := "route_table_root"
abbrev versionSlot : FieldName := "version"
abbrev committeeRootSlot : FieldName := "governance_committee_root"
abbrev thresholdSlot : FieldName := "threshold"
abbrev disputeWindowSlot : FieldName := "dispute_window_height"
abbrev pendingProposalSlot : FieldName := "pending_proposal_root"

def nsCaveats : List SlotCaveat :=
  [ .immutable committeeRootSlot, .immutable thresholdSlot,
    .monotonicSeq versionSlot, .monotonic disputeWindowSlot ]

/-! ## §2 — Governed ops as REAL executor turns (`setFieldA` through `execFullForestA`). -/

def gnOp (slot : FieldName) (value : Int) : FullForestA :=
  ⟨ .setFieldA nsActor nsCell slot value, [] ⟩

def commitRoot (newRoot : Int) : FullForestA :=
  gnOp routeTableRootSlot newRoot

def versionBump (newVersion : Int) : FullForestA :=
  gnOp versionSlot newVersion

def disputeWindowBump (newHeight : Int) : FullForestA :=
  gnOp disputeWindowSlot newHeight

def amendCommittee (newRoot : Int) : FullForestA :=
  gnOp committeeRootSlot newRoot

def amendThreshold (newThreshold : Int) : FullForestA :=
  gnOp thresholdSlot newThreshold

/-! ## §3 — Constitutional caveat teeth (executor-enforced, credential-blind). -/

theorem gn_committee_immutable (s : RecChainedState) (newRoot : Int)
    (hfix : caveatsAdmit s.kernel committeeRootSlot nsActor nsCell newRoot = false) :
    execFullForestA s (amendCommittee newRoot) = none := by
  have hnone := stateStepGuarded_caveat_violation_fails s committeeRootSlot nsActor nsCell newRoot hfix
  rw [execFullForestA_eq_execFullTurnA]
  simp only [amendCommittee, gnOp, lowerForestA, lowerChildrenA, execFullTurnA, execFullA, hnone]

theorem gn_threshold_immutable (s : RecChainedState) (newThreshold : Int)
    (hfix : caveatsAdmit s.kernel thresholdSlot nsActor nsCell newThreshold = false) :
    execFullForestA s (amendThreshold newThreshold) = none := by
  have hnone := stateStepGuarded_caveat_violation_fails s thresholdSlot nsActor nsCell newThreshold hfix
  rw [execFullForestA_eq_execFullTurnA]
  simp only [amendThreshold, gnOp, lowerForestA, lowerChildrenA, execFullTurnA, execFullA, hnone]

theorem gn_version_monotonic_seq (s : RecChainedState) (newVersion : Int)
    (hseq : caveatsAdmit s.kernel versionSlot nsActor nsCell newVersion = false) :
    execFullForestA s (versionBump newVersion) = none := by
  have hnone := stateStepGuarded_caveat_violation_fails s versionSlot nsActor nsCell newVersion hseq
  rw [execFullForestA_eq_execFullTurnA]
  simp only [versionBump, gnOp, lowerForestA, lowerChildrenA, execFullTurnA, execFullA, hnone]

theorem gn_dispute_window_cannot_shrink (s : RecChainedState) (newHeight : Int)
    (hback : caveatsAdmit s.kernel disputeWindowSlot nsActor nsCell newHeight = false) :
    execFullForestA s (disputeWindowBump newHeight) = none := by
  have hnone := stateStepGuarded_caveat_violation_fails s disputeWindowSlot nsActor nsCell newHeight hback
  rw [execFullForestA_eq_execFullTurnA]
  simp only [disputeWindowBump, gnOp, lowerForestA, lowerChildrenA, execFullTurnA, execFullA, hnone]

/-! ## §4 — Conservation (governance is balance-orthogonal). -/

theorem gnOp_delta_zero (slot : FieldName) (value : Int) (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (gnOp slot value)) b = 0 := by
  simp [gnOp, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem gn_commit_conserves (s s' : RecChainedState) (newRoot : Int) (b : AssetId)
    (h : execFullForestA s (commitRoot newRoot) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestA_conserves_per_asset s s' (commitRoot newRoot) b h
    (gnOp_delta_zero routeTableRootSlot newRoot b)

theorem gn_op_conserves (s s' : RecChainedState) (slot : FieldName) (value : Int) (b : AssetId)
    (h : execFullForestA s (gnOp slot value) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestA_conserves_per_asset s s' (gnOp slot value) b h
    (gnOp_delta_zero slot value b)

/-! ## §5 — NON-VACUITY: `gn0` + `#guard` witnesses (mirrors `GovernedNamespaceGated.gn0`). -/

def gn0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then
                  .record [("balance", .int 0), (routeTableRootSlot, .int 111),
                           (versionSlot, .int 7), (committeeRootSlot, .int 555),
                           (thresholdSlot, .int 3), (disputeWindowSlot, .int 1000),
                           (pendingProposalSlot, .int 0)]
                else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        slotCaveats := fun c => if c = 0 then nsCaveats else [] }
    log := [] }

#guard ((execFullForestA gn0 (commitRoot 222)).isSome)               --  true
#guard ((execFullForestA gn0 (commitRoot 222)).map
        (fun s => fieldOf routeTableRootSlot (s.kernel.cell 0))) == some 222  --  some 222

#guard (caveatsAdmit gn0.kernel committeeRootSlot nsActor nsCell 999) == false  --  false
#guard ((execFullForestA gn0 (amendCommittee 999)).isSome) == false             --  false

#guard (caveatsAdmit gn0.kernel thresholdSlot nsActor nsCell 1) == false        --  false
#guard ((execFullForestA gn0 (amendThreshold 1)).isSome) == false                --  false

#guard (caveatsAdmit gn0.kernel versionSlot nsActor nsCell 7) == false           --  false (replay)
#guard (caveatsAdmit gn0.kernel versionSlot nsActor nsCell 9) == false           --  false (skip)
#guard (caveatsAdmit gn0.kernel versionSlot nsActor nsCell 8)                    --  true  (+1)
#guard ((execFullForestA gn0 (versionBump 7)).isSome) == false                   --  false
#guard ((execFullForestA gn0 (versionBump 9)).isSome) == false                   --  false
#guard ((execFullForestA gn0 (versionBump 8)).isSome)                          --  true

#guard (caveatsAdmit gn0.kernel disputeWindowSlot nsActor nsCell 500) == false   --  false
#guard ((execFullForestA gn0 (disputeWindowBump 500)).isSome) == false           --  false
#guard (caveatsAdmit gn0.kernel disputeWindowSlot nsActor nsCell 2000)          --  true
#guard ((execFullForestA gn0 (disputeWindowBump 2000)).isSome)                  --  true

#guard ((execFullForestA gn0 (commitRoot 222)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

/-! ## §6 — Axiom-hygiene pins. -/

#assert_axioms gn_committee_immutable
#assert_axioms gn_threshold_immutable
#assert_axioms gn_version_monotonic_seq
#assert_axioms gn_dispute_window_cannot_shrink
#assert_axioms gnOp_delta_zero
#assert_axioms gn_commit_conserves
#assert_axioms gn_op_conserves

end Dregg2.Apps.GovernedNamespace