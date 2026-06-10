/-
# Dregg2.Apps.SubscriptionGated — the subscription app on the ONE gated executor: NO replay, NO skip.

The subscription protocol (starbridge-apps/subscription, dregg1's subscription cell-program) is a
replay-safe SEQUENCE automaton: a subscription head advances by EXACTLY ONE per consume step — never
replays an old sequence number, never skips ahead. That invariant is precisely the `MonotonicSequence`
slot caveat (`SlotCaveat.monotonicSeq`, `new == old + 1`), enforced by `stateStepGuarded` on every
`SetField` to the sequence slot.

This module models the consume step as a credential-gated `SetField` through the ONE production turn
entry (`FullForestAuth.execFullForestG`, the 4-leg gate). The end-user theorems are about the EXECUTED
turn: a forged credential is rejected; a +1 advance commits; a replay or skip is rejected by the
executor (not merely carried); the op conserves every asset.

## End-user theorems (general; concrete `#guard` witnesses for non-vacuity)
  1. `sub_forged_rejected`    — a forged credential ⇒ the whole gated turn rejects (`none`), ∀ state.
  2. `sub_nonsequential_rejected` — a write that is NOT `old+1` (replay OR skip) ⇒ `none` (Monotonic-
                                Sequence caveat fail-closes inside the gated executor), with a genuine credential.
  3. `sub_op_conserves`       — a committed consume moves NO asset's supply (per-asset Δ = 0).

Mirrors the green `NameserviceGated`/`IdentityGated` template.

## App-level semantics (Hatchery bridge — §4b)

Per-op teeth (forged/replay/skip rejection) are obligations; the production payoff is
`sub_pay_conserved_forever`: along `trajG` the payment-asset supply stays fixed (the
`assetConserved` Hatchery shape). F2b: the `subWF` living-cell capacity headline moved to the
FACTORY story (`Apps/QueueFactory.lean` relational-caveat keystones) with the kernel queue
side-table's deletion — the gated SetField path here (MonotonicSequence, no replay / no skip)
is exactly the factory-born consume verb.
-/
import Dregg2.Exec.GatedForestCfg
import Dregg2.Exec.CellExecutor
import Dregg2.Exec.CellReal
import Dregg2.Apps.Subscription
import Dregg2.Verify.Contract

namespace Dregg2.Apps.SubscriptionGated

open Dregg2.Exec
open Dregg2.Exec (cellObsA trajG SchedG)
open Dregg2.Verify (composeContracts assetConserved logAppendOnly)
open Dregg2.Verify.Production (Contract Sched)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.StarbridgeGated

/-- The subscription cell. Cell `0` so `actor = 0` self-authorizes — the gate's load-bearing leg is the
§8 credential, and the SEQUENCE invariant is the `MonotonicSequence` slot caveat. -/
abbrev subCell : CellId := 0
abbrev subActor : CellId := 0
/-- The sequence-head slot — carries `MonotonicSequence` (`new == old + 1`): no replay, no skip. -/
abbrev seqSlot : FieldName := "seq"

/-- The subscription cell's slot caveat: `MonotonicSequence { seq }`. -/
def subCaveats : List SlotCaveat := [ .monotonicSeq seqSlot ]

/-- A consume step: credential `cred`, a `SetField seq value` on the subscription cell, no children. -/
def subNode (cred : Authorization Dg Pf) (value : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA subActor subCell seqSlot value, [] ⟩

/-- **`execFullForestG_leaf`** (childless gated forest = its single gated node). -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

/-- **`execFullForestG_subNode` — the consume-step collapse.** -/
theorem execFullForestG_subNode (s : RecChainedState) (cred : Authorization Dg Pf) (value : Int) :
    execFullForestG s (subNode cred value)
      = (if gateOK (mkAuth cred []) s = true
         then stateStepGuarded s seqSlot subActor subCell value
         else none) := by
  rw [subNode, execFullForestG_leaf, execFullAGated]
  rfl

/-- **`gateOK_forged_false`** (forged credential ⇒ gate `false`, state-independent). -/
theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK
  rw [hcred]
  simp

/-- **`sub_forged_rejected` (THEOREM 1).** A forged credential ⇒ the consume rejects, ∀ state. -/
theorem sub_forged_rejected (s : RecChainedState) (value : Int) :
    execFullForestG s (subNode forgedCred value) = none := by
  rw [subNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.setFieldA subActor subCell seqSlot value) [] (gateOK_forged_false s)

/-- **`sub_good_runs_write` — the gate-passing collapse for `goodCred`.** -/
theorem sub_good_runs_write (s : RecChainedState) (value : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (subNode goodCred value)
      = stateStepGuarded s seqSlot subActor subCell value := by
  rw [execFullForestG_subNode, if_pos hgate]

/-- **`sub_nonsequential_rejected` (THEOREM 2).** A consume whose write is NOT the next
sequence number (`caveatsAdmit = false`: a REPLAY of an old seq, or a SKIP ahead) is rejected by the
executor — `execFullForestG s (subNode goodCred value) = none` — EVEN with a genuine credential. The
`MonotonicSequence seq` slot caveat fail-closes the write. No replay, no skip. -/
theorem sub_nonsequential_rejected (s : RecChainedState) (value : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hseq : caveatsAdmit s.kernel seqSlot subActor subCell value = false) :
    execFullForestG s (subNode goodCred value) = none := by
  rw [sub_good_runs_write s value hgate]
  exact stateStepGuarded_caveat_violation_fails s seqSlot subActor subCell value hseq

/-- The per-asset turn delta of a consume is `0` (a `SetField` is balance-neutral), every asset. -/
theorem subNode_delta_zero (cred : Authorization Dg Pf) (value : Int) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (subNode cred value)).map Prod.snd) b = 0 := by
  simp [subNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- **`sub_op_conserves` (THEOREM 3).** A committed consume preserves every asset's supply. -/
theorem sub_op_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (value : Int) (b : AssetId)
    (h : execFullForestG s (subNode cred value) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  execFullForestG_conserves_per_asset s s' (subNode cred value) b h (subNode_delta_zero cred value b)

/-! ## §4b — Hatchery bridge: payment-asset conservation forever on `trajG`.

(F2b: the `subWF` queue-capacity crown moved to the factory story with the kernel queue
side-table's deletion — `Apps/QueueFactory.lean`.) -/

/-- **`sub_pay_conserved_forever` — APP SEMANTICS (production crown).** Along EVERY adversarial
production schedule, the subscription cell's payment-asset supply stays fixed. -/
theorem sub_pay_conserved_forever (s0 : RecChainedState) (a : AssetId) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) a = cellObsA s0 a :=
  (assetConserved s0 a).forever rfl sched

/-! ## §4c — Composability: conservation ∩ log-monotonicity on `trajG`. -/

/-- **Per-asset conservation ∩ log append-only** — composed contract for a gated subscription cell:
the payment ledger stays fixed AND the audit log only grows. -/
noncomputable def subPayLogSafety (s0 : RecChainedState) (a : AssetId) : Contract :=
  composeContracts (assetConserved s0 a) (logAppendOnly s0)

/-- **`sub_pay_and_log_mono_forever` — COMPOSED PRODUCTION CROWN.** Fixed payment-asset supply AND a
monotone audit log, at every `trajG` index — one composed `.forever`, no hand carry proof. -/
theorem sub_pay_and_log_mono_forever (s0 : RecChainedState) (a : AssetId) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) a = cellObsA s0 a ∧
         s0.log.length ≤ (trajG s0 sched n).log.length :=
  (subPayLogSafety s0 a).forever (And.intro rfl (le_refl s0.log.length)) sched

/-! ## Non-vacuity: a concrete subscription-cell state (seq currently = 5) + `#guard` witnesses. -/

/-- A subscription cell with `MonotonicSequence seq`, the head currently at `5`. -/
def sub0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 0), (seqSlot, .int 5)]
                         else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        slotCaveats := fun c => if c = 0 then subCaveats else [] }
    log := [] }

#guard (gateOK (mkAuth goodCred []) sub0)                                  --  true (genuine credential)
-- the next sequence number (6 = 5+1) is admitted and the consume COMMITS:
#guard (caveatsAdmit sub0.kernel seqSlot subActor subCell 6)               --  true (old+1)
#guard ((execFullForestG sub0 (subNode goodCred 6)).isSome)                --  true (consume commits)
-- a REPLAY (write the SAME seq 5) is rejected (5 ≠ 5+1):
#guard (caveatsAdmit sub0.kernel seqSlot subActor subCell 5) == false      --  false (replay)
#guard ((execFullForestG sub0 (subNode goodCred 5)).isSome) == false       --  false (no replay)
-- a SKIP (write 7, skipping 6) is rejected (7 ≠ 5+1):
#guard (caveatsAdmit sub0.kernel seqSlot subActor subCell 7) == false      --  false (skip)
#guard ((execFullForestG sub0 (subNode goodCred 7)).isSome) == false       --  false (no skip)
-- a FORGED credential ⇒ none even for the valid next seq:
#guard ((execFullForestG sub0 (subNode forgedCred 6)).isSome) == false     --  false (forged)
-- the committed consume CONSERVES both assets:
#guard ((execFullForestG sub0 (subNode goodCred 6)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  (105, 7)

#assert_axioms execFullForestG_leaf
#assert_axioms execFullForestG_subNode
#assert_axioms gateOK_forged_false
#assert_axioms sub_forged_rejected
#assert_axioms sub_nonsequential_rejected
#assert_axioms subNode_delta_zero
#assert_axioms sub_op_conserves
#assert_axioms sub_pay_conserved_forever
#assert_axioms subPayLogSafety
#assert_axioms sub_pay_and_log_mono_forever

end Dregg2.Apps.SubscriptionGated
