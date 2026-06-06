/-
# Dregg2.Apps.ComputeExchange — compute market as a verified cell-program (escrow order/settle/refund).

`apps/compute-exchange/` and `starbridge-apps/compute-exchange/` model a buyer/provider compute job
market: the buyer escrows payment, the provider is paid on delivery, or the buyer is refunded on failure.
Each step is a single escrow `FullActionA` on the REAL `RecordKernelState`, composed through
`execFullForestA`.

This is the ungated cell-program dual of `ComputeExchangeGated`. Load-bearing guarantees:

  * **CONSERVATION** — order/settle/refund preserve `recTotalAssetWithEscrow` per asset.
  * **LIVENESS (D3)** — settle to a non-live provider fail-closes.
  * **AUTHORITY (honest scope)** — self-authorized escrow ops (`actor = buyer`).

Templates: `Apps/BountyBoard.lean`, `Apps/ComputeExchangeGated.lean`. Zero `sorry`/`admit`/`axiom`.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.FullForest

namespace Dregg2.Apps.ComputeExchange

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest

abbrev JobId := Nat

abbrev buyer : CellId := 0
abbrev provider : CellId := 1
abbrev payAsset : AssetId := 0
abbrev jobId : JobId := 42

def hasOpenJob (s : RecChainedState) (id : JobId) : Bool :=
  match s.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some _ => true
  | none   => false

def cxOrder (amount : Int) : FullForestA :=
  ⟨ .createEscrowA jobId buyer buyer provider payAsset amount, [] ⟩

def cxSettle : FullForestA :=
  ⟨ .releaseEscrowA jobId buyer, [] ⟩

def cxRefund : FullForestA :=
  ⟨ .refundEscrowA jobId buyer, [] ⟩

theorem cxOrder_delta_zero {amount : Int} (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (cxOrder amount)) b = 0 := by
  simp [cxOrder, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem cxSettle_delta_zero (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA cxSettle) b = 0 := by
  simp [cxSettle, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem cxRefund_delta_zero (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA cxRefund) b = 0 := by
  simp [cxRefund, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem cx_order_conserves {s s' : RecChainedState} {amount : Int} (b : AssetId)
    (h : execFullForestA s (cxOrder amount) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestA_conserves_per_asset s s' (cxOrder amount) b h (cxOrder_delta_zero (amount:=amount) b)

theorem cx_settle_conserves {s s' : RecChainedState} (b : AssetId)
    (h : execFullForestA s cxSettle = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestA_conserves_per_asset s s' cxSettle b h (cxSettle_delta_zero b)

theorem cx_refund_conserves {s s' : RecChainedState} (b : AssetId)
    (h : execFullForestA s cxRefund = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestA_conserves_per_asset s s' cxRefund b h (cxRefund_delta_zero b)

theorem cx_settle_requires_live_provider (s : RecChainedState) {r : EscrowRecord}
    (hfind : s.kernel.escrows.find? (fun r => decide (r.id = jobId ∧ r.resolved = false)) = some r)
    (hdead : cellLifecycleLive s.kernel r.recipient = false) :
    execFullForestA s cxSettle = none := by
  have hchain : releaseEscrowChainA s jobId buyer = none := by
    unfold releaseEscrowChainA
    rw [releaseEscrowKAsset_nonlive_fails hfind hdead]
  rw [execFullForestA_eq_execFullTurnA]
  simp only [cxSettle, lowerForestA, lowerChildrenA, execFullTurnA, execFullA, hchain]

def mkt0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

abbrev payAmt : Int := 40

def mktOrdered : Option RecChainedState :=
  execFullForestA mkt0 (cxOrder payAmt)

#guard (mktOrdered.isSome)  --  true
#guard (mktOrdered.map (fun s => s.kernel.bal buyer payAsset)) == some 60  --  some 60
#guard (mktOrdered.map (fun s => hasOpenJob s jobId)) == some true  --  some true
#guard (mktOrdered.map (fun s => (recTotalAssetWithEscrow s.kernel 0,
                                 recTotalAssetWithEscrow s.kernel 1)))
      == some (105, 7)  --  some (105, 7)

#guard ((mktOrdered.bind (fun s => execFullForestA s cxSettle)).map
        (fun s => s.kernel.bal provider payAsset)) == some 45  --  some 45

#guard ((mktOrdered.bind (fun s => execFullForestA s cxRefund)).map
        (fun s => s.kernel.bal buyer payAsset)) == some 100  --  some 100

#assert_axioms cxOrder_delta_zero
#assert_axioms cxSettle_delta_zero
#assert_axioms cxRefund_delta_zero
#assert_axioms cx_order_conserves
#assert_axioms cx_settle_conserves
#assert_axioms cx_refund_conserves
#assert_axioms cx_settle_requires_live_provider

end Dregg2.Apps.ComputeExchange