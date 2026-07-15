/-
# Market.FhEggLedgerBinding — the fhEgg `(p*, V*)` output lowered to the exact ledger ring.

`FhEggClearing` proves that the histogram fold selects the volume-maximising price `p*` and
matched volume `V*`, but its aggregate `clearedBatch` lived only in the rational `Fill` model.
This module gives that output concrete executor content.  For a positive integral clearing it
builds the canonical bilateral `MatchNode` cycle:

* the buyer offers `V*p` units of numeraire and wants `V` units of base;
* the seller offers `V` units of base and wants `V*p` units of numeraire.

The nodes are a genuine `CycleValid` cycle, and `settlementsOf` lowers that exact list to the two
self-authorised balance movements which commit through `settleRing`.  Thus the `DrexClearing`
constructed here does not merely share `(p,V)` with fhEgg: its executed `nodes` are definitionally
the allocation derived from those values.

This is a specification-level content theorem.  Binding a deployed encrypted/MPC output proof to
this constructor remains the cryptographic source-refinement/API routing obligation; it is not
silently assumed here.
-/
import Market.FhEggClearing
import Market.CrossChainSettlement
import Dregg2.Tactics

namespace Market

open Dregg2.Exec
open Dregg2.Intent.Ring

set_option autoImplicit false

/-! ## 1. The exact bilateral allocation selected by `(p,V)`. -/

/-- Canonical buyer cell used by the aggregate bilateral lowering. -/
def fhEggBuyer : CellId := 1

/-- Canonical seller cell used by the aggregate bilateral lowering. -/
def fhEggSeller : CellId := 2

/-- The base asset bought by bids and sold by asks. -/
def fhEggBaseAsset : AssetId := 0

/-- The numeraire in which the clearing bucket is quoted. -/
def fhEggNumeraireAsset : AssetId := 1

/-- **The exact `MatchNode` allocation of an integral uniform-price output `(p,V)`.**
Node zero is the aggregate buyer and node one the aggregate seller.  Both offers are tight, so the
two fields consumed by `settlementsOf` are exactly `V*p` numeraire and `V` base. -/
def fhEggMatchNodes (p : Nat) (V : Int) : List MatchNode :=
  [ { creator := fhEggBuyer
      offerAsset := fhEggNumeraireAsset
      offerAmount := V * p
      wantAsset := fhEggBaseAsset
      wantMin := V },
    { creator := fhEggSeller
      offerAsset := fhEggBaseAsset
      offerAmount := V
      wantAsset := fhEggNumeraireAsset
      wantMin := V * p } ]

/-- The fhEgg allocation is a genuine two-party matching cycle whenever price and volume are
positive.  The edge amounts are equal, not merely bounded. -/
theorem fhEggMatchNodes_valid (p : Nat) (V : Int) (_hp : 0 < p) (_hV : 0 < V) :
    CycleValid (fhEggMatchNodes p V) where
  len := by simp [fhEggMatchNodes]
  edges := by
    intro k hk
    have hk2 : k < 2 := by simpa [fhEggMatchNodes] using hk
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl <;>
      simp [fhEggMatchNodes, isCompatible, fhEggBuyer, fhEggSeller,
        fhEggBaseAsset, fhEggNumeraireAsset]
  distinct := by
    intro i j hi hj hij
    have hi2 : i < 2 := by simpa [fhEggMatchNodes] using hi
    have hj2 : j < 2 := by simpa [fhEggMatchNodes] using hj
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
      simp_all [fhEggMatchNodes, fhEggBuyer, fhEggSeller]

/-- Both declared receive minima of the exact allocation are positive. -/
theorem fhEggMatchNodes_wantPos (p : Nat) (V : Int) (hp : 0 < p) (hV : 0 < V) :
    ∀ n ∈ fhEggMatchNodes p V, 0 < n.wantMin := by
  intro n hn
  simp only [fhEggMatchNodes, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact hV
  · exact mul_pos hV (by exact_mod_cast hp)

/-! ## 2. The exact allocation executes through `settleRing`. -/

/-- The funded pre-state for the aggregate bilateral allocation.  The buyer owns exactly `V*p`
numeraire and the seller exactly `V` base; self-authorisation (`actor = src`) makes the authority
gate explicit and no capability is fabricated. -/
def fhEggSettlePre (p : Nat) (V : Int) : RecordKernelState where
  accounts := {fhEggBuyer, fhEggSeller}
  cell := fun c =>
    if c ∈ ({fhEggBuyer, fhEggSeller} : Finset CellId) then
      Value.record [("balance", Value.int 0)]
    else default
  caps := fun _ => []
  bal := fun c a =>
    if c = fhEggBuyer ∧ a = fhEggNumeraireAsset then V * p
    else if c = fhEggSeller ∧ a = fhEggBaseAsset then V
    else 0

/-- The first exact settlement leg: buyer pays `V*p` numeraire to the seller. -/
def fhEggPayTurn (p : Nat) (V : Int) : Turn :=
  { actor := fhEggBuyer, src := fhEggBuyer, dst := fhEggSeller, amt := V * p }

/-- The intermediate kernel after the buyer's numeraire payment. -/
def fhEggSettleMid (p : Nat) (V : Int) : RecordKernelState :=
  { fhEggSettlePre p V with
    bal := recTransferBal (fhEggSettlePre p V).bal fhEggBuyer fhEggSeller
      fhEggNumeraireAsset (V * p) }

/-- The second exact settlement leg: seller delivers `V` base to the buyer. -/
def fhEggDeliverTurn (V : Int) : Turn :=
  { actor := fhEggSeller, src := fhEggSeller, dst := fhEggBuyer, amt := V }

/-- The final kernel after both exact fhEgg allocation legs. -/
def fhEggSettlePost (p : Nat) (V : Int) : RecordKernelState :=
  { fhEggSettleMid p V with
    bal := recTransferBal (fhEggSettleMid p V).bal fhEggSeller fhEggBuyer
      fhEggBaseAsset V }

/-- The generated node list lowers to exactly the two intended turns/assets. -/
theorem fhEggMatchNodes_settlements (p : Nat) (V : Int) :
    settlementsOf (fhEggMatchNodes p V) =
      [ { actor := fhEggBuyer, from_ := fhEggBuyer, to_ := fhEggSeller,
          asset := fhEggNumeraireAsset, amount := V * p },
        { actor := fhEggSeller, from_ := fhEggSeller, to_ := fhEggBuyer,
          asset := fhEggBaseAsset, amount := V } ] := by
  simp [settlementsOf, fhEggMatchNodes, MatchNode.toRingNode, chainedRing_two,
    fhEggBuyer, fhEggSeller, fhEggBaseAsset, fhEggNumeraireAsset]

/-- **The exact fhEgg allocation SETTLES through the verified executor.**  This is the content
bridge absent from the previous ledger: the `MatchNode` list derived from `(p,V)` is the very list
fed to `settleRing`, and its two transfers commit. -/
theorem fhEggMatchNodes_settle (p : Nat) (V : Int) (hp : 0 < p) (hV : 0 < V) :
    settleRing (fhEggSettlePre p V) (settlementsOf (fhEggMatchNodes p V)) =
      some (fhEggSettlePost p V) := by
  rw [fhEggMatchNodes_settlements]
  simp only [settleRing_cons, settleRing_nil, RingLeg.toTurn]
  have hpI : (0 : Int) < p := by exact_mod_cast hp
  have hVp : 0 ≤ V * (p : Int) := le_of_lt (mul_pos hV hpI)
  have hpay : recKExecAsset (fhEggSettlePre p V) (fhEggPayTurn p V)
      fhEggNumeraireAsset = some (fhEggSettleMid p V) := by
    simp [recKExecAsset, fhEggPayTurn, fhEggSettlePre, fhEggSettleMid,
      authorizedB, cellLifecycleLive, fhEggBuyer, fhEggSeller,
      fhEggBaseAsset, fhEggNumeraireAsset, hVp]
  have hdeliver : recKExecAsset (fhEggSettleMid p V) (fhEggDeliverTurn V)
      fhEggBaseAsset = some (fhEggSettlePost p V) := by
    simp [recKExecAsset, fhEggDeliverTurn, fhEggSettlePre, fhEggSettleMid,
      fhEggSettlePost, recTransferBal, authorizedB, cellLifecycleLive,
      fhEggBuyer, fhEggSeller, fhEggBaseAsset, fhEggNumeraireAsset, le_of_lt hV]
  change (recKExecAsset (fhEggSettlePre p V) (fhEggPayTurn p V)
      fhEggNumeraireAsset).bind (fun mid =>
        (recKExecAsset mid (fhEggDeliverTurn V) fhEggBaseAsset).bind fun out => some out) =
      some (fhEggSettlePost p V)
  simp [hpay, hdeliver]

/-! ## 3. The fhEgg book/output content theorem. -/

/-- The proof-carrying ledger clearing whose content is definitionally the fhEgg output `(p,V)`. -/
def fhEggDrexClearing (bk : OrderBook) (K : Nat)
    (hp : 0 < crossing bk K) (hV : 0 < clearedVolume bk K) : DrexClearing where
  pre := fhEggSettlePre (crossing bk K) (clearedVolume bk K)
  post := fhEggSettlePost (crossing bk K) (clearedVolume bk K)
  nodes := fhEggMatchNodes (crossing bk K) (clearedVolume bk K)
  valid := fhEggMatchNodes_valid _ _ hp hV
  wantPos := fhEggMatchNodes_wantPos _ _ hp hV
  settled := fhEggMatchNodes_settle _ _ hp hV

/-- **`fhEgg_output_executes_exact_drex_clearing` — the fhEgg→ledger CONTENT theorem.**
For every positive integral fhEgg output, there is a `DrexClearing` whose executed node list is
exactly `fhEggMatchNodes p* V*`; its buyer/seller receive minima expose precisely `V*` and `V*·p*`.
The `DrexClearing.settled` field is therefore a proof about this exact allocation, not merely a
post-state with the same aggregate totals. -/
theorem fhEgg_output_executes_exact_drex_clearing (bk : OrderBook) (K : Nat)
    (hp : 0 < crossing bk K) (hV : 0 < clearedVolume bk K) :
    ∃ c : DrexClearing,
      c.nodes = fhEggMatchNodes (crossing bk K) (clearedVolume bk K) ∧
      (c.nodes.getD 0 default).wantMin = clearedVolume bk K ∧
      (c.nodes.getD 1 default).wantMin = clearedVolume bk K * crossing bk K ∧
      settleRing c.pre (settlementsOf c.nodes) = some c.post := by
  refine ⟨fhEggDrexClearing bk K hp hV, rfl, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact (fhEggDrexClearing bk K hp hV).settled

/-- The exact remaining deployed source/API obligation.  `runEncrypted` is the cryptographically
verified fhEgg output path and `routeLedger` is the production participant/allocation router.  A
successful output must be the Lean `(crossing,clearedVolume)`, and every positive output must route to
the exact node list constructed here.  No implementation is installed by this definition. -/
def FhEggLedgerSourceBinding
    (runEncrypted : OrderBook → Nat → Option (Nat × Int))
    (routeLedger : Nat → Int → List MatchNode) : Prop :=
  ∀ bk K p V, runEncrypted bk K = some (p, V) →
    p = crossing bk K ∧ V = clearedVolume bk K ∧
      (0 < V → routeLedger p V = fhEggMatchNodes p V)

/-- Named residual: instantiate `FhEggLedgerSourceBinding` with the deployed encrypted evaluator and
the ledger router that assigns the canonical aggregate buyer/seller identities. -/
abbrev FhEggLedgerSourceBindingResidual := FhEggLedgerSourceBinding

/-! ## 4. Non-vacuity and refusal teeth. -/

/-- The worked fhEgg book's exact `(p*,V*) = (1,8)` allocation executes on the ledger. -/
theorem workBook_exact_drex_clearing :
    ∃ c : DrexClearing,
      c.nodes = fhEggMatchNodes 1 8 ∧
      settleRing c.pre (settlementsOf c.nodes) = some c.post := by
  obtain ⟨c, hnodes, _, _, hsettle⟩ :=
    fhEgg_output_executes_exact_drex_clearing workBook 3 (by decide) (by decide)
  simpa [workBook_crossing, workBook_clearedVolume] using ⟨c, hnodes, hsettle⟩

/-- A zero-volume output cannot be packaged by the positive-content constructor.  The positivity
premise is load-bearing: without traded volume the generated cycle would violate `wantPos`. -/
theorem fhEgg_zero_volume_not_wantPos (p : Nat) :
    ¬ (∀ n ∈ fhEggMatchNodes p 0, 0 < n.wantMin) := by
  intro h
  have := h (fhEggMatchNodes p 0 |>.getD 0 default) (by simp [fhEggMatchNodes])
  simp [fhEggMatchNodes] at this

#guard (fhEggMatchNodes 1 8).length == 2
#guard ((fhEggMatchNodes 1 8).getD 0 default).offerAmount == (8 : Int)
#guard ((fhEggMatchNodes 1 8).getD 1 default).wantMin == (8 : Int)

#assert_all_clean [Market.fhEggMatchNodes_valid, Market.fhEggMatchNodes_wantPos,
  Market.fhEggMatchNodes_settlements, Market.fhEggMatchNodes_settle,
  Market.fhEgg_output_executes_exact_drex_clearing, Market.workBook_exact_drex_clearing,
  Market.fhEgg_zero_volume_not_wantPos]

#assert_axioms fhEggMatchNodes_valid
#assert_axioms fhEggMatchNodes_wantPos
#assert_axioms fhEggMatchNodes_settlements
#assert_axioms fhEggMatchNodes_settle
#assert_axioms fhEgg_output_executes_exact_drex_clearing
#assert_axioms workBook_exact_drex_clearing
#assert_axioms fhEgg_zero_volume_not_wantPos

end Market
