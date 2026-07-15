/-
# Market.ShieldedRingEndpointDescriptor

Lean-authored semantic and wire descriptor for the deployed two-leg shielded-ring
endpoint apex.  The numeric AIR proves the ring algebra and publishes faithful
eight-lane endpoints; the recursive fold supplies the two verified shielded-spend
openings connected to the first six claim lanes.

No axioms, `sorry`, `admit`, or native decision procedure.
-/
import Market.WideCommitBoundary
import Market.LedgerRealizationExt
import Market.CrossChainSettlement
import Dregg2.Circuit.Emit.EffectVmEmitRotationWide
import Dregg2.Tactics

namespace Market.ShieldedRingEndpointDescriptor

open Market
open Dregg2.Exec
open Dregg2.Intent.Ring
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
  (Poseidon2WideCR Poseidon2Width8 wireCommitR8 wireCommitR8_binds)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option autoImplicit false

/-! ## The exact two-action kernel normal form used by the endpoint AIR. -/

def ringNode0 (c0 c1 a0 a1 : Nat) (m0 m1 : ℤ) : MatchNode :=
  { creator := c0, offerAsset := a0, offerAmount := m0,
    wantAsset := a1, wantMin := m1 }

def ringNode1 (c0 c1 a0 a1 : Nat) (m0 m1 : ℤ) : MatchNode :=
  { creator := c1, offerAsset := a1, offerAmount := m1,
    wantAsset := a0, wantMin := m0 }

def ringNodes (c0 c1 a0 a1 : Nat) (m0 m1 : ℤ) : List MatchNode :=
  [ringNode0 c0 c1 a0 a1 m0 m1, ringNode1 c0 c1 a0 a1 m0 m1]

def ringKernelPre (c0 c1 a0 a1 : Nat) (m0 m1 : ℤ) : RecordKernelState where
  accounts := {c0, c1}
  cell := fun c =>
    if c ∈ ({c0, c1} : Finset CellId) then Value.record [("balance", Value.int 0)] else default
  caps := fun _ => []
  bal := fun c a => if c = c0 ∧ a = a0 then m0 else if c = c1 ∧ a = a1 then m1 else 0

def ringKernelPost (c0 c1 a0 a1 : Nat) (m0 m1 : ℤ) : RecordKernelState :=
  { accounts := {c0, c1}
    cell := fun c =>
      if c ∈ ({c0, c1} : Finset CellId) then Value.record [("balance", Value.int 0)] else default
    caps := fun _ => []
    bal := fun c a => if c = c0 ∧ a = a1 then m1 else if c = c1 ∧ a = a0 then m0 else 0 }

theorem ringNodes_cycleValid (c0 c1 a0 a1 : Nat) (m0 m1 : ℤ)
    (hc : c0 ≠ c1) : CycleValid (ringNodes c0 c1 a0 a1 m0 m1) where
  len := by simp [ringNodes]
  edges := by
    intro k hk
    have hk2 : k = 0 ∨ k = 1 := by
      change k < 2 at hk
      omega
    rcases hk2 with rfl | rfl <;>
      simp [ringNodes, ringNode0, ringNode1, isCompatible]
  distinct := by
    intro i j hi hj hij
    have hi2 : i = 0 ∨ i = 1 := by
      change i < 2 at hi
      omega
    have hj2 : j = 0 ∨ j = 1 := by
      change j < 2 at hj
      omega
    rcases hi2 with rfl | rfl <;> rcases hj2 with rfl | rfl
    · exact absurd rfl hij
    · simpa [ringNodes, ringNode0, ringNode1] using hc
    · simpa [ringNodes, ringNode0, ringNode1] using hc.symm
    · exact absurd rfl hij

theorem ringNodes_wantPos (c0 c1 a0 a1 : Nat) (m0 m1 : ℤ)
    (hm0 : 0 < m0) (hm1 : 0 < m1) :
    ∀ n ∈ ringNodes c0 c1 a0 a1 m0 m1, 0 < n.wantMin := by
  intro n hn
  simp [ringNodes, ringNode0, ringNode1] at hn
  rcases hn with rfl | rfl
  · exact hm1
  · exact hm0

theorem ringKernel_settles (c0 c1 a0 a1 : Nat) (m0 m1 : ℤ)
    (hc : c0 ≠ c1) (ha : a0 ≠ a1) (hm0 : 0 < m0) (hm1 : 0 < m1) :
    settleRing (ringKernelPre c0 c1 a0 a1 m0 m1)
      (settlementsOf (ringNodes c0 c1 a0 a1 m0 m1)) =
        some (ringKernelPost c0 c1 a0 a1 m0 m1) := by
  rw [show settlementsOf (ringNodes c0 c1 a0 a1 m0 m1) =
      chainedRing
        [{ creator := c0, offerAsset := a0, wantMin := m1 },
         { creator := c1, offerAsset := a1, wantMin := m0 }] by rfl]
  rw [chainedRing_two]
  simp [ringKernelPost, ringKernelPre, settleRing, recKExecAsset, RingLeg.toTurn, authorizedB,
    recTransferBal, cellLifecycleLive, hc, hc.symm, ha, ha.symm, hm0.le, hm1.le]
  funext c a
  by_cases haa0 : a = a0
  · subst a
    by_cases hcc0 : c = c0
    · subst c; simp [recTransferBal, hc, ha, ha.symm]
    · by_cases hcc1 : c = c1
      · subst c; simp [recTransferBal, hc, hc.symm, ha, ha.symm]
      · simp [recTransferBal, hcc0, hcc1, ha, ha.symm]
  · by_cases haa1 : a = a1
    · subst a
      by_cases hcc0 : c = c0
      · subst c; simp [recTransferBal, hc, ha, ha.symm]
      · by_cases hcc1 : c = c1
        · subst c; simp [recTransferBal, hc, hc.symm, ha, ha.symm]
        · simp [recTransferBal, hcc0, hcc1, ha, ha.symm]
    · simp [recTransferBal, haa0, haa1]

/-- The proof-carrying clearing extracted from the endpoint fields. -/
def ringClearing (c0 c1 a0 a1 : Nat) (m0 m1 : ℤ)
    (hc : c0 ≠ c1) (ha : a0 ≠ a1) (hm0 : 0 < m0) (hm1 : 0 < m1) : DrexClearing where
  pre := ringKernelPre c0 c1 a0 a1 m0 m1
  post := ringKernelPost c0 c1 a0 a1 m0 m1
  nodes := ringNodes c0 c1 a0 a1 m0 m1
  valid := ringNodes_cycleValid c0 c1 a0 a1 m0 m1 hc
  wantPos := ringNodes_wantPos c0 c1 a0 a1 m0 m1 hm0 hm1
  settled := ringKernel_settles c0 c1 a0 a1 m0 m1 hc ha hm0 hm1

#guard (ringNodes 1 2 0 1 3 4).length == 2
#assert_axioms ringNodes_cycleValid
#assert_axioms ringNodes_wantPos
#assert_axioms ringKernel_settles

/-! ## The exact 27-lane endpoint surface and 178-limb wide commitment. -/

/-- Semantic fields carried by the endpoint AIR.  `noteClaim i` is the deployed
`[nullifier, merkleRoot, valueBinding]` prefix for leg `i`. -/
structure RingEndpointFields where
  creator0 : CellId
  creator1 : CellId
  asset0 : AssetId
  asset1 : AssetId
  amount0 : ℤ
  amount1 : ℤ
  noteClaim : Fin 2 → Fin 3 → ℤ

def RingEndpointFields.turn0 (f : RingEndpointFields) : Turn :=
  { actor := f.creator0, src := f.creator0, dst := f.creator1, amt := f.amount0 }

def RingEndpointFields.turn1 (f : RingEndpointFields) : Turn :=
  { actor := f.creator1, src := f.creator1, dst := f.creator0, amt := f.amount1 }

def endpointPostLog (f : RingEndpointFields) (log : List Turn) : List Turn :=
  [f.turn1, f.turn0] ++ log

/-- One of the two canonical kernel payloads used by the deployed endpoint AIR.
The four balance slots are the only before/after difference. -/
def ringKernelPayload (f : RingEndpointFields) (post : Bool) : List ℤ :=
  ([(f.creator0 : ℤ), (f.creator1 : ℤ), (f.asset0 : ℤ), (f.asset1 : ℤ),
    if post then 0 else f.amount0, if post then f.amount0 else 0,
    if post then 0 else f.amount1, if post then f.amount1 else 0,
    1, 1, 1, 1, 1, 1, 2,
    f.noteClaim 0 0, f.noteClaim 1 0, f.noteClaim 0 1,
    f.noteClaim 1 1, f.noteClaim 0 2, f.noteClaim 1 2] : List ℤ) ++
    List.replicate 157 0

theorem ringKernelPayload_length (f : RingEndpointFields) (post : Bool) :
    (ringKernelPayload f post).length = 178 := by
  -- `length_append` + `length_replicate` as REWRITES: the 157-element tail is never unfolded,
  -- only its length is read off. The explicit prefix costs 21 `length_cons` steps.
  simp only [ringKernelPayload, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil]

/-- The deployed endpoint's genuine eight-lane wide commitment. -/
def ringCommit8 (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW) (f : RingEndpointFields) (post : Bool)
    (receiptRoot : ℤ) : Market.WideCommitBoundary.Felt8 :=
  ⟨wireCommitR8 permW (ringKernelPayload f post) receiptRoot,
    Market.WideCommitBoundary.wireCommitR8_length permW hW _ _⟩

/-- The exact public endpoint layout: six note lanes, creators, wide pre/post,
count, and the receipt roots before/after the two-action batch. -/
structure PublishedRingEndpoint where
  noteClaim : Fin 2 → Fin 3 → ℤ
  creators : Fin 2 → CellId
  preCommit : Market.WideCommitBoundary.Felt8
  postCommit : Market.WideCommitBoundary.Felt8
  turnCount : Nat
  preReceiptRoot : ℤ
  postReceiptRoot : ℤ

/-- Faithful decode of the endpoint lanes to the normal-form kernel transition. -/
structure RingEndpointDecode (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW) (hash : List ℤ → ℤ)
    (pub : PublishedRingEndpoint) (f : RingEndpointFields)
    (pre post : RecChainedState) : Prop where
  claims : pub.noteClaim = f.noteClaim
  creator0 : pub.creators 0 = f.creator0
  creator1 : pub.creators 1 = f.creator1
  count : pub.turnCount = 2
  preReceipt : pub.preReceiptRoot = Market.WideCommitBoundary.receiptRoot hash pre.log
  postReceipt : pub.postReceiptRoot = Market.WideCommitBoundary.receiptRoot hash post.log
  preWide : pub.preCommit = ringCommit8 permW hW f false pub.preReceiptRoot
  postWide : pub.postCommit = ringCommit8 permW hW f true pub.postReceiptRoot
  preKernel : pre.kernel = ringKernelPre f.creator0 f.creator1 f.asset0 f.asset1
    f.amount0 f.amount1
  postKernel : post.kernel = ringKernelPost f.creator0 f.creator1 f.asset0 f.asset1
    f.amount0 f.amount1
  receiptTransition : post.log = endpointPostLog f pre.log

theorem ringCommit8_pre_binds_kernel (permW : List ℤ → List ℤ)
    (hCR : Poseidon2WideCR permW) (hW : Poseidon2Width8 permW)
    (f g : RingEndpointFields) (rf rg : ℤ)
    (h : ringCommit8 permW hW f false rf = ringCommit8 permW hW g false rg) :
    ringKernelPre f.creator0 f.creator1 f.asset0 f.asset1 f.amount0 f.amount1 =
      ringKernelPre g.creator0 g.creator1 g.asset0 g.asset1 g.amount0 g.amount1 := by
  have hw : wireCommitR8 permW (ringKernelPayload f false) rf =
      wireCommitR8 permW (ringKernelPayload g false) rg := by
    simpa [ringCommit8] using congrArg Market.WideCommitBoundary.Felt8.vals h
  obtain ⟨hp, _⟩ := wireCommitR8_binds permW hCR hW
    (by rw [ringKernelPayload_length, ringKernelPayload_length]) hw
  have h0 := congrArg (fun xs : List ℤ => xs.getD 0 0) hp
  have h1 := congrArg (fun xs : List ℤ => xs.getD 1 0) hp
  have h2 := congrArg (fun xs : List ℤ => xs.getD 2 0) hp
  have h3 := congrArg (fun xs : List ℤ => xs.getD 3 0) hp
  have h4 := congrArg (fun xs : List ℤ => xs.getD 4 0) hp
  have h6 := congrArg (fun xs : List ℤ => xs.getD 6 0) hp
  -- `cons_append` exposes each head so `getD` walks only the 0..6 prefix; the 157-element
  -- replicate tail is never unfolded.
  simp only [ringKernelPayload, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
    at h0 h1 h2 h3 h4 h6
  simp_all

theorem ringCommit8_post_binds_kernel (permW : List ℤ → List ℤ)
    (hCR : Poseidon2WideCR permW) (hW : Poseidon2Width8 permW)
    (f g : RingEndpointFields) (rf rg : ℤ)
    (h : ringCommit8 permW hW f true rf = ringCommit8 permW hW g true rg) :
    ringKernelPost f.creator0 f.creator1 f.asset0 f.asset1 f.amount0 f.amount1 =
      ringKernelPost g.creator0 g.creator1 g.asset0 g.asset1 g.amount0 g.amount1 := by
  have hw : wireCommitR8 permW (ringKernelPayload f true) rf =
      wireCommitR8 permW (ringKernelPayload g true) rg := by
    simpa [ringCommit8] using congrArg Market.WideCommitBoundary.Felt8.vals h
  obtain ⟨hp, _⟩ := wireCommitR8_binds permW hCR hW
    (by rw [ringKernelPayload_length, ringKernelPayload_length]) hw
  have h0 := congrArg (fun xs : List ℤ => xs.getD 0 0) hp
  have h1 := congrArg (fun xs : List ℤ => xs.getD 1 0) hp
  have h2 := congrArg (fun xs : List ℤ => xs.getD 2 0) hp
  have h3 := congrArg (fun xs : List ℤ => xs.getD 3 0) hp
  have h5 := congrArg (fun xs : List ℤ => xs.getD 5 0) hp
  have h7 := congrArg (fun xs : List ℤ => xs.getD 7 0) hp
  simp only [ringKernelPayload, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
    at h0 h1 h2 h3 h5 h7
  simp_all

theorem receiptRoot_endpointPostLog (hash : List ℤ → ℤ) (f : RingEndpointFields)
    (log : List Turn) :
    Market.WideCommitBoundary.receiptRoot hash (endpointPostLog f log) =
      Market.WideCommitBoundary.factHash hash
        (Market.WideCommitBoundary.factHash hash
          (Market.WideCommitBoundary.receiptRoot hash log)
          [Market.WideCommitBoundary.turnDigest hash f.turn0])
        [Market.WideCommitBoundary.turnDigest hash f.turn1] := by
  rfl

/-! ## Lean-authored deployed descriptor. -/

namespace Col

def legWidth : Nat := 14
def leg (i field : Nat) : Nat := i * legWidth + field
def value : Nat := 0
def randomness : Nat := 1
def vbPad0 : Nat := 2
def vbPad1 : Nat := 3
def valueBinding : Nat := 4
def asset : Nat := 5
def offerAsset : Nat := 6
def offerAmount : Nat := 7
def wantAsset : Nat := 8
def wantMin : Nat := 9
def nullifier : Nat := 10
def merkleRoot : Nat := 11
def outVal : Nat := 12
def outBlind : Nat := 13
def nfDiffInv : Nat := 28
def rangeBitBase : Nat := 29
def valueBits : Nat := 29
def rangeTargets : List Nat :=
  [leg 0 value, leg 1 value, leg 0 outVal, leg 1 outVal]
def preLaneWidth : Nat := 145
def endpointBase : Nat := 159
def actionWidth : Nat := 12
def action (i field : Nat) : Nat := endpointBase + i * actionWidth + field
def creator : Nat := 0
def receiver : Nat := 1
def actionAsset : Nat := 2
def amount : Nat := 3
def srcPre : Nat := 4
def srcPost : Nat := 5
def dstPre : Nat := 6
def dstPost : Nat := 7
def authorized : Nat := 8
def srcLive : Nat := 9
def dstLive : Nat := 10
def actionHash : Nat := 11
def creatorDiffInv : Nat := 183
def assetDiffInv : Nat := 184
def amount0Inv : Nat := 185
def amount1Inv : Nat := 186
def turnCount : Nat := 187
def preReceipt : Nat := 188
def midReceipt : Nat := 189
def postReceipt : Nat := 190
def preLimbs : Nat := 191
def preIroot : Nat := 369
def postLimbs : Nat := 370
def postIroot : Nat := 548
def receiptLanes : Nat := 549
def hostWidth : Nat := 577

end Col

private def negE (x : EmittedExpr) : EmittedExpr := .mul (.const (-1)) x
private def subE (x y : EmittedExpr) : EmittedExpr := .add x (negE y)
private def gateE (x : EmittedExpr) : VmConstraint2 := .base (.gate x)
private def eqCol (a b : Nat) : VmConstraint2 := gateE (subE (.var a) (.var b))
private def zeroCol (a : Nat) : VmConstraint2 := gateE (.var a)
private def oneCol (a : Nat) : VmConstraint2 := gateE (subE (.var a) (.const 1))
private def inverseGate (a b inv : Nat) : VmConstraint2 :=
  gateE (subE (.mul (subE (.var a) (.var b)) (.var inv)) (.const 1))
private def nonzeroGate (a inv : Nat) : VmConstraint2 :=
  gateE (subE (.mul (.var a) (.var inv)) (.const 1))

private def rangeBitCol (target bit : Nat) : Nat :=
  Col.rangeBitBase + target * Col.valueBits + bit

private def rangeConstraintsFor (target col : Nat) : List VmConstraint2 :=
  (List.range Col.valueBits).map (fun j =>
    let b := EmittedExpr.var (rangeBitCol target j)
    gateE (.mul b (subE b (.const 1)))) ++
  [gateE ((List.range Col.valueBits).foldl
    (fun acc j => subE acc (.mul (.const (2 ^ j)) (.var (rangeBitCol target j))))
    (.var col))]

private def factLookup (output : Nat) (inputs : List EmittedExpr) (laneBase : Nat) : VmConstraint2 :=
  .lookup (siteLookupN
    (inputs ++ List.replicate (5 - inputs.length) (.const 0) ++ [.const 64207, .const 1])
    (output :: (List.range 7).map (fun j => laneBase + j)))

private def commonPayloadSource : Nat → Option Nat
  | 0 => some (Col.action 0 Col.creator)
  | 1 => some (Col.action 1 Col.creator)
  | 2 => some (Col.action 0 Col.actionAsset)
  | 3 => some (Col.action 1 Col.actionAsset)
  | 8 => some (Col.action 0 Col.authorized)
  | 9 => some (Col.action 1 Col.authorized)
  | 10 => some (Col.action 0 Col.srcLive)
  | 11 => some (Col.action 1 Col.srcLive)
  | 12 => some (Col.action 0 Col.dstLive)
  | 13 => some (Col.action 1 Col.dstLive)
  | 14 => some Col.turnCount
  | 15 => some (Col.leg 0 Col.nullifier)
  | 16 => some (Col.leg 1 Col.nullifier)
  | 17 => some (Col.leg 0 Col.merkleRoot)
  | 18 => some (Col.leg 1 Col.merkleRoot)
  | 19 => some (Col.leg 0 Col.valueBinding)
  | 20 => some (Col.leg 1 Col.valueBinding)
  | _ => none

private def preBalanceSource : Nat → Option Nat
  | 4 => some (Col.action 0 Col.srcPre)
  | 5 => some (Col.action 0 Col.dstPre)
  | 6 => some (Col.action 1 Col.srcPre)
  | 7 => some (Col.action 1 Col.dstPre)
  | _ => none

private def postBalanceSource : Nat → Option Nat
  | 4 => some (Col.action 0 Col.srcPost)
  | 5 => some (Col.action 0 Col.dstPost)
  | 6 => some (Col.action 1 Col.srcPost)
  | 7 => some (Col.action 1 Col.dstPost)
  | _ => none

private def payloadPin (base j : Nat) (sideSource : Nat → Option Nat) : VmConstraint2 :=
  match commonPayloadSource j with
  | some c => eqCol (base + j) c
  | none => match sideSource j with
    | some c => eqCol (base + j) c
    | none => zeroCol (base + j)

private def ringCoreConstraints : List VmConstraint2 :=
  [eqCol (Col.leg 0 Col.offerAsset) (Col.leg 0 Col.asset),
   eqCol (Col.leg 1 Col.offerAsset) (Col.leg 1 Col.asset),
   eqCol (Col.leg 0 Col.offerAmount) (Col.leg 0 Col.value),
   eqCol (Col.leg 1 Col.offerAmount) (Col.leg 1 Col.value),
   eqCol (Col.leg 0 Col.offerAsset) (Col.leg 1 Col.wantAsset),
   eqCol (Col.leg 1 Col.offerAsset) (Col.leg 0 Col.wantAsset),
   eqCol (Col.leg 0 Col.offerAmount) (Col.leg 1 Col.wantMin),
   eqCol (Col.leg 1 Col.offerAmount) (Col.leg 0 Col.wantMin),
   inverseGate (Col.leg 0 Col.nullifier) (Col.leg 1 Col.nullifier) Col.nfDiffInv,
   gateE (subE (.add (.var (Col.leg 0 Col.value)) (.var (Col.leg 1 Col.value)))
     (.add (.var (Col.leg 0 Col.outVal)) (.var (Col.leg 1 Col.outVal)))),
   gateE (subE (.add (.var (Col.leg 0 Col.randomness)) (.var (Col.leg 1 Col.randomness)))
     (.add (.var (Col.leg 0 Col.outBlind)) (.var (Col.leg 1 Col.outBlind)))),
   zeroCol (Col.leg 0 Col.vbPad0), zeroCol (Col.leg 0 Col.vbPad1),
   zeroCol (Col.leg 1 Col.vbPad0), zeroCol (Col.leg 1 Col.vbPad1),
   factLookup (Col.leg 0 Col.valueBinding)
     [.var (Col.leg 0 Col.value), .var (Col.leg 0 Col.asset),
      .var (Col.leg 0 Col.randomness), .var (Col.leg 0 Col.vbPad0)] Col.preLaneWidth,
   factLookup (Col.leg 1 Col.valueBinding)
     [.var (Col.leg 1 Col.value), .var (Col.leg 1 Col.asset),
      .var (Col.leg 1 Col.randomness), .var (Col.leg 1 Col.vbPad0)] (Col.preLaneWidth + 7)] ++
  (Col.rangeTargets.zipIdx).flatMap (fun p => rangeConstraintsFor p.2 p.1)

private def endpointActionConstraints : List VmConstraint2 :=
  [eqCol (Col.action 0 Col.receiver) (Col.action 1 Col.creator),
   eqCol (Col.action 1 Col.receiver) (Col.action 0 Col.creator),
   eqCol (Col.action 0 Col.actionAsset) (Col.leg 0 Col.offerAsset),
   eqCol (Col.action 1 Col.actionAsset) (Col.leg 1 Col.offerAsset),
   eqCol (Col.action 0 Col.amount) (Col.leg 0 Col.offerAmount),
   eqCol (Col.action 1 Col.amount) (Col.leg 1 Col.offerAmount),
   eqCol (Col.action 0 Col.srcPre) (Col.action 0 Col.amount),
   eqCol (Col.action 1 Col.srcPre) (Col.action 1 Col.amount),
   zeroCol (Col.action 0 Col.srcPost), zeroCol (Col.action 1 Col.srcPost),
   zeroCol (Col.action 0 Col.dstPre), zeroCol (Col.action 1 Col.dstPre),
   eqCol (Col.action 0 Col.dstPost) (Col.action 0 Col.amount),
   eqCol (Col.action 1 Col.dstPost) (Col.action 1 Col.amount),
   oneCol (Col.action 0 Col.authorized), oneCol (Col.action 1 Col.authorized),
   oneCol (Col.action 0 Col.srcLive), oneCol (Col.action 1 Col.srcLive),
   oneCol (Col.action 0 Col.dstLive), oneCol (Col.action 1 Col.dstLive),
   inverseGate (Col.action 0 Col.creator) (Col.action 1 Col.creator) Col.creatorDiffInv,
   inverseGate (Col.action 0 Col.actionAsset) (Col.action 1 Col.actionAsset) Col.assetDiffInv,
   nonzeroGate (Col.action 0 Col.amount) Col.amount0Inv,
   nonzeroGate (Col.action 1 Col.amount) Col.amount1Inv,
   gateE (subE (.var Col.turnCount) (.const 2)),
   factLookup (Col.action 0 Col.actionHash)
     [.var (Col.action 0 Col.creator), .var (Col.action 0 Col.creator),
      .var (Col.action 0 Col.receiver), .var (Col.action 0 Col.amount)] Col.receiptLanes,
   factLookup (Col.action 1 Col.actionHash)
     [.var (Col.action 1 Col.creator), .var (Col.action 1 Col.creator),
      .var (Col.action 1 Col.receiver), .var (Col.action 1 Col.amount)] (Col.receiptLanes + 7),
   factLookup Col.midReceipt [.var Col.preReceipt, .var (Col.action 0 Col.actionHash)]
     (Col.receiptLanes + 14),
   factLookup Col.postReceipt [.var Col.midReceipt, .var (Col.action 1 Col.actionHash)]
     (Col.receiptLanes + 21)]

private def payloadConstraints : List VmConstraint2 :=
  (List.range 178).flatMap (fun j =>
    [payloadPin Col.preLimbs j preBalanceSource,
     payloadPin Col.postLimbs j postBalanceSource]) ++
  [eqCol Col.preIroot Col.preReceipt, eqCol Col.postIroot Col.postReceipt]

private def endpointPins : List VmConstraint2 :=
  [ .base (.piBinding .first (Col.leg 0 Col.nullifier) 0),
    .base (.piBinding .first (Col.leg 0 Col.merkleRoot) 1),
    .base (.piBinding .first (Col.leg 0 Col.valueBinding) 2),
    .base (.piBinding .first (Col.leg 1 Col.nullifier) 3),
    .base (.piBinding .first (Col.leg 1 Col.merkleRoot) 4),
    .base (.piBinding .first (Col.leg 1 Col.valueBinding) 5),
    .base (.piBinding .first (Col.action 0 Col.creator) 6),
    .base (.piBinding .first (Col.action 1 Col.creator) 7),
    .base (.piBinding .first Col.turnCount 8),
    .base (.piBinding .first Col.preReceipt 9),
    .base (.piBinding .first Col.postReceipt 10) ]

/-- The exact Lean-authored host whose constraints mirror the deployed Rust endpoint
row before the two wide carrier blocks are appended. -/
def shieldedRingEndpointHost : EffectVmDescriptor2 where
  name := "shielded-ring-clear-2-endpoint-wide"
  traceWidth := Col.hostWidth
  piCount := 11
  tables := []
  constraints := ringCoreConstraints ++ endpointActionConstraints ++ payloadConstraints ++ endpointPins
  hashSites := []
  ranges := []

/-- The deployed descriptor: host teeth plus the proved 60-step wide pre/post chains
and their sixteen public lanes. -/
def shieldedRingEndpointDescriptor : EffectVmDescriptor2 :=
  wideAppend shieldedRingEndpointHost Col.preLimbs Col.postLimbs

/-- The recursive fold opening tied to the first six lanes: two genuine shielded
spend legs, with their matcher rows equal to the endpoint AIR fields. -/
structure RingFoldBinding (f : RingEndpointFields) where
  poolOf : AssetId → CellId
  ring : ShieldedRing poolOf
  nodes : matchNodes ring = ringNodes f.creator0 f.creator1 f.asset0 f.asset1 f.amount0 f.amount1
  fused : ∀ leg ∈ ring, LegFused leg

/-- Acceptance object of the deployed apex. `satisfied` is the endpoint AIR proof;
`fold` is the two child-verifier/connect opening; `decode` is the faithful wide
boundary decode. The remaining four fields are precisely the inverse/range teeth
the AIR enforces and are kept as named projections of the accepted trace. -/
structure RingEndpointAccepted (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW) (hash : List ℤ → ℤ)
    (pub : PublishedRingEndpoint) (pre post : RecChainedState) where
  minit : ℤ → ℤ
  mfin : ℤ → ℤ × Nat
  maddrs : List ℤ
  trace : VmTrace
  satisfied : Satisfied2 hash shieldedRingEndpointDescriptor minit mfin maddrs trace
  fields : RingEndpointFields
  decode : RingEndpointDecode permW hW hash pub fields pre post
  fold : RingFoldBinding fields
  creatorsDistinct : fields.creator0 ≠ fields.creator1
  assetsDistinct : fields.asset0 ≠ fields.asset1
  amount0Positive : 0 < fields.amount0
  amount1Positive : 0 < fields.amount1

/-- The clearing forced by an accepted endpoint apex. -/
def RingEndpointAccepted.clearing {permW : List ℤ → List ℤ}
    {hW : Poseidon2Width8 permW} {hash : List ℤ → ℤ}
    {pub : PublishedRingEndpoint} {pre post : RecChainedState}
    (h : RingEndpointAccepted permW hW hash pub pre post) : DrexClearing :=
  ringClearing h.fields.creator0 h.fields.creator1 h.fields.asset0 h.fields.asset1
    h.fields.amount0 h.fields.amount1 h.creatorsDistinct h.assetsDistinct
    h.amount0Positive h.amount1Positive

theorem RingEndpointAccepted.clearing_nodes {permW : List ℤ → List ℤ}
    {hW : Poseidon2Width8 permW} {hash : List ℤ → ℤ}
    {pub : PublishedRingEndpoint} {pre post : RecChainedState}
    (h : RingEndpointAccepted permW hW hash pub pre post) :
    h.clearing.nodes = matchNodes h.fold.ring := by
  rw [h.fold.nodes]
  rfl

theorem RingEndpointAccepted.kernel_endpoints {permW : List ℤ → List ℤ}
    {hW : Poseidon2Width8 permW} {hash : List ℤ → ℤ}
    {pub : PublishedRingEndpoint} {pre post : RecChainedState}
    (h : RingEndpointAccepted permW hW hash pub pre post) :
    h.clearing.pre = pre.kernel ∧ h.clearing.post = post.kernel := by
  exact ⟨h.decode.preKernel.symm, h.decode.postKernel.symm⟩

theorem RingEndpointAccepted.receipt_transition {permW : List ℤ → List ℤ}
    {hW : Poseidon2Width8 permW} {hash : List ℤ → ℤ}
    {pub : PublishedRingEndpoint} {pre post : RecChainedState}
    (h : RingEndpointAccepted permW hW hash pub pre post) :
    post.log =
      ((settlementsOf h.clearing.nodes).map RingLeg.toTurn).reverse ++ pre.log := by
  -- Rewrite `h.clearing.nodes` while `clearing` is still FOLDED (unfolding it first destroys the
  -- pattern `clearing_nodes`/`fold.nodes` match on), then unfold the log form.
  rw [h.decode.receiptTransition, h.clearing_nodes, h.fold.nodes]
  simp [endpointPostLog, ringNodes, ringNode0, ringNode1, settlementsOf, chainedRing_two,
    Dregg2.Intent.Ring.MatchNode.toRingNode,
    RingEndpointFields.turn0, RingEndpointFields.turn1, RingLeg.toTurn]

#guard shieldedRingEndpointHost.traceWidth == 577
#guard shieldedRingEndpointHost.piCount == 11
#guard shieldedRingEndpointDescriptor.traceWidth == 1537
#guard shieldedRingEndpointDescriptor.piCount == 27
#guard shieldedRingEndpointDescriptor.name == "shielded-ring-clear-2-endpoint-wide"

#guard (ringKernelPayload
  { creator0 := 1, creator1 := 2, asset0 := 0, asset1 := 1,
    amount0 := 3, amount1 := 4, noteClaim := fun _ _ => 0 } false).length == 178
#guard (endpointPostLog
  { creator0 := 1, creator1 := 2, asset0 := 0, asset1 := 1,
    amount0 := 3, amount1 := 4, noteClaim := fun _ _ => 0 } []).length == 2
#assert_axioms ringKernelPayload_length
#assert_axioms ringCommit8_pre_binds_kernel
#assert_axioms ringCommit8_post_binds_kernel
#assert_axioms receiptRoot_endpointPostLog
#assert_axioms RingEndpointAccepted.clearing_nodes
#assert_axioms RingEndpointAccepted.kernel_endpoints
#assert_axioms RingEndpointAccepted.receipt_transition

end Market.ShieldedRingEndpointDescriptor
