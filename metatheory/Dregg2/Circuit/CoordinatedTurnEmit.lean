/-
# Dregg2.Circuit.CoordinatedTurnEmit — Wave 1 inter-vat coordinated turn circuit emission.

Extends `CoordinatedTurnRefinement` with an `Expr`/`ConstraintSystem` scaffold: public-input EQ
gates (`rootA`/`rootB`/`charterHash`/`bindingHash`) plus per-leg frame EQ gates reusing the
`StateCommit` rest/frame/moved pattern. Serializes via `CircuitEmit.emit` with emit-faithfulness
and composes soundness with `coordinated_turn_circuit_refines_spec_honest`.

No `sorry`/`admit`/`axiom`.
-/
import Dregg2.Circuit
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.CoordinatedTurnRefinement
import Dregg2.Circuit.StateCommit

namespace Dregg2.Circuit.CoordinatedTurnEmit

open Dregg2.Circuit
open Dregg2.Circuit.CoordinatedTurnRefinement
open Dregg2.Circuit.StateCommit
open Dregg2.Exec
open Dregg2.Exec.CoordinatedCaveat (CoordinatedCaveat)
open Dregg2.Exec.CoordinatedForestGate
open Dregg2.Exec.JointCell
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.CoordinatedForestGLift

/-! ## §0 — decidability (for concrete `#guard`s). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — named wires (public inputs + per-leg digest columns). -/

/-- Published public input: pre-state root for vat `A`. -/
def vPubRootA       : Var := 0
/-- Published public input: pre-state root for vat `B`. -/
def vPubRootB       : Var := 1
/-- Published public input: covenant digest on the joint pre-snapshot. -/
def vPubCharterHash : Var := 2
/-- Published public input: CG-2 shared-binding digest. -/
def vPubBindingHash : Var := 3
/-- Witness: leg-`A` pre-root digest (bound to `vPubRootA`). -/
def vLegRootA       : Var := 4
/-- Witness: covenant digest (bound to `vPubCharterHash`). -/
def vCharterDig     : Var := 5
/-- Witness: binding digest (bound to `vPubBindingHash`). -/
def vBindingDig     : Var := 6
/-- Leg `A` rest-hash pre/post (the `cSRestFrame` pattern). -/
def vRestDigPreA    : Var := 7
def vRestDigPostA   : Var := 8
/-- Leg `A` untouched-frame digest pre/post (`cSFrameReuse`). -/
def vFrameDigPreA   : Var := 9
def vFrameDigPostA  : Var := 10
/-- Leg `A` moved-cell digest post / expected (`cSMovedBind`). -/
def vMovedDigPostA    : Var := 11
def vMovedDigExpectedA : Var := 12
/-- Witness: leg-`B` pre-root digest (bound to `vPubRootB`). -/
def vLegRootB       : Var := 13
/-- Leg `B` rest/frame/moved digest columns (same pattern as leg `A`). -/
def vRestDigPreB    : Var := 14
def vRestDigPostB   : Var := 15
def vFrameDigPreB   : Var := 16
def vFrameDigPostB  : Var := 17
def vMovedDigPostB    : Var := 18
def vMovedDigExpectedB : Var := 19

/-- Coordinated-turn trace width: four public wires + sixteen witness digest columns. -/
def coordinatedTurnTraceWidth : Nat := 20

/-! ## §2 — `encodeCoordinatedTurn` — honest witness layout. -/

section Surface

variable (CH : CellId → Value → ℤ)
variable (RH : RecordKernelState → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)
variable (legRootA legRootB : RecordKernelState → BiTurn → ℤ)
variable (covenantH : CoordinatedCaveat → KernelState → KernelState → ℤ)
variable (bindH : (bt : BiTurn) → SharedBinding bt → ℤ)

/-- **`encodeCoordinatedTurn`** — lay bilateral pre/post snapshots and public inputs out as the
witness vector. Public columns carry `pub`; digest columns carry the honest `legRoot`/`covenantH`/
`bindH` values and the per-leg `StateCommit` frame/moved digests. -/
def encodeCoordinatedTurn
    (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) : Assignment := fun v =>
  if      v = vPubRootA       then pub.rootA
  else if v = vPubRootB       then pub.rootB
  else if v = vPubCharterHash then pub.charterHash
  else if v = vPubBindingHash then pub.bindingHash
  else if v = vLegRootA       then legRootA sA.kernel step.bt
  else if v = vCharterDig     then covenantH step.covenant (recChainedKernelView sA) (recChainedKernelView sB)
  else if v = vBindingDig     then bindH step.bt step.bind
  else if v = vRestDigPreA    then RH sA.kernel
  else if v = vRestDigPostA   then RH sA'.kernel
  else if v = vFrameDigPreA   then frameDigest CH compressN sA.kernel (halfOutCarrier sA.kernel step.bt)
  else if v = vFrameDigPostA  then frameDigest CH compressN sA'.kernel (halfOutCarrier sA.kernel step.bt)
  else if v = vMovedDigPostA  then movedDigest CH compress sA'.kernel.cell step.bt.srcA step.bt.srcA
  else if v = vMovedDigExpectedA then
    movedDigest CH compress (recDebit sA.kernel.cell step.bt.srcA step.bt.amt) step.bt.srcA step.bt.srcA
  else if v = vLegRootB       then legRootB sB.kernel step.bt
  else if v = vRestDigPreB    then RH sB.kernel
  else if v = vRestDigPostB   then RH sB'.kernel
  else if v = vFrameDigPreB   then frameDigest CH compressN sB.kernel (halfInCarrier sB.kernel step.bt)
  else if v = vFrameDigPostB  then frameDigest CH compressN sB'.kernel (halfInCarrier sB.kernel step.bt)
  else if v = vMovedDigPostB  then movedDigest CH compress sB'.kernel.cell step.bt.dstB step.bt.dstB
  else if v = vMovedDigExpectedB then
    movedDigest CH compress (recCredit sB.kernel.cell step.bt.dstB step.bt.amt) step.bt.dstB step.bt.dstB
  else 0

/-! ### Encoder wire lookups (collapse the `if`-cascade at each index). -/

private theorem encCT_vPubRootA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vPubRootA = pub.rootA := by simp [encodeCoordinatedTurn, vPubRootA]

private theorem encCT_vPubRootB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vPubRootB = pub.rootB := by
  simp [encodeCoordinatedTurn, vPubRootB, vPubRootA, vPubCharterHash, vPubBindingHash]

private theorem encCT_vPubCharterHash (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vPubCharterHash = pub.charterHash := by
  simp [encodeCoordinatedTurn, vPubCharterHash, vPubRootB, vPubRootA, vPubBindingHash]

private theorem encCT_vPubBindingHash (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vPubBindingHash = pub.bindingHash := by
  simp [encodeCoordinatedTurn, vPubBindingHash, vPubCharterHash, vPubRootB, vPubRootA]

private theorem encCT_vLegRootA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vLegRootA = legRootA sA.kernel step.bt := by
  simp [encodeCoordinatedTurn, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

private theorem encCT_vCharterDig (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vCharterDig =
        covenantH step.covenant (recChainedKernelView sA) (recChainedKernelView sB) := by
  simp [encodeCoordinatedTurn, vCharterDig, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

private theorem encCT_vBindingDig (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vBindingDig = bindH step.bt step.bind := by
  simp [encodeCoordinatedTurn, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB,
    vPubCharterHash, vPubBindingHash]

private theorem encCT_vRestDigPreA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vRestDigPreA = RH sA.kernel := by
  simp [encodeCoordinatedTurn, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB,
    vPubCharterHash, vPubBindingHash]

private theorem encCT_vRestDigPostA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vRestDigPostA = RH sA'.kernel := by
  simp [encodeCoordinatedTurn, vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA,
    vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

private theorem encCT_vFrameDigPreA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vFrameDigPreA = frameDigest CH compressN sA.kernel (halfOutCarrier sA.kernel step.bt) := by
  simp [encodeCoordinatedTurn, vFrameDigPreA, vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig,
    vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

private theorem encCT_vFrameDigPostA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vFrameDigPostA = frameDigest CH compressN sA'.kernel (halfOutCarrier sA.kernel step.bt) := by
  simp [encodeCoordinatedTurn, vFrameDigPostA, vFrameDigPreA, vRestDigPostA, vRestDigPreA, vBindingDig,
    vCharterDig, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

private theorem encCT_vMovedDigPostA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vMovedDigPostA = movedDigest CH compress sA'.kernel.cell step.bt.srcA step.bt.srcA := by
  simp [encodeCoordinatedTurn, vMovedDigPostA, vMovedDigExpectedA, vFrameDigPostA, vFrameDigPreA,
    vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB,
    vPubCharterHash, vPubBindingHash]

private theorem encCT_vMovedDigExpectedA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vMovedDigExpectedA =
        movedDigest CH compress (recDebit sA.kernel.cell step.bt.srcA step.bt.amt) step.bt.srcA step.bt.srcA := by
  simp [encodeCoordinatedTurn, vMovedDigExpectedA, vMovedDigPostA, vFrameDigPostA, vFrameDigPreA,
    vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB,
    vPubCharterHash, vPubBindingHash]

private theorem encCT_vLegRootB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vLegRootB = legRootB sB.kernel step.bt := by
  simp [encodeCoordinatedTurn, vLegRootB, vMovedDigExpectedA, vMovedDigPostA, vFrameDigPostA, vFrameDigPreA,
    vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash,
    vPubBindingHash]

private theorem encCT_vRestDigPreB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vRestDigPreB = RH sB.kernel := by
  simp [encodeCoordinatedTurn, vRestDigPreB, vLegRootB, vMovedDigExpectedA, vMovedDigPostA, vFrameDigPostA,
    vFrameDigPreA, vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB,
    vPubCharterHash, vPubBindingHash]

private theorem encCT_vRestDigPostB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vRestDigPostB = RH sB'.kernel := by
  simp [encodeCoordinatedTurn, vRestDigPostB, vRestDigPreB, vLegRootB, vMovedDigExpectedA, vMovedDigPostA,
    vFrameDigPostA, vFrameDigPreA, vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA,
    vPubRootB, vPubCharterHash, vPubBindingHash]

private theorem encCT_vFrameDigPreB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vFrameDigPreB = frameDigest CH compressN sB.kernel (halfInCarrier sB.kernel step.bt) := by
  simp [encodeCoordinatedTurn, vFrameDigPreB, vRestDigPostB, vRestDigPreB, vLegRootB, vMovedDigExpectedA,
    vMovedDigPostA, vFrameDigPostA, vFrameDigPreA, vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig,
    vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

private theorem encCT_vFrameDigPostB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vFrameDigPostB = frameDigest CH compressN sB'.kernel (halfInCarrier sB.kernel step.bt) := by
  simp [encodeCoordinatedTurn, vFrameDigPostB, vFrameDigPreB, vRestDigPostB, vRestDigPreB, vLegRootB,
    vMovedDigExpectedA, vMovedDigPostA, vFrameDigPostA, vFrameDigPreA, vRestDigPostA, vRestDigPreA, vBindingDig,
    vCharterDig, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

private theorem encCT_vMovedDigPostB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vMovedDigPostB = movedDigest CH compress sB'.kernel.cell step.bt.dstB step.bt.dstB := by
  simp [encodeCoordinatedTurn, vMovedDigPostB, vMovedDigExpectedB, vFrameDigPostB, vFrameDigPreB,
    vRestDigPostB, vRestDigPreB, vLegRootB, vMovedDigExpectedA, vMovedDigPostA, vFrameDigPostA, vFrameDigPreA,
    vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash,
    vPubBindingHash]

private theorem encCT_vMovedDigExpectedB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vMovedDigExpectedB =
        movedDigest CH compress (recCredit sB.kernel.cell step.bt.dstB step.bt.amt) step.bt.dstB step.bt.dstB := by
  simp [encodeCoordinatedTurn, vMovedDigExpectedB, vMovedDigPostB, vFrameDigPostB, vFrameDigPreB, vRestDigPostB,
    vRestDigPreB, vLegRootB, vMovedDigExpectedA, vMovedDigPostA, vFrameDigPostA, vFrameDigPreA, vRestDigPostA,
    vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

/-! ## §3 — `coordinatedTurnCircuit`: public EQ gates + per-leg frame EQ gates. -/

/-- Public-input binding: leg-`A` root wire equals the published `rootA`. -/
def cCTPubRootA : Constraint := { lhs := .var vLegRootA, rhs := .var vPubRootA }
/-- Public-input binding: leg-`B` root wire equals the published `rootB`. -/
def cCTPubRootB : Constraint := { lhs := .var vLegRootB, rhs := .var vPubRootB }
/-- Public-input binding: covenant digest equals `charterHash`. -/
def cCTPubCharter : Constraint := { lhs := .var vCharterDig, rhs := .var vPubCharterHash }
/-- Public-input binding: binding digest equals `bindingHash`. -/
def cCTPubBinding : Constraint := { lhs := .var vBindingDig, rhs := .var vPubBindingHash }

/-- Leg `A` rest-frame gate (`StateCommit.cSRestFrame` pattern). -/
def cCTARestFrame : Constraint := { lhs := .var vRestDigPreA, rhs := .var vRestDigPostA }
/-- Leg `A` frame-reuse gate (`StateCommit.cSFrameReuse` pattern). -/
def cCTAFrameReuse : Constraint := { lhs := .var vFrameDigPreA, rhs := .var vFrameDigPostA }
/-- Leg `A` moved-bind gate (`StateCommit.cSMovedBind` pattern). -/
def cCTAMovedBind : Constraint := { lhs := .var vMovedDigPostA, rhs := .var vMovedDigExpectedA }

/-- Leg `B` rest-frame gate. -/
def cCTBRestFrame : Constraint := { lhs := .var vRestDigPreB, rhs := .var vRestDigPostB }
/-- Leg `B` frame-reuse gate. -/
def cCTBFrameReuse : Constraint := { lhs := .var vFrameDigPreB, rhs := .var vFrameDigPostB }
/-- Leg `B` moved-bind gate. -/
def cCTBMovedBind : Constraint := { lhs := .var vMovedDigPostB, rhs := .var vMovedDigExpectedB }

/-- **The coordinated-turn circuit** — four public-input EQ gates plus six per-leg frame EQ gates
(two legs × the `StateCommit` rest/frame/moved trio). -/
def coordinatedTurnCircuit : ConstraintSystem :=
  [ cCTPubRootA, cCTPubRootB, cCTPubCharter, cCTPubBinding
  , cCTARestFrame, cCTAFrameReuse, cCTAMovedBind
  , cCTBRestFrame, cCTBFrameReuse, cCTBMovedBind ]

example : coordinatedTurnCircuit.length = 10 := rfl

/-! ## §4 — gate ↔ digest lemmas (circuit content under `encodeCoordinatedTurn`). -/

private abbrev enc := encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH

theorem ct_pub_rootA_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTPubRootA.holds (enc pub sA sB step sA' sB') ↔ legRootA sA.kernel step.bt = pub.rootA := by
  unfold Constraint.holds cCTPubRootA
  simp only [Expr.eval, encCT_vLegRootA, encCT_vPubRootA]

theorem ct_pub_rootB_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTPubRootB.holds (enc pub sA sB step sA' sB') ↔ legRootB sB.kernel step.bt = pub.rootB := by
  unfold Constraint.holds cCTPubRootB
  simp only [Expr.eval, encCT_vLegRootB, encCT_vPubRootA, encCT_vPubRootB]

theorem ct_pub_charter_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTPubCharter.holds (enc pub sA sB step sA' sB') ↔
      covenantH step.covenant (recChainedKernelView sA) (recChainedKernelView sB) = pub.charterHash := by
  unfold Constraint.holds cCTPubCharter
  simp only [Expr.eval, encCT_vCharterDig, encCT_vPubRootA, encCT_vPubCharterHash]

theorem ct_pub_binding_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTPubBinding.holds (enc pub sA sB step sA' sB') ↔ bindH step.bt step.bind = pub.bindingHash := by
  unfold Constraint.holds cCTPubBinding
  simp only [Expr.eval, encCT_vBindingDig, encCT_vPubBindingHash]

theorem ct_a_restframe_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTARestFrame.holds (enc pub sA sB step sA' sB') ↔ RH sA.kernel = RH sA'.kernel := by
  unfold Constraint.holds cCTARestFrame
  simp only [Expr.eval, encCT_vRestDigPreA, encCT_vRestDigPostA]

theorem ct_a_framereuse_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTAFrameReuse.holds (enc pub sA sB step sA' sB') ↔
      frameDigest CH compressN sA.kernel (halfOutCarrier sA.kernel step.bt)
        = frameDigest CH compressN sA'.kernel (halfOutCarrier sA.kernel step.bt) := by
  unfold Constraint.holds cCTAFrameReuse
  simp only [Expr.eval, encCT_vFrameDigPreA, encCT_vFrameDigPostA]

theorem ct_a_movedbind_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTAMovedBind.holds (enc pub sA sB step sA' sB') ↔
      movedDigest CH compress sA'.kernel.cell step.bt.srcA step.bt.srcA
        = movedDigest CH compress (recDebit sA.kernel.cell step.bt.srcA step.bt.amt) step.bt.srcA step.bt.srcA := by
  unfold Constraint.holds cCTAMovedBind
  simp only [Expr.eval, encCT_vMovedDigPostA, encCT_vMovedDigExpectedA]

theorem ct_b_restframe_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTBRestFrame.holds (enc pub sA sB step sA' sB') ↔ RH sB.kernel = RH sB'.kernel := by
  unfold Constraint.holds cCTBRestFrame
  simp only [Expr.eval, encCT_vRestDigPreB, encCT_vRestDigPostB]

theorem ct_b_framereuse_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTBFrameReuse.holds (enc pub sA sB step sA' sB') ↔
      frameDigest CH compressN sB.kernel (halfInCarrier sB.kernel step.bt)
        = frameDigest CH compressN sB'.kernel (halfInCarrier sB.kernel step.bt) := by
  unfold Constraint.holds cCTBFrameReuse
  simp only [Expr.eval, encCT_vFrameDigPreB, encCT_vFrameDigPostB]

theorem ct_b_movedbind_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTBMovedBind.holds (enc pub sA sB step sA' sB') ↔
      movedDigest CH compress sB'.kernel.cell step.bt.dstB step.bt.dstB
        = movedDigest CH compress (recCredit sB.kernel.cell step.bt.dstB step.bt.amt) step.bt.dstB step.bt.dstB := by
  unfold Constraint.holds cCTBMovedBind
  simp only [Expr.eval, encCT_vMovedDigPostB, encCT_vMovedDigExpectedB]

/-! ## §5 — circuit ⊑ Prop scaffold bridge + completeness on honest digests. -/

/-- **`coordinated_circuit_step_of_sat`** — polynomial satisfaction on the honest encoder yields the
Prop-level `coordinatedTurnCircuitStep` when the half-edge commits, well-formedness, and covenant
guard are supplied (the scaffold gates carry commit-sat + frame digest equalities). -/
theorem coordinated_circuit_step_of_sat
    (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState)
    (hwfA : AccountsWF sA.kernel) (hwfB : AccountsWF sB.kernel)
    (hwfA' : AccountsWF sA'.kernel) (hwfB' : AccountsWF sB'.kernel)
    (hOut : applyRecHalfOut sA.kernel step.bt = some sA'.kernel)
    (hIn : applyRecHalfIn sB.kernel step.bt = some sB'.kernel)
    (hφ : step.covenant.φ (recChainedKernelView sA) (recChainedKernelView sB) = true)
    (h : satisfied coordinatedTurnCircuit (enc pub sA sB step sA' sB')) :
    coordinatedTurnCircuitStep legRootA legRootB covenantH bindH CH RH compress compressN
      pub sA sB step sA' sB' := by
  unfold coordinatedTurnCircuitStep
  refine ⟨hwfA, hwfB, hwfA', hwfB', ?_, ?_, ?_, hφ⟩
  · exact ⟨
      (ct_pub_rootA_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mp
        (h cCTPubRootA (by unfold coordinatedTurnCircuit; simp)),
      (ct_pub_rootB_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mp
        (h cCTPubRootB (by unfold coordinatedTurnCircuit; simp)),
      (ct_pub_charter_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mp
        (h cCTPubCharter (by unfold coordinatedTurnCircuit; simp)),
      (ct_pub_binding_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mp
        (h cCTPubBinding (by unfold coordinatedTurnCircuit; simp)) ⟩
  · dsimp [CoordinatedLegFrameSat]
    exact ⟨hOut,
      (ct_a_restframe_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mp
        (h cCTARestFrame (by unfold coordinatedTurnCircuit; simp)),
      (ct_a_framereuse_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mp
        (h cCTAFrameReuse (by unfold coordinatedTurnCircuit; simp)),
      (ct_a_movedbind_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mp
        (h cCTAMovedBind (by unfold coordinatedTurnCircuit; simp)) ⟩
  · dsimp [CoordinatedLegFrameSat]
    exact ⟨hIn,
      (ct_b_restframe_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mp
        (h cCTBRestFrame (by unfold coordinatedTurnCircuit; simp)),
      (ct_b_framereuse_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mp
        (h cCTBFrameReuse (by unfold coordinatedTurnCircuit; simp)),
      (ct_b_movedbind_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mp
        (h cCTBMovedBind (by unfold coordinatedTurnCircuit; simp)) ⟩

/-- **`coordinated_circuit_complete_of_digests`** — COMPLETENESS on the honest encoder: digest
equalities + public-input alignment make every EQ gate hold by `rfl`. -/
theorem coordinated_circuit_complete_of_digests
    (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState)
    (hPub :
      pub.rootA = legRootA sA.kernel step.bt ∧
        pub.rootB = legRootB sB.kernel step.bt ∧
        pub.charterHash =
          covenantH step.covenant (recChainedKernelView sA) (recChainedKernelView sB) ∧
        pub.bindingHash = bindH step.bt step.bind)
    (hRestA : RH sA.kernel = RH sA'.kernel)
    (hRestB : RH sB.kernel = RH sB'.kernel)
    (hFrameA :
      frameDigest CH compressN sA.kernel (halfOutCarrier sA.kernel step.bt)
        = frameDigest CH compressN sA'.kernel (halfOutCarrier sA.kernel step.bt))
    (hFrameB :
      frameDigest CH compressN sB.kernel (halfInCarrier sB.kernel step.bt)
        = frameDigest CH compressN sB'.kernel (halfInCarrier sB.kernel step.bt))
    (hMovedA :
      movedDigest CH compress sA'.kernel.cell step.bt.srcA step.bt.srcA
        = movedDigest CH compress (recDebit sA.kernel.cell step.bt.srcA step.bt.amt) step.bt.srcA step.bt.srcA)
    (hMovedB :
      movedDigest CH compress sB'.kernel.cell step.bt.dstB step.bt.dstB
        = movedDigest CH compress (recCredit sB.kernel.cell step.bt.dstB step.bt.amt) step.bt.dstB step.bt.dstB) :
    satisfied coordinatedTurnCircuit (enc pub sA sB step sA' sB') := by
  unfold satisfied coordinatedTurnCircuit
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (ct_pub_rootA_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hPub.1
  · exact (ct_pub_rootB_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hPub.2.1
  · exact (ct_pub_charter_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hPub.2.2.1
  · exact (ct_pub_binding_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hPub.2.2.2
  · exact (ct_a_restframe_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hRestA
  · exact (ct_a_framereuse_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hFrameA
  · exact (ct_a_movedbind_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hMovedA
  · exact (ct_b_restframe_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hRestB
  · exact (ct_b_framereuse_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hFrameB
  · exact (ct_b_movedbind_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hMovedB

end Surface

/-! ## §6 — EMISSION: `emit` faithfulness. -/

/-- The AIR identity string the coordinated-turn wire form carries. -/
def coordinatedTurnAirName : String := "dregg-coordinated-turn-v1"

/-- **The emitted coordinated-turn circuit** — `coordinatedTurnCircuit` serialized via `CircuitEmit.emit`. -/
def emittedCoordinatedTurn : EmittedDescriptor :=
  emit coordinatedTurnAirName coordinatedTurnTraceWidth coordinatedTurnCircuit

/-- **`coordinated_emitted_refines_circuit`** — emit faithfulness: satisfying the emitted descriptor
is EXACTLY satisfying `coordinatedTurnCircuit`. -/
theorem coordinated_emitted_refines_circuit (a : Assignment) :
    satisfied coordinatedTurnCircuit a ↔ satisfiedEmitted emittedCoordinatedTurn a :=
  emit_faithful coordinatedTurnAirName coordinatedTurnTraceWidth coordinatedTurnCircuit a

/-- **`coordinated_emitted_refines_spec`** — SOUNDNESS: emitted polynomial satisfaction on the honest
encoder + half-edge commits / well-formedness / covenant guard ⇒ `BilateralTurnSpec`. Composes
`coordinated_emitted_refines_circuit` with `coordinated_circuit_step_of_sat` and
`coordinated_turn_circuit_refines_spec_honest`. -/
theorem coordinated_emitted_refines_spec
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (legRootA legRootB : RecordKernelState → BiTurn → ℤ)
    (covenantH : CoordinatedCaveat → KernelState → KernelState → ℤ)
    (bindH : (bt : BiTurn) → SharedBinding bt → ℤ)
    (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState)
    (hwfA : AccountsWF sA.kernel) (hwfB : AccountsWF sB.kernel)
    (hwfA' : AccountsWF sA'.kernel) (hwfB' : AccountsWF sB'.kernel)
    (hOut : applyRecHalfOut sA.kernel step.bt = some sA'.kernel)
    (hIn : applyRecHalfIn sB.kernel step.bt = some sB'.kernel)
    (hφ : step.covenant.φ (recChainedKernelView sA) (recChainedKernelView sB) = true)
    (hPub :
      pub.rootA = legRootA sA.kernel step.bt ∧
        pub.rootB = legRootB sB.kernel step.bt ∧
        pub.charterHash =
          covenantH step.covenant (recChainedKernelView sA) (recChainedKernelView sB) ∧
        pub.bindingHash = bindH step.bt step.bind)
    (hEmit : satisfiedEmitted emittedCoordinatedTurn
        (encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB')) :
    BilateralTurnSpec sA.kernel sB.kernel step sA'.kernel sB'.kernel := by
  let a := encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
  have hCircuit := (coordinated_emitted_refines_circuit a).mp hEmit
  have hstep := coordinated_circuit_step_of_sat CH RH compress compressN legRootA legRootB covenantH bindH
      pub sA sB step sA' sB' hwfA hwfB hwfA' hwfB' hOut hIn hφ hCircuit
  exact coordinated_turn_circuit_refines_spec_honest CH RH compress compressN legRootA legRootB
      covenantH bindH pub sA sB step sA' sB' hPub hstep

/-- Round-trip decode recovers the source circuit. -/
theorem decodeE_emittedCoordinatedTurn :
    decodeE emittedCoordinatedTurn = coordinatedTurnCircuit :=
  decodeE_emit coordinatedTurnAirName coordinatedTurnTraceWidth coordinatedTurnCircuit

/-- Canonical JSON wire string for the emitted coordinated-turn circuit. -/
def coordinatedTurnDescriptorJson : String := emitDescriptorJson emittedCoordinatedTurn

#guard emittedCoordinatedTurn.constraints.length == 10
#guard emittedCoordinatedTurn.traceWidth == coordinatedTurnTraceWidth
#guard emittedCoordinatedTurn.traceWidth == 20

/-! ## §7 — Demo `#guard`: honest demo forest step satisfies the emitted circuit. -/

/-- Toy leaf hash for the demo (balance projection, injective on live cells). -/
def chDemo : CellId → Value → ℤ := fun _ v => balOf v

/-- Toy rest hash: stable under single-cell debit/credit on committed half-edges. -/
def rhDemo : RecordKernelState → ℤ := fun k => (k.accounts.card : ℤ)

/-- Toy Merkle node / sponge (pairing and list sum). -/
def compressDemo : ℤ → ℤ → ℤ := fun a b => a * 1000 + b
def compressNDemo : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc + x) 0

/-- Abstract leg roots for the demo public-input bundle. -/
def legRootDemoA : RecordKernelState → BiTurn → ℤ := fun k _ => (k.accounts.card : ℤ) * 10
def legRootDemoB : RecordKernelState → BiTurn → ℤ := fun k _ => (k.accounts.card : ℤ) * 10 + 1

/-- Covenant / binding digests for the demo step. -/
def covenantHDemo (c : CoordinatedCaveat) (A B : KernelState) : ℤ :=
  if c.φ A B then 1 else 0
def bindHDemo (bt : BiTurn) (bind : SharedBinding bt) : ℤ := bind.sidOfA

/-- Honest public inputs for `demoForestStep`. -/
def demoPub : CoordinatedPublicInputs :=
  { rootA := legRootDemoA demoRecA.kernel demoStep.bt
  , rootB := legRootDemoB demoRecB.kernel demoStep.bt
  , charterHash := covenantHDemo demoStep.covenant (recChainedKernelView demoRecA) (recChainedKernelView demoRecB)
  , bindingHash := bindHDemo demoStep.bind }

def demoPostPair : RecChainedState × RecChainedState :=
  (execCoordinatedForestG demoForestStep).getD (demoRecA, demoRecB)

def demoPostA : RecChainedState := demoPostPair.1
def demoPostB : RecChainedState := demoPostPair.2

-- The emitted circuit ACCEPTS the honest demo witness (every gate decides true):
#guard decide (satisfiedEmitted emittedCoordinatedTurn
  (encodeCoordinatedTurn chDemo rhDemo compressDemo compressNDemo legRootDemoA legRootDemoB
    covenantHDemo bindHDemo demoPub demoRecA demoRecB demoStep demoPostA demoPostB))

/-! ## §8 — Axiom hygiene. -/

#assert_axioms ct_pub_rootA_iff
#assert_axioms ct_pub_rootB_iff
#assert_axioms ct_pub_charter_iff
#assert_axioms ct_pub_binding_iff
#assert_axioms ct_a_restframe_iff
#assert_axioms ct_a_framereuse_iff
#assert_axioms ct_a_movedbind_iff
#assert_axioms ct_b_restframe_iff
#assert_axioms ct_b_framereuse_iff
#assert_axioms ct_b_movedbind_iff
#assert_axioms coordinated_circuit_step_of_sat
#assert_axioms coordinated_circuit_complete_of_digests
#assert_axioms coordinated_emitted_refines_circuit
#assert_axioms coordinated_emitted_refines_spec
#assert_axioms decodeE_emittedCoordinatedTurn

end Dregg2.Circuit.CoordinatedTurnEmit