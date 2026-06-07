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
/-- Witness: covenant φ guard bit (`propBit` of `step.covenant.φ` on the joint pre-snapshot). -/
def vCovenantGuard   : Var := 20

/-- Coordinated-turn trace width: four public wires + sixteen witness digest columns + φ guard. -/
def coordinatedTurnTraceWidth : Nat := 21

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
  else if v = vCovenantGuard then
    propBit (step.covenant.φ (recChainedKernelView sA) (recChainedKernelView sB) = true)
  else 0

/-! ### Encoder wire lookups (collapse the `if`-cascade at each index). -/

theorem encCT_vPubRootA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vPubRootA = pub.rootA := by simp [encodeCoordinatedTurn, vPubRootA]

theorem encCT_vPubRootB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vPubRootB = pub.rootB := by
  simp [encodeCoordinatedTurn, vPubRootB, vPubRootA, vPubCharterHash, vPubBindingHash]

theorem encCT_vPubCharterHash (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vPubCharterHash = pub.charterHash := by
  simp [encodeCoordinatedTurn, vPubCharterHash, vPubRootB, vPubRootA, vPubBindingHash]

theorem encCT_vPubBindingHash (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vPubBindingHash = pub.bindingHash := by
  simp [encodeCoordinatedTurn, vPubBindingHash, vPubCharterHash, vPubRootB, vPubRootA]

theorem encCT_vLegRootA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vLegRootA = legRootA sA.kernel step.bt := by
  simp [encodeCoordinatedTurn, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

theorem encCT_vCharterDig (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vCharterDig =
        covenantH step.covenant (recChainedKernelView sA) (recChainedKernelView sB) := by
  simp [encodeCoordinatedTurn, vCharterDig, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

theorem encCT_vBindingDig (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vBindingDig = bindH step.bt step.bind := by
  simp [encodeCoordinatedTurn, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB,
    vPubCharterHash, vPubBindingHash]

theorem encCT_vRestDigPreA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vRestDigPreA = RH sA.kernel := by
  simp [encodeCoordinatedTurn, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB,
    vPubCharterHash, vPubBindingHash]

theorem encCT_vRestDigPostA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vRestDigPostA = RH sA'.kernel := by
  simp [encodeCoordinatedTurn, vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA,
    vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

theorem encCT_vFrameDigPreA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vFrameDigPreA = frameDigest CH compressN sA.kernel (halfOutCarrier sA.kernel step.bt) := by
  simp [encodeCoordinatedTurn, vFrameDigPreA, vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig,
    vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

theorem encCT_vFrameDigPostA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vFrameDigPostA = frameDigest CH compressN sA'.kernel (halfOutCarrier sA.kernel step.bt) := by
  simp [encodeCoordinatedTurn, vFrameDigPostA, vFrameDigPreA, vRestDigPostA, vRestDigPreA, vBindingDig,
    vCharterDig, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

theorem encCT_vMovedDigPostA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vMovedDigPostA = movedDigest CH compress sA'.kernel.cell step.bt.srcA step.bt.srcA := by
  simp [encodeCoordinatedTurn, vMovedDigPostA, vMovedDigExpectedA, vFrameDigPostA, vFrameDigPreA,
    vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB,
    vPubCharterHash, vPubBindingHash]

theorem encCT_vMovedDigExpectedA (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vMovedDigExpectedA =
        movedDigest CH compress (recDebit sA.kernel.cell step.bt.srcA step.bt.amt) step.bt.srcA step.bt.srcA := by
  simp [encodeCoordinatedTurn, vMovedDigExpectedA, vMovedDigPostA, vFrameDigPostA, vFrameDigPreA,
    vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB,
    vPubCharterHash, vPubBindingHash]

theorem encCT_vLegRootB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vLegRootB = legRootB sB.kernel step.bt := by
  simp [encodeCoordinatedTurn, vLegRootB, vMovedDigExpectedA, vMovedDigPostA, vFrameDigPostA, vFrameDigPreA,
    vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash,
    vPubBindingHash]

theorem encCT_vRestDigPreB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vRestDigPreB = RH sB.kernel := by
  simp [encodeCoordinatedTurn, vRestDigPreB, vLegRootB, vMovedDigExpectedA, vMovedDigPostA, vFrameDigPostA,
    vFrameDigPreA, vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB,
    vPubCharterHash, vPubBindingHash]

theorem encCT_vRestDigPostB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vRestDigPostB = RH sB'.kernel := by
  simp [encodeCoordinatedTurn, vRestDigPostB, vRestDigPreB, vLegRootB, vMovedDigExpectedA, vMovedDigPostA,
    vFrameDigPostA, vFrameDigPreA, vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA,
    vPubRootB, vPubCharterHash, vPubBindingHash]

theorem encCT_vFrameDigPreB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vFrameDigPreB = frameDigest CH compressN sB.kernel (halfInCarrier sB.kernel step.bt) := by
  simp [encodeCoordinatedTurn, vFrameDigPreB, vRestDigPostB, vRestDigPreB, vLegRootB, vMovedDigExpectedA,
    vMovedDigPostA, vFrameDigPostA, vFrameDigPreA, vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig,
    vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

theorem encCT_vFrameDigPostB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vFrameDigPostB = frameDigest CH compressN sB'.kernel (halfInCarrier sB.kernel step.bt) := by
  simp [encodeCoordinatedTurn, vFrameDigPostB, vFrameDigPreB, vRestDigPostB, vRestDigPreB, vLegRootB,
    vMovedDigExpectedA, vMovedDigPostA, vFrameDigPostA, vFrameDigPreA, vRestDigPostA, vRestDigPreA, vBindingDig,
    vCharterDig, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

theorem encCT_vMovedDigPostB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vMovedDigPostB = movedDigest CH compress sB'.kernel.cell step.bt.dstB step.bt.dstB := by
  simp [encodeCoordinatedTurn, vMovedDigPostB, vMovedDigExpectedB, vFrameDigPostB, vFrameDigPreB,
    vRestDigPostB, vRestDigPreB, vLegRootB, vMovedDigExpectedA, vMovedDigPostA, vFrameDigPostA, vFrameDigPreA,
    vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash,
    vPubBindingHash]

theorem encCT_vMovedDigExpectedB (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vMovedDigExpectedB =
        movedDigest CH compress (recCredit sB.kernel.cell step.bt.dstB step.bt.amt) step.bt.dstB step.bt.dstB := by
  simp [encodeCoordinatedTurn, vMovedDigExpectedB, vMovedDigPostB, vFrameDigPostB, vFrameDigPreB, vRestDigPostB,
    vRestDigPreB, vLegRootB, vMovedDigExpectedA, vMovedDigPostA, vFrameDigPostA, vFrameDigPreA, vRestDigPostA,
    vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash, vPubBindingHash]

theorem encCT_vCovenantGuard (pub : CoordinatedPublicInputs) (sA sB : RecChainedState)
    (step : BilateralStep) (sA' sB' : RecChainedState) :
    encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'
      vCovenantGuard =
        propBit (step.covenant.φ (recChainedKernelView sA) (recChainedKernelView sB) = true) := by
  simp [encodeCoordinatedTurn, vCovenantGuard, vMovedDigExpectedB, vMovedDigPostB, vFrameDigPostB, vFrameDigPreB,
    vRestDigPostB, vRestDigPreB, vLegRootB, vMovedDigExpectedA, vMovedDigPostA, vFrameDigPostA, vFrameDigPreA,
    vRestDigPostA, vRestDigPreA, vBindingDig, vCharterDig, vLegRootA, vPubRootA, vPubRootB, vPubCharterHash,
    vPubBindingHash]

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
/-- Covenant φ guard gate: `propBit (covenant.φ preA preB) = 1` (scaffold; full polynomial φ deferred). -/
def cCTCovenantGuard : Constraint := { lhs := .var vCovenantGuard, rhs := .const 1 }

/-- **The coordinated-turn circuit** — four public-input EQ gates, six per-leg frame EQ gates,
and the covenant φ guard bit gate. -/
def coordinatedTurnCircuit : ConstraintSystem :=
  [ cCTPubRootA, cCTPubRootB, cCTPubCharter, cCTPubBinding
  , cCTARestFrame, cCTAFrameReuse, cCTAMovedBind
  , cCTBRestFrame, cCTBFrameReuse, cCTBMovedBind
  , cCTCovenantGuard ]

example : coordinatedTurnCircuit.length = 11 := rfl

/-! ## §4 — gate ↔ digest lemmas (circuit content under `encodeCoordinatedTurn`). -/

def encCT (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) : Assignment :=
  encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB'

theorem ct_pub_rootA_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTPubRootA.holds (@encCT CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB') ↔
      legRootA sA.kernel step.bt = pub.rootA := by
  unfold Constraint.holds cCTPubRootA encCT
  simp only [Expr.eval, encCT_vLegRootA, encCT_vPubRootA]

theorem ct_pub_rootB_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTPubRootB.holds (@encCT CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB') ↔ legRootB sB.kernel step.bt = pub.rootB := by
  unfold Constraint.holds cCTPubRootB encCT
  simp only [Expr.eval, encCT_vLegRootB, encCT_vPubRootA, encCT_vPubRootB]

theorem ct_pub_charter_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTPubCharter.holds (@encCT CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB') ↔
      covenantH step.covenant (recChainedKernelView sA) (recChainedKernelView sB) = pub.charterHash := by
  unfold Constraint.holds cCTPubCharter encCT
  simp only [Expr.eval, encCT_vCharterDig, encCT_vPubRootA, encCT_vPubCharterHash]

theorem ct_pub_binding_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTPubBinding.holds (@encCT CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB') ↔ bindH step.bt step.bind = pub.bindingHash := by
  unfold Constraint.holds cCTPubBinding encCT
  simp only [Expr.eval, encCT_vBindingDig, encCT_vPubBindingHash]

theorem ct_a_restframe_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTARestFrame.holds (@encCT CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB') ↔ RH sA.kernel = RH sA'.kernel := by
  unfold Constraint.holds cCTARestFrame encCT
  simp only [Expr.eval, encCT_vRestDigPreA, encCT_vRestDigPostA]

theorem ct_a_framereuse_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTAFrameReuse.holds (@encCT CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB') ↔
      frameDigest CH compressN sA.kernel (halfOutCarrier sA.kernel step.bt)
        = frameDigest CH compressN sA'.kernel (halfOutCarrier sA.kernel step.bt) := by
  unfold Constraint.holds cCTAFrameReuse encCT
  simp only [Expr.eval, encCT_vFrameDigPreA, encCT_vFrameDigPostA]

theorem ct_a_movedbind_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTAMovedBind.holds (@encCT CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB') ↔
      movedDigest CH compress sA'.kernel.cell step.bt.srcA step.bt.srcA
        = movedDigest CH compress (recDebit sA.kernel.cell step.bt.srcA step.bt.amt) step.bt.srcA step.bt.srcA := by
  unfold Constraint.holds cCTAMovedBind encCT
  simp only [Expr.eval, encCT_vMovedDigPostA, encCT_vMovedDigExpectedA]

theorem ct_b_restframe_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTBRestFrame.holds (@encCT CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB') ↔ RH sB.kernel = RH sB'.kernel := by
  unfold Constraint.holds cCTBRestFrame encCT
  simp only [Expr.eval, encCT_vRestDigPreB, encCT_vRestDigPostB]

theorem ct_b_framereuse_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTBFrameReuse.holds (@encCT CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB') ↔
      frameDigest CH compressN sB.kernel (halfInCarrier sB.kernel step.bt)
        = frameDigest CH compressN sB'.kernel (halfInCarrier sB.kernel step.bt) := by
  unfold Constraint.holds cCTBFrameReuse encCT
  simp only [Expr.eval, encCT_vFrameDigPreB, encCT_vFrameDigPostB]

theorem ct_b_movedbind_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTBMovedBind.holds (@encCT CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB') ↔
      movedDigest CH compress sB'.kernel.cell step.bt.dstB step.bt.dstB
        = movedDigest CH compress (recCredit sB.kernel.cell step.bt.dstB step.bt.amt) step.bt.dstB step.bt.dstB := by
  unfold Constraint.holds cCTBMovedBind encCT
  simp only [Expr.eval, encCT_vMovedDigPostB, encCT_vMovedDigExpectedB]

theorem ct_covenant_guard_iff (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) :
    cCTCovenantGuard.holds (@encCT CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB') ↔
      step.covenant.φ (recChainedKernelView sA) (recChainedKernelView sB) = true := by
  unfold Constraint.holds cCTCovenantGuard encCT
  simp only [Expr.eval, encCT_vCovenantGuard, propBit]
  by_cases hφ : step.covenant.φ (recChainedKernelView sA) (recChainedKernelView sB) = true
  · simp [hφ]
  · simp [hφ]

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
    (h : satisfied coordinatedTurnCircuit (@encCT CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB')) :
    coordinatedTurnCircuitStep legRootA legRootB covenantH (fun {bt} bind => bindH bt bind) CH RH compress compressN
      pub sA sB step sA' sB' := by
  have hφ :=
    (ct_covenant_guard_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mp
      (h cCTCovenantGuard (by unfold coordinatedTurnCircuit; simp))
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
        = movedDigest CH compress (recCredit sB.kernel.cell step.bt.dstB step.bt.amt) step.bt.dstB step.bt.dstB)
    (hφ : step.covenant.φ (recChainedKernelView sA) (recChainedKernelView sB) = true) :
    satisfied coordinatedTurnCircuit (@encCT CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB') := by
  unfold satisfied coordinatedTurnCircuit
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (ct_pub_rootA_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hPub.1.symm
  · exact (ct_pub_rootB_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hPub.2.1.symm
  · exact (ct_pub_charter_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hPub.2.2.1.symm
  · exact (ct_pub_binding_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hPub.2.2.2.symm
  · exact (ct_a_restframe_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hRestA
  · exact (ct_a_framereuse_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hFrameA
  · exact (ct_a_movedbind_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hMovedA
  · exact (ct_b_restframe_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hRestB
  · exact (ct_b_framereuse_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hFrameB
  · exact (ct_b_movedbind_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hMovedB
  · exact (ct_covenant_guard_iff CH RH compress compressN legRootA legRootB covenantH bindH pub sA sB step sA' sB').mpr hφ

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
    (hCompress : compressInjective compress) (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH) (hRest : RestHashIffFrame RH)
    (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState)
    (hwfA : AccountsWF sA.kernel) (hwfB : AccountsWF sB.kernel)
    (hwfA' : AccountsWF sA'.kernel) (hwfB' : AccountsWF sB'.kernel)
    (hOut : applyRecHalfOut sA.kernel step.bt = some sA'.kernel)
    (hIn : applyRecHalfIn sB.kernel step.bt = some sB'.kernel)
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
  have hCircuit := (coordinated_emitted_refines_circuit a).mpr hEmit
  have hstep := coordinated_circuit_step_of_sat CH RH compress compressN legRootA legRootB covenantH bindH
      pub sA sB step sA' sB' hwfA hwfB hwfA' hwfB' hOut hIn hCircuit
  exact coordinated_turn_circuit_refines_spec_honest CH RH compress compressN legRootA legRootB
      covenantH (fun {bt} bind => bindH bt bind) hCompress hCompressN hLeaf hRest
      pub sA sB step sA' sB' hPub hstep

/-- Round-trip decode recovers the source circuit. -/
theorem decodeE_emittedCoordinatedTurn :
    decodeE emittedCoordinatedTurn = coordinatedTurnCircuit :=
  decodeE_emit coordinatedTurnAirName coordinatedTurnTraceWidth coordinatedTurnCircuit

/-- Canonical JSON wire string for the emitted coordinated-turn circuit. -/
def coordinatedTurnDescriptorJson : String := emitDescriptorJson emittedCoordinatedTurn

#guard emittedCoordinatedTurn.constraints.length == 11
#guard emittedCoordinatedTurn.traceWidth == coordinatedTurnTraceWidth
#guard emittedCoordinatedTurn.traceWidth == 21

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
  , bindingHash := bindHDemo demoStep.bt demoStep.bind }

def demoPostPair : RecChainedState × RecChainedState :=
  (execCoordinatedForestG demoForestStep).getD (demoRecA, demoRecB)

def demoPostA : RecChainedState := demoPostPair.1
def demoPostB : RecChainedState := demoPostPair.2

-- The circuit ACCEPTS the honest demo witness (every gate decides true):
#guard decide (satisfied coordinatedTurnCircuit
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
#assert_axioms ct_covenant_guard_iff
#assert_axioms coordinated_circuit_step_of_sat
#assert_axioms coordinated_circuit_complete_of_digests
#assert_axioms coordinated_emitted_refines_circuit
#assert_axioms coordinated_emitted_refines_spec
#assert_axioms decodeE_emittedCoordinatedTurn

/-! ## §9 — Wave 6 covenant-guard predicate + exec bridge (RecordKernelState lift CLOSED).

The two former Wave-6 portals (`hole_coordinated_covenant_guard` + `coordinated_emitted_refines_execCoordinatedForestG`'s
`sorry`) are now genuine proofs:

  * `coordinatedCovenantGuardHolds` is the covenant-`φ` guard as a named `Prop` (the single
    `vCovenantGuard` column). The former `hole_coordinated_covenant_guard : ∀ step sA sB, …guard…`
    was an UNPROVABLE universal (the covenant need NOT hold on an arbitrary triple) — it has been
    DELETED, not weakened. Instead `covenantGuard_of_emitted` EXTRACTS the guard from the satisfying
    witness: the `vCovenantGuard` polynomial column forces `φ = true` (anti-vacuity — a triple where
    `φ = false` has NO satisfying witness, see `covenantGuard_emitted_teeth`).
  * `coordinated_emitted_refines_execCoordinatedForestG` lifts to `execCoordinatedForestG` (the
    `RecordKernelState` step), consuming the extracted guard + the half-edge applies + the per-leg
    log-frame (the honest forest leaves receipt logs untouched). No `sorry`. -/

/-- Covenant φ guard as a named Prop (the single `vCovenantGuard` column). -/
def coordinatedCovenantGuardHolds (step : BilateralStep) (sA sB : RecChainedState) : Prop :=
  step.covenant.φ (recChainedKernelView sA) (recChainedKernelView sB) = true

/-- **`covenantGuard_of_emitted`** — EXTRACT the covenant guard from the satisfying witness. The
`vCovenantGuard` polynomial column constrains its wire to `propBit (φ …)` and gates it `= 1`, so any
satisfying assignment (on the honest encoder) forces `φ = true`. This replaces the former
unprovable `hole_coordinated_covenant_guard` universal: the guard is a CONSEQUENCE of satisfaction,
not an assumed fact. -/
theorem covenantGuard_of_emitted
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (legRootA legRootB : RecordKernelState → BiTurn → ℤ)
    (covenantH : CoordinatedCaveat → KernelState → KernelState → ℤ)
    (bindH : (bt : BiTurn) → SharedBinding bt → ℤ)
    (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState)
    (hEmit : satisfiedEmitted emittedCoordinatedTurn
        (encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub
          sA sB step sA' sB')) :
    coordinatedCovenantGuardHolds step sA sB := by
  have hCircuit :=
    (coordinated_emitted_refines_circuit
      (encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub
        sA sB step sA' sB')).mpr hEmit
  -- the `cCTCovenantGuard` gate is satisfied; its `iff` lemma yields `φ = true`.
  exact (ct_covenant_guard_iff CH RH compress compressN legRootA legRootB covenantH bindH
      pub sA sB step sA' sB').mp
    (hCircuit cCTCovenantGuard (by unfold coordinatedTurnCircuit; simp))

/-- **`covenantGuard_emitted_teeth`** — ANTI-VACUITY tooth. A step whose covenant `φ` is FALSE on the
joint pre-snapshot has NO satisfying witness on the honest encoder: the `vCovenantGuard` gate
rejects it. (Contrapositive of `covenantGuard_of_emitted`.) -/
theorem covenantGuard_emitted_teeth
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (legRootA legRootB : RecordKernelState → BiTurn → ℤ)
    (covenantH : CoordinatedCaveat → KernelState → KernelState → ℤ)
    (bindH : (bt : BiTurn) → SharedBinding bt → ℤ)
    (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState)
    (hφfalse : step.covenant.φ (recChainedKernelView sA) (recChainedKernelView sB) = false) :
    ¬ satisfiedEmitted emittedCoordinatedTurn
        (encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub
          sA sB step sA' sB') := by
  intro hEmit
  have hguard : coordinatedCovenantGuardHolds step sA sB :=
    covenantGuard_of_emitted CH RH compress compressN legRootA legRootB covenantH bindH
      pub sA sB step sA' sB' hEmit
  rw [coordinatedCovenantGuardHolds, hφfalse] at hguard
  exact Bool.noConfusion hguard

/-- **`coordinated_emitted_refines_execCoordinatedForestG`** — emitted coordinated-turn satisfaction
on the honest encoder COMMITS `execCoordinatedForestG` (the `RecordKernelState` step). The covenant
guard is EXTRACTED from the witness (`covenantGuard_of_emitted`), the half-edge applies are supplied,
and the per-leg logs are framed (the honest forest does not splice receipt logs). No `sorry`. -/
theorem coordinated_emitted_refines_execCoordinatedForestG
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (legRootA legRootB : RecordKernelState → BiTurn → ℤ)
    (covenantH : CoordinatedCaveat → KernelState → KernelState → ℤ)
    (bindH : (bt : BiTurn) → SharedBinding bt → ℤ)
    (g : BilateralForestStepG) {sA' sB' : RecChainedState}
    (pub : CoordinatedPublicInputs)
    (hOut : applyRecHalfOut g.pair.sA.kernel g.step.bt = some sA'.kernel)
    (hIn : applyRecHalfIn g.pair.sB.kernel g.step.bt = some sB'.kernel)
    (hLogA : sA'.log = g.pair.sA.log) (hLogB : sB'.log = g.pair.sB.log)
    (hEmit : satisfiedEmitted emittedCoordinatedTurn
        (encodeCoordinatedTurn CH RH compress compressN legRootA legRootB covenantH bindH pub
          g.pair.sA g.pair.sB g.step sA' sB')) :
    execCoordinatedForestG g = some (sA', sB') := by
  have hφ : g.step.covenant.φ (recChainedKernelView g.pair.sA) (recChainedKernelView g.pair.sB) = true :=
    covenantGuard_of_emitted CH RH compress compressN legRootA legRootB covenantH bindH
      pub g.pair.sA g.pair.sB g.step sA' sB' hEmit
  unfold execCoordinatedForestG jointApplyRec
  rw [if_pos hφ, hOut, hIn]
  -- the committed pair is `({kernel := sA'.kernel, log := sA.log}, {kernel := sB'.kernel, log := sB.log})`;
  -- frame the logs back to the witnessed post-states (logs are unchanged by the honest forest).
  rw [← hLogA, ← hLogB]

#assert_axioms covenantGuard_of_emitted
#assert_axioms covenantGuard_emitted_teeth
#assert_axioms coordinated_emitted_refines_execCoordinatedForestG

end Dregg2.Circuit.CoordinatedTurnEmit