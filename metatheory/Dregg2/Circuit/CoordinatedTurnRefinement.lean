/-
# Dregg2.Circuit.CoordinatedTurnRefinement — Wave 1 inter-vat coordinated turn circuit scaffold.

Bridges the exec joint/charter layer (`CoordinatedForestGLift`, `JointCharterBridge`,
`CoordinatedForestGate`) to the circuit refinement tower (`Refinement`, `StateCommit`).

  exec coordinated forest  ⊑  `BilateralTurnSpec`  ⊑  circuit witness (Prop scaffold)

Wave 1 is Prop-level: per-leg abstract digest wires reuse the `StateCommit` frame pattern;
full `Expr` emission is a later wave. No `sorry`/`admit`/`axiom`.
-/
import Dregg2.Circuit.Refinement
import Dregg2.Circuit.StateCommit
import Dregg2.Exec.CoordinatedForestGLift
import Dregg2.Exec.JointCharterBridge
import Dregg2.Exec.CoordinatedForestGate
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.JointCell

namespace Dregg2.Circuit.CoordinatedTurnRefinement

open Dregg2.Authority
open Dregg2.Circuit
open Dregg2.Circuit.Refinement
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Transfer
open Dregg2.Exec
open Dregg2.Exec.CoordinatedCaveat (dischargeCoordinated coordinated_discharge_sound)
open Dregg2.Exec.CrossCaveat (jointApplyCaveated)
open Dregg2.Exec.CoordinatedForestGLift
open Dregg2.Exec.JointCharterBridge
open Dregg2.Exec.CoordinatedForestGate
open Dregg2.Exec.JointCell
open Dregg2.Exec.CrossVatCharter

/-! ## §1 — Declarative bilateral turn spec (matches `jointApplyRec` / `execBilateralCoordinated`). -/

/-- **`BilateralTurnSpec`** — declarative spec for a coordinated bilateral step over two record
kernels: covenant `φ` on the projected joint pre-view, atomic `jointApplyRec` commit, and CG-2
binding (`sidOfA = sidOfB`). Matches `execBilateralCoordinated` on `recordKernelView` and
`execCoordinatedForestG` on the kernel halves (logs are separate at the forest layer). -/
def BilateralTurnSpec (kA kB : RecordKernelState) (step : BilateralStep)
    (kA' kB' : RecordKernelState) : Prop :=
  step.covenant.φ (recordKernelView kA) (recordKernelView kB) ∧
  jointApplyRec kA kB step.bt = some (kA', kB') ∧
  step.bind.sidOfA = step.bind.sidOfB

/-- Kernel-carrier spec (the `execBilateralCoordinated` target). -/
def BilateralKernelTurnSpec (A B : KernelState) (step : BilateralStep)
    (A' B' : KernelState) : Prop :=
  step.covenant.φ A B ∧
  jointApply A B step.bt = some (A', B') ∧
  step.bind.sidOfA = step.bind.sidOfB

/-- Forest-layer spec: kernel spec + per-leg receipt logs unchanged (honest routing). -/
def CoordinatedTurnStep (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) : Prop :=
  BilateralTurnSpec sA.kernel sB.kernel step sA'.kernel sB'.kernel ∧
  sA'.log = sA.log ∧ sB'.log = sB.log

/-! ## §2 — Exec steps as relations. -/

/-- Executable coordinated-forest step over a `BilateralForestPairG`. -/
def coordinatedForestExecStep (pair : BilateralForestPairG) (g : BilateralForestStepG)
    (pair' : BilateralForestPairG) : Prop :=
  g.pair = pair ∧
  execCoordinatedForestG g = some (pair'.sA, pair'.sB)

/-- Executable bilateral equalizer step on projected kernel views. -/
def bilateralExecStep (A B : KernelState) (step : BilateralStep) (A' B' : KernelState) : Prop :=
  execBilateralCoordinated A B step = some (A', B')

/-- Executable charter discharge step. -/
def charterExecStep (ch : Charter) (A B : KernelState) (heightA heightB : Nat)
    (dA dB : Discharges Unit) (A' B' : KernelState) : Prop :=
  charterDischarge ch A B heightA heightB dA dB = some (A', B')

/-! ## §3 — Exec ⊑ spec refinements. -/

/-- **`jointApplyRec_of_halves`** — atomic bilateral record commit from per-leg half-edges. -/
theorem jointApplyRec_of_halves {kA kB kA' kB' : RecordKernelState} {bt : BiTurn}
    (hA : applyRecHalfOut kA bt = some kA') (hB : applyRecHalfIn kB bt = some kB') :
    jointApplyRec kA kB bt = some (kA', kB') := by
  unfold jointApplyRec
  rw [hA, hB]

/-- **`bilateral_kernel_exec_refines_spec`** — every committed `execBilateralCoordinated` step
satisfies `BilateralKernelTurnSpec`. -/
theorem bilateral_kernel_exec_refines_spec (A B A' B' : KernelState) (step : BilateralStep)
    (h : bilateralExecStep A B step A' B') :
    BilateralKernelTurnSpec A B step A' B' := by
  dsimp [bilateralExecStep, BilateralKernelTurnSpec] at h ⊢
  have hexec : dischargeCoordinated step.covenant A B step.bt = some (A', B') := by
    simpa [execBilateralCoordinated] using h
  have hsound := coordinated_discharge_sound step.covenant step.bind hexec
  obtain ⟨_, hcg2, hφ⟩ := hsound
  have hja : jointApply A B step.bt = some (A', B') := by
    unfold dischargeCoordinated jointApplyCaveated at hexec
    rw [if_pos hφ] at hexec
    exact hexec
  exact ⟨hφ, hja, hcg2⟩

/-- Characterisation of a committed `execCoordinatedForestG` step. -/
theorem execCoordinatedForestG_commit_iff (g : BilateralForestStepG) (sApost sBpost : RecChainedState) :
    execCoordinatedForestG g = some (sApost, sBpost) ↔
      g.step.covenant.φ (recChainedKernelView g.pair.sA) (recChainedKernelView g.pair.sB) ∧
        jointApplyRec g.pair.sA.kernel g.pair.sB.kernel g.step.bt
          = some (sApost.kernel, sBpost.kernel) ∧
          sApost.log = g.pair.sA.log ∧ sBpost.log = g.pair.sB.log := by
  constructor
  · intro h
    unfold execCoordinatedForestG at h
    by_cases hφ : g.step.covenant.φ (recChainedKernelView g.pair.sA) (recChainedKernelView g.pair.sB) = true
    · rw [if_pos hφ] at h
      rcases hrec : jointApplyRec g.pair.sA.kernel g.pair.sB.kernel g.step.bt
          with _ | ⟨kApost, kBpost⟩
      · simp [hrec] at h
      · simp only [hrec, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hsAeq, hsBeq⟩ := h
        have hkA := (congrArg RecChainedState.kernel hsAeq).symm
        have hkB := (congrArg RecChainedState.kernel hsBeq).symm
        have hsAlog := congrArg RecChainedState.log hsAeq
        have hsBlog := congrArg RecChainedState.log hsBeq
        exact And.intro hφ
          (And.intro (by simpa [hkA, hkB] using hrec) (And.intro hsAlog.symm hsBlog.symm))
    · simp [hφ] at h
  · rintro ⟨hφ, hrec, hsAlog, hsBlog⟩
    unfold execCoordinatedForestG
    rw [if_pos hφ, hrec]
    apply congr_arg some
    apply Prod.ext
    · obtain ⟨k, l⟩ := sApost
      dsimp at hsAlog ⊢
      rw [hsAlog.symm]
    · obtain ⟨k, l⟩ := sBpost
      dsimp at hsBlog ⊢
      rw [hsBlog.symm]

/-- **`coordinated_turn_refines_joint`** — every committed `execCoordinatedForestG` step satisfies
`CoordinatedTurnStep` (the forest routing spec). -/
theorem coordinated_turn_refines_joint (g : BilateralForestStepG) {sApost sBpost : RecChainedState}
    (h : execCoordinatedForestG g = some (sApost, sBpost)) :
    CoordinatedTurnStep g.pair.sA g.pair.sB g.step sApost sBpost := by
  obtain ⟨hφ, hrec, hsAlog, hsBlog⟩ := (execCoordinatedForestG_commit_iff g sApost sBpost).mp h
  exact ⟨⟨hφ, hrec, SharedBinding.agree g.step.bind⟩, hsAlog, hsBlog⟩

/-- **`coordinated_forest_refines_kernel_spec`** — forest commits refine the kernel-layer spec on
projected views (via `coordinated_forest_refines_bilateral`). -/
theorem coordinated_forest_refines_kernel_spec (g : BilateralForestStepG) {sA' sB' : RecChainedState}
    (h : execCoordinatedForestG g = some (sA', sB')) :
    BilateralKernelTurnSpec (recChainedKernelView g.pair.sA) (recChainedKernelView g.pair.sB) g.step
      (recChainedKernelView sA') (recChainedKernelView sB') := by
  have href := coordinated_forest_refines_bilateral g h
  simpa [bilateralExecStep] using
    bilateral_kernel_exec_refines_spec (recChainedKernelView g.pair.sA) (recChainedKernelView g.pair.sB)
      (recChainedKernelView sA') (recChainedKernelView sB') g.step href

/-! ## §4 — Charter ⊑ coordinated (reuses `JointCharterBridge`). -/

/-- **`charter_turn_refines_coordinated`** — every committed charter discharge is ALSO a committed
`execBilateralCoordinated` on the same covenant/turn (direct reuse of
`charter_refines_bilateral_coordinated`). -/
theorem charter_turn_refines_coordinated (ch : Charter) {A B A' B' : KernelState}
    (heightA heightB : Nat) (dA dB : Discharges Unit)
    (h : charterExecStep ch A B heightA heightB dA dB A' B') :
    bilateralExecStep A B (charterBilateral ch) A' B' := by
  unfold charterExecStep bilateralExecStep at *
  exact charter_refines_bilateral_coordinated ch heightA heightB dA dB h

/-- Charter discharge satisfies the kernel declarative spec. -/
theorem charter_turn_refines_spec (ch : Charter) {A B A' B' : KernelState}
    (heightA heightB : Nat) (dA dB : Discharges Unit)
    (h : charterExecStep ch A B heightA heightB dA dB A' B') :
    BilateralKernelTurnSpec A B (charterBilateral ch) A' B' :=
  bilateral_kernel_exec_refines_spec A B A' B' (charterBilateral ch)
    (charter_turn_refines_coordinated ch heightA heightB dA dB h)

/-! ## §5 — Circuit scaffold: public inputs + per-leg digest frame (Prop-level Wave 1). -/

/-- **Published public inputs** for an inter-vat coordinated turn proof: per-leg pre-state roots
and the cross-binding / charter digests carried on the wire. -/
structure CoordinatedPublicInputs where
  /-- Pre-state root commitment for vat `A`. -/
  rootA       : ℤ
  /-- Pre-state root commitment for vat `B`. -/
  rootB       : ℤ
  /-- Digest of the coordinated covenant `φ` on the joint pre-snapshot. -/
  charterHash : ℤ
  /-- Digest of the CG-2 `SharedBinding` (both halves agree on `sid`). -/
  bindingHash : ℤ

/-- Per-leg frame carrier: the live accounts minus the single cell the half-edge touches. -/
def halfOutCarrier (k : RecordKernelState) (bt : BiTurn) : Finset CellId :=
  k.accounts \ {bt.srcA}

def halfInCarrier (k : RecordKernelState) (bt : BiTurn) : Finset CellId :=
  k.accounts \ {bt.dstB}

/-- Abstract per-leg pre-root binding against the published public inputs. -/
def CoordinatedTurnCommitSat
    (legRootA legRootB : RecordKernelState → BiTurn → ℤ)
    (covenantH : Dregg2.Exec.CoordinatedCaveat.CoordinatedCaveat → KernelState → KernelState → ℤ)
    (bindH : ∀ {bt : BiTurn}, SharedBinding bt → ℤ)
    (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep) : Prop :=
  legRootA sA.kernel step.bt = pub.rootA ∧
  legRootB sB.kernel step.bt = pub.rootB ∧
  covenantH step.covenant (recChainedKernelView sA) (recChainedKernelView sB) = pub.charterHash ∧
  bindH step.bind = pub.bindingHash

/-- **Per-leg frame scaffold** — Prop-level digest equalities reusing the `StateCommit` frame
pattern: rest hash frozen, untouched-cell sponge reused, moved digest pins the half-edge cell map.
The executable half-edge commit is carried as the first conjunct (the positive path). -/
def CoordinatedLegFrameSat (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (k k' : RecordKernelState) (bt : BiTurn) (isA : Bool) : Prop :=
  if isA then
    applyRecHalfOut k bt = some k' ∧
    RH k = RH k' ∧
    frameDigest CH compressN k (halfOutCarrier k bt) = frameDigest CH compressN k' (halfOutCarrier k bt) ∧
    movedDigest CH compress k'.cell bt.srcA bt.srcA =
      movedDigest CH compress (recDebit k.cell bt.srcA bt.amt) bt.srcA bt.srcA
  else
    applyRecHalfIn k bt = some k' ∧
    RH k = RH k' ∧
    frameDigest CH compressN k (halfInCarrier k bt) = frameDigest CH compressN k' (halfInCarrier k bt) ∧
    movedDigest CH compress k'.cell bt.dstB bt.dstB =
      movedDigest CH compress (recCredit k.cell bt.dstB bt.amt) bt.dstB bt.dstB

/-- **`coordinatedTurnCircuitStep`** — Prop-level circuit acceptance: well-formedness, public-input
binding, per-leg frame witnesses, covenant guard on the joint pre-snapshot. -/
def coordinatedTurnCircuitStep
    (legRootA legRootB : RecordKernelState → BiTurn → ℤ)
    (covenantH : Dregg2.Exec.CoordinatedCaveat.CoordinatedCaveat → KernelState → KernelState → ℤ)
    (bindH : ∀ {bt : BiTurn}, SharedBinding bt → ℤ)
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState) : Prop :=
  AccountsWF sA.kernel ∧ AccountsWF sB.kernel ∧
  AccountsWF sA'.kernel ∧ AccountsWF sB'.kernel ∧
  CoordinatedTurnCommitSat legRootA legRootB covenantH bindH pub sA sB step ∧
  CoordinatedLegFrameSat CH RH compress compressN sA.kernel sA'.kernel step.bt true ∧
  CoordinatedLegFrameSat CH RH compress compressN sB.kernel sB'.kernel step.bt false ∧
  step.covenant.φ (recChainedKernelView sA) (recChainedKernelView sB)

/-- **`coordinated_turn_circuit_refines_spec`** — SOUNDNESS: a well-formed circuit witness implies
`BilateralTurnSpec`. Carries the standard Poseidon-CR portals (for the frame anti-ghost layer) plus
abstract leg-root / charter / binding injectivity portals on the public-input digests. -/
theorem coordinated_turn_circuit_refines_spec
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (legRootA legRootB : RecordKernelState → BiTurn → ℤ)
    (covenantH : Dregg2.Exec.CoordinatedCaveat.CoordinatedCaveat → KernelState → KernelState → ℤ)
    (bindH : ∀ {bt : BiTurn}, SharedBinding bt → ℤ)
    (hCompress : compressInjective compress) (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH) (hRest : RestHashIffFrame RH)
    (hLegA : Function.Injective (fun p : RecordKernelState × BiTurn => legRootA p.1 p.2))
    (hLegB : Function.Injective (fun p : RecordKernelState × BiTurn => legRootB p.1 p.2))
    (hCov : ∀ (c : Dregg2.Exec.CoordinatedCaveat.CoordinatedCaveat) A B,
      covenantH c A B = pubCharter → c.φ A B = true)
    (hBind : ∀ {bt} (bind : SharedBinding bt), bindH bind = pubBind → bind.sidOfA = bind.sidOfB)
    (pubCharter pubBind : ℤ)
    (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState)
    (h : coordinatedTurnCircuitStep legRootA legRootB covenantH bindH CH RH compress compressN
        pub sA sB step sA' sB') :
    BilateralTurnSpec sA.kernel sB.kernel step sA'.kernel sB'.kernel := by
  unfold coordinatedTurnCircuitStep CoordinatedTurnCommitSat CoordinatedLegFrameSat at h
  dsimp [CoordinatedLegFrameSat] at h
  obtain ⟨_, _, _, _, _, hframeA, hframeB, hφ⟩ := h
  rcases hframeA with ⟨hOut, _, _, _⟩
  rcases hframeB with ⟨hIn, _, _, _⟩
  exact ⟨by simpa [recChainedKernelView] using hφ, jointApplyRec_of_halves hOut hIn,
    SharedBinding.agree step.bind⟩

/-- Convenience: circuit soundness when public-input hashes are definitionally the honest values. -/
theorem coordinated_turn_circuit_refines_spec_honest
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (legRootA legRootB : RecordKernelState → BiTurn → ℤ)
    (covenantH : Dregg2.Exec.CoordinatedCaveat.CoordinatedCaveat → KernelState → KernelState → ℤ)
    (bindH : ∀ {bt : BiTurn}, SharedBinding bt → ℤ)
    (hCompress : compressInjective compress) (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH) (hRest : RestHashIffFrame RH)
    (pub : CoordinatedPublicInputs) (sA sB : RecChainedState) (step : BilateralStep)
    (sA' sB' : RecChainedState)
    (hPub : pub.rootA = legRootA sA.kernel step.bt ∧
      pub.rootB = legRootB sB.kernel step.bt ∧
      pub.charterHash =
        covenantH step.covenant (recChainedKernelView sA) (recChainedKernelView sB) ∧
      pub.bindingHash = bindH step.bind)
    (h : coordinatedTurnCircuitStep legRootA legRootB covenantH bindH CH RH compress compressN
        pub sA sB step sA' sB') :
    BilateralTurnSpec sA.kernel sB.kernel step sA'.kernel sB'.kernel := by
  unfold coordinatedTurnCircuitStep CoordinatedLegFrameSat at h
  dsimp [CoordinatedLegFrameSat] at h
  obtain ⟨_, _, _, _, _, hframeA, hframeB, hφ⟩ := h
  rcases hframeA with ⟨hOut, _, _, _⟩
  rcases hframeB with ⟨hIn, _, _, _⟩
  exact ⟨by simpa [recChainedKernelView] using hφ, jointApplyRec_of_halves hOut hIn,
    SharedBinding.agree step.bind⟩

/-- Circuit ⊑ spec aligned with exec: a circuit witness and a matching forest commit imply the same
`CoordinatedTurnStep` (kernel spec from the circuit; logs from the exec routing). -/
theorem coordinated_turn_circuit_exec_agree
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (legRootA legRootB : RecordKernelState → BiTurn → ℤ)
    (covenantH : Dregg2.Exec.CoordinatedCaveat.CoordinatedCaveat → KernelState → KernelState → ℤ)
    (bindH : ∀ {bt : BiTurn}, SharedBinding bt → ℤ)
    (hCompress : compressInjective compress) (hCompressN : compressNInjective compressN)
    (hLeaf : cellLeafInjective CH) (hRest : RestHashIffFrame RH)
    (hLegA : Function.Injective (fun p : RecordKernelState × BiTurn => legRootA p.1 p.2))
    (hLegB : Function.Injective (fun p : RecordKernelState × BiTurn => legRootB p.1 p.2))
    (hCov : ∀ (c : Dregg2.Exec.CoordinatedCaveat.CoordinatedCaveat) A B,
      covenantH c A B = pubCharter → c.φ A B = true)
    (hBind : ∀ {bt} (bind : SharedBinding bt), bindH bind = pubBind → bind.sidOfA = bind.sidOfB)
    (pubCharter pubBind : ℤ)
    (pub : CoordinatedPublicInputs) (g : BilateralForestStepG) {sA' sB' : RecChainedState}
    (hCircuit : coordinatedTurnCircuitStep legRootA legRootB covenantH bindH CH RH compress compressN
        pub g.pair.sA g.pair.sB g.step sA' sB')
    (hExec : execCoordinatedForestG g = some (sA', sB')) :
    BilateralTurnSpec g.pair.sA.kernel g.pair.sB.kernel g.step sA'.kernel sB'.kernel ∧
      CoordinatedTurnStep g.pair.sA g.pair.sB g.step sA' sB' := by
  refine ⟨
    coordinated_turn_circuit_refines_spec CH RH compress compressN legRootA legRootB covenantH bindH
      hCompress hCompressN hLeaf hRest hLegA hLegB hCov hBind pubCharter pubBind pub g.pair.sA
      g.pair.sB g.step sA' sB' hCircuit,
    coordinated_turn_refines_joint g hExec⟩

/-! ## §7 — Demo `#guard` witnesses (non-vacuity). -/

#guard ((execCoordinatedForestG demoForestStep).isSome)  --  exec commits on demo pair
#guard ((execCoordinatedForestG { pair := demoPairHigh, step := demoStep }).isSome) == false  --  teeth

#guard ((charterDischarge demoCharter sA sB 0 0 CrossVatCharter.noDischarges CrossVatCharter.noDischarges).isSome)  --  charter path live

/-! ## §8 — Axiom hygiene. -/

#assert_axioms execCoordinatedForestG_commit_iff
#assert_axioms jointApplyRec_of_halves
#assert_axioms bilateral_kernel_exec_refines_spec
#assert_axioms coordinated_turn_refines_joint
#assert_axioms coordinated_forest_refines_kernel_spec
#assert_axioms charter_turn_refines_coordinated
#assert_axioms charter_turn_refines_spec
#assert_axioms coordinated_turn_circuit_refines_spec
#assert_axioms coordinated_turn_circuit_refines_spec_honest
#assert_axioms coordinated_turn_circuit_exec_agree

end Dregg2.Circuit.CoordinatedTurnRefinement