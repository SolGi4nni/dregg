/-
# Dregg2.Circuit.TurnEmit — turn-level witnesses linked to per-effect emitted AIRs.

Maps each `FullActionA` constructor to its Inst AIR name (`actionAirName`), checks per-step
`StepEmittedSat` against a descriptor lookup, and folds whole-turn satisfaction (`turnEmittedSat`)
through an abstract root-compress chain (reusing `TurnWitness.foldStepRoots`). Soundness composes
per-step emitted→spec refinement (EffectRefinement diamonds where available, or generic circuit step)
to `turnSpec`, then to `execFullTurnA` via `ActionDispatch.execFullTurnA_iff_turnSpec`.

No `sorry`/`admit`/`native_decide`/`axiom`.
-/
import Dregg2.Circuit.TurnWitness
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.TurnRefinement
import Dregg2.Circuit.EffectRefinement
import Dregg2.Circuit.EffectEmitRegistry
import Dregg2.Circuit.Inst.mintA
import Dregg2.Circuit.Inst.burnA
import Dregg2.Exec.CircuitEmit

namespace Dregg2.Circuit.TurnEmit

open Dregg2.Circuit
open Dregg2.Circuit.TurnWitness
  (StepWitness TurnWitness stepWitnessDigest foldStepRoots turnWitnessSatisfies)
open Dregg2.Circuit.ActionDispatch
  (actionTag fullActionStep turnSpec turnSpec_eq_spec execFullTurnA_iff_turnSpec)
open Dregg2.Circuit.TurnRefinement (turnSpec_of_turnStateChain)
open Dregg2.Circuit.EffectEmitRegistry
  (effectEmitRegistry actionAirName unknownAirName actionAirNameCoverage registryCoverage)
open Dregg2.Circuit.Inst.MintA (mintAirName mintEmitted mintDescriptorJson)
open Dregg2.Circuit.Inst.BurnA (burnAirName burnEmitted burnDescriptorJson)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.CircuitEmit (EmittedDescriptor satisfiedEmitted emitDescriptorJson)

/-! ## §0 — decidability (for concrete `#guard`s / `#eval`s). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — `actionAirName` + registry (re-exported from `EffectEmitRegistry`). -/

/-! ## §2 — Descriptor lookup + per-step emitted satisfaction. -/

/-- AIR-name registry lookup: the Rust `lean_descriptor_air` registry portal. -/
abbrev DescriptorLookup := String → Option EmittedDescriptor

/-- Decode abstract wire bytes (`List ℤ`) into a circuit `Assignment` (out-of-range wires = 0). -/
def assignmentOf (ws : List ℤ) : Assignment :=
  fun v => ws.getD v 0

/-- **`stepEmittedSat`** / **`StepEmittedSat`** — one step's emitted witness: tag matches the action,
and the looked-up descriptor is satisfied on the step's assignment bytes. -/
def stepEmittedSat (lookup : DescriptorLookup) (sw : StepWitness)
    (_st _st' : RecChainedState) (fa : FullActionA) : Prop :=
  sw.tag = actionTag fa ∧
  ∃ d, lookup (actionAirName fa) = some d ∧
    satisfiedEmitted d (assignmentOf sw.assignment)

/-- Alias matching the Wave-1 naming convention (`StepEmittedSat`). -/
abbrev StepEmittedSat := stepEmittedSat

/-- **`descriptorLookup_of_actionAirName`** — when the registry resolves `actionAirName fa`, per-step
emitted satisfaction reduces to tag match + `satisfiedEmitted` on the resolved descriptor. -/
theorem descriptorLookup_of_actionAirName (lookup : DescriptorLookup) (fa : FullActionA)
    (d : EmittedDescriptor) (hlookup : lookup (actionAirName fa) = some d) :
    ∀ sw (st st' : RecChainedState), stepEmittedSat lookup sw st st' fa ↔
      sw.tag = actionTag fa ∧ satisfiedEmitted d (assignmentOf sw.assignment) := by
  intro sw st st'
  dsimp [stepEmittedSat]
  constructor
  · rintro ⟨htag, d', hfind, hsat⟩
    have : d' = d := Option.some.inj (hfind.symm.trans hlookup)
    subst this
    exact ⟨htag, hsat⟩
  · rintro ⟨htag, hsat⟩
    exact ⟨htag, d, hlookup, hsat⟩

/-! ## §3 — Default registry (central `EffectEmitRegistry`). -/

/-- **`defaultDescriptorLookup`** — the Wave-2 central registry (53 Inst/commit AIRs + coordinated). -/
abbrev defaultDescriptorLookup : DescriptorLookup := effectEmitRegistry

/-- Mint+burn demo lookup (alias of the default registry). -/
abbrev demoMintBurnLookup : DescriptorLookup := defaultDescriptorLookup

/-! ## §4 — Whole-turn emitted satisfaction (root chain + state chain + per-step emitted). -/

/-- **`TurnEmittedChain`** — turn-level emitted witness: boundary roots fold under `compress`
(`TurnWitness.foldStepRoots`), states chain left-to-right, and every step satisfies its emitted AIR. -/
structure TurnEmittedChain (lookup : DescriptorLookup) (compress : ℤ → ℤ → ℤ)
    (stepRoot : StepWitness → ℤ) (s : RecChainedState) (acts : List FullActionA)
    (s' : RecChainedState) (w : TurnWitness) where
  steps_len : acts.length = w.steps.length
  root_chain : turnWitnessSatisfies compress stepRoot w
  chain : List RecChainedState
  chain_len : chain.length = acts.length + 1
  chain_head : chain[0]'(by rw [chain_len]; omega) = s
  chain_last : chain[acts.length]'(by rw [chain_len]; omega) = s'
  step_sat :
    ∀ (i : Fin acts.length),
      stepEmittedSat lookup (w.steps[i]) (chain[i.val]'(by rw [chain_len]; omega))
        (chain[i.val + 1]'(by rw [chain_len]; omega)) acts[i]

/-- **`turnEmittedSat`** — alias for a bundled `TurnEmittedChain` (the turn emission portal). -/
abbrev turnEmittedSat (lookup : DescriptorLookup) (compress : ℤ → ℤ → ℤ)
    (stepRoot : StepWitness → ℤ) (s s' : RecChainedState) (acts : List FullActionA)
    (w : TurnWitness) : Prop :=
  Nonempty (TurnEmittedChain lookup compress stepRoot s acts s' w)

/-! ## §5 — Soundness: emitted turn ⊑ `turnSpec` ⊑ `execFullTurnA`. -/

/-- **`turn_emitted_refines_turnSpec`** — if each step's emitted witness refines `fullActionStep`
(via EffectRefinement diamonds where available, or a generic circuit-step hypothesis), the whole
turn refines `turnSpec`. -/
theorem turn_emitted_refines_turnSpec
    (lookup : DescriptorLookup)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat lookup sw st st' fa → fullActionStep st fa st')
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w) :
    turnSpec s acts s' :=
  (turnSpec_eq_spec s acts s').mpr <|
    turnSpec_of_turnStateChain fullActionStep s s' acts {
      chain := h.chain
      chain_len := h.chain_len
      chain_head := h.chain_head
      chain_last := h.chain_last
      step_witness := fun i => hstep _ _ _ _ (h.step_sat i) }

/-- **`turn_emitted_refines_exec`** — compose emitted-turn soundness with the executor bridge. -/
theorem turn_emitted_refines_exec
    (lookup : DescriptorLookup)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat lookup sw st st' fa → fullActionStep st fa st')
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w) :
    execFullTurnA s acts = some s' :=
  (execFullTurnA_iff_turnSpec s s' acts).mpr
    (turn_emitted_refines_turnSpec lookup hstep s s' acts w compress stepRoot h)

/-! ## §6 — Demo: mint + burn two-step turn via `defaultDescriptorLookup`. -/

/-- **`turn_emitted_demo_mint_burn`** — the default registry resolves mint and burn AIR identities
to their Inst-emitted descriptors (the two-step supply demo chain). -/
theorem turn_emitted_demo_mint_burn :
    defaultDescriptorLookup mintAirName = some mintEmitted ∧
    defaultDescriptorLookup burnAirName = some burnEmitted := ⟨rfl, rfl⟩

#eval actionAirName (.mintA 0 1 0 100)
#eval actionAirName (.burnA 0 1 0 50)
#eval defaultDescriptorLookup mintAirName |>.map (·.name)
#eval defaultDescriptorLookup burnAirName |>.map (·.name)
#eval defaultDescriptorLookup Dregg2.Circuit.Inst.Delegate.delegateAirName |>.map (·.name)
#eval defaultDescriptorLookup Dregg2.Circuit.Inst.ExerciseA.exerciseAAirName |>.map (·.name)

#guard (actionAirName (.mintA 0 1 0 100) == mintAirName)
#guard (actionAirName (.burnA 0 1 0 50) == burnAirName)
#guard (actionAirName (.balanceA ⟨0, 0, 1, 0⟩ 0) == Dregg2.Circuit.Inst.BalanceA.balanceAAirName)
#guard (actionAirName (.delegate 0 1 2) == Dregg2.Circuit.Inst.Delegate.delegateAirName)
#guard (actionAirName (.exerciseA 0 1 []) == Dregg2.Circuit.Inst.ExerciseA.exerciseAAirName)
#guard (actionAirName (.setFieldA 0 0 "balance" 0) == Dregg2.Circuit.SetFieldCommit.setFieldAirName)
#guard (actionAirName (.bridgeMintA 0 0 0 0) == mintAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup mintAirName) == some mintAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup burnAirName) == some burnAirName)
#guard (Option.map EmittedDescriptor.name (defaultDescriptorLookup Dregg2.Circuit.Inst.Delegate.delegateAirName) ==
  some Dregg2.Circuit.Inst.Delegate.delegateAirName)
#guard (Option.map EmittedDescriptor.name (demoMintBurnLookup mintAirName) == some mintAirName)
#guard (Option.map EmittedDescriptor.name (demoMintBurnLookup burnAirName) == some burnAirName)
#guard (burnDescriptorJson == emitDescriptorJson burnEmitted)
#guard (mintDescriptorJson == emitDescriptorJson mintEmitted)
#guard mintEmitted.name == mintAirName
#guard burnEmitted.name == burnAirName
#guard burnEmitted.traceWidth == 72
#guard (defaultDescriptorLookup unknownAirName == none)
#guard registryCoverage == 53

#assert_axioms descriptorLookup_of_actionAirName
#assert_axioms turn_emitted_demo_mint_burn
#assert_axioms turn_emitted_refines_turnSpec
#assert_axioms turn_emitted_refines_exec

end Dregg2.Circuit.TurnEmit