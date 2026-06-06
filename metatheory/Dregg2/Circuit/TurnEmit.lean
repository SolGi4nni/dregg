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
import Dregg2.Circuit.EffectEmittedRefinement
import Dregg2.Circuit.EffectEmitRegistry
import Dregg2.Circuit.TurnEffectRefinement
import Dregg2.Circuit.Inst.mintA
import Dregg2.Circuit.Inst.burnA
import Dregg2.Exec.CircuitEmit

set_option maxHeartbeats 800000

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
open Dregg2.Authority
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.EffectCommit2 (encodeE2)
open Dregg2.Circuit.EffectCommit2Dual (encodeE2Dual)
open Dregg2.Circuit.EffectCommit3 (encodeE2Triple)
open Dregg2.Circuit.EffectCommit5 (encodeE2Quint)
open Dregg2.Circuit.EffectCommit (encodeE)
open Dregg2.Circuit.EffectInstances (setFieldE)
open Dregg2.Exec.CircuitEmit (EmittedDescriptor satisfiedEmitted emitDescriptorJson)
open Dregg2.Circuit.EffectEmittedRefinement
open Dregg2.Circuit.TurnEffectRefinement (fullActionCircuitStepInst fullAction_circuit_refines_spec)
open Dregg2.Circuit.StateCommit
  (logHashInjective compressNInjective RestHashIffFrame AccountsWF cellLeafInjective)
open Dregg2.Circuit.EffectCommit (CommitSurface)
open Dregg2.Circuit.EffectCommit2 (Surface2 RestIffNoBal RestIffNoNullifiers)
open Dregg2.Circuit.EffectCommit2Dual (RestIffNoBalEscrows)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.Inst.Delegate (RestIffNoCaps)
open Dregg2.Circuit.Inst.CreateCellA (RestIffNoAccountsBalBorn)
open Dregg2.Circuit.Inst.SpawnA (RestIffNoSpawnTouched)
open Dregg2.Circuit.Inst.NoteCreateA (RestIffNoCommitments)
open Dregg2.Circuit.Inst.SealA (RestIffNoSealedBoxes)
open Dregg2.Circuit.Inst.QueueEnqueueA (RestIffNoQueuesBalEscrows)

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

/-! ## §5b — Per-step emitted ⊑ `fullActionStep` (registry + honest encoder). -/

/-- `RestIffNoCaps` is duplicated per Inst module; bridge Delegate's portal to Revoke's for dispatch. -/
private theorem restIffNoCaps_delegate_to_revoke (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.Revoke.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.Revoke.RestIffNoCaps]
  exact h

/-- **`stepEmittedEncodeAgrees`** — the step witness bytes are the honest encoder for `(st, fa, st')`. -/
def stepEmittedEncodeAgrees
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (LE_sealed : SealedBoxRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow) (hLE_sealed : listLeafInjective LE_sealed)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ)
    (CS : CommitSurface)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA) : Prop :=
  match fa with
  | .balanceA t a =>
      assignmentOf sw.assignment = encodeE2 S (balanceAE D_bal hD_bal) st ⟨t, a⟩ st'
  | .delegate del rec t =>
      assignmentOf sw.assignment = encodeE2 S (delegateE D_caps hD_caps) st ⟨del, rec, t⟩ st'
  | .mintA actor cell a amt =>
      assignmentOf sw.assignment = encodeE2 S (mintE D_bal hD_bal) st ⟨actor, cell, a, amt⟩ st'
  | .burnA actor cell a amt =>
      assignmentOf sw.assignment = encodeE2 S (burnE D_bal hD_bal) st ⟨actor, cell, a, amt⟩ st'
  | .introduceA intro rec t =>
      assignmentOf sw.assignment = encodeE2 S (delegateE D_caps hD_caps) st ⟨intro, rec, t⟩ st'
  | .validateHandoffA intro rec t =>
      assignmentOf sw.assignment = encodeE2 S (delegateE D_caps hD_caps) st ⟨intro, rec, t⟩ st'
  | .createCellA actor newCell =>
      assignmentOf sw.assignment =
        encodeE2Triple S (createCellE LE_cell cN hN hLE_cell DBal hDBal DSide hDSide) st
          ⟨actor, newCell⟩ st'
  | .spawnA actor child target =>
      assignmentOf sw.assignment =
        encodeE2Quint S (spawnE LE_cell cN hN hLE_cell DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) st
          ⟨actor, child, target⟩ st'
  | .bridgeMintA actor cell a value =>
      assignmentOf sw.assignment = encodeE2 S (mintE D_bal hD_bal) st ⟨actor, cell, a, value⟩ st'
  | .createEscrowA id actor creator recipient asset amount =>
      assignmentOf sw.assignment =
        encodeE2Dual S (createEscrowE D_bal hD_bal LE_escrow cN hN hLE_escrow) st
          ⟨id, actor, creator, recipient, asset, amount⟩ st'
  | .noteSpendA nf actor =>
      assignmentOf sw.assignment =
        encodeE2 S (noteSpendE LE_null cN hN hLE_null) st ⟨nf, actor⟩ st'
  | .noteCreateA cm actor =>
      assignmentOf sw.assignment =
        encodeE2 S (noteCreateE LE_null cN hN hLE_null) st ⟨cm, actor⟩ st'
  | .releaseEscrowA id actor =>
      assignmentOf sw.assignment =
        encodeE2Dual S (releaseEscrowE D_bal hD_bal LE_escrow cN hN hLE_escrow) st ⟨id, actor⟩ st'
  | .refundEscrowA id actor =>
      assignmentOf sw.assignment =
        encodeE2Dual S (refundEscrowE D_bal hD_bal LE_escrow cN hN hLE_escrow) st ⟨id, actor⟩ st'
  | .fulfillObligationA id actor =>
      assignmentOf sw.assignment =
        encodeE2Dual S (refundEscrowE D_bal hD_bal LE_escrow cN hN hLE_escrow) st ⟨id, actor⟩ st'
  | .slashObligationA id actor =>
      assignmentOf sw.assignment =
        encodeE2Dual S (releaseEscrowE D_bal hD_bal LE_escrow cN hN hLE_escrow) st ⟨id, actor⟩ st'
  | .revoke holder t =>
      assignmentOf sw.assignment = encodeE2 S (revokeE D_caps hD_caps) st ⟨holder, t⟩ st'
  | .dropRefA holder t =>
      assignmentOf sw.assignment = encodeE2 S (revokeE D_caps hD_caps) st ⟨holder, t⟩ st'
  | .revokeDelegationA holder t =>
      assignmentOf sw.assignment = encodeE2 S (revokeE D_caps hD_caps) st ⟨holder, t⟩ st'
  | .sealA pid actor payload =>
      assignmentOf sw.assignment =
        encodeE2 S (sealE LE_sealed cN hN hLE_sealed) st ⟨pid, actor, payload⟩ st'
  | .bridgeLockA id actor originator destination asset amount =>
      assignmentOf sw.assignment =
        encodeE2Dual S (bridgeLockE D_bal hD_bal LE_escrow cN hN hLE_escrow) st
          ⟨id, actor, originator, destination, asset, amount⟩ st'
  | .queueEnqueueA id m actor cell depId dAsset deposit =>
      assignmentOf sw.assignment =
        encodeE2Triple S (queueEnqueueE D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow) st
          ⟨id, m, actor, cell, depId, dAsset, deposit⟩ st'
  | .setFieldA actor cell f v =>
      assignmentOf sw.assignment = encodeE S CS setFieldE st ⟨actor, cell, f, v⟩ st'
  | fa' =>
      assignmentOf sw.assignment = assignmentOf sw.assignment ∧ fa' = fa'

/-- **`step_emitted_refines_fullActionStep`** — `stepEmittedSat` on the central registry + honest
encoder refines to `fullActionStep` for every effect with an emitted diamond; other arms defer to
the circuit dispatch (`fullAction_circuit_refines_spec`). -/
theorem step_emitted_refines_fullActionStep
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (LE_sealed : SealedBoxRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow) (hLE_sealed : listLeafInjective LE_sealed)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ)
    (CS : CommitSurface)
    (hCSN : compressNInjective CS.compressN) (hCSL : cellLeafInjective CS.CH)
    (hRestFrame : RestHashIffFrame CS.RH) (hLogCS : logHashInjective CS.LH)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH) (hRestEscrow : RestIffNoBalEscrows S.RH)
    (hRestCommitments : RestIffNoCommitments S.RH) (hRestSealed : RestIffNoSealedBoxes S.RH)
    (hRestQueues : RestIffNoQueuesBalEscrows S.RH)
    (hLog : logHashInjective S.LH)
    (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA)
    (h : stepEmittedSat defaultDescriptorLookup sw st st' fa)
    (hEnc : stepEmittedEncodeAgrees S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow LE_sealed
      cN hN hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS DBal hDBal DSide hDSide DLeg hDLeg
      DCaps hDCaps DDel hDDel DDgs hDDgs sw st st' fa)
    (hcircuit :
      fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow LE_sealed cN hN
        hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS DBal hDBal DSide hDSide DLeg hDLeg
        DCaps hDCaps DDel hDDel DDgs hDDgs st fa st') :
    fullActionStep st fa st' := by
  unfold stepEmittedEncodeAgrees at hEnc
  unfold fullActionCircuitStepInst at hcircuit
  rcases h with ⟨htag, d, hlookup, hsat⟩
  match fa with
  | .balanceA t a =>
      simp only [fullActionStep]
      exact balanceA_emitted_refines_spec S D_bal hD_bal hRestBal hLog st _ st'
        ((balanceA_emitted_equiv_circuit S D_bal hD_bal st _ st').mpr
          (by simpa [hEnc, balanceAEmittedStep, effect2EmittedStepLocal] using hsat))
  | .delegate del rec t =>
      simp only [fullActionStep]
      exact delegate_emitted_refines_spec S D_caps hD_caps hRestCaps hLog st _ st'
        ((delegate_emitted_equiv_circuit S D_caps hD_caps st _ st').mpr
          (by simpa [hEnc, delegateEmittedStep, effect2EmittedStepLocal] using hsat))
  | .mintA actor cell a amt =>
      simp only [fullActionStep]
      exact mint_emitted_refines_spec S D_bal hD_bal hRestBal hLog st _ st'
        ((mint_emitted_equiv_circuit S D_bal hD_bal st _ st').mpr
          (by simpa [hEnc, mintEmittedStep, effect2EmittedStepLocal] using hsat))
  | .burnA actor cell a amt =>
      simp only [fullActionStep]
      exact burn_emitted_refines_spec S D_bal hD_bal hRestBal hLog st _ st'
        ((burn_emitted_equiv_circuit S D_bal hD_bal st _ st').mpr
          (by simpa [hEnc, burnEmittedStep, effect2EmittedStepLocal] using hsat))
  | .introduceA intro rec t =>
      simp only [fullActionStep]
      exact delegate_emitted_refines_spec S D_caps hD_caps hRestCaps hLog st _ st'
        ((delegate_emitted_equiv_circuit S D_caps hD_caps st _ st').mpr
          (by simpa [hEnc, delegateEmittedStep, effect2EmittedStepLocal] using hsat))
  | .validateHandoffA intro rec t =>
      simp only [fullActionStep]
      exact delegate_emitted_refines_spec S D_caps hD_caps hRestCaps hLog st _ st'
        ((delegate_emitted_equiv_circuit S D_caps hD_caps st _ st').mpr
          (by simpa [hEnc, delegateEmittedStep, effect2EmittedStepLocal] using hsat))
  | .createCellA actor newCell =>
      simp only [fullActionStep]
      exact createCell_emitted_refines_spec S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide hRestAccounts
        hLog st _ st'
        ((createCell_emitted_equiv_circuit S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide st _ st').mpr
          (by simpa [hEnc, createCellEmittedStep, effect2tripleEmittedStepLocal] using hsat))
  | .spawnA actor child target =>
      simp only [fullActionStep]
      exact spawn_emitted_refines_spec S LE_cell cN hN hLE_cell DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs
        hRestSpawn hLog st _ st'
        ((spawn_emitted_equiv_circuit S LE_cell cN hN hLE_cell DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs
            st _ st').mpr
          (by simpa [hEnc, spawnEmittedStep, effect2quintEmittedStepLocal] using hsat))
  | .bridgeMintA actor cell a value =>
      simp only [fullActionStep]
      exact mint_emitted_refines_spec S D_bal hD_bal hRestBal hLog st _ st'
        ((mint_emitted_equiv_circuit S D_bal hD_bal st _ st').mpr
          (by simpa [hEnc, mintEmittedStep, effect2EmittedStepLocal] using hsat))
  | .createEscrowA id actor creator recipient asset amount =>
      simp only [fullActionStep]
      exact createEscrow_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog st _ st'
        ((createEscrow_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st _ st').mpr
          (by simpa [hEnc, createEscrowEmittedStep, effect2dualEmittedStepLocal] using hsat))
  | .noteSpendA nf actor =>
      simp only [fullActionStep]
      exact noteSpend_emitted_refines_spec S LE_null cN hN hLE_null hRestNull hLog st _ st'
        ((noteSpend_emitted_equiv_circuit S LE_null cN hN hLE_null st _ st').mpr
          (by simpa [hEnc, noteSpendEmittedStep, effect2EmittedStepLocal] using hsat))
  | .noteCreateA cm actor =>
      simp only [fullActionStep]
      exact noteCreate_emitted_refines_spec S LE_null cN hN hLE_null hRestCommitments hLog st _ st'
        ((noteCreate_emitted_equiv_circuit S LE_null cN hN hLE_null st _ st').mpr
          (by simpa [hEnc, noteCreateEmittedStep, effect2EmittedStepLocal] using hsat))
  | .revoke holder t =>
      simp only [fullActionStep]
      exact revoke_emitted_refines_spec S D_caps hD_caps (restIffNoCaps_delegate_to_revoke S.RH hRestCaps) hLog
        st _ st'
        ((revoke_emitted_equiv_circuit S D_caps hD_caps st _ st').mpr
          (by simpa [hEnc, revokeEmittedStep, effect2EmittedStepLocal] using hsat))
  | .setFieldA actor cell f v =>
      simp only [fullActionStep]
      rcases hcircuit with ⟨hwf, hwf', hc⟩
      exact setField_emitted_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf'
        ((setField_emitted_equiv_circuit CS st _ st').mpr
          (by simpa [hEnc, setFieldEmittedStep, effect1EmittedStepLocal] using hsat))
  | .dropRefA holder t =>
      simp only [fullActionStep]
      exact revoke_emitted_refines_spec S D_caps hD_caps (restIffNoCaps_delegate_to_revoke S.RH hRestCaps) hLog
        st _ st'
        ((revoke_emitted_equiv_circuit S D_caps hD_caps st _ st').mpr
          (by simpa [hEnc, revokeEmittedStep, effect2EmittedStepLocal] using hsat))
  | .revokeDelegationA holder t =>
      simp only [fullActionStep]
      exact revoke_emitted_refines_spec S D_caps hD_caps (restIffNoCaps_delegate_to_revoke S.RH hRestCaps) hLog
        st _ st'
        ((revoke_emitted_equiv_circuit S D_caps hD_caps st _ st').mpr
          (by simpa [hEnc, revokeEmittedStep, effect2EmittedStepLocal] using hsat))
  | .releaseEscrowA id actor =>
      simp only [fullActionStep]
      exact releaseEscrow_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st _ st'
        ((releaseEscrow_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st _ st').mpr
          (by simpa [hEnc, releaseEscrowEmittedStep, effect2dualEmittedStepLocal] using hsat))
  | .refundEscrowA id actor =>
      simp only [fullActionStep]
      exact refundEscrow_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st _ st'
        ((refundEscrow_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st _ st').mpr
          (by simpa [hEnc, refundEscrowEmittedStep, effect2dualEmittedStepLocal] using hsat))
  | .fulfillObligationA id actor =>
      simp only [fullActionStep]
      exact refundEscrow_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st _ st'
        ((refundEscrow_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st _ st').mpr
          (by simpa [hEnc, refundEscrowEmittedStep, effect2dualEmittedStepLocal] using hsat))
  | .slashObligationA id actor =>
      simp only [fullActionStep]
      exact releaseEscrow_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st _ st'
        ((releaseEscrow_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st _ st').mpr
          (by simpa [hEnc, releaseEscrowEmittedStep, effect2dualEmittedStepLocal] using hsat))
  | .bridgeLockA id actor originator destination asset amount =>
      simp only [fullActionStep]
      exact bridgeLock_emitted_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog st _ st'
        ((bridgeLock_emitted_equiv_circuit S D_bal hD_bal LE_escrow cN hN hLE_escrow st _ st').mpr
          (by simpa [hEnc, bridgeLockEmittedStep, effect2dualEmittedStepLocal] using hsat))
  | .sealA pid actor payload =>
      simp only [fullActionStep]
      exact seal_emitted_refines_spec S LE_sealed cN hN hLE_sealed hRestSealed hLog st _ st'
        ((seal_emitted_equiv_circuit S LE_sealed cN hN hLE_sealed st _ st').mpr
          (by simpa [hEnc, sealEmittedStep, effect2EmittedStepLocal] using hsat))
  | .queueEnqueueA id m actor cell depId dAsset deposit =>
      simp only [fullActionStep]
      exact queueEnqueue_emitted_refines_spec S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow
        hRestQueues hLog st _ st'
        ((queueEnqueue_emitted_equiv_circuit S D_bal hD_bal LQ cNQ hNQ hLQ LE_escrow cN hN hLE_escrow st _ st').mpr
          (by simpa [hEnc, queueEnqueueEmittedStep, effect2tripleEmittedStepLocal] using hsat))
  | fa' =>
      exact fullAction_circuit_refines_spec S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow LE_sealed
        cN hN hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS hCSN hCSL hRestFrame hLogCS DBal hDBal
        DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRestBal hRestAccounts hRestSpawn hRestCaps
        hRestNull hRestEscrow hRestCommitments hRestSealed hRestQueues hLog st fa' st' hcircuit

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
#assert_axioms step_emitted_refines_fullActionStep

end Dregg2.Circuit.TurnEmit