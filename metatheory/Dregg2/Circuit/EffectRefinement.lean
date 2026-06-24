/-
# Dregg2.Circuit.EffectRefinement — the v2 effect diamond: circuit ⟺ spec ⟺ executor.

Extends `Refinement.lean`'s tower to v2 single-component effects. The generic layer proves
`effect2CircuitStep ⟺ apex` and `emitted ⟺ circuit` for ANY `EffectSpec2`; concrete instances
(mint, burn, …) compose with their executor⟺spec bridges for the full diamond down to `execFullA`
and the Plonky3 wire bytes.
-/
import Dregg2.Circuit.Refinement
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.EffectCommit3
import Dregg2.Circuit.EffectCommit5
import Dregg2.Circuit.BornEmptyCommit
import Dregg2.Circuit.ListCommit
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Circuit.Inst.mintA
import Dregg2.Circuit.Inst.burnA
import Dregg2.Circuit.Inst.transfer
import Dregg2.Circuit.Inst.balanceA
import Dregg2.Circuit.Inst.delegate
import Dregg2.Circuit.Inst.noteSpendA
import Dregg2.Circuit.Inst.createCellA
import Dregg2.Circuit.Inst.spawnA
import Dregg2.Circuit.Inst.noteCreateA
import Dregg2.Circuit.Inst.revoke
import Dregg2.Circuit.Inst.revokeDelegationFullA
import Dregg2.Circuit.EffectCommit
import Dregg2.Circuit.EffectInstances
import Dregg2.Circuit.Inst.exerciseA
import Dregg2.Circuit.Spec.exercise

namespace Dregg2.Circuit.EffectRefinement

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit3
open Dregg2.Circuit.EffectCommit5
open Dregg2.Authority
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Refinement (Refines Equiv StepRel)
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.Inst.MintA
open Dregg2.Circuit.Inst.BurnA
open Dregg2.Circuit.Inst.Delegate
open Dregg2.Circuit.Inst.NoteSpendA
open Dregg2.Circuit.Inst.CreateCellA
open Dregg2.Circuit.Inst.SpawnA
open Dregg2.Circuit.Inst.NoteCreateA
open Dregg2.Circuit.Inst.Revoke
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.EffectInstances
open Dregg2.Circuit.Inst.ExerciseA
open Dregg2.Circuit.Spec.Exercise
open Dregg2.Circuit.ActionDispatch
open Dregg2.Circuit.Spec.SupplyCreation
open Dregg2.Circuit.Spec.SupplyDestruction
open Dregg2.Circuit.Spec.AccountGrowth
open Dregg2.Circuit.Spec.BalanceMovement
open Dregg2.Circuit.Spec.AuthorityUnattenuated
open Dregg2.Circuit.Spec.NoteNullifier
open Dregg2.Circuit.Spec.NoteCommitment
open Dregg2.Circuit.Spec.AuthorityRevocation
open Dregg2.Circuit.Spec.CellStateField
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — Generic v2 refinement (any `EffectSpec2`). -/

section GenericEffect2
variable {St Args : Type}
variable (S : Surface2) (E : EffectSpec2 St Args)

/-- The CIRCUIT step: full-state v2 arithmetization satisfied on the encoded triple. -/
abbrev effect2CircuitStep : StepRel St Args St :=
  fun pre args post => satisfiedE2 S E (encodeE2 S E pre args post)

/-- The APEX step: the framework's derived full-state declarative spec. -/
abbrev effect2ApexStep : StepRel St Args St :=
  fun pre args post => E.apex pre args post

/-- The EMITTED step: the polynomial gates the Rust prover checks. -/
abbrev effect2EmittedStep (name : String) : StepRel St Args St :=
  fun pre args post =>
    satisfiedEmitted (emittedEffect2 name E) (encodeE2 S E pre args post)

/-- **`effect2_circuit_refines_apex`** — SOUNDNESS: circuit ⊑ apex. -/
theorem effect2_circuit_refines_apex
    (hRestF : RestFrameDecodes2 S E) (hLog : logHashInjective S.LH) (hGuard : GuardDecodes2 E)
    (pre : St) (args : Args) (post : St) (h : effect2CircuitStep S E pre args post) :
    effect2ApexStep E pre args post :=
  effect2_circuit_full_sound S E hRestF hLog hGuard pre args post h

/-- **`effect2_apex_refines_circuit`** — COMPLETENESS: apex ⊑ circuit. -/
theorem effect2_apex_refines_circuit
    (hRestE : RestFrameEncodes2 S E) (hGuardE : GuardEncodes2 E)
    (pre : St) (args : Args) (post : St) (h : effect2ApexStep E pre args post) :
    effect2CircuitStep S E pre args post :=
  effect2_circuit_full_complete S E hRestE hGuardE pre args post h

/-- **`effect2_circuit_equiv_apex`** — mutual refinement on the algebraic layer. -/
theorem effect2_circuit_equiv_apex
    (hRestF : RestFrameDecodes2 S E) (hLog : logHashInjective S.LH) (hGuard : GuardDecodes2 E)
    (hRestE : RestFrameEncodes2 S E) (hGuardE : GuardEncodes2 E) :
    Equiv (effect2CircuitStep S E) (effect2ApexStep E) :=
  fun pre args post =>
    ⟨effect2_circuit_refines_apex S E hRestF hLog hGuard pre args post,
     effect2_apex_refines_circuit S E hRestE hGuardE pre args post⟩

/-- **`effect2_emitted_equiv_circuit`** — emitted wire form ⟺ algebraic circuit. -/
theorem effect2_emitted_equiv_circuit (name : String) (pre : St) (args : Args) (post : St) :
    effect2EmittedStep S E name pre args post ↔ effect2CircuitStep S E pre args post :=
  (emitEffect2Faithful name E (encodeE2 S E pre args post)).symm

/-- **`effect2_emitted_refines_apex`** — the Plonky3 layer refines to the apex spec. -/
theorem effect2_emitted_refines_apex
    (name : String) (hRestF : RestFrameDecodes2 S E) (hLog : logHashInjective S.LH)
    (hGuard : GuardDecodes2 E) (pre : St) (args : Args) (post : St)
    (h : effect2EmittedStep S E name pre args post) :
    effect2ApexStep E pre args post :=
  effect2_circuit_refines_apex S E hRestF hLog hGuard pre args post
    ((effect2_emitted_equiv_circuit S E name pre args post).mp h)

#assert_axioms effect2_circuit_refines_apex
#assert_axioms effect2_apex_refines_circuit
#assert_axioms effect2_circuit_equiv_apex
#assert_axioms effect2_emitted_equiv_circuit
#assert_axioms effect2_emitted_refines_apex

end GenericEffect2

/-! ## §2 — MintA diamond (circuit ⟺ MintASpec ⟺ execFullA ⟺ emitted). -/

def mintExecStep (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.mintA args.actor args.cell args.a args.amt) = some s'

def mintSpecStep (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) : Prop :=
  MintASpec s args.actor args.cell args.a args.amt s'

def mintCircuitStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (mintE D hD) s args s'

def mintEmittedStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStep S (mintE D hD) mintAirName s args s'

theorem mintRestFrameEncodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameEncodes2 S (mintE D hD) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem mint_exec_equiv_spec (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) :
    mintExecStep s args s' ↔ mintSpecStep s args s' :=
  execMintA_iff_spec s args.actor args.cell args.a args.amt s'

theorem mint_circuit_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : mintCircuitStep S D hD s args s') :
    mintSpecStep s args s' :=
  mintA_full_sound S D hD hRest hLog s args s' h

theorem mint_spec_refines_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : mintSpecStep s args s') :
    mintCircuitStep S D hD s args s' :=
  effect2_apex_refines_circuit S (mintE D hD)
    (mintRestFrameEncodes S D hD hRest) (mintGuardEncodes D hD) s args s'
    ((apex_iff_mintASpec D hD s args s').mpr h)

theorem mint_circuit_refines_exec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : mintCircuitStep S D hD s args s') :
    mintExecStep s args s' :=
  (mint_exec_equiv_spec s args s').mpr
    (mint_circuit_refines_spec S D hD hRest hLog s args s' h)

/-- W1: a circuit-accepted mint CONSERVES every asset exactly — the issuer-move's exactness
descends through the refinement chain (circuit → spec → executor → `mintA_supply_delta`). -/
theorem mint_supply_delta_descends (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : mintCircuitStep S D hD s args s') (b : AssetId) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  mintA_supply_delta s args.actor args.cell args.a args.amt s'
    ((mint_exec_equiv_spec s args s').mpr
      (mint_circuit_refines_spec S D hD hRest hLog s args s' h)) b

theorem mint_emitted_equiv_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) :
    mintEmittedStep S D hD s args s' ↔ mintCircuitStep S D hD s args s' :=
  effect2_emitted_equiv_circuit S (mintE D hD) mintAirName s args s'

theorem mint_emitted_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : mintEmittedStep S D hD s args s') :
    mintSpecStep s args s' :=
  mint_circuit_refines_spec S D hD hRest hLog s args s'
    ((mint_emitted_equiv_circuit S D hD s args s').mp h)

#assert_axioms mint_exec_equiv_spec
#assert_axioms mint_circuit_refines_spec
#assert_axioms mint_spec_refines_circuit
#assert_axioms mint_circuit_refines_exec
#assert_axioms mint_supply_delta_descends
#assert_axioms mint_emitted_equiv_circuit
#assert_axioms mint_emitted_refines_spec

/-! ## §3 — BurnA diamond (the mint dual: debit instead of credit). -/

def burnExecStep (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.burnA args.actor args.cell args.a args.amt) = some s'

def burnSpecStep (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState) : Prop :=
  BurnSpec s args.actor args.cell args.a args.amt s'

def burnCircuitStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (burnE D hD) s args s'

theorem burnRestFrameEncodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameEncodes2 S (burnE D hD) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem burn_exec_equiv_spec (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState) :
    burnExecStep s args s' ↔ burnSpecStep s args s' :=
  execFullA_burnA_iff_spec s args.actor args.cell args.a args.amt s'

theorem burn_circuit_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState)
    (h : burnCircuitStep S D hD s args s') :
    burnSpecStep s args s' :=
  burnA_full_sound S D hD hRest hLog s args s' h

theorem burn_spec_refines_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState)
    (h : burnSpecStep s args s') :
    burnCircuitStep S D hD s args s' :=
  effect2_apex_refines_circuit S (burnE D hD)
    (burnRestFrameEncodes S D hD hRest) (burnGuardEncodes D hD) s args s'
    ((apex_iff_burnSpec D hD s args s').mpr h)

theorem burn_circuit_refines_exec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState)
    (h : burnCircuitStep S D hD s args s') :
    burnExecStep s args s' :=
  (burn_exec_equiv_spec s args s').mpr
    (burn_circuit_refines_spec S D hD hRest hLog s args s' h)

#assert_axioms burn_exec_equiv_spec
#assert_axioms burn_circuit_refines_spec
#assert_axioms burn_spec_refines_circuit
#assert_axioms burn_circuit_refines_exec

/-! ## §4 — CreateCellA diamond (circuit ⟺ CreateCellSpec ⟺ execFullA). -/

def createCellExecStep (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.createCellA args.actor args.newCell) = some s'

def createCellSpecStep (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState) : Prop :=
  CreateCellSpec s args.actor args.newCell s'

def createCellCircuitStep (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide)
    (encodeE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide) s args s')

theorem createCell_exec_equiv_spec (s : RecChainedState) (args : CreateCellArgs)
    (s' : RecChainedState) :
    createCellExecStep s args s' ↔ createCellSpecStep s args s' :=
  execCreateCellA_iff_spec s args.actor args.newCell s'

theorem createCell_circuit_refines_spec (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState)
    (h : createCellCircuitStep S LE cN hN hLE DBal hDBal DSide hDSide s args s') :
    createCellSpecStep s args s' :=
  createCellA_full_sound S LE cN hN hLE DBal hDBal DSide hDSide hRest hLog s args s' h

theorem createCell_spec_refines_circuit (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : RestIffNoAccountsBalBorn S.RH)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState)
    (h : createCellSpecStep s args s') :
    createCellCircuitStep S LE cN hN hLE DBal hDBal DSide hDSide s args s' :=
  effect2triple_circuit_full_complete S (createCellE LE cN hN hLE DBal hDBal DSide hDSide)
    (createCellRestFrameEncodes S LE cN hN hLE DBal hDBal DSide hDSide hRest)
    (createCellGuardEncodes LE cN hN hLE DBal hDBal DSide hDSide) s args s'
    ((apex_iff_createCellSpec LE cN hN hLE DBal hDBal DSide hDSide s args s').mpr h)

theorem createCell_circuit_refines_exec (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState)
    (h : createCellCircuitStep S LE cN hN hLE DBal hDBal DSide hDSide s args s') :
    createCellExecStep s args s' :=
  (createCell_exec_equiv_spec s args s').mpr
    (createCell_circuit_refines_spec S LE cN hN hLE DBal hDBal DSide hDSide hRest hLog s args s' h)

#assert_axioms createCell_exec_equiv_spec
#assert_axioms createCell_circuit_refines_spec
#assert_axioms createCell_spec_refines_circuit
#assert_axioms createCell_circuit_refines_exec

/-! ## §5 — SpawnA diamond (circuit ⟺ Spawn(Full)Spec ⟺ execFullA).

The deployed quint `spawnE` descriptor now binds `delegationEpochAt` as part of its PRODUCT `active5`
component (`(delegations, delegationEpochAt)` bound to `(spawnDelegationsMap, spawnEpochAtMap)`), so the
deployed circuit alone FORCES the STRENGTHENED `SpawnFullSpec`: the child's epoch tag is gate-bound to the
spawner-parent's CURRENT epoch read off the SAME before-kernel. The `SpawnEpochStampResidual` is DISCHARGED
— no longer a carried clause.

**Census D3 verdict (CLOSED at the abstract descriptor layer — the genuine cross-cell force).** The
`delegationEpochAt` stamp is a CROSS-CELL relation (`child.delegationEpochAt = parent.delegationEpoch`): the
parent is a DIFFERENT cell than the child. The deployed SINGLE-CELL rotated row (`B_EPOCH = 30` on the
child's row) CANNOT reach the parent's epoch column, and the turn-composition layer chains effects by
published `state_commit` PIs (commitment equality), NOT by a constraint system relating two cells' row
columns — so the literal "lift `delegationEpochAt` to limb 37→38 + a cross-row turn gate" is structurally
unreachable (there is no transfer-conservation cross-ROW gate to mirror; transfer conservation is carried
WITHIN one effect's whole-kernel abstract transition). The genuine forcing layer is THIS abstract per-effect
descriptor, which commits over the WHOLE abstract kernel (`chainView`): `spawnEpochAtMap`/`refreshEpochAtMap`
read `before.delegationEpoch parent`, and binding the whole post `delegationEpochAt` map into an injective
product digest (the SAME mechanism the `delegations` map / the deployed DELEG system-root already use) FORCES
`child.delegationEpochAt = parent_epoch` — a real force via digest injectivity, NOT a freely-witnessed param.
The deployed analog is a `delegationEpochAt` keyed-map system-root, forced exactly as `delegations` (DELEG)
is. -/

def spawnExecStep (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.spawnA args.actor args.child args.target) = some s'

/-- The deployed-quint frozen-face spec (`delegationEpochAt` UNCHANGED) — what the deployed circuit binds. -/
def spawnSpecStep (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) : Prop :=
  SpawnSpec s args.actor args.child args.target s'

/-- The STRENGTHENED faithful spec (`delegationEpochAt` STAMPED at birth) — what the executor meets. -/
def spawnFullSpecStep (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) : Prop :=
  SpawnFullSpec s args.actor args.child args.target s'

/-- **`SpawnEpochStampResidual`** — DISCHARGED. The birth-epoch-stamp is now WRITE-GATE-forced by the
deployed spawn descriptor's PRODUCT `active5` component (`(delegations, delegationEpochAt)` bound to
`(spawnDelegationsMap, spawnEpochAtMap)`), not a carried residual. Retained as the proposition the force
delivers (`delegationEpochAt = spawnEpochAtMap`, stamping the child's tag with the spawner-parent's CURRENT
epoch); `spawn_circuit_refines_spec` now proves it directly out of the descriptor. -/
def SpawnEpochStampResidual (s : RecChainedState) (actor child : CellId) (s' : RecChainedState) : Prop :=
  s'.kernel.delegationEpochAt = spawnEpochAtMap s.kernel actor child

def spawnCircuitStep (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
    (encodeE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) s args s')

/-- **`spawnFullCircuitStep`** — the deployed `spawnCircuitStep`, which now ALONE forces the birth stamp
(the product `active5` component). The FAITHFUL circuit-side relation for `.spawnA` is the deployed step
itself. -/
def spawnFullCircuitStep (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) : Prop :=
  spawnCircuitStep S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s'

theorem spawn_exec_equiv_spec (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) :
    spawnExecStep s args s' ↔ spawnFullSpecStep s args s' :=
  spawnChainA_iff_spec s args.actor args.child args.target s'

theorem spawnRestFrameEncodes (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoSpawnTouched S.RH) :
    RestFrameEncodes2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) :=
  fun k k' h => (hRest k k').mpr h

/-- **Deployed circuit ⟹ STRENGTHENED `SpawnFullSpec`.** The deployed quint's PRODUCT `active5` component
binds `(delegations, delegationEpochAt)`, so it FORCES the birth stamp (no residual): the child is stamped
FRESH with the spawner-parent's current epoch, read off the same before-kernel. This is what
`spawnA_full_sound` now proves. -/
theorem spawn_circuit_refines_spec (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoSpawnTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (h : spawnCircuitStep S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s') :
    spawnFullSpecStep s args s' :=
  spawnA_full_sound S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRest hLog s args s' h

/-- **`spawn_full_circuit_refines_spec` — the FAITHFUL refinement.** The deployed product descriptor FORCES
`SpawnFullSpec` directly (the child stamped FRESH at birth — the stamp is gate-forced, no residual). A forge
that births the child but skips the stamp violates the product component's `postClause` and is UNSAT. -/
theorem spawn_full_circuit_refines_spec (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoSpawnTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (h : spawnFullCircuitStep S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s') :
    spawnFullSpecStep s args s' :=
  spawn_circuit_refines_spec S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRest hLog
    s args s' h

theorem spawn_spec_refines_circuit (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoSpawnTouched S.RH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (h : spawnFullSpecStep s args s') :
    spawnCircuitStep S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s' :=
  effect2quint_circuit_full_complete S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
    (spawnRestFrameEncodes S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRest)
    (spawnGuardEncodes LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) s args s'
    ((apex_iff_spawnSpec LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s').mpr h)

-- The spawn descriptor is now a MOVING face: the product `active5` forces `delegationEpochAt` to the birth
-- stamp, so BOTH directions run over the STRENGTHENED `SpawnFullSpec` (soundness AND completeness). The
-- residual-carrier era for the spawn epoch-stamp is over — it is gate-forced.

/-- **`spawn_full_circuit_refines_exec` — the FAITHFUL circuit ⟹ executor.** The deployed quint + the
birth-stamp residual force a genuine committed spawn (with the fresh-at-birth child). -/
theorem spawn_full_circuit_refines_exec (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoSpawnTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (h : spawnFullCircuitStep S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s') :
    spawnExecStep s args s' :=
  (spawn_exec_equiv_spec s args s').mpr
    (spawn_full_circuit_refines_spec S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRest hLog
      s args s' h)

#assert_axioms spawn_exec_equiv_spec
#assert_axioms spawn_circuit_refines_spec
#assert_axioms spawn_full_circuit_refines_spec
#assert_axioms spawn_spec_refines_circuit
#assert_axioms spawn_full_circuit_refines_exec

/-! ## §6 — Transfer diamond (circuit ⟺ BalanceMovementSpec ⟺ execFullA). -/

section TransferDiamond
open Dregg2.Circuit.Inst.Transfer

def transferExecStep (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.balanceA args.t args.a) = some s'

def transferSpecStep (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  BalanceMovementSpec s args.t args.a s'

def transferCircuitStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (balanceE D hD) s args s'

theorem transferRestFrameEncodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameEncodes2 S (balanceE D hD) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem transfer_exec_equiv_spec (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) :
    transferExecStep s args s' ↔ transferSpecStep s args s' :=
  execFullA_balanceA_iff_spec s args.t args.a s'

theorem transfer_circuit_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : transferCircuitStep S D hD s args s') :
    transferSpecStep s args s' :=
  transfer_full_sound S D hD hRest hLog s args s' h

theorem transfer_spec_refines_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : transferSpecStep s args s') :
    transferCircuitStep S D hD s args s' :=
  effect2_apex_refines_circuit S (balanceE D hD)
    (transferRestFrameEncodes S D hD hRest) (balanceGuardEncodes D hD) s args s'
    ((apex_iff_balanceMovementSpec D hD s args s').mpr h)

theorem transfer_circuit_refines_exec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : transferCircuitStep S D hD s args s') :
    transferExecStep s args s' :=
  (transfer_exec_equiv_spec s args s').mpr
    (transfer_circuit_refines_spec S D hD hRest hLog s args s' h)

#assert_axioms transfer_exec_equiv_spec
#assert_axioms transfer_circuit_refines_spec
#assert_axioms transfer_spec_refines_circuit
#assert_axioms transfer_circuit_refines_exec

end TransferDiamond

/-! ## §7 — BalanceA diamond (`balanceAE` instance; same spec, distinct circuit package). -/

section BalanceADiamond
open Dregg2.Circuit.Inst.BalanceA

def balanceAExecStep (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.balanceA args.t args.a) = some s'

def balanceASpecStep (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  BalanceMovementSpec s args.t args.a s'

def balanceACircuitStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (balanceAE D hD) s args s'

theorem balanceARestFrameEncodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameEncodes2 S (balanceAE D hD) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem balanceA_exec_equiv_spec (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) :
    balanceAExecStep s args s' ↔ balanceASpecStep s args s' :=
  execFullA_balanceA_iff_spec s args.t args.a s'

theorem balanceA_circuit_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : balanceACircuitStep S D hD s args s') :
    balanceASpecStep s args s' :=
  balanceA_full_sound S D hD hRest hLog s args s' h

theorem balanceA_spec_refines_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : balanceASpecStep s args s') :
    balanceACircuitStep S D hD s args s' :=
  effect2_apex_refines_circuit S (balanceAE D hD)
    (balanceARestFrameEncodes S D hD hRest) (balanceGuardEncodes D hD) s args s'
    ((apex_iff_balanceASpec D hD s args s').mpr h)

theorem balanceA_circuit_refines_exec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : balanceACircuitStep S D hD s args s') :
    balanceAExecStep s args s' :=
  (balanceA_exec_equiv_spec s args s').mpr
    (balanceA_circuit_refines_spec S D hD hRest hLog s args s' h)

#assert_axioms balanceA_exec_equiv_spec
#assert_axioms balanceA_circuit_refines_spec
#assert_axioms balanceA_spec_refines_circuit
#assert_axioms balanceA_circuit_refines_exec

end BalanceADiamond

/-! ## §8 — Delegate diamond (circuit ⟺ DelegateSpec ⟺ execFullA). -/

def delegateExecStep (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.delegate args.del args.recipient args.target) = some s'

def delegateSpecStep (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState) : Prop :=
  DelegateSpec s args.del args.recipient args.target s'

def delegateCircuitStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (delegateE D hD) s args s'

theorem delegateRestFrameEncodes (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps S.RH) :
    RestFrameEncodes2 S (delegateE D hD) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem delegate_exec_equiv_spec (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState) :
    delegateExecStep s args s' ↔ delegateSpecStep s args s' :=
  execFullA_delegate_iff_spec s args.del args.recipient args.target s'

theorem delegate_circuit_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState)
    (h : delegateCircuitStep S D hD s args s') :
    delegateSpecStep s args s' :=
  delegate_full_sound S D hD hRest hLog s args s' h

theorem delegate_spec_refines_circuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps S.RH)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState)
    (h : delegateSpecStep s args s') :
    delegateCircuitStep S D hD s args s' :=
  effect2_apex_refines_circuit S (delegateE D hD)
    (delegateRestFrameEncodes S D hD hRest) (delegateGuardEncodes D hD) s args s'
    ((apex_iff_delegateSpec D hD s args s').mpr h)

theorem delegate_circuit_refines_exec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState)
    (h : delegateCircuitStep S D hD s args s') :
    delegateExecStep s args s' :=
  (delegate_exec_equiv_spec s args s').mpr
    (delegate_circuit_refines_spec S D hD hRest hLog s args s' h)

#assert_axioms delegate_exec_equiv_spec
#assert_axioms delegate_circuit_refines_spec
#assert_axioms delegate_spec_refines_circuit
#assert_axioms delegate_circuit_refines_exec

/-! ## §9 — NoteSpendA diamond (circuit ⟺ NoteSpendSpec ⟺ execFullA). -/

def noteSpendExecStep (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.noteSpendA args.nf args.actor args.spendProof) = some s'

def noteSpendSpecStep (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState) : Prop :=
  NoteSpendSpec s args.nf args.actor args.spendProof s'

def noteSpendCircuitStep (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (noteSpendE LE cN hN hLE) s args s'

theorem noteSpendRestFrameEncodes (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoNullifiers S.RH) :
    RestFrameEncodes2 S (noteSpendE LE cN hN hLE) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem noteSpend_exec_equiv_spec (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState) :
    noteSpendExecStep s args s' ↔ noteSpendSpecStep s args s' :=
  execFullA_noteSpend_iff_spec s args.nf args.actor args.spendProof s'

theorem noteSpend_circuit_refines_spec (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (h : noteSpendCircuitStep S LE cN hN hLE s args s') :
    noteSpendSpecStep s args s' :=
  noteSpendA_full_sound S LE cN hN hLE hRest hLog s args s' h

theorem noteSpend_spec_refines_circuit (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (h : noteSpendSpecStep s args s') :
    noteSpendCircuitStep S LE cN hN hLE s args s' :=
  effect2_apex_refines_circuit S (noteSpendE LE cN hN hLE)
    (noteSpendRestFrameEncodes S LE cN hN hLE hRest) (noteSpendGuardEncodes LE cN hN hLE) s args s'
    ((apex_iff_noteSpendSpec LE cN hN hLE s args s').mpr h)

theorem noteSpend_circuit_refines_exec (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (h : noteSpendCircuitStep S LE cN hN hLE s args s') :
    noteSpendExecStep s args s' :=
  (noteSpend_exec_equiv_spec s args s').mpr
    (noteSpend_circuit_refines_spec S LE cN hN hLE hRest hLog s args s' h)

#assert_axioms noteSpend_exec_equiv_spec
#assert_axioms noteSpend_circuit_refines_spec
#assert_axioms noteSpend_spec_refines_circuit
#assert_axioms noteSpend_circuit_refines_exec

/-! ## §11 — NoteCreateA diamond (circuit ⟺ NoteCreateASpec ⟺ execFullA). -/

def noteCreateExecStep (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.noteCreateA args.cm args.actor) = some s'

def noteCreateSpecStep (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState) : Prop :=
  NoteCreateASpec s args.cm args.actor s'

def noteCreateCircuitStep (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (noteCreateE LE cN hN hLE) s args s'

theorem noteCreateRestFrameEncodes (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoCommitments S.RH) :
    RestFrameEncodes2 S (noteCreateE LE cN hN hLE) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem noteCreate_exec_equiv_spec (s : RecChainedState) (args : NoteCreateArgs)
    (s' : RecChainedState) :
    noteCreateExecStep s args s' ↔ noteCreateSpecStep s args s' :=
  execNoteCreateA_iff_spec s args.cm args.actor s'

theorem noteCreate_circuit_refines_spec (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoCommitments S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState)
    (h : noteCreateCircuitStep S LE cN hN hLE s args s') :
    noteCreateSpecStep s args s' :=
  noteCreateA_full_sound S LE cN hN hLE hRest hLog s args s' h

theorem noteCreate_spec_refines_circuit (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoCommitments S.RH)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState)
    (h : noteCreateSpecStep s args s') :
    noteCreateCircuitStep S LE cN hN hLE s args s' :=
  effect2_apex_refines_circuit S (noteCreateE LE cN hN hLE)
    (noteCreateRestFrameEncodes S LE cN hN hLE hRest) (noteCreateGuardEncodes LE cN hN hLE) s args s'
    ((apex_iff_noteCreateASpec LE cN hN hLE s args s').mpr h)

theorem noteCreate_circuit_refines_exec (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoCommitments S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState)
    (h : noteCreateCircuitStep S LE cN hN hLE s args s') :
    noteCreateExecStep s args s' :=
  (noteCreate_exec_equiv_spec s args s').mpr
    (noteCreate_circuit_refines_spec S LE cN hN hLE hRest hLog s args s' h)

#assert_axioms noteCreate_exec_equiv_spec
#assert_axioms noteCreate_circuit_refines_spec
#assert_axioms noteCreate_spec_refines_circuit
#assert_axioms noteCreate_circuit_refines_exec

/-! ## §14 — Revoke diamond (circuit ⟺ RevokeSpec ⟺ execFullA). -/

def revokeExecStep (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.revoke args.holder args.t) = some s'

def revokeSpecStep (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) : Prop :=
  RevokeSpec s args.holder args.t s'

def revokeCircuitStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (revokeE D hD) s args s'

theorem revokeRestFrameEncodes (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Revoke.RestIffNoCaps S.RH) :
    RestFrameEncodes2 S (revokeE D hD) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem revoke_exec_equiv_spec (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) :
    revokeExecStep s args s' ↔ revokeSpecStep s args s' :=
  execFullA_revoke_iff_spec s args.holder args.t s'

theorem revoke_circuit_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Revoke.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : revokeCircuitStep S D hD s args s') :
    revokeSpecStep s args s' :=
  revoke_full_sound S D hD hRest hLog s args s' h

theorem revoke_spec_refines_circuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Revoke.RestIffNoCaps S.RH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : revokeSpecStep s args s') :
    revokeCircuitStep S D hD s args s' :=
  effect2_apex_refines_circuit S (revokeE D hD)
    (revokeRestFrameEncodes S D hD hRest) (revokeGuardEncodes D hD) s args s'
    ((apex_iff_revokeSpec D hD s args s').mpr h)

theorem revoke_circuit_refines_exec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Revoke.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : revokeCircuitStep S D hD s args s') :
    revokeExecStep s args s' :=
  (revoke_exec_equiv_spec s args s').mpr
    (revoke_circuit_refines_spec S D hD hRest hLog s args s' h)

#assert_axioms revoke_exec_equiv_spec
#assert_axioms revoke_circuit_refines_spec
#assert_axioms revoke_spec_refines_circuit
#assert_axioms revoke_circuit_refines_exec

/-! ## §14.EPOCH — the FAITHFUL delegation-revoke diamond (circuit ⟺ RevokeDelegationFullSpec).

`.revokeDelegationA holder t` does the FULL `apply_revoke_delegation` (the cap-edge `removeEdge` COMPOSED
with the epoch bump + child-snapshot clear), so it meets the STRENGTHENED `RevokeDelegationFullSpec`, not
the bare `RevokeSpec`. The deployed `revokeE` circuit binds the cap-edge `RevokeSpec` (its `caps`+log+frame)
AND — in the deployed commitment — the parent's bumped `delegation_epoch` (rotated limb 30,
`cell/src/commitment.rs:940`) and the cleared child snapshot (`record_digest` =
`compute_authority_digest_felt`, limb 24, `commitment.rs:805-813`).

**§14.EPOCH UPDATE (Census D3, WIRED):** the parent's `delegationEpoch += 1` clause is now WRITE-GATE-FORCED
on the deployed wire. The deployed `EffectVmEmitRotationV3.revokeDelegationWriteV3` carries the
`epochBumpGate` (selector-gated on `sel.REVOKE_DELEGATION`) forcing the committed AFTER epoch limb
(`B_EPOCH = 30`) to equal the committed BEFORE epoch + 1 — proven by
`revokeDelegationWriteV3_forces_epoch_bump`, with the deployed forge-rejection
`revokeDelegationWriteV3_rejects_wrong_epoch` (a frozen/wrong epoch is UNSAT for a ledgerless client). The
limb was previously a FREE witness limb (`weldsAtNoCapRoot` does not weld it, `rotateV3CapWrite` does not
freeze it), so the epoch move rode OFF-ROW; the gate closes that.

The epoch step is no longer a CARRIED residual: the dedicated DUAL descriptor `revokeDelegationFullE`
(`Inst/revokeDelegationFullA.lean`) binds the three delegation registries as a FORCED second component, so
the FAITHFUL `RevokeDelegationFullSpec` falls straight out of the dual apex (the SAME forcing the
spawn/refresh `delegationEpochAt` stamps received via their product components). -/

/-- **`RevokeDelegationEpochResidual`** — RETAINED only as the documentation of WHAT the forced epoch step
delivers (the parent's `delegationEpoch += 1`, the child's `delegations` snapshot cleared, the child's
`delegationEpochAt` stamp reset). No longer load-bearing: `revokeDelegationCircuitStep` is now the FORCED
dual step, and `revokeDelegation_circuit_refines_spec` PROVES this Prop out of the descriptor rather than
carrying it as a hypothesis. -/
def RevokeDelegationEpochResidual (s : RecChainedState) (parent child : CellId)
    (s' : RecChainedState) : Prop :=
  s'.kernel.delegationEpoch
      = (fun c => if c = parent then s.kernel.delegationEpoch c + 1 else s.kernel.delegationEpoch c)
  ∧ s'.kernel.delegations = (fun c => if c = child then [] else s.kernel.delegations c)
  ∧ s'.kernel.delegationEpochAt = (fun c => if c = child then 0 else s.kernel.delegationEpochAt c)

/-- **`revokeDelegationCircuitStep`** — the FORCED dual circuit step for `.revokeDelegationA`:
`satisfiedE2Dual` of `revokeDelegationFullE` (cap-edge `removeEdge` `active1` + the FORCED epoch-step
`active2`). The epoch step is bound by the second component's injective product digest — NO conjoined
residual. The FAITHFUL circuit-side relation for `.revokeDelegationA`. -/
def revokeDelegationCircuitStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (DStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDStep : Function.Injective DStep)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Dual S (Dregg2.Circuit.Inst.RevokeDelegationFullA.revokeDelegationFullE D hD DStep hDStep)
    (encodeE2Dual S (Dregg2.Circuit.Inst.RevokeDelegationFullA.revokeDelegationFullE D hD DStep hDStep)
      s ⟨args.holder, args.t⟩ s')

/-- **`revokeDelegation_circuit_refines_spec` — circuit ⟹ STRENGTHENED `RevokeDelegationFullSpec`.** The
FORCED dual step ALONE yields the FAITHFUL `RevokeDelegationFullSpec` (the `caps` removeEdge + log + the
thirteen-field frame AND the epoch step — parent epoch bumped `+1`, child snapshot cleared, stamp reset).
The epoch step is gate-forced by the second component's product digest, no carried residual. -/
theorem revokeDelegation_circuit_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (DStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDStep : Function.Injective DStep)
    (hRest : Dregg2.Circuit.Inst.RevokeDelegationFullA.RestIffNoCapsEpoch S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : revokeDelegationCircuitStep S D hD DStep hDStep s args s') :
    RevokeDelegationFullSpec s args.holder args.t s' :=
  Dregg2.Circuit.Inst.RevokeDelegationFullA.revokeDelegationFull_full_sound
    S D hD DStep hDStep hRest hLog s ⟨args.holder, args.t⟩ s' h

#assert_axioms revokeDelegation_circuit_refines_spec

-- (F2a) §17 QueueEnqueueA diamond DELETED with the queue effect family (VerbRegistry:
-- `.factory .queue`; the FIFO behavior is the verified `Dregg2/Apps/QueueFactory`).
-- (F3) §15 SealA diamond DELETED with the seal/swiss/sturdyref family (VerbRegistry:
-- `.factory .capsInSlots`; stored-cap behavior is the verified `Dregg2/Apps/CapSlotFactory`,
-- R7 epoch-at-retrieval).

/-! ## §18 — SetFieldA diamond (v1 circuit ⟺ SetFieldSpec ⟺ execFullA). -/

def setFieldExecStep (s : RecChainedState) (args : SetFieldArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.setFieldA args.actor args.cell args.f args.v) = some s'

def setFieldSpecStep (s : RecChainedState) (args : SetFieldArgs) (s' : RecChainedState) : Prop :=
  SetFieldSpec s args.actor args.cell args.f args.v s'

def setFieldCircuitStep (S : CommitSurface) (s : RecChainedState) (args : SetFieldArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE S setFieldE (encodeE S setFieldE s args s')

theorem setField_exec_equiv_spec (s : RecChainedState) (args : SetFieldArgs) (s' : RecChainedState) :
    setFieldExecStep s args s' ↔ setFieldSpecStep s args s' :=
  execFullA_setFieldA_iff_spec s args.actor args.cell args.f args.v s'

theorem setField_circuit_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetFieldArgs) (s' : RecChainedState)
    (hnr : Dregg2.Exec.EffectsState.reservedField args.f = false)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : setFieldCircuitStep S s args s') :
    setFieldSpecStep s args s' :=
  setFieldE_full_sound S hN hL hRest hLog s args s' hnr hwf hwf' h

theorem setField_spec_refines_circuit (S : CommitSurface) (hRest : RestHashIffFrame S.RH)
    (s : RecChainedState) (args : SetFieldArgs) (s' : RecChainedState)
    (h : setFieldSpecStep s args s') :
    setFieldCircuitStep S s args s' :=
  -- §RESERVED-SLOT: the spec ALREADY carries `reservedField args.f = false` (its `.1` leg), so the
  -- `apex_iff` hypothesis is discharged from `h` itself.
  effect_circuit_full_complete S setFieldE hRest setFieldGuardEncodes s args s'
    ((apex_iff_setFieldSpec s args s' h.1).mpr h)

theorem setField_circuit_refines_exec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetFieldArgs) (s' : RecChainedState)
    (hnr : Dregg2.Exec.EffectsState.reservedField args.f = false)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : setFieldCircuitStep S s args s') :
    setFieldExecStep s args s' :=
  (setField_exec_equiv_spec s args s').mpr
    (setField_circuit_refines_spec S hN hL hRest hLog s args s' hnr hwf hwf' h)

#assert_axioms setField_exec_equiv_spec
#assert_axioms setField_circuit_refines_spec
#assert_axioms setField_spec_refines_circuit
#assert_axioms setField_circuit_refines_exec

/-! ## §19 — ExerciseA composite (v1 hold-layer ⟺ `ExerciseHoldSpec`; inner turn composed). -/

def exerciseHoldSpecStep (pre : RecChainedState) (args : ExerciseHoldArgs) (post : RecChainedState) :
    Prop :=
  ExerciseHoldSpec pre args.actor args.target post

theorem exerciseHold_exec_equiv_spec_step (pre post : RecChainedState) (args : ExerciseHoldArgs) :
    exerciseHoldExecStep pre post args ↔ exerciseHoldSpecStep pre args post :=
  exerciseHold_exec_equiv_spec pre post args

theorem exerciseHold_circuit_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (pre post : RecChainedState) (args : ExerciseHoldArgs)
    (hwf : AccountsWF pre.kernel) (hwf' : AccountsWF post.kernel)
    (h : exerciseHoldCircuitStep S pre args post) :
    exerciseHoldSpecStep pre args post :=
  exercise_circuit_refines_hold_spec S hN hL hRest hLog pre post args hwf hwf' h

theorem exercise_composite_circuit_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (pre post : RecChainedState) (args : ExerciseFullArgs)
    (innerTurnH : Prop) (hinner : innerTurnH)
    (hinnerBridge : innerTurnH ↔ turnSpec (exerciseHoldState pre args.actor) args.inner post)
    (hfacet : innerFacetsAdmittedA pre args.actor args.target args.inner = true)
    (hwf : AccountsWF pre.kernel)
    (hhold : exerciseHoldCircuitStep S pre ⟨args.actor, args.target⟩
        (exerciseHoldState pre args.actor)) :
    exerciseSpecStep pre post args :=
  exercise_circuit_refines_spec S hN hL hRest hLog pre post args innerTurnH hinner hinnerBridge hfacet hwf hhold

theorem exercise_composite_circuit_refines_exec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (pre post : RecChainedState) (args : ExerciseFullArgs)
    (innerTurnH : Prop) (hinner : innerTurnH)
    (hinnerBridge : innerTurnH ↔ turnSpec (exerciseHoldState pre args.actor) args.inner post)
    (hfacet : innerFacetsAdmittedA pre args.actor args.target args.inner = true)
    (hwf : AccountsWF pre.kernel)
    (hhold : exerciseHoldCircuitStep S pre ⟨args.actor, args.target⟩
        (exerciseHoldState pre args.actor)) :
    exerciseExecStep pre post args :=
  exercise_circuit_refines_exec S hN hL hRest hLog pre post args innerTurnH hinner hinnerBridge hfacet hwf hhold

#assert_axioms exerciseHold_exec_equiv_spec_step
#assert_axioms exerciseHold_circuit_refines_spec
#assert_axioms exercise_composite_circuit_refines_spec
#assert_axioms exercise_composite_circuit_refines_exec

end Dregg2.Circuit.EffectRefinement