/-
# Dregg2.Circuit.Witness.burnAWitness — `execute → satisfying assignment` for `burnA` (the per-asset
SUPPLY DESTRUCTION effect; v2 family, touched component = `bal`).

The burn analog of `balanceAWitness`/`TransferWitness`: `burnWitnessVec` RUNS the REAL chained executor
`recCBurnAsset` (the arm `execFullA` dispatches `.burnA` to) and lays the satisfying 72-wire `encodeE2`
assignment out as a flat `List Int`, every digest column filled by the concrete commitment surface
(`rhConcrete2`/`lhConcrete`/the injective `balDigestC` Horner fold). `Inst.burnA.burnA_full_sound`
already proved the v2 circuit⟺spec crown jewel (`⇒ BurnSpec`, the 17-field declarative post-state).

`#guard`s certify (decidably, no `native_decide`): the executor-derived witness SATISFIES
`effectCircuit2`, and a REAL forged post-state (a bystander third cell minted into) is REJECTED by the
component-bind gate `68 ≠ 69` — the anti-ghost tooth, end-to-end from a genuine forged state. The
JSON strings are the EXACT bytes the Rust `lean_executor_derived_burn_a` test proves+verifies / rejects.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Circuit.Inst.burnA

namespace Dregg2.Circuit.Witness.BurnAWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.BurnA
open Dregg2.Circuit.Spec.SupplyDestruction
open Dregg2.Authority (Cap)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false
set_option linter.unusedVariables false

/-! ## §0 — decidability re-exports. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the CONCRETE commitment surface (shared shape with `balanceAWitness`). -/

def rhConcrete2 : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
def lhConcrete : List Turn → ℤ := fun l => (l.length : ℤ)

/-- The probe cells the concrete `bal` digest samples: the burned `cell`, plus a bystander cell `2`. -/
def balProbes (cell : CellId) : List (CellId × AssetId) := [(cell, 0), (2, 0)]

def balDigestC (cell : CellId) (bal : CellId → AssetId → ℤ) : ℤ :=
  (balProbes cell).foldl (fun acc p => acc * 1000000 + bal p.1 p.2) 0

def burnSurfaceC : Surface2 := { RH := rhConcrete2, LH := lhConcrete }

/-! ## §2 — the concrete `ActiveComponent` + the concrete `burnEC`. -/

def balComponentC (cell : CellId) : ActiveComponent RecChainedState BurnArgs where
  digest    := fun k => balDigestC cell k.bal
  expected  := fun s args => balDigestC cell (recBalCredit s.kernel.bal args.cell args.a (-args.amt))
  postClause := fun s args post =>
    balDigestC cell post.bal = balDigestC cell (recBalCredit s.kernel.bal args.cell args.a (-args.amt))
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def burnEC (cell : CellId) : EffectSpec2 RecChainedState BurnArgs where
  view         := chainView
  active       := balComponentC cell
  logUpdate    := some (fun s args => burnReceipt args.actor args.cell args.amt :: s.log)
  restFrame    := fun k k' => True
  guardGates   := burnGuardGates
  guardProp    := burnGuardProp
  guardWidth   := 1
  guardEncode  := burnGuardEncode
  guardLocal   := burnGuardLocal
  guardWidth_le := by decide

/-! ## §3 — THE WITNESS GENERATOR. -/

def witnessOf (cell : CellId) (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState) : List Int :=
  (List.range (burnEC cell).traceWidth).map
    (fun v => encodeE2 burnSurfaceC (burnEC cell) s args s' v)

/-- **`burnWitnessVec s args`** — runs `recCBurnAsset`, on commit lays out the satisfying witness. -/
def burnWitnessVec (s : RecChainedState) (args : BurnArgs) : List Int :=
  match recCBurnAsset s args.actor args.cell args.a args.amt with
  | some s' => witnessOf args.cell s args s'
  | none    => witnessOf args.cell s args s

theorem burnWitnessVec_commit {s s' : RecChainedState} {args : BurnArgs}
    (h : recCBurnAsset s args.actor args.cell args.a args.amt = some s') :
    burnWitnessVec s args = witnessOf args.cell s args s' := by
  unfold burnWitnessVec; rw [h]

theorem witnessOf_get (cell : CellId) (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState)
    (v : Nat) (hv : v < (burnEC cell).traceWidth) :
    (witnessOf cell s args s')[v]'(by simpa [witnessOf] using hv)
      = encodeE2 burnSurfaceC (burnEC cell) s args s' v := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- Concrete pre-state: cells {0,1,2}, `bal` column 0 = 100/5/50; actor 0 holds a mint cap over cell 0
(`Cap.node 0`); all live; empty log. -/
def sC0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun _ => default
        caps := fun x => if x = 0 then [Cap.node 0] else []
        bal := fun c a => if a = 0 then (if c = 0 then 100 else if c = 1 then 5 else if c = 2 then 50 else 0) else 0 }
    log := [] }

/-- Burn 30 of asset 0 out of cell 0 (actor 0). -/
def goodArgsC : BurnArgs := { actor := 0, cell := 0, a := 0, amt := 30 }

def goodPostC : RecChainedState := (recCBurnAsset sC0 0 0 0 30).getD sC0

/-- THE FORGERY: cell 0 honestly debited (70), but bystander cell 2 minted 50 → 999. -/
def forgedBalC : CellId → AssetId → ℤ :=
  fun c a => if a = 0 then (if c = 0 then 70 else if c = 1 then 5 else if c = 2 then 999 else 0) else 0

def forgedPostC : RecChainedState :=
  { kernel := { goodPostC.kernel with bal := forgedBalC }, log := goodPostC.log }

def honestWitness : List Int := burnWitnessVec sC0 goodArgsC
def forgedWitness : List Int := witnessOf 0 sC0 goodArgsC forgedPostC

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

-- (2) EXECUTE→PROVE: the executor-derived witness SATISFIES the circuit.
#guard decide (satisfied (effectCircuit2 (burnEC 0))
  (encodeE2 burnSurfaceC (burnEC 0) sC0 goodArgsC goodPostC))
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0

-- (3) ANTI-GHOST: the forged bystander-mint post-state FAILS the component-bind gate (68 ≠ 69).
#guard decide (satisfied (effectCircuit2 (burnEC 0))
  (encodeE2 burnSurfaceC (burnEC 0) sC0 goodArgsC forgedPostC)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def burnHonestWitnessJson : String := witnessJson honestWitness
def burnForgedWitnessJson : String := witnessJson forgedWitness

-- The EXACT bytes the Rust `lean_executor_derived_burn_a` test pastes (goldens).
#guard burnHonestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100000053,70000054,3,3,70000050,70000050,1,1]"
#guard burnForgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100000053,70001003,3,3,70000999,70000050,1,1]"

#assert_axioms burnWitnessVec_commit
#assert_axioms witnessOf_get

end Dregg2.Circuit.Witness.BurnAWitness
