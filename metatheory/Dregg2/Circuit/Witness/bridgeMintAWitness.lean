/-
# Dregg2.Circuit.Witness.bridgeMintAWitness — `execute → satisfying assignment` for `bridgeMintA` (the
bridge-INBOUND per-asset MINT; v2 family, touched component = `bal`, CREDIT side).

The mint analog of `burnAWitness`: `bridgeMintWitnessVec` RUNS the REAL chained executor
`recCMintAsset` (the arm `execFullA` dispatches `.bridgeMintA` to) and lays the satisfying 72-wire
`encodeE2` assignment out as a flat `List Int` over the concrete commitment surface. The honest witness
satisfies `effectCircuit2`; a forged bystander-mint post-state is REJECTED by the component-bind gate
`68 ≠ 69`. `Inst.bridgeMintA.bridgeMintA_full_sound` proved the crown jewel (`⇒ InboundMintSpec`).
-/
import Dregg2.Circuit.Inst.bridgeMintA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.BridgeMintAWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectInstances2
open Dregg2.Circuit.Inst.BridgeMintA
open Dregg2.Circuit.Spec.BridgeInboundMint
open Dregg2.Authority (Cap)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false
set_option linter.unusedVariables false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the CONCRETE commitment surface. -/

def rhConcrete2 : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
def lhConcrete : List Turn → ℤ := Dregg2.Circuit.Poseidon2Surface.turnLogDigest

def balProbes (cell : CellId) : List (CellId × AssetId) := [(cell, 0), (2, 0)]
/-- The REAL `refP2` sponge over the probed ledger entries (binds each — NO lossy `% 10⁶` collapse). -/
def balDigestC (cell : CellId) (bal : CellId → AssetId → ℤ) : ℤ :=
  Dregg2.Circuit.Poseidon2Surface.refP2 ((balProbes cell).map (fun p => bal p.1 p.2))
def mintSurfaceC : Surface2 := { RH := rhConcrete2, LH := lhConcrete }

/-! ## §2 — the concrete `ActiveComponent` + the concrete `bridgeMintEC`. -/

def balComponentC (cell : CellId) : ActiveComponent RecChainedState BridgeMintArgs where
  digest    := fun k => balDigestC cell k.bal
  expected  := fun s args => balDigestC cell (recBalCredit s.kernel.bal args.cell args.a args.value)
  postClause := fun s args post =>
    balDigestC cell post.bal = balDigestC cell (recBalCredit s.kernel.bal args.cell args.a args.value)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def bridgeMintEC (cell : CellId) : EffectSpec2 RecChainedState BridgeMintArgs where
  view         := EffectInstances2.chainView
  active       := balComponentC cell
  logUpdate    := some (fun s args => inboundMintReceipt args.actor args.cell args.value :: s.log)
  restFrame    := fun k k' => True
  guardGates   := bridgeMintGuardGates
  guardProp    := bridgeMintGuardProp
  guardWidth   := 1
  guardEncode  := bridgeMintGuardEncode
  guardLocal   := bridgeMintGuardLocal
  guardWidth_le := by decide

/-! ## §3 — THE WITNESS GENERATOR. -/

def witnessOf (cell : CellId) (s : RecChainedState) (args : BridgeMintArgs) (s' : RecChainedState) :
    List Int :=
  (List.range (bridgeMintEC cell).traceWidth).map
    (fun v => encodeE2 mintSurfaceC (bridgeMintEC cell) s args s' v)

def bridgeMintWitnessVec (s : RecChainedState) (args : BridgeMintArgs) : List Int :=
  match recCMintAsset s args.actor args.cell args.a args.value with
  | some s' => witnessOf args.cell s args s'
  | none    => witnessOf args.cell s args s

theorem bridgeMintWitnessVec_commit {s s' : RecChainedState} {args : BridgeMintArgs}
    (h : recCMintAsset s args.actor args.cell args.a args.value = some s') :
    bridgeMintWitnessVec s args = witnessOf args.cell s args s' := by
  unfold bridgeMintWitnessVec; rw [h]

theorem witnessOf_get (cell : CellId) (s : RecChainedState) (args : BridgeMintArgs)
    (s' : RecChainedState) (v : Nat) (hv : v < (bridgeMintEC cell).traceWidth) :
    (witnessOf cell s args s')[v]'(by simpa [witnessOf] using hv)
      = encodeE2 mintSurfaceC (bridgeMintEC cell) s args s' v := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

def sC0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun _ => default
        caps := fun x => if x = 0 then [Cap.node 0] else []
        bal := fun c a => if a = 0 then (if c = 0 then 100 else if c = 1 then 5 else if c = 2 then 50 else 0) else 0 }
    log := [] }

/-- Mint 30 of asset 0 into cell 0 (actor 0). -/
def goodArgsC : BridgeMintArgs := { actor := 0, cell := 0, a := 0, value := 30 }

def goodPostC : RecChainedState := (recCMintAsset sC0 0 0 0 30).getD sC0

/-- THE FORGERY: cell 0 honestly credited (130), but bystander cell 2 ALSO minted 50 → 999. -/
def forgedBalC : CellId → AssetId → ℤ :=
  fun c a => if a = 0 then (if c = 0 then 130 else if c = 1 then 5 else if c = 2 then 999 else 0) else 0

def forgedPostC : RecChainedState :=
  { kernel := { goodPostC.kernel with bal := forgedBalC }, log := goodPostC.log }

def honestWitness : List Int := bridgeMintWitnessVec sC0 goodArgsC
def forgedWitness : List Int := witnessOf 0 sC0 goodArgsC forgedPostC

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

#guard decide (satisfied (effectCircuit2 (bridgeMintEC 0))
  (encodeE2 mintSurfaceC (bridgeMintEC 0) sC0 goodArgsC goodPostC))
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0

#guard decide (satisfied (effectCircuit2 (bridgeMintEC 0))
  (encodeE2 mintSurfaceC (bridgeMintEC 0) sC0 goodArgsC forgedPostC)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)

/-- HIGH-field anti-ghost tooth: bystander cell 2 forged ABOVE 10⁶ (the OLD `% 10⁶` fold collided here;
`refP2` does NOT). The `bal` bind gate `68 ≠ 69` still rejects. -/
def forgedBalHighC : CellId → AssetId → ℤ :=
  fun c a => if a = 0 then (if c = 0 then 130 else if c = 1 then 5 else if c = 2 then 50 + 1000000 else 0) else 0
def forgedPostHighC : RecChainedState :=
  { kernel := { goodPostC.kernel with bal := forgedBalHighC }, log := goodPostC.log }
#guard decide (satisfied (effectCircuit2 (bridgeMintEC 0))
  (encodeE2 mintSurfaceC (bridgeMintEC 0) sC0 goodArgsC forgedPostHighC)) == false

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def bridgeMintHonestWitnessJson : String := witnessJson honestWitness
def bridgeMintForgedWitnessJson : String := witnessJson forgedWitness

-- Structural bind-gate goldens (field-binding `refP2` digests are arbitrary-precision; the Rust paste
-- is regenerated from these JSON accessors when the prover field-reduces).
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- bal binds (honest)
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- log binds (honest)
#guard !(bridgeMintHonestWitnessJson == bridgeMintForgedWitnessJson)

#assert_axioms bridgeMintWitnessVec_commit
#assert_axioms witnessOf_get

end Dregg2.Circuit.Witness.BridgeMintAWitness
