/-
# Dregg2.Circuit.Witness.NoteSpendWitness — the WITNESS GENERATOR for `noteSpendA` (v2).

Mirrors the mint/noteCreate witness generators, for `noteSpendA` — the fail-closed note-spend (touched
component = the `nullifiers` LIST; guard = anti-replay `nf ∉ nullifiers`; the log GROWS by the
note-spend receipt). The concrete digest reads the nullifier LIST positionally, so a forged
nullifier-set rewrite (a dropped/reordered prior nullifier — a double-spend laundering) is visible to
the BIND gate (the circuit-level anti-replay tooth).

Reuses (not re-proved): `Inst.NoteSpendA.noteSpendA_full_sound`, `effect2_circuit_full_complete`,
`encodeE2`. No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Circuit.Inst.noteSpendA

namespace Dregg2.Circuit.Witness.NoteSpendWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.NoteSpendA
open Dregg2.Circuit.Spec.NoteNullifier
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

instance {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args) (a : Assignment) :
    Decidable (satisfiedE2 S E a) := by unfold satisfiedE2; infer_instance

/-! ## §1 — the CONCRETE commitment surface. -/

/-- Concrete nullifier-list digest: INJECTIVE positional Horner fold over the `nullifiers` list. -/
def nulDigConcrete : List Nat → ℤ :=
  fun xs => xs.foldl (fun acc x => acc * 1000000 + (x : ℤ)) (xs.length : ℤ)

/-- Concrete rest hash: a field-count of the non-`nullifiers` components. -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.commitments.length : ℤ) * 7
            + (k.escrows.length : ℤ) * 13 + (k.queues.length : ℤ) * 17

/-- Concrete log hash: INJECTIVE positional Horner fold over the receipts. -/
def lhConcrete : List Turn → ℤ :=
  fun ts => ts.foldl (fun acc t => acc * 1000000 + (t.actor : ℤ) + t.amt) (ts.length : ℤ)

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `ActiveComponent` for noteSpend: digest equality on the nullifier list. -/
def nulActiveConcrete : ActiveComponent RecChainedState NoteSpendArgs where
  digest    := fun k => nulDigConcrete k.nullifiers
  expected  := fun s args => nulDigConcrete (args.nf :: s.kernel.nullifiers)
  postClause := fun s args post =>
    nulDigConcrete post.nullifiers = nulDigConcrete (args.nf :: s.kernel.nullifiers)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def noteSpendEConcrete : EffectSpec2 RecChainedState NoteSpendArgs where
  view         := chainView
  active       := nulActiveConcrete
  logUpdate    := some (fun s args => noteSpendReceipt args.actor :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.bal = k.bal ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := noteSpendGuardGates
  guardProp    := noteSpendGuardProp
  guardWidth   := 1
  guardEncode  := noteSpendGuardEncode
  guardLocal   := noteSpendGuardLocal
  guardWidth_le := by decide

/-! ## §2 — THE WITNESS GENERATOR. -/

def witnessOf (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState) : List Int :=
  (List.range noteSpendEConcrete.traceWidth).map (fun w => encodeE2 SC noteSpendEConcrete s args s' w)

def noteSpendWitnessVec (s : RecChainedState) (args : NoteSpendArgs) : List Int :=
  match execFullA s (.noteSpendA args.nf args.actor) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem noteSpendWitnessVec_commit {s s' : RecChainedState} {args : NoteSpendArgs}
    (h : execFullA s (.noteSpendA args.nf args.actor) = some s') :
    noteSpendWitnessVec s args = witnessOf s args s' := by
  unfold noteSpendWitnessVec; rw [h]

theorem witnessOf_get (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (w : Nat) (hw : w < noteSpendEConcrete.traceWidth) :
    (witnessOf s args s')[w]'(by simpa [witnessOf] using hw)
      = encodeE2 SC noteSpendEConcrete s args s' w := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §3 — the EXECUTE → PROVE / PROVE → SPEC theorems (abstract surface). -/

variable (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : ListCommit.listLeafInjective LE)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (hspec : NoteSpendSpec s args.nf args.actor s') :
    satisfiedE2 S (noteSpendE LE cN hN hLE) (encodeE2 S (noteSpendE LE cN hN hLE) s args s') := by
  refine effect2_circuit_full_complete S (noteSpendE LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h) (noteSpendGuardEncodes LE cN hN hLE) s args s' ?_
  exact (apex_iff_noteSpendSpec LE cN hN hLE s args s').mpr hspec

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (noteSpendE LE cN hN hLE) (encodeE2 S (noteSpendE LE cN hN hLE) s args s')) :
    NoteSpendSpec s args.nf args.actor s' :=
  noteSpendA_full_sound S LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- The concrete pre-kernel: cells {0,1}, nullifier set already holding [11, 22] (the bystanders); the
spent nullifier 77 is FRESH (so the anti-replay guard passes). -/
def kS0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => default
    caps := fun _ => []
    nullifiers := [11, 22] }

def sS0 : RecChainedState := { kernel := kS0, log := [] }

/-- The good note-spend args: actor 0 spends fresh nullifier 77. -/
def goodNSArgs : NoteSpendArgs := { nf := 77, actor := 0 }

def goodNSPost : RecChainedState :=
  (execFullA sS0 (.noteSpendA goodNSArgs.nf goodNSArgs.actor)).getD sS0

/-- **THE FORGERY:** the spent nullifier is honest (77 prepended) but a BYSTANDER nullifier is dropped
(22 silently removed) — a double-spend laundering. The BIND digest gate catches the forged set. -/
def forgedNullifierDrop : RecChainedState :=
  { goodNSPost with kernel := { goodNSPost.kernel with nullifiers := [77, 11] } }

def honestWitness : List Int := noteSpendWitnessVec sS0 goodNSArgs
def forgedWitness : List Int := witnessOf sS0 goodNSArgs forgedNullifierDrop

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

#guard decide (satisfiedE2 SC noteSpendEConcrete (encodeE2 SC noteSpendEConcrete sS0 goodNSArgs goodNSPost))
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0

#guard decide (satisfiedE2 SC noteSpendEConcrete (encodeE2 SC noteSpendEConcrete sS0 goodNSArgs forgedNullifierDrop)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- compDigPost ≠ compDigExpected
#guard forgedWitness.getD 0 0 == 1
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

def noteSpendDescriptorJson : String := emitDescriptorJson noteSpendAEmitted

#guard (noteSpendDescriptorJson == r#"{"name":"dregg-noteSpendA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#)

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms noteSpendWitnessVec_commit
#assert_axioms witnessOf_get
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.NoteSpendWitness
