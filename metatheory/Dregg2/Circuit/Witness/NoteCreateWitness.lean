/-
# Dregg2.Circuit.Witness.NoteCreateWitness — the WITNESS GENERATOR for `noteCreateA` (v2).

Mirrors `Dregg2.Circuit.Witness.MintWitness` exactly, but for `noteCreateA` — the GROW-ONLY
note-commitment publish (touched component = the `commitments` LIST; guard = trivial `True`; the log
GROWS by the note-create receipt). The concrete digest reads the commitment LIST positionally, so a
forged third commitment (a tampered post-list — drop/reorder/inject) is visible to the BIND gate.

Reuses (not re-proved): `Inst.NoteCreateA.noteCreateA_full_sound` (a satisfying v2 witness ⇒
`NoteCreateASpec`), `effect2_circuit_full_complete` (execute ⇒ satisfying), `encodeE2` (the layout).

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on the keystones.
-/
import Dregg2.Circuit.Inst.noteCreateA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.NoteCreateWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.NoteCreateA
open Dregg2.Circuit.Spec.NoteCommitment
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

/-- Concrete commitment-list digest: an INJECTIVE positional Horner fold over the `commitments` list
(length folded in so distinct-length lists never collide; each entry shifted by a base larger than any
toy commitment). A drop/reorder/inject of an entry changes this digest. -/
def comDigConcrete : List Nat → ℤ :=
  fun xs => xs.foldl (fun acc x => acc * 1000000 + (x : ℤ)) (xs.length : ℤ)

/-- Concrete rest hash: a field-count of the non-`commitments` components. -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
            + (k.escrows.length : ℤ) * 13 + (k.queues.length : ℤ) * 17

/-- Concrete log hash: the REAL `Poseidon2Surface.refP2` sponge over the FULL `encTurnRec` (binds
`src`/`dst`, which the OLD `lhConcrete` DROPPED — `acc*10⁶ + actor + amt`). CR-grounded on the real
`babyBearD4W16` Poseidon2 via `Poseidon2Surface.realRealizedSponge`. -/
def lhConcrete : List Turn → ℤ := Dregg2.Circuit.Poseidon2Surface.turnLogDigest

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `ActiveComponent` for noteCreate: `postClause` is the (honest, trivially-bound) digest
equality on the commitment list; `binds`/`encodes` are `id`. For materializing witness numbers + the
decidable `#guard`s (the injectivity-carrying `noteCreateE` is what `noteCreateA_full_sound` consumes). -/
def comActiveConcrete : ActiveComponent RecChainedState NoteCreateArgs where
  digest    := fun k => comDigConcrete k.commitments
  expected  := fun s args => comDigConcrete (args.cm :: s.kernel.commitments)
  postClause := fun s args post =>
    comDigConcrete post.commitments = comDigConcrete (args.cm :: s.kernel.commitments)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

/-- A CONCRETE `EffectSpec2` for noteCreate — used ONLY to materialize the witness + drive `#guard`s. -/
def noteCreateEConcrete : EffectSpec2 RecChainedState NoteCreateArgs where
  view         := chainView
  active       := comActiveConcrete
  logUpdate    := some (fun s args => noteCreateReceipt args.actor :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.bal = k.bal ∧ k'.queues = k.queues ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := noteCreateGuardGates
  guardProp    := noteCreateGuardProp
  guardWidth   := 1
  guardEncode  := noteCreateGuardEncode
  guardLocal   := noteCreateGuardLocal
  guardWidth_le := by decide

/-! ## §2 — THE WITNESS GENERATOR. -/

def witnessOf (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState) : List Int :=
  (List.range noteCreateEConcrete.traceWidth).map (fun w => encodeE2 SC noteCreateEConcrete s args s' w)

/-- **`noteCreateWitnessVec s args` — the executor-driven witness generator.** Runs `execFullA s
(.noteCreateA …)`; on commit lays out the satisfying full-state witness for the executor's post-state. -/
def noteCreateWitnessVec (s : RecChainedState) (args : NoteCreateArgs) : List Int :=
  match execFullA s (.noteCreateA args.cm args.actor) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem noteCreateWitnessVec_commit {s s' : RecChainedState} {args : NoteCreateArgs}
    (h : execFullA s (.noteCreateA args.cm args.actor) = some s') :
    noteCreateWitnessVec s args = witnessOf s args s' := by
  unfold noteCreateWitnessVec; rw [h]

theorem witnessOf_get (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState)
    (w : Nat) (hw : w < noteCreateEConcrete.traceWidth) :
    (witnessOf s args s')[w]'(by simpa [witnessOf] using hw)
      = encodeE2 SC noteCreateEConcrete s args s' w := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §3 — the EXECUTE → PROVE / PROVE → SPEC theorems (abstract surface, CR portals carried). -/

variable (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : ListCommit.listLeafInjective LE)

/-- **`execute_produces_satisfying_witness`.** A committed `NoteCreateASpec` step makes the v2 witness
SATISFY the circuit (via `effect2_circuit_full_complete` + the apex bridge). -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoCommitments S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState)
    (hspec : NoteCreateASpec s args.cm args.actor s') :
    satisfiedE2 S (noteCreateE LE cN hN hLE) (encodeE2 S (noteCreateE LE cN hN hLE) s args s') := by
  refine effect2_circuit_full_complete S (noteCreateE LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h) (noteCreateGuardEncodes LE cN hN hLE) s args s' ?_
  exact (apex_iff_noteCreateASpec LE cN hN hLE s args s').mpr hspec

/-- **`satisfying_witness_proves_full_state`** — ANY satisfying witness proves `NoteCreateASpec`. IS
`noteCreateA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoCommitments S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (noteCreateE LE cN hN hLE) (encodeE2 S (noteCreateE LE cN hN hLE) s args s')) :
    NoteCreateASpec s args.cm args.actor s' :=
  noteCreateA_full_sound S LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- The concrete pre-kernel: cells {0,1}, commitment set already holding [11, 22] (the bystanders). -/
def kN0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => default
    caps := fun _ => []
    commitments := [11, 22] }

def sN0 : RecChainedState := { kernel := kN0, log := [] }

/-- The good note-create args: actor 0 publishes commitment 77. -/
def goodNCArgs : NoteCreateArgs := { cm := 77, actor := 0 }

def goodNCPost : RecChainedState :=
  (execFullA sN0 (.noteCreateA goodNCArgs.cm goodNCArgs.actor)).getD sN0

/-- **THE FORGERY:** the new commitment is honest (77 prepended) but a BYSTANDER commitment is rewritten
(22 → 999) — a tampered post-list. The BIND digest gate catches the forged list. -/
def forgedThirdCommit : RecChainedState :=
  { goodNCPost with kernel := { goodNCPost.kernel with commitments := [77, 11, 999] } }

def honestWitness : List Int := noteCreateWitnessVec sN0 goodNCArgs
def forgedWitness : List Int := witnessOf sN0 goodNCArgs forgedThirdCommit

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

#guard decide (satisfiedE2 SC noteCreateEConcrete (encodeE2 SC noteCreateEConcrete sN0 goodNCArgs goodNCPost))
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0

#guard decide (satisfiedE2 SC noteCreateEConcrete (encodeE2 SC noteCreateEConcrete sN0 goodNCArgs forgedThirdCommit)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- compDigPost ≠ compDigExpected
#guard forgedWitness.getD 0 0 == 1
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

/-- The noteCreate v2 descriptor (4 gates, 72 wires). -/
def noteCreateDescriptorJson : String := emitDescriptorJson noteCreateAEmitted

#guard (noteCreateDescriptorJson == r#"{"name":"dregg-noteCreateA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#)

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms noteCreateWitnessVec_commit
#assert_axioms witnessOf_get
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.NoteCreateWitness
