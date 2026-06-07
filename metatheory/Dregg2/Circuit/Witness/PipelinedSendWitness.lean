/-
# Dregg2.Circuit.Witness.PipelinedSendWitness — the WITNESS GENERATOR for `pipelinedSendA` (v1).

`pipelinedSendA` is the apply-time-neutral clock tick over the v1 `EffectCommit` (`EffectSpec`) cell-
touching framework: it prepends ONE neutral receipt to the log and LITERALLY freezes the whole kernel
(touched set = ∅). This module supplies the executor-derived witness generator (74-wide, digest wires
64..73), mirroring the transfer/v2 witness modules. Because the kernel is frozen, the anti-ghost forgery
is a THIRD-CELL tamper (any cell value changed) — caught by the FRAME-reuse gate (68 ≠ 69) — exactly the
"pale ghost" the projection circuit would miss.

Reuses (not re-proved): `Inst.PipelinedSendA.pipelinedSendA_full_sound`, `effect_circuit_full_complete`,
`encodeE`. No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on the keystones.
-/
import Dregg2.Circuit.Inst.pipelinedSendA

namespace Dregg2.Circuit.Witness.PipelinedSendWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.Inst.PipelinedSendA
open Dregg2.Circuit.Spec.QueuePipelinedSend
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

instance {St Args : Type} (S : CommitSurface) (E : EffectSpec St Args) (a : Assignment) :
    Decidable (satisfiedE S E a) := by unfold satisfiedE; infer_instance

/-! ## §1 — the CONCRETE commitment surface (real numbers for the Rust prover).

The v1 `CommitSurface` carries `CH`/`RH`/`cmb`/`compressN`/`LH`. We fix CONCRETE, COMPUTABLE versions
over the tiny `#guard` domain — INJECTIVE positional folds, never lossy `+` — so the digest columns are
real field values. -/

/-- Concrete cell-leaf hash: the cell's `balance` field (so a tampered cell value is visible). -/
def chConcrete : CellId → Value → ℤ := fun _ v => balOf v

/-- Concrete rest hash: a field-count of the non-`cell` components (frozen by the apex). -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7 + (k.commitments.length : ℤ) * 11

/-- Concrete root combiner: an INJECTIVE-on-the-toy-domain pairing, reduced mod a large prime so the
NESTED root wires (`preRoot`/`postRoot` at 64/65, which `cmb` the cell digest with `cmb RH LH`) stay
within `i64` for the Rust prover. The root wires are UNCONSTRAINED by `effectCircuit` (no gate reads
64/65), so the reduction is harmless; the CONSTRAINED frame/rest/log gate wires read `frameDigest`/`RH`/
`LH` DIRECTLY (not through `cmb`), so they are unaffected. -/
def cmbConcrete : ℤ → ℤ → ℤ := fun a b => (a * 1000003 + b) % 2000000000000000000

/-- Concrete sponge: an INJECTIVE positional Horner fold (each leaf shifted by a base larger than any
toy leaf; the length folded in so distinct-length lists never collide). -/
def compressNConcrete : List ℤ → ℤ :=
  fun xs => xs.foldl (fun acc x => acc * 1000000 + x) (xs.length : ℤ)

/-- Concrete log hash: an INJECTIVE positional Horner fold over the receipts. -/
def lhConcrete : List Turn → ℤ :=
  fun ts => ts.foldl (fun acc t => acc * 1000000 + (t.actor : ℤ) + t.amt) (ts.length : ℤ)

def SC : CommitSurface :=
  { CH := chConcrete, RH := rhConcrete, cmb := cmbConcrete, compressN := compressNConcrete,
    LH := lhConcrete }

/-! ## §2 — THE WITNESS GENERATOR.

`encodeE SC pipelinedSendE s args s'` lays the full-state v1 witness out; the touched carrier is `∅`
(kernel frozen), the frame carrier is `accounts`. -/

def witnessOf (s : RecChainedState) (args : PipelinedSendArgs) (s' : RecChainedState) : List Int :=
  (List.range pipelinedSendE.traceWidth).map (fun w => encodeE SC pipelinedSendE s args s' w)

/-- **`pipelinedSendWitnessVec s args` — the executor-driven witness generator.** Runs `execFullA s
(.pipelinedSendA …)`; on commit lays out the satisfying full-state witness for the executor's
post-state. -/
def pipelinedSendWitnessVec (s : RecChainedState) (args : PipelinedSendArgs) : List Int :=
  match execFullA s (.pipelinedSendA args.actor) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem pipelinedSendWitnessVec_commit {s s' : RecChainedState} {args : PipelinedSendArgs}
    (h : execFullA s (.pipelinedSendA args.actor) = some s') :
    pipelinedSendWitnessVec s args = witnessOf s args s' := by
  unfold pipelinedSendWitnessVec; rw [h]

theorem witnessOf_get (s : RecChainedState) (args : PipelinedSendArgs) (s' : RecChainedState)
    (w : Nat) (hw : w < pipelinedSendE.traceWidth) :
    (witnessOf s args s')[w]'(by simpa [witnessOf] using hw)
      = encodeE SC pipelinedSendE s args s' w := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §3 — the EXECUTE → PROVE / PROVE → SPEC theorems (abstract surface, CR portals carried). -/

variable (S : CommitSurface)

theorem execute_produces_satisfying_witness
    (hRest : RestHashIffFrame S.RH)
    (s : RecChainedState) (args : PipelinedSendArgs) (s' : RecChainedState)
    (hspec : PipelinedSendSpec s args.actor s') :
    satisfiedE S pipelinedSendE (encodeE S pipelinedSendE s args s') := by
  refine effect_circuit_full_complete S pipelinedSendE hRest pipelinedSendGuardEncodes s args s' ?_
  exact (apex_iff_pipelinedSendSpec s args s').mpr hspec

theorem satisfying_witness_proves_full_state
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : PipelinedSendArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S pipelinedSendE (encodeE S pipelinedSendE s args s')) :
    PipelinedSendSpec s args.actor s' :=
  pipelinedSendA_full_sound S hN hL hRest hLog s args s' hwf hwf' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- The concrete pre-kernel: cells {0,1,2} with balances 100/5/50 (the bystanders the frozen frame must
preserve). -/
def kP0 : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun c => if c = 0 then .record [("balance", .int 100)]
                     else if c = 1 then .record [("balance", .int 5)]
                     else if c = 2 then .record [("balance", .int 50)]
                     else default
    caps := fun _ => [] }

def sP0 : RecChainedState := { kernel := kP0, log := [] }

/-- The good pipelined-send args: actor 0 ticks the clock (no fail-closed gate). -/
def goodPSArgs : PipelinedSendArgs := { actor := 0 }

def goodPSPost : RecChainedState :=
  (execFullA sP0 (.pipelinedSendA goodPSArgs.actor)).getD sP0

/-- **THE FORGERY:** the log advance is honest, but a BYSTANDER cell (cell 2) is minted (50 → 999) — a
tampered frozen-frame cell. The FRAME-reuse digest gate (68 ≠ 69) catches it. -/
def forgedThirdCell : RecChainedState :=
  { goodPSPost with kernel := { goodPSPost.kernel with
      cell := fun c => if c = 2 then .record [("balance", .int 999)] else goodPSPost.kernel.cell c } }

def honestWitness : List Int := pipelinedSendWitnessVec sP0 goodPSArgs
def forgedWitness : List Int := witnessOf sP0 goodPSArgs forgedThirdCell

#guard honestWitness.length == 74
#guard forgedWitness.length == 74

#guard decide (satisfiedE SC pipelinedSendE (encodeE SC pipelinedSendE sP0 goodPSArgs goodPSPost))
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0   -- rest frame
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- frame-reuse (all cells frozen)
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- touched (∅ carrier — trivially equal)
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0   -- log

#guard decide (satisfiedE SC pipelinedSendE (encodeE SC pipelinedSendE sP0 goodPSArgs forgedThirdCell)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- frameDigPre ≠ frameDigPost: REJECTED
#guard forgedWitness.getD 0 0 == 1
#guard forgedWitness.getD 72 0 == forgedWitness.getD 73 0      -- log still honest

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

def pipelinedSendDescriptorJson : String := emitDescriptorJson pipelinedSendAEmitted

#guard (pipelinedSendDescriptorJson == r#"{"name":"dregg-pipelinedSendA-v1","trace_width":74,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}}]}"#)

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms pipelinedSendWitnessVec_commit
#assert_axioms witnessOf_get
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.PipelinedSendWitness
