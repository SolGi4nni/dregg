/-
# Dregg2.Circuit.Witness.MintWitness — the WITNESS GENERATOR for `mintA` (v2 family reference).

This closes the verifiable-execution beachhead for `mintA` exactly like
`Dregg2.Circuit.TransferWitness` does for `Transfer`, but over the v2 `EffectCommit2` framework
(`mintA` touches the per-asset ledger `bal`, a `funcComponent`, with a GROWING receipt log). The pieces
that already exist (reused, not re-proved):

  * `Exec.TurnExecutorFull.execFullA` — the REAL executor (`execFullA st (.mintA …) = recCMintAsset …`).
  * `Circuit.Inst.MintA.mintA_full_sound` — a satisfying v2 full-state witness PROVES the complete
    declarative `MintASpec` (all 19 components). The crown-jewel soundness, reused verbatim.
  * `Circuit.EffectCommit2.effect2_circuit_full_complete` — every apex step yields a satisfying witness.
  * `Circuit.EffectCommit2.encodeE2` — the full-state v2 witness layout (74-wide, digests at 64..71).

THE MISSING PIECE this module supplies (the transfer-template's `transferWitnessVec` analog):

    mintWitnessVec : RecChainedState → MintArgs → List Int

that RUNS `execFullA` and lays out the satisfying assignment as a flat `List Int` (column index = wire
index, length = `EffectSpec2.traceWidth = 72`), with the digest columns filled by a CONCRETE commitment
surface (real numbers, not abstract Poseidon terms). This is `execute → the satisfying assignment for
the real per-effect circuit`, materialized for the Rust prover.

Two halves (both reuse existing machinery, no new portals):

  * `execute_produces_satisfying_witness` (abstract): a committed `MintASpec` step makes the full-state
    v2 witness SATISFY the circuit (via `effect2_circuit_full_complete` + the apex bridge).
  * `satisfying_witness_proves_full_state` (abstract): ANY satisfying witness proves `MintASpec` (= the
    reused `mintA_full_sound`).
  * the concrete `#guard`s: the EXECUTOR-DERIVED witness SATISFIES `effectCircuit2` (decidably), and a
    REAL forged post-state (a tampered THIRD ledger entry / a wrong-amount mint) produces a vector the
    circuit REJECTS — a real UNSAT (the bind or rest gate fails). These are the EXACT bytes the Rust
    adversarial test feeds the prover.
-/
import Dregg2.Circuit.Inst.mintA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.MintWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.MintA
open Dregg2.Circuit.Spec.SupplyCreation
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap)
open Dregg2.Circuit.Poseidon2Surface (refP2 turnLogDigest)

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports (so the executor-derived `#guard`s can `decide`). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

instance {St Args : Type} (S : Surface2) (E : EffectSpec2 St Args) (a : Assignment) :
    Decidable (satisfiedE2 S E a) := by unfold satisfiedE2; infer_instance

/-! ## §1 — the CONCRETE commitment surface (real numbers for the Rust prover).

The v2 framework references the rest hash `RH` + log hash `LH` (a `Surface2`) and the touched
component's digest internally. We fix CONCRETE, COMPUTABLE versions over the tiny `#guard` domain — an
INJECTIVE positional fold, never a lossy `+` — so the digest columns are real field values. -/

/-- Concrete per-asset-ledger digest: the REAL `refP2` sponge over the THREE toy `(cell, asset)` entries
the test touches — `(0,0)`, `(1,0)`, `(2,0)` — so a forged THIRD ledger entry is visible EVEN ABOVE 10⁶
(the OLD packed `bal*10¹² + bal*10⁶ + bal` truncated/carried across that window; `refP2` does NOT). -/
def balDigConcrete : (CellId → AssetId → ℤ) → ℤ :=
  fun bal => refP2 [bal 0 0, bal 1 0, bal 2 0]

/-- Concrete rest hash: a field-count of the non-`bal` components (account cardinality + the lengths of
the side-tables) — unchanged by a pure ledger forgery, so the BIND gate (not the rest gate) bites on a
wrong-ledger forgery; a side-table forgery bites the rest gate. -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
            + (k.commitments.length : ℤ) * 11

/-- Concrete log hash: the REAL `turnLogDigest` (`refP2` over the FULL `encTurnRec`, binding
`actor`/`src`/`dst` which the OLD `amt`-only fold DROPPED). CR-grounded on the real `babyBearD4W16`
Poseidon2. -/
def lhConcrete : List Turn → ℤ := turnLogDigest

/-- The concrete v2 surface (rest + log hashes). -/
def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `ActiveComponent` for mint: its `postClause` is the (honest, trivially-bound) DIGEST
EQUALITY `balDigConcrete post.bal = balDigConcrete (recBalCredit …)`. `binds`/`encodes` are then plain
`id` (no injectivity needed) — this carrier exists ONLY to materialize the witness numbers and drive
the decidable `#guard`s. (The injectivity-carrying `mintE D hD`, whose `postClause` is FULL function
equality, is what `mintA_full_sound` consumes abstractly; the gate VALUES the `#guard` decides depend
only on the digest value, identical between the two carriers.) -/
def mintActiveConcrete : ActiveComponent RecChainedState MintArgs where
  digest    := fun k => balDigConcrete k.bal
  expected  := fun s args => balDigConcrete (recBalCredit s.kernel.bal args.cell args.a args.amt)
  postClause := fun s args post =>
    balDigConcrete post.bal = balDigConcrete (recBalCredit s.kernel.bal args.cell args.a args.amt)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

/-- A CONCRETE `EffectSpec2` for mint — used ONLY to materialize the witness vector + drive the
decidable `#guard`s. The guard sub-system, log update and rest frame are mint's real ones (shared with
`mintE`); only the `active` carrier is the trivially-bound concrete one above. -/
def mintEConcrete : EffectSpec2 RecChainedState MintArgs where
  view         := chainView
  active       := mintActiveConcrete
  logUpdate    := some (fun s args => mintReceipt args.actor args.cell args.amt :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt)
  guardGates   := mintGuardGates
  guardProp    := mintGuardProp
  guardWidth   := 1
  guardEncode  := mintGuardEncode
  guardLocal   := mintGuardLocal
  guardWidth_le := by decide

/-! ## §2 — THE WITNESS GENERATOR: `execute → satisfying assignment`.

`mintWitnessFor s args s'` materializes `encodeE2 SC mintEConcrete s args s'` as a flat `List Int` of
length `traceWidth = 72`. `mintWitnessVec s args` is the executor-driven entry: it RUNS `execFullA s
(.mintA …)`; on commit it lays out the witness for the real post-state; on a fail-closed turn it falls
back to `s` (the vector then fails the guard/bind gates, as it should). The digest columns are computed
from the EXECUTOR'S post-state, not hand-picked. -/

/-- Lay an `encodeE2 SC mintEConcrete s args s'` assignment out as a flat `List Int` indexed
`0 .. traceWidth-1`. The witness vector the Rust `build_trace` consumes (column index = wire index). -/
def witnessOf (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) : List Int :=
  (List.range mintEConcrete.traceWidth).map (fun w => encodeE2 SC mintEConcrete s args s' w)

/-- **`mintWitnessVec s args` — the executor-driven witness generator.** Runs `execFullA s (.mintA …)`;
on commit produces the satisfying full-state witness for the executor's post-state, every digest column
filled by the concrete commitment surface. THIS is `execute → the satisfying assignment for the real
per-effect circuit`. -/
def mintWitnessVec (s : RecChainedState) (args : MintArgs) : List Int :=
  match execFullA s (.mintA args.actor args.cell args.a args.amt) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s   -- fail-closed: a non-admissible turn yields a guard-failing vector

/-- **`mintWitnessVec` IS `witnessOf` of the EXECUTOR's post-state** (the some-branch unfold). -/
theorem mintWitnessVec_commit {s s' : RecChainedState} {args : MintArgs}
    (h : execFullA s (.mintA args.actor args.cell args.a args.amt) = some s') :
    mintWitnessVec s args = witnessOf s args s' := by
  unfold mintWitnessVec; rw [h]

/-- Reading the generated vector at a wire `< traceWidth` recovers `encodeE2`. -/
theorem witnessOf_get (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (w : Nat) (hw : w < mintEConcrete.traceWidth) :
    (witnessOf s args s')[w]'(by simpa [witnessOf] using hw) = encodeE2 SC mintEConcrete s args s' w := by
  unfold witnessOf
  rw [List.getElem_map, List.getElem_range]

/-! ## §3 — THE EXECUTE → PROVE / PROVE → SPEC theorems (abstract surface, CR portals carried).

The witness generator is SOUND. We state both halves at the ABSTRACT surface level (carrying the
standard Poseidon-CR portals as hypotheses, exactly as `mintA_full_sound` does). -/

variable (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)

/-- **`execute_produces_satisfying_witness` — the execute→prove direction.** A committed `MintASpec`
step (the executor running the mint) makes the full-state v2 witness `encodeE2 S (mintE D hD) …` SATISFY
the full-state circuit. Reuses `effect2_circuit_full_complete` via the `mintE` apex bridge. -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (hspec : MintASpec s args.actor args.cell args.a args.amt s') :
    satisfiedE2 S (mintE D hD) (encodeE2 S (mintE D hD) s args s') := by
  refine effect2_circuit_full_complete S (mintE D hD)
    (fun k k' h => (hRest k k').mpr h) (mintGuardEncodes D hD) s args s' ?_
  exact (apex_iff_mintASpec D hD s args s').mpr hspec

/-- **`satisfying_witness_proves_full_state` — the verify→accept direction (soundness).** ANY witness
satisfying the full-state circuit proves the complete declarative `MintASpec` (all 19 components). This
IS `mintA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (mintE D hD) (encodeE2 S (mintE D hD) s args s')) :
    MintASpec s args.actor args.cell args.a args.amt s' :=
  mintA_full_sound S D hD hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves).

A concrete THREE-ledger-entry chained state: cells {0,1,2}, ledger `bal` holding 100/5/50 of asset 0 at
cells 0/1/2; actor 0 holds a `node` cap on cell 0 (so `mintAuthorizedB` passes) and mints 30 of asset 0
into cell 0. Cell 2's ledger entry (50) is the bystander. We RUN the executor and materialize the
witness. The `#guard`s certify (decidably, no `native_decide`):

  (1) the generated vector has length 72 (= `traceWidth`);
  (2) the EXECUTOR-DERIVED witness SATISFIES `effectCircuit2` — `execute → prove`;
  (3) the REAL forged post-state (mint bystander cell 2's ledger 50 → 999) produces a witness the
      circuit REJECTS — a real UNSAT (the BIND digest gate fails on the forged ledger). This is the
      anti-ghost tooth, computed end-to-end from a real forged state (NOT a hand-bumped digest). -/

/-- The concrete pre-kernel: cells {0,1,2}, ledger 100/5/50 of asset 0, actor 0 holds a `node` cap on
cell 0 (privileged supply authority over cell 0). -/
def kM0 : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun _ => default
    caps := fun c => if c = 0 then [Cap.node 0] else []
    bal  := fun c a => if a = 0 then (if c = 0 then 100 else if c = 1 then 5 else if c = 2 then 50 else 0)
                       else 0 }

/-- The concrete pre chained state (empty receipt log). -/
def sM0 : RecChainedState := { kernel := kM0, log := [] }

/-- The good mint args: actor 0 mints 30 of asset 0 into cell 0. -/
def goodMintArgs : MintArgs := { actor := 0, cell := 0, a := 0, amt := 30 }

/-- The honest post-state (the executor's committed result of the mint). -/
def goodMintPost : RecChainedState :=
  (execFullA sM0 (.mintA goodMintArgs.actor goodMintArgs.cell goodMintArgs.a goodMintArgs.amt)).getD sM0

/-- **THE FORGERY:** cells 0/1 honest, but the bystander ledger entry `(2,0)` is MINTED from 50 to 999
— value forged into a third ledger slot. The mint's own credit at cell 0 is honest, so the guard +
log pass; the BIND digest gate catches the forged third entry. -/
def forgedThirdLedger : RecChainedState :=
  { goodMintPost with kernel :=
      { goodMintPost.kernel with
        bal := fun c a => if c = 2 ∧ a = 0 then 999 else goodMintPost.kernel.bal c a } }

/-- The honest executor-derived witness vector (= `witnessOf sM0 goodMintArgs goodMintPost`). -/
def honestWitness : List Int := mintWitnessVec sM0 goodMintArgs
/-- The forged witness vector: the SAME pre/args but the REAL `forgedThirdLedger` post-state. -/
def forgedWitness : List Int := witnessOf sM0 goodMintArgs forgedThirdLedger

-- (1) the witness has the trace width the Rust descriptor declares.
#guard honestWitness.length == 72
#guard forgedWitness.length == 72

-- (2) THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the full-state circuit.
#guard decide (satisfiedE2 SC mintEConcrete (encodeE2 SC mintEConcrete sM0 goodMintArgs goodMintPost))
-- ...the generated vector materializes that assignment: guard bit at 0, the three EQ-gate wire-pairs
--    equal (rest 66/67, component 68/69, log 70/71).
#guard honestWitness.getD 0 0 == 1                            -- guard bit
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0     -- restDigPre = restDigPost
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0     -- compDigPost = compDigExpected
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0     -- logDigPost = logDigExpected

-- (3) THE ANTI-GHOST TOOTH (real UNSAT): the forged post-state's witness FAILS the circuit, and
--     specifically it is the COMPONENT-BIND gate (68 ≠ 69) that breaks — the forged ledger is caught.
#guard decide (satisfiedE2 SC mintEConcrete (encodeE2 SC mintEConcrete sM0 goodMintArgs forgedThirdLedger)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- compDigPost ≠ compDigExpected: REJECTED
-- ...while the forgery still keeps the guard bit + log honest (so a guard-only projection would pass):
#guard forgedWitness.getD 0 0 == 1
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0

-- HIGH-field anti-ghost tooth: the bystander entry `(2,0)` forged ABOVE 10⁶ (the OLD packed
-- `bal*10¹² + bal*10⁶ + bal` carried/aliased across that window; `refP2` does NOT). Gate `68 ≠ 69`.
def forgedThirdLedgerHigh : RecChainedState :=
  { goodMintPost with kernel :=
      { goodMintPost.kernel with
        bal := fun c a => if c = 2 ∧ a = 0 then 1000000 else goodMintPost.kernel.bal c a } }
#guard decide (satisfiedE2 SC mintEConcrete (encodeE2 SC mintEConcrete sM0 goodMintArgs forgedThirdLedgerHigh)) == false

/-! ## §5 — JSON export of the witness vectors (the bytes the Rust prover consumes). -/

/-- Render a `List Int` as a JSON number array (the witness wire form). -/
def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

/-- The honest executor-derived witness, as the JSON array the Rust prover proves+verifies. -/
def honestWitnessJson : String := witnessJson honestWitness
/-- The forged witness, as the JSON array the Rust prover REJECTS (component-bind UNSAT). -/
def forgedWitnessJson : String := witnessJson forgedWitness

/-- The mint v2 descriptor (reused from the Inst module — 4 gates, 72 wires). The Rust prover parses
THIS and proves the witness vectors above. -/
def mintDescriptorJson : String := Inst.MintA.mintDescriptorJson

#guard (mintDescriptorJson == r#"{"name":"dregg-mint-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#)

/-! ## §6 — axiom-hygiene tripwires (the witness generator carries no axiom). -/

#assert_axioms mintWitnessVec_commit
#assert_axioms witnessOf_get
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.MintWitness
