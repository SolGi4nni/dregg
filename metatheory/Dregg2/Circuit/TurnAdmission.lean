/-
# Dregg2.Circuit.TurnAdmission — Wave 5 Prop-level whole-turn proof gate (scaffold).

Documents the operational gap between Lean's emitted-turn soundness scaffold and the Rust
commit-time proof requirement (`turnProofRequired`). No silent admission — the Rust seam is
an explicit `sorry` portal (`hole_rust_proof_at_commit`).
-/
import Dregg2.Circuit.TurnWitness
import Dregg2.Circuit.TurnEmit
import Dregg2.Circuit.TurnCircuitCompose
import Dregg2.Circuit.ActionDispatch

namespace Dregg2.Circuit.TurnAdmission

open Dregg2.Circuit.TurnWitness
  (StepWitness TurnWitness turnWitnessSatisfies foldStepRoots)
open Dregg2.Circuit.TurnEmit
  (TurnEmittedChain turnEmittedSat stepEmittedSat DescriptorLookup defaultDescriptorLookup)
open Dregg2.Circuit.TurnCircuitCompose (turnCircuitOfEmitted hole_turn_macaroon_chain)
open Dregg2.Circuit.ActionDispatch (turnSpec execFullTurnA_iff_turnSpec)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — Prop-level admission gate. -/

/-- **`turnProofRequired`** — a turn commit requires a whole-turn witness whose step-root fold
reaches `postRoot` under the abstract `compress` portal, plus a non-trivial auth-chain digest
(the macaroon caveat-chain column is an explicit Wave-5 sorry). -/
def turnProofRequired (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (w : TurnWitness) : Prop :=
  turnWitnessSatisfies compress stepRoot w ∧
    w.authChain ≠ 0

/-- Turn emission satisfaction implies the root-chain half of `turnProofRequired`. -/
theorem turnProofRequired_of_emitted_chain
    (lookup : DescriptorLookup) (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w) :
    turnWitnessSatisfies compress stepRoot w :=
  h.root_chain

/-! ## §2 — Rust commit-time proof seam (explicit sorry). -/

/-- HOLE W5: the Rust executor's commit path requires a STARK proof over the folded turn circuit,
but the Lean↔Rust proof bundle alignment (descriptor fold + macaroon columns) is not yet wired. -/
theorem hole_rust_proof_at_commit
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (hproof : turnProofRequired compress stepRoot w)
    (h : TurnEmittedChain defaultDescriptorLookup compress stepRoot s acts s' w) :
    execFullTurnA s acts = some s' := by
  sorry

end Dregg2.Circuit.TurnAdmission