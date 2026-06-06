/-
# Dregg2.Circuit.TurnWitness — circuit-level turn witness scaffolding.

Abstract turn witnesses for the Wave-1 gadget/witness layer: per-action `StepWitness` records
(action tag + encoded assignment), bundled into a `TurnWitness` with pre/post roots and an auth-chain
digest. `turnWitnessSatisfies` folds step witnesses through an abstract `compress` portal (state-root
chaining); `turn_witness_refines_turnCircuit` lifts per-step declarative satisfaction to `turnSpec`.

§4b makes the turn root AUTHENTIC (no longer decorative): `authenticTurnRoots` binds `preRoot`/
`postRoot` to `StateCommit.recStateCommit` of the boundary kernels (a genuine binding full-state
commitment over all 17 fields). `turnWitnessSatisfies_binds_postRoot` makes `turnWitnessSatisfies`
load-bearing — the prover-folded post-root is forced to equal the real post-state commitment —
`tampered_postRoot_rejects` is the anti-ghost tooth (a forged post-root has no authentic witness),
and `authentic_roots_bind_state` is the headline (the published root binds the whole post-state).

Links to `execFullTurnA` via `ActionDispatch.execFullTurnA_iff_turnSpec` and `fullActionStep_exec_iff`.

Wave 7 precursor: `InnerTurnWitness` for exercise inner-fold scaffolding (`inner_turn_witness_refines_spec`
is an explicit `sorry`). Core §1–§4 remain `#assert_axioms`-clean.
-/
import Dregg2.Circuit.Refinement
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.TurnRefinement

namespace Dregg2.Circuit.TurnWitness

open Dregg2.Circuit.Refinement (Refines StepRel)
open Dregg2.Circuit.ActionDispatch
  (fullActionStep fullActionStep_exec_iff actionTag turnSpec turnSpec_eq_spec
   execFullTurnA_iff_turnSpec exerciseHoldState)
open Dregg2.Circuit.TurnRefinement (TurnStateChain turnSpec_of_turnStateChain)
open Dregg2.Circuit.StateCommit (recStateCommit recStateCommit_binds compressInjective cellDigest)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — Witness carriers. -/

/-- **`StepWitness`** — one action's circuit witness: the constructor tag (wire metadata) plus the
encoded assignment bytes as an abstract `List ℤ` (the trace columns the prover fills). -/
structure StepWitness where
  /-- The `FullActionA` constructor tag (abstract index for the wire decoder). -/
  tag        : Nat
  /-- The encoded assignment bytes (abstract field elements over the trace). -/
  assignment : List ℤ
  deriving Repr, DecidableEq

/-- **`TurnWitness`** — a whole-turn witness bundle: boundary roots, per-step witnesses, and the
auth-chain digest (the §8 credential/delegation chain the turn's auth receipts commit to). -/
structure TurnWitness where
  /-- Pre-turn state root (abstract `compress` portal). -/
  preRoot    : ℤ
  /-- Post-turn state root. -/
  postRoot   : ℤ
  /-- Per-action step witnesses, left-to-right. -/
  steps      : List StepWitness
  /-- Auth-chain digest (abstract commitment to the turn's authority receipts). -/
  authChain  : ℤ
  deriving Repr, DecidableEq

/-! ## §2 — Step-root chaining (abstract `compress` portal). -/

/-- Digest of a single step witness under abstract `stepRoot` (the per-action commitment portal). -/
def stepWitnessDigest (stepRoot : StepWitness → ℤ) (sw : StepWitness) : ℤ :=
  stepRoot sw

/-- Fold step witnesses into a root chain: `foldl (compress acc (stepRoot sw)) preRoot steps`. -/
def foldStepRoots (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (preRoot : ℤ) (steps : List StepWitness) : ℤ :=
  steps.foldl (fun acc sw => compress acc (stepWitnessDigest stepRoot sw)) preRoot

/-- **`turnWitnessSatisfies`** — the turn witness is satisfied when the step fold reaches `postRoot`
under the abstract `compress` portal (realized by Poseidon `compress` at the Rust layer). -/
def turnWitnessSatisfies (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (w : TurnWitness) : Prop :=
  foldStepRoots compress stepRoot w.preRoot w.steps = w.postRoot

/-! ## §3 — Per-step satisfaction and turn-circuit refinement. -/

/-- Per-step witness satisfaction: tag matches the action and the declarative step holds. -/
def stepWitnessSatisfies (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA) : Prop :=
  sw.tag = actionTag fa ∧ fullActionStep st fa st'

/-- **`turn_witness_refines_turnCircuit`** — if each step witness satisfies its declarative step
along a matching state chain, the full turn refines to `turnSpec`. -/
theorem turn_witness_refines_turnCircuit
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (hlen : acts.length = w.steps.length)
    (states : List RecChainedState)
    (hchain_len : states.length = acts.length + 1)
    (hchain_head : states[0]'(by rw [hchain_len]; omega) = s)
    (hchain_last : states[acts.length]'(by rw [hchain_len]; omega) = s')
    (hsteps :
      ∀ (i : Fin acts.length),
        stepWitnessSatisfies w.steps[i] (states[i.val]'(by rw [hchain_len]; omega))
          (states[i.val + 1]'(by rw [hchain_len]; omega)) acts[i]) :
    turnSpec s acts s' :=
  (turnSpec_eq_spec s acts s').mpr <|
    turnSpec_of_turnStateChain fullActionStep s s' acts {
      chain := states
      chain_len := hchain_len
      chain_head := hchain_head
      chain_last := hchain_last
      step_witness := fun i => (hsteps i).2 }

/-! ## §4 — Link to `execFullTurnA` (via `ActionDispatch` bridge). -/

/-- **`turn_witness_refines_exec`** — a `turnSpec` commitment refines to a genuine
`execFullTurnA` execution. -/
theorem turn_witness_refines_exec (s s' : RecChainedState) (acts : List FullActionA)
    (h : turnSpec s acts s') :
    execFullTurnA s acts = some s' :=
  (execFullTurnA_iff_turnSpec s s' acts).mpr h

/-- **`turnWitness_exec_link`** — alias: declarative turn spec ⟹ executor commit. -/
theorem turnWitness_exec_link (s s' : RecChainedState) (acts : List FullActionA)
    (h : turnSpec s acts s') :
    execFullTurnA s acts = some s' :=
  turn_witness_refines_exec s s' acts h

/-! ## §4b — AUTHENTIC turn roots (the root is a genuine full-state commitment, not decoration).

The §1 `TurnWitness.preRoot`/`postRoot` are free `ℤ` fields and `turnWitnessSatisfies` folds them
over an UNINTERPRETED `compress`/`stepRoot` — so on their own they are decorative (any fold value
reaches any `postRoot`). This section pins them to `StateCommit.recStateCommit`, the GENUINE binding
full-state commitment (a Poseidon Merkle root over all 17 `RecordKernelState` fields), and makes
`turnWitnessSatisfies` load-bearing: the prover-folded post-root is forced to equal the real
post-state commitment, so a tampered `postRoot` is rejected. -/

/-- **`authenticTurnRoots`** — bind the witness boundary roots to the GENUINE full-state commitments
of the boundary kernels (under a chosen commitment surface + turn). The roots are no longer free
decoration: `preRoot` IS `recStateCommit` of `s.kernel` and `postRoot` IS `recStateCommit` of
`s'.kernel`. -/
def authenticTurnRoots
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (s s' : RecChainedState) (t : Turn) (w : TurnWitness) : Prop :=
  w.preRoot  = recStateCommit CH RH cmb compress compressN s.kernel  t ∧
  w.postRoot = recStateCommit CH RH cmb compress compressN s'.kernel t

/-- **`authStepRoot`** — the realized step-root portal: the per-step commitment is the genuine
full-state commitment of the step's emitted kernel (decoded from the step witness). Instantiating
`stepRoot` with this makes `foldStepRoots` chain REAL commitments, not abstract tags. -/
def authStepRoot
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (decodeK : StepWitness → RecordKernelState) (t : Turn) : StepWitness → ℤ :=
  fun sw => recStateCommit CH RH cmb compress compressN (decodeK sw) t

/-- **`turnWitnessSatisfies_binds_postRoot`** — `turnWitnessSatisfies` is CONSUMED (load-bearing):
the step-root fold reaching `postRoot`, together with authentic boundary roots, forces the folded
value to equal the GENUINE `recStateCommit` of `s'.kernel`. The root chain equates the prover-folded
root with the real post-state commitment. -/
theorem turnWitnessSatisfies_binds_postRoot
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (stepRoot : StepWitness → ℤ) (foldCompress : ℤ → ℤ → ℤ)
    (s s' : RecChainedState) (t : Turn) (w : TurnWitness)
    (hauth : authenticTurnRoots CH RH cmb compress compressN s s' t w)
    (hsat : turnWitnessSatisfies foldCompress stepRoot w) :
    foldStepRoots foldCompress stepRoot w.preRoot w.steps
      = recStateCommit CH RH cmb compress compressN s'.kernel t := by
  rw [hsat]; exact hauth.2

/-- **`tampered_postRoot_rejects`** — ANTI-GHOST tooth. A witness declaring a `postRoot` that is NOT
the genuine post-state commitment cannot have authentic roots: the root chain rejects a silent
post-state swap. (Combined with `turnWitnessSatisfies_binds_postRoot`, a satisfying witness with a
forged `postRoot` is impossible.) -/
theorem tampered_postRoot_rejects
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (s s' : RecChainedState) (t : Turn) (w : TurnWitness)
    (htamper : w.postRoot ≠ recStateCommit CH RH cmb compress compressN s'.kernel t) :
    ¬ authenticTurnRoots CH RH cmb compress compressN s s' t w := by
  intro hauth
  exact htamper hauth.2

/-- **`authentic_roots_bind_state`** — the headline: with injective `cmb`, two witnesses carrying
equal authentic `postRoot`s force their post-states to commit to equal cell-digest + rest-hash (the
published root binds the whole state, via `StateCommit.recStateCommit_binds`). The turn root is a
genuine binding commitment to the post-state, not decoration. -/
theorem authentic_roots_bind_state
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hCmb : compressInjective cmb)
    (s s' s'' : RecChainedState) (t : Turn) (w w' : TurnWitness)
    (hauth  : authenticTurnRoots CH RH cmb compress compressN s s'  t w)
    (hauth' : authenticTurnRoots CH RH cmb compress compressN s s'' t w')
    (heq : w.postRoot = w'.postRoot) :
    cellDigest CH compress compressN s'.kernel t
        = cellDigest CH compress compressN s''.kernel t
      ∧ RH s'.kernel = RH s''.kernel := by
  have hroot : recStateCommit CH RH cmb compress compressN s'.kernel t
       = recStateCommit CH RH cmb compress compressN s''.kernel t := by
    rw [← hauth.2, ← hauth'.2, heq]
  exact recStateCommit_binds CH RH cmb compress compressN hCmb s'.kernel s''.kernel t hroot

/-! ### Non-vacuity: a witness where `authenticTurnRoots` HOLDS, and a tampered one where it is FALSE.

These are closed proofs (not `#guard` — the abstract surface is `ℤ`-valued and not `Decidable` on a
free state), pinning the spec as genuinely two-sided: the honest witness inhabits it, the tampered
witness refutes it. -/

/-- WITNESS (HOLDS): the genuine-root witness inhabits `authenticTurnRoots`. -/
example (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (s s' : RecChainedState) (t : Turn) :
    authenticTurnRoots CH RH cmb compress compressN s s' t
      { preRoot  := recStateCommit CH RH cmb compress compressN s.kernel t,
        postRoot := recStateCommit CH RH cmb compress compressN s'.kernel t,
        steps := [], authChain := 0 } :=
  ⟨rfl, rfl⟩

/-- WITNESS (FALSE): a witness whose `postRoot` is provably NOT the genuine commitment refutes
`authenticTurnRoots` — the spec is non-vacuous (it can fail). Here `cmb := fun _ _ => 0` and
`postRoot := 1 ≠ 0 = recStateCommit …`, so the tamper is concrete. -/
example (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (s s' : RecChainedState) (t : Turn) :
    ¬ authenticTurnRoots CH RH (fun _ _ => 0) compress compressN s s' t
      { preRoot := 0, postRoot := 1, steps := [], authChain := 0 } := by
  apply tampered_postRoot_rejects
  -- genuine commitment is `cmb _ _ = 0`; the forged `postRoot = 1 ≠ 0`.
  simp [recStateCommit]

/-! ## §5 — Inner turn witness (exercise `exerciseA` scaffold, Wave 7 precursor). -/

/-- **`InnerTurnWitness`** — bundles the exercise hold-gate step witness with an inner whole-turn
witness for the nested `List FullActionA` fold (R4 facet-mask arithmetization deferred). -/
structure InnerTurnWitness where
  /-- Hold-gate step witness (outer `exerciseA` frame). -/
  holdStep   : StepWitness
  /-- Inner turn witness over the nested action list. -/
  innerTurn  : TurnWitness
  /-- Inner step count matches the inner turn witness length. -/
  inner_len  : Nat
  deriving Repr, DecidableEq

/-- Inner fold satisfaction: hold step tagged as exercise + inner turn root chain. -/
def innerTurnWitnessSatisfies (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (itw : InnerTurnWitness) (innerActs : List FullActionA) : Prop :=
  itw.inner_len = innerActs.length ∧
    itw.inner_len = itw.innerTurn.steps.length ∧
    turnWitnessSatisfies compress stepRoot itw.innerTurn

/-- HOLE W7: inner turn witness soundness — lift inner fold to `turnSpec` under the exercise hold. -/
theorem inner_turn_witness_refines_spec
    (pre post : RecChainedState) (actor target : CellId) (inner : List FullActionA)
    (itw : InnerTurnWitness) (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (h : innerTurnWitnessSatisfies compress stepRoot itw inner) :
    turnSpec (exerciseHoldState pre actor) inner post := by
  sorry

#assert_axioms turn_witness_refines_turnCircuit
#assert_axioms turn_witness_refines_exec
#assert_axioms turnWitness_exec_link
#assert_axioms turnWitnessSatisfies_binds_postRoot
#assert_axioms tampered_postRoot_rejects
#assert_axioms authentic_roots_bind_state

end Dregg2.Circuit.TurnWitness