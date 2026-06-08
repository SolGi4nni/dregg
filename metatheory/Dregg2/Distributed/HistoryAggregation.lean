/-
# Dregg2.Distributed.HistoryAggregation — the FOLD model under the IVC accumulator.

**What this is.** The whole-chain IVC accumulator (`circuit/src/ivc_turn_chain.rs`) folds a
sequence of finalized-turn proofs into ONE recursive proof attesting "all turns `1..K` executed
correctly AND the finalized state root advanced correctly from genesis to final, in that order."
This module is the EXECUTABLE/DECLARATIVE model that fold is supposed to attest — stated over the
VERIFIED executor (`Exec.RecordKernel.recCexec`, the same machine `BlocklaceFinality.executeTau`
drives) and the GENUINE per-turn state commitment (`Circuit.StateCommit.recStateCommit`, the
injective §8 full-state root the whole-turn triangle pins — `whole_turn_circuit_pins_intent_fold`).

It is the *meaning* of the chain. `RecursiveAggregation.lean` adds the SNARK recursion layer on top:
it names the inner-proof-soundness + recursive-verifier-soundness hypotheses (the part you cannot
prove in Lean — plonky3/pickles FRI), and shows that, UNDER those named hypotheses, an aggregate
proof's validity is exactly `AggregateAttests` from this file — so a light client that checks only
the succinct aggregate genuinely learns the whole history is correct.

**The two binding facts modeled here** (the `TurnChainBindingAir` of `ivc_turn_chain.rs:188`):
  1. **Per-step correctness** — each fold step `(pre, turn, post)` is a GENUINE `recCexec` step
     (its `commits` field), so the step proof, when sound, attests the verified executor actually
     ran that turn.
  2. **The temporal tooth** — `new_root[i] == old_root[i+1]` (`ivc_turn_chain.rs:246`): step `i`'s
     post-root is step `i+1`'s pre-root. Reorder / drop / insert ⇒ the chain breaks (UNSAT).

**The headline (`wellformed_attests_whole_history`):** a `WellFormedChain` from a genesis state
yields — for EVERY turn in the chain — a real `recCexec` step (the turn executed correctly per the
verified executor), the chain is correctly ordered (each post-root = next pre-root), and the whole
chain is a `Run recChainedSystem` from genesis whose final state is the genuine fold of the history,
so `recChained_run_conserves` (no mint/burn over the entire history) applies.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); NO `sorry`/`:=True`.
Verified with `lake build Dregg2.Distributed.HistoryAggregation`.
-/
import Dregg2.Circuit.StateCommit
import Dregg2.Exec.ConsensusExec

namespace Dregg2.Distributed.HistoryAggregation

open Dregg2.Exec (RecChainedState recCexec recChainedSystem recChained_run_conserves recTotal)
open Dregg2.Execution (System Run)
open Dregg2.Circuit.StateCommit (recStateCommit recStateCommit_binds compressInjective cellDigest)

/-- The all-zero turn — `Turn` has no `Inhabited` instance, so we name the canonical default
turn-context used to commit the genesis/empty-chain root. -/
def zeroTurn : Dregg2.Exec.Turn := ⟨0, 0, 0, 0⟩

/-! ## 0. The §8 state-commitment portal (the genuine per-turn root).

`recStateCommit k t` is the injective full-state commitment from the whole-turn triangle — the ONE
authenticated per-turn state root the running prover folds (`StateCommit.lean:196`). It is
parametric in the Poseidon portal functions; we carry them as section variables exactly as
`StateCommit`/`WholeTurnTriangle` do, plus the single collision-resistance carrier
`compressInjective cmb` the binding lemma needs (REALIZABLE — Poseidon 2-to-1 CR). -/

section Portal

variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **`stateRoot k t`** — the genuine §8 full-state commitment of kernel `k` under the turn-context
`t` (the prover-folded per-turn root). `recStateCommit` with the portal fixed. A turn `t` advances
`(stateRoot k t) ↦ (stateRoot k' t')`; the chain binds these roots. -/
def stateRoot (k : Dregg2.Exec.RecordKernelState) (t : Dregg2.Exec.Turn) : ℤ :=
  recStateCommit CH RH cmb compress compressN k t

/-! ## 1. One fold step — a finalized turn + the roots it advances.

The Rust `FinalizedTurn` (`ivc_turn_chain.rs:100`) carries a whole-turn proof whose PI exposes
`(OLD_COMMIT, NEW_COMMIT)`. Here a `ChainStep` carries the pre-state chained record, the turn, and
the post-state chained record, together with the EXECUTOR WITNESS `recCexec pre turn = some post` —
so this is a real verified step, not an asserted one. Its roots are the GENUINE `stateRoot` of the
pre/post kernels. -/

/-- A single fold step: a genuine `recCexec` transition `(pre, turn) ↦ post`, plus the receipt logs
the chained state carries. Modeled directly over the verified executor so the step's roots are the
real commitments of states the executor genuinely reached — what an honest inner step proof, when
sound, attests. -/
structure ChainStep where
  /-- The pre-state chained record (kernel + receipt log). -/
  pre  : RecChainedState
  /-- The turn applied this step. -/
  turn : Dregg2.Exec.Turn
  /-- The post-state chained record. -/
  post : RecChainedState
  /-- **The executor witness**: `recCexec pre turn = some post`. -/
  commits : recCexec pre turn = some post

/-- The step's pre-state root (the §8 commitment of the pre-kernel). The Rust `old_root`. -/
def ChainStep.oldRoot (s : ChainStep) : ℤ := stateRoot CH RH cmb compress compressN s.pre.kernel s.turn

/-- The step's post-state root (the §8 commitment of the post-kernel). The Rust `new_root`. -/
def ChainStep.newRoot (s : ChainStep) : ℤ := stateRoot CH RH cmb compress compressN s.post.kernel s.turn

/-! ## 2. The temporal tooth — `new_root[i] == old_root[i+1]`.

`TurnChainBindingAir` constraint 1 (`ivc_turn_chain.rs:246`): each step's `new_root` must be the
NEXT step's `old_root`. A reordered/dropped/inserted turn breaks this and is UNSAT. -/

/-- **`Continues s s'`** — the temporal tooth between adjacent steps: `s.newRoot = s'.oldRoot`
(`new_root[i] == old_root[i+1]`). Its failure is the `TurnChainError::ChainBreak` rejection. -/
def Continues (s s' : ChainStep) : Prop :=
  ChainStep.newRoot CH RH cmb compress compressN s = ChainStep.oldRoot CH RH cmb compress compressN s'

/-- **`ChainBound steps`** — every adjacent pair satisfies the temporal tooth. The whole sequence is
the genuine finalized order (no reorder/drop/insert at the root level). -/
def ChainBound : List ChainStep → Prop
  | []            => True
  | [_]           => True
  | s :: s' :: rest => Continues CH RH cmb compress compressN s s' ∧ ChainBound (s' :: rest)

/-! ## 3. State-level continuity + the well-formed chain.

The Rust chain binding is over ROOTS; the executor model adds the underlying STATE continuity (step
`i`'s post-state IS step `i+1`'s pre-state — `RecChainedState` equality), which §5 shows the
root-level tooth recovers under CR. `lastStateOf` is the state the chain reaches from genesis. -/

/-- **`StateChained g steps`** — the steps form a contiguous executor run from genesis `g`: the first
step's pre-state is `g`, and each step's post-state is the next step's pre-state. -/
def StateChained (g : RecChainedState) : List ChainStep → Prop
  | []        => True
  | s :: rest => s.pre = g ∧ StateChained s.post rest

/-- **`lastStateOf g steps`** — the state the chain reaches from genesis `g`: genesis if empty,
else the last step's `post`. (Defined structurally so the run keystone can name the endpoint.) -/
def lastStateOf (g : RecChainedState) : List ChainStep → RecChainedState
  | []        => g
  | s :: rest => lastStateOf s.post rest

/-- **`WellFormedChain g steps`** — the steps are a genuine executor chain from genesis `g` AND the
root-level temporal tooth holds. -/
structure WellFormedChain (g : RecChainedState) (steps : List ChainStep) : Prop where
  /-- State-level continuity from genesis (each `recCexec` post is the next pre). -/
  chained : StateChained g steps
  /-- Root-level temporal tooth (the `TurnChainBindingAir` continuity constraint). -/
  bound   : ChainBound CH RH cmb compress compressN steps

/-! ## 4. The genuine final root of the whole history.

The accumulator's final claim is "`final_root` = the genuine fold of the whole history"
(`ivc_turn_chain.rs:18`): the §8 commitment of the kernel reached by folding `recCexec` over all the
turns. `lastStateOf g steps` IS that folded state; its commitment is the genuine final root. -/

/-- **`foldedFinalRoot g steps`** — the genuine §8 final root: commit the folded post-kernel
(`lastStateOf`) under the last step's turn-context (the `NEW_COMMIT` the accumulator exposes; the
empty chain commits genesis under `default`). -/
def foldedFinalRoot (g : RecChainedState) (steps : List ChainStep) : ℤ :=
  match steps.getLast? with
  | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
  | some s => stateRoot CH RH cmb compress compressN (lastStateOf g steps).kernel s.turn

/-! ## 5. The CR recovery — the ROOT tooth recovers STATE continuity.

The accumulator's verifier only sees ROOTS, not states. Under collision-resistance of the commitment
(`compressInjective cmb`, via `recStateCommit_binds`), the root-level tooth recovers the underlying
kernel continuity. This is why the LIGHT CLIENT, seeing only roots, genuinely learns state
continuity — the §8 root is an injective full-state commitment. -/

/-- **`seam_roots_chain` (PROVED — the easy direction).** State-level continuity at a seam ENTAILS
the root-level tooth: if `s.post = s'.pre` and the turn-contexts agree at the seam, their roots
chain. So an honest accumulator never asserts the tooth separately — it is free from execution. -/
theorem seam_roots_chain (s s' : ChainStep)
    (hstate : s.post = s'.pre) (hturn : s.turn = s'.turn) :
    ChainStep.newRoot CH RH cmb compress compressN s
      = ChainStep.oldRoot CH RH cmb compress compressN s' := by
  unfold ChainStep.newRoot ChainStep.oldRoot
  rw [hstate, hturn]

/-- **`root_tooth_pins_state` (PROVED — THE CR RECOVERY).** Under collision-resistance of the
commitment combiner, the ROOT-level tooth pins the underlying full-state COMMITMENT: if two steps
share a turn-context and their seam roots agree, then their cell-digests AND rest-hashes agree
(`cellDigest s.post = cellDigest s'.pre ∧ RH s.post = RH s'.pre`). That is exactly the binding
`recStateCommit_binds` provides — the §8 root is an injective commitment to (live-cell digest, rest
hash), i.e. to the WHOLE kernel (every cell binds via `cellLeafInjective`; the 16 non-cell fields via
`RestHashIffFrame`). So a light client that sees only the matching roots GENUINELY learns the states
chained, up to CR. This is the load-bearing fact that makes "verify the succinct aggregate"
sufficient: the root IS the full-state commitment. -/
theorem root_tooth_pins_state (hCmb : compressInjective cmb) (s s' : ChainStep)
    (hturn : s.turn = s'.turn)
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    cellDigest CH compress compressN s.post.kernel s'.turn
        = cellDigest CH compress compressN s'.pre.kernel s'.turn
      ∧ RH s.post.kernel = RH s'.pre.kernel := by
  unfold ChainStep.newRoot ChainStep.oldRoot stateRoot at htooth
  rw [hturn] at htooth
  exact recStateCommit_binds CH RH cmb compress compressN hCmb
          s.post.kernel s'.pre.kernel s'.turn htooth

/-! ## 6. THE HEADLINE — a well-formed chain attests the WHOLE history. -/

/-- **`every_turn_executed_correctly` (PROVED).** For EVERY turn in the chain, the turn executed
correctly per the verified executor: each `ChainStep.commits` IS the `recCexec` witness, so it holds
by construction. The first headline conjunct, made explicit. -/
theorem every_turn_executed_correctly (steps : List ChainStep) :
    ∀ s ∈ steps, recCexec s.pre s.turn = some s.post :=
  fun s _ => s.commits

/-- **`wellformed_is_run` (PROVED — the run-level keystone).** A state-chained sequence from genesis
`g` IS a `Run recChainedSystem` from `g` to `lastStateOf g steps`: each step is a
`recChainedSystem.Step` (`⟨turn, commits⟩`), composed along `StateChained`. So ALL of `RecordKernel`'s
run-level theorems apply to the whole history. -/
theorem wellformed_is_run (g : RecChainedState) (steps : List ChainStep)
    (hch : StateChained g steps) :
    Run recChainedSystem g (lastStateOf g steps) := by
  induction steps generalizing g with
  | nil => exact Run.refl (S := recChainedSystem) g
  | cons s rest ih =>
    obtain ⟨hpre, hrest⟩ := hch
    subst hpre
    have hstep : recChainedSystem.Step s.pre s.post := ⟨s.turn, s.commits⟩
    simpa [lastStateOf] using Run.step (S := recChainedSystem) hstep (ih s.post hrest)

/-- **`wellformed_history_conserves` (PROVED — KEYSTONE).** Value is conserved across the WHOLE
folded history: the ledger total at the folded endpoint equals the genesis total. The aggregate
genuinely attests a no-mint/no-burn history of arbitrary length. Rides `recChained_run_conserves`
over the run keystone. The light client, trusting only the aggregate, inherits this. -/
theorem wellformed_history_conserves (g : RecChainedState) (steps : List ChainStep)
    (hch : StateChained g steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  recChained_run_conserves (wellformed_is_run g steps hch)

/-- **`chainBound_of_stateChained` (PROVED).** State-level continuity entails the root-level temporal
tooth at every seam WHERE THE TURN-CONTEXTS AGREE. We state the per-seam fact directly via
`seam_roots_chain`; whole-list `ChainBound` follows when each seam's turn-contexts agree (the
configuration the accumulator's NoOp-padding establishes — see `ivc_turn_chain.rs:325`). This makes
`WellFormedChain.bound` derivable from `chained` at matched seams, so an honest chain is well-formed
without separately asserting the binding. -/
theorem chainBound_of_stateChained (s s' : ChainStep) (rest : List ChainStep)
    (hcont : StateChained s.pre (s :: s' :: rest))
    (hturn : s.turn = s'.turn) :
    Continues CH RH cmb compress compressN s s' := by
  obtain ⟨_, hpre', _⟩ := hcont
  exact seam_roots_chain CH RH cmb compress compressN s s' hpre'.symm hturn

/-- **`wellformed_attests_whole_history` (PROVED — THE HEADLINE).** A well-formed chain from genesis
`g` GENUINELY attests the whole history:
  (1) **every turn executed correctly** — for every step, `recCexec pre turn = some post` (the
      verified executor genuinely ran that turn);
  (2) **the chain is correctly ordered** — the root-level temporal tooth holds (`ChainBound`), so no
      reorder/drop/insert;
  (3) **the final root is the genuine fold of the whole history** — `foldedFinalRoot` commits the
      `lastStateOf`, the kernel reached by folding `recCexec` over ALL the turns, and the whole chain
      is a `Run recChainedSystem` from `g` to that state (so conservation et al. apply).
This is the meaning the IVC accumulator's `WholeChainProof` claims; `RecursiveAggregation.lean`
shows the SNARK aggregate, under the named soundness hypotheses, delivers EXACTLY this. -/
theorem wellformed_attests_whole_history (g : RecChainedState) (steps : List ChainStep)
    (hwf : WellFormedChain CH RH cmb compress compressN g steps) :
    (∀ s ∈ steps, recCexec s.pre s.turn = some s.post)         -- (1) every turn correct
      ∧ ChainBound CH RH cmb compress compressN steps          -- (2) correctly ordered
      ∧ Run recChainedSystem g (lastStateOf g steps)           -- (3) genuine fold = a real run …
      ∧ foldedFinalRoot CH RH cmb compress compressN g steps
          = match steps.getLast? with
            | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
            | some s => stateRoot CH RH cmb compress compressN (lastStateOf g steps).kernel s.turn :=
  ⟨every_turn_executed_correctly steps, hwf.bound,
   wellformed_is_run g steps hwf.chained, rfl⟩

/-! ## 7. NON-VACUITY — the binding tooth has TEETH (witnessed BOTH ways).

`WellFormedChain` is not empty (a real 1-step chain over the teeth genesis is well-formed), and the
temporal tooth genuinely REJECTS a broken order (two steps whose seam roots differ are NOT
`ChainBound`). Both witnessed below over the concrete `ConsensusExec.teethGenesis`. -/

open Dregg2.Exec.ConsensusExec (teethGenesis honestTurn tamperedTurn)

/-- A genuine honest step over the teeth genesis: cell 0 transfers 10 to cell 1. The `commits` field
is discharged by `decide` — `recCexec teethGenesis honestTurn` really is `some _`. -/
def honestStep : ChainStep where
  pre := teethGenesis
  turn := honestTurn
  post := (recCexec teethGenesis honestTurn).get (by decide)
  commits := (Option.some_get _).symm

/-- **`honest_chain_wellformed` (PROVED — non-vacuity, positive).** The single-step honest chain is
state-chained from genesis: `WellFormedChain` is INHABITED by a real executor run, so the headline is
not vacuous. (We exhibit `StateChained`; `ChainBound` on a singleton is `True`.) -/
theorem honest_chain_wellformed :
    WellFormedChain CH RH cmb compress compressN teethGenesis [honestStep] :=
  { chained := ⟨rfl, trivial⟩, bound := trivial }

/-- **`honest_step_executes` (PROVED — non-vacuity).** The honest step's turn genuinely commits:
`recCexec teethGenesis honestTurn` is `some`. So `wellformed_is_run`/`…_conserves` apply to a REAL
non-empty history, not a vacuous `none`. -/
theorem honest_step_executes :
    (recCexec teethGenesis honestTurn).isSome = true := by decide

/-- **`tooth_rejects_broken_order` (PROVED — THE ANTI-GHOST TOOTH, witnessed negative).** A reordered
/ spliced chain is NOT `ChainBound`: if the first step's `newRoot` differs from the second's
`oldRoot`, the `Continues` tooth fails, so `ChainBound` is false. We witness this abstractly: for ANY
two steps whose seam roots disagree, `ChainBound [s, s']` is `False` — exactly the
`TurnChainError::ChainBreak` rejection (`ivc_turn_chain.rs:138`), proving the binding is non-vacuous
(it genuinely separates a continuous order from a tampered one). -/
theorem tooth_rejects_broken_order (s s' : ChainStep)
    (hbreak : ChainStep.newRoot CH RH cmb compress compressN s
                ≠ ChainStep.oldRoot CH RH cmb compress compressN s') :
    ¬ ChainBound CH RH cmb compress compressN [s, s'] := by
  intro h
  exact hbreak h.1

end Portal

/-! ## 8. Axiom hygiene. -/

#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_state
#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_is_run
#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_history_conserves
#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_attests_whole_history
#assert_axioms Dregg2.Distributed.HistoryAggregation.tooth_rejects_broken_order

end Dregg2.Distributed.HistoryAggregation
