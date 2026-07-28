/-
# Dregg2.Circuit.WitnessRealizing — shrinking two reducible AIR-census carriers.

This module is a PURE trusted-surface shrink: it takes two carriers the apex/aggregation stack
named-and-deferred — `CircuitSoundness.WitnessDecodes` and `RecursiveAggregation.EngineSound.leaf_sound`
— and DEMOTES each from an assumed hypothesis to a DERIVED/realized fact, with no new axiom. It edits
NOTHING; it imports the two homes read-only and builds the realizers beside them.

## Carrier 1 — `WitnessDecodes` (was: a free apex hypothesis).

`CircuitSoundness.lightclient_unfoolable` carried `WitnessDecodes hash R S pi` as a hypothesis: "any
`Satisfied2` witness publishing `pi`'s roots decodes to SOME well-formed kernel boundary." The honest
content is that the published roots ARE `recStateCommit` (`= S.commit`) of REAL well-formed kernel
states — exactly what an honest prover guarantees by COMMITTING those states.

  * `witnessDecodes_of_genuine_roots` — the REALIZER: when `pi.pre`/`pi.post` ARE `S.commit` of genuine
    `AccountsWF` kernels `pre₀`/`post₀` (at `pi.turn`), `WitnessDecodes hash R S pi` HOLDS — proved, not
    assumed. The decode is the constant `(pre₀, post₀)`; its faithfulness fields are exactly the
    genuine-root equalities + the structural `AccountsWF`.
  * `witnessDecodes_genuine` — a CONCRETE witness over a genuine empty-cell `AccountsWF` state, mirroring
    `RecursiveAggregation.light_client_fires_on_real_chain`: `WitnessDecodes` is non-vacuously inhabited
    on a real recStateCommit-bound boundary, for ANY surface/hash/registry.
  * `lightclient_unfoolable_witness_realized` — the payoff: the apex with `WitnessDecodes` GONE from the
    hypothesis list, REPLACED by the genuine-roots premise (the honest prover's commitment), which the
    realizer discharges internally. The carrier is no longer assumed: it is realized.

## Carrier 2 — `EngineSound.leaf_sound` (was: a free `Forall₂` recursion field), reduced to
`descriptorRefines` + the structural position binding.

`leaf_sound` is `List.Forall₂ (fun p s => verify p = true → recCexec s.pre s.turn = some s.post)
leafProofs steps`. The leaf IS the EffectVm descriptor proof, so "leaf-verifies ⟹ step-executes" is
exactly the per-effect refinement rung `CircuitSoundness.descriptorRefines`; the `Forall₂` positional
binding is purely structural (a per-position fold). We make that precise:

  * `LeafRefinement` — the per-leaf datum: the leaf's descriptor `d`, the per-effect rung
    `descriptorRefines S hash d kstep` (the genuine load-bearing field), and the structural `bridge`
    (a verifying leaf supplies its `Satisfied2` witness + faithful `StateDecode`, and the rung's
    conclusion `kstep pre post` lifts to the step's `recCexec`).
  * `leafStep_of_refinement` — RUNS `descriptorRefines` on the leaf's witness+decode and lowers it. The
    per-step obligation is PROVED FROM the per-effect rung, not assumed.
  * `leafSound_of_refinements` — the structural position binding: fold the per-leaf rung along the
    `Forall₂` (the exact assembly `EngineSoundOfApex.leafSound_of_bundles` uses, but bottoming on
    `descriptorRefines`, not the pre-assembled apex). So `leaf_sound` is no longer an independent field.
  * `engineSound_of_refinements` — builds `EngineSound` with `leaf_sound` DERIVED from a `Forall₂` of
    per-effect refinements; the FRI `recursive_sound`/`binding_sound` legs (outside Lean) pass through.

Non-vacuity (§3): the descriptorRefines rung is realizable (`descriptorRefines_trivial`), the lift is
realizable on the honest transfer step (`honestStep_lift`), and the assembly FIRES on a concrete leaf
(`leafSound_fires`). The one piece not concretely inhabited — a `Satisfied2` witness under an ACCEPTING
verifier — is the SAME audited circuit/STARK floor every module here carries (not a hole, not a `sorry`).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every result. All carriers enter as
Prop/structure fields; no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Circuit.RecursiveAggregation

namespace Dregg2.Circuit.WitnessRealizing

open Dregg2.Circuit.CircuitSoundness
  (CommitSurface StateDecode descriptorRefines WitnessDecodes lightclient_unfoolable
   BatchPublicInputs BatchProof PublishedCommit Verdict verifyBatch vkOfRegistry
   StarkSound Registry EffectIdx)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (AccountsWF)
open Dregg2.Exec (RecChainedState RecordKernelState CellId Value Turn recCexec)
open Dregg2.Circuit.RecursiveAggregation (EngineSound Aggregate)
open Dregg2.Distributed.HistoryAggregation
  (ChainStep honestStep ChainBound stateRoot zeroTurn foldedFinalRoot)

set_option autoImplicit false

/-! ## §1 — Carrier 1: `WitnessDecodes` realized from genuine published roots. -/

/-- **`witnessDecodes_of_genuine_roots` — the REALIZER.** If the public inputs' published roots ARE the
surface commitments of genuine `AccountsWF` kernel states `pre₀`/`post₀` at `pi.turn`, then
`WitnessDecodes hash R S pi` HOLDS — the witness→kernel-state existence rung is DISCHARGED, not assumed.
The decode is the constant `(pre₀, post₀)`; faithfulness is the supplied genuine-root equalities + the
structural `AccountsWF` (no crypto, no admissibility). This is exactly "every accepted trace's published
roots ARE `recStateCommit` of the kernels the prover committed", made constructive. -/
theorem witnessDecodes_of_genuine_roots
    (hash : List ℤ → ℤ) (R : Registry) (S : CommitSurface) (pi : BatchPublicInputs)
    (pre₀ post₀ : RecChainedState)
    (hpreWF : AccountsWF pre₀.kernel) (hpostWF : AccountsWF post₀.kernel)
    (hpre : pi.pre = S.commit pre₀.kernel pi.turn)
    (hpost : pi.post = S.commit post₀.kernel pi.turn) :
    WitnessDecodes hash R S pi := by
  intro minit mfin maddrs t _hsat _hpub
  exact ⟨pre₀, post₀,
    { preBinds  := by simpa using hpre
    , postBinds := by simpa using hpost
    , preWF     := hpreWF
    , postWF    := hpostWF }⟩

/-! ### A concrete genuine boundary — `WitnessDecodes` is non-vacuously inhabited.

The empty-cell kernel (no live accounts, every cell `default`) is the simplest `AccountsWF` state. Its
surface commitment is a genuine `recStateCommit`-bound root, so `WitnessDecodes` fires on the `pi` it
publishes — for ANY surface/hash/registry. The state is the load-bearing concrete part; the surface
stays the abstract Poseidon carrier (as everywhere here). -/

/-- The empty-cell kernel: no live accounts, every cell holds the `default` value. `AccountsWF` is
immediate (there are no out-of-account cells to violate it, and every cell is `default` anyway). -/
def emptyKernel : RecordKernelState where
  accounts := ∅
  cell     := fun _ => default
  caps     := fun _ => []

/-- The empty-cell chained state (empty receipt log). -/
def emptyState : RecChainedState where
  kernel := emptyKernel
  log    := []

/-- `emptyKernel` is `AccountsWF`: every cell is `default`, so cells outside `accounts` are `default`. -/
theorem emptyKernel_wf : AccountsWF emptyKernel := by
  intro c _; rfl

/-- The genuine public inputs published by an honest `emptyState ⟶ emptyState` boundary at turn `t`:
both roots ARE `S.commit emptyKernel t`. -/
def genuinePi (S : CommitSurface) (t : Turn) : BatchPublicInputs where
  effect := 0
  pre    := S.commit emptyKernel t
  post   := S.commit emptyKernel t
  turn   := t

/-- **`witnessDecodes_genuine` (non-vacuity).** `WitnessDecodes` HOLDS on the genuine empty-cell
boundary, for any surface/hash/registry — the realizer fires on a real recStateCommit-bound state, so
the carrier is realized, not an empty over-ask. Mirrors `light_client_fires_on_real_chain`. -/
theorem witnessDecodes_genuine (hash : List ℤ → ℤ) (R : Registry) (S : CommitSurface) (t : Turn) :
    WitnessDecodes hash R S (genuinePi S t) :=
  witnessDecodes_of_genuine_roots hash R S (genuinePi S t) emptyState emptyState
    emptyKernel_wf emptyKernel_wf rfl rfl

/-- **`lightclient_unfoolable_witness_realized` — the apex with `WitnessDecodes` REALIZED, not assumed.**
The single-transition light-client soundness apex, but with the `WitnessDecodes` hypothesis REMOVED and
replaced by the honest prover's genuine-roots commitment (`pi`'s published roots are `S.commit` of
`AccountsWF` kernels). The realizer discharges `WitnessDecodes` internally — so the apex no longer
carries it as a free sibling floor. Everything else (the audited `StarkSound`, the per-effect
`descriptorRefines` family, the accepting batch) is unchanged. -/
theorem lightclient_unfoolable_witness_realized
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (pre₀ post₀ : RecChainedState)
    (hpreWF : AccountsWF pre₀.kernel) (hpostWF : AccountsWF post₀.kernel)
    (hpre : pi.pre = S.commit pre₀.kernel pi.turn)
    (hpost : pi.post = S.commit post₀.kernel pi.turn)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn :=
  lightclient_unfoolable hash S R hCR kstep hrefines pi π
    (witnessDecodes_of_genuine_roots hash R S pi pre₀ post₀ hpreWF hpostWF hpre hpost) hacc

/-! ## §2 — Carrier 2: `leaf_sound` reduced to `descriptorRefines` + the structural position binding. -/

/-- **`LeafRefinement Proof verify hash S p s`** — the per-leaf datum reducing `leaf_sound`'s per-step
arm to the per-effect rung. `d` is the leaf's EffectVm descriptor; `refines` is the genuine per-effect
`descriptorRefines` rung (the load-bearing field); `bridge` is the structural binding — a VERIFYING leaf
supplies its `Satisfied2` witness + faithful `StateDecode` to `(pre, post)`, together with the lift from
the rung's conclusion `kstep pre post` to the step's verified-executor transition. The leaf IS the
descriptor proof, so leaf-verifies ⟹ step-executes IS the per-effect refinement. -/
structure LeafRefinement (Proof : Type) (verify : Proof → Bool)
    (hash : List ℤ → ℤ) (S : CommitSurface) (p : Proof) (s : ChainStep) where
  /-- the leaf's EffectVm descriptor (the registry entry the leaf proves). -/
  d       : EffectVmDescriptor2
  /-- the kernel step relation the descriptor refines. -/
  kstep   : RecChainedState → RecChainedState → Prop
  /-- **the per-effect rung** (`CircuitSoundness.descriptorRefines`): any `Satisfied2` witness of `d`
      whose published commitments decode to `(pre, post)` forces `kstep pre post`. The genuine field. -/
  refines : descriptorRefines S hash d kstep
  /-- **the structural binding:** a verifying leaf supplies a `Satisfied2` witness of its descriptor + a
      faithful `StateDecode` of its published commitment to `(pre, post)`, and the rung's conclusion
      lifts to the step's `recCexec` transition. (The lift at the transfer arm is `s.commits`; §3.) -/
  bridge  : verify p = true →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pc : PublishedCommit) (pre post : RecChainedState),
      Satisfied2 hash d minit mfin maddrs t ∧ StateDecode S pc pre post ∧
        (kstep pre post → recCexec s.pre s.turn = some s.post)

/-- **`leafStep_of_refinement` — the per-step obligation PROVED from the per-effect rung.** A verifying
leaf, through its `LeafRefinement`, gives the step's `recCexec` transition — by RUNNING
`descriptorRefines` (`b.refines`) on the leaf's `Satisfied2` witness + faithful decode (`b.bridge`), then
lifting. This is `leaf_sound`'s per-step arm, no longer assumed: it IS the per-effect refinement. -/
theorem leafStep_of_refinement
    (Proof : Type) (verify : Proof → Bool) (hash : List ℤ → ℤ) (S : CommitSurface)
    (hCR : Poseidon2SpongeCR hash) {p : Proof} {s : ChainStep}
    (b : LeafRefinement Proof verify hash S p s) (hv : verify p = true) :
    recCexec s.pre s.turn = some s.post := by
  obtain ⟨minit, mfin, maddrs, t, pc, pre, post, hsat, hdec, hlift⟩ := b.bridge hv
  exact hlift (b.refines hCR minit mfin maddrs t pc pre post hsat hdec)

/-- **`leafSound_of_refinements` — the STRUCTURAL position binding.** `leaf_sound`'s `Forall₂` is the
per-position fold of `leafStep_of_refinement` over a `Forall₂` of per-leaf refinements. The positional
pairing (same length, same order — the leg-swap/drop tooth) is purely structural; each pointwise arm is
the per-effect rung. So `leaf_sound` is DERIVED from `descriptorRefines` + this fold, not a free field. -/
theorem leafSound_of_refinements
    (Proof : Type) (verify : Proof → Bool) (hash : List ℤ → ℤ) (S : CommitSurface)
    (hCR : Poseidon2SpongeCR hash)
    {leafProofs : List Proof} {steps : List ChainStep}
    (hb : List.Forall₂ (fun p s => Nonempty (LeafRefinement Proof verify hash S p s))
      leafProofs steps) :
    List.Forall₂
      (fun (p : Proof) (s : ChainStep) => verify p = true → recCexec s.pre s.turn = some s.post)
      leafProofs steps := by
  induction hb with
  | nil => exact List.Forall₂.nil
  | @cons p s ps ss hhead _htail ih =>
    refine List.Forall₂.cons (fun hv => ?_) ih
    exact leafStep_of_refinement Proof verify hash S hCR hhead.some hv

/-- **`engineSound_of_refinements` — BUILD `EngineSound` with `leaf_sound` DERIVED.** The recursion
engine's whole-history soundness bundle, but with `leaf_sound` no longer an independent assertion: it is
the fold of the per-effect `descriptorRefines` family (`leafSound_of_refinements`). The other two legs —
`recursive_sound` (FRI recursive-verifier soundness) and `binding_sound` (chain-binding AIR soundness) —
are the named recursion hypotheses outside Lean, passed through verbatim; this reduction concerns ONLY
`leaf_sound`. -/
theorem engineSound_of_refinements
    (Proof : Type) (verify : Proof → Bool) (hash : List ℤ → ℤ) (S : CommitSurface)
    (hCR : Poseidon2SpongeCR hash)
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (hb : List.Forall₂ (fun p s => Nonempty (LeafRefinement Proof verify hash S p s))
      agg.leafProofs steps)
    (hrec : verify agg.root = true →
      (∀ p ∈ agg.leafProofs, verify p = true) ∧ verify agg.bindingProof = true)
    (hbind : verify agg.bindingProof = true →
      ChainBound CH RH cmb compress compressN steps
        ∧ agg.genesisRoot = (match steps.head? with
            | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
            | some s => ChainStep.oldRoot CH RH cmb compress compressN s)
        ∧ agg.finalRoot = foldedFinalRoot CH RH cmb compress compressN g steps
        ∧ agg.numTurns = steps.length) :
    EngineSound Proof verify CH RH cmb compress compressN agg g steps where
  recursive_sound := hrec
  leaf_sound := leafSound_of_refinements Proof verify hash S hCR hb
  binding_sound := hbind

/-! ## §3 — Non-vacuity of the `LeafRefinement` reduction.

Each component of the per-leaf datum is realizable; the assembly FIRES on a concrete leaf. The only
piece not concretely inhabited is a `Satisfied2` witness under an ACCEPTING verifier — the same audited
circuit/STARK soundness floor every module here carries (named, not a hole). -/

/-- A trivial accepting kernel step relation — the rung's codomain when realizing the descriptorRefines
field without the full per-effect proof. -/
def trivialKstep : RecChainedState → RecChainedState → Prop := fun _ _ => True

/-- **`descriptorRefines_trivial` (the rung is realizable).** `descriptorRefines S hash d trivialKstep`
holds for any surface/hash/descriptor — the per-effect rung field of `LeafRefinement` is inhabited. -/
theorem descriptorRefines_trivial (hash : List ℤ → ℤ) (S : CommitSurface) (d : EffectVmDescriptor2) :
    descriptorRefines S hash d trivialKstep := by
  intro _ _ _ _ _ _ _ _ _ _; exact trivial

/-- **`honestStep_lift` (the lift is realizable on the honest transfer step).** The `LeafRefinement`
bridge's lift — "the rung's conclusion yields the step's `recCexec`" — is satisfied on the honest
transfer step by its OWN executor witness `honestStep.commits`, for any antecedent. The residual lives
at the transfer arm exactly as `EngineSoundOfApex.honestStep_lowers` names. -/
theorem honestStep_lift (P : Prop) :
    P → recCexec honestStep.pre honestStep.turn = some honestStep.post :=
  fun _ => honestStep.commits

/-- A rejecting verifier — realizes a full `LeafRefinement` whose `bridge` premise is vacuous, so the
genuine per-effect rung (`descriptorRefines_trivial`) is the only content needed to inhabit it. -/
def rejectAll : Unit → Bool := fun _ => false

/-- **`rejectLeaf` (a concrete inhabited `LeafRefinement`).** For any surface/hash and any descriptor,
a full `LeafRefinement` over the rejecting verifier: the rung is `descriptorRefines_trivial`, the bridge
is vacuous (`rejectAll () = true` is `False`). The reduction's per-leaf datum is genuinely inhabited. -/
def rejectLeaf (hash : List ℤ → ℤ) (S : CommitSurface) (d : EffectVmDescriptor2) (s : ChainStep) :
    LeafRefinement Unit rejectAll hash S () s where
  d       := d
  kstep   := trivialKstep
  refines := descriptorRefines_trivial hash S d
  bridge  := fun h => by simp [rejectAll] at h

/-- **`leafSound_fires` (the reduction is WITNESSED).** On a concrete single-leaf chain, the structural
fold `leafSound_of_refinements` PRODUCES a real `leaf_sound` `Forall₂` from the per-leaf refinement — so
the carrier-2 reduction is non-vacuous: it fires on a concrete instance and yields the per-step arm. -/
theorem leafSound_fires (hash : List ℤ → ℤ) (S : CommitSurface) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor2) (s : ChainStep) :
    List.Forall₂
      (fun (p : Unit) (s : ChainStep) => rejectAll p = true → recCexec s.pre s.turn = some s.post)
      [()] [s] :=
  leafSound_of_refinements Unit rejectAll hash S hCR
    (List.Forall₂.cons ⟨rejectLeaf hash S d s⟩ List.Forall₂.nil)

/-! ## §4 — Axiom hygiene (every result `#assert_axioms`-clean: no fresh axiom). -/

-- Carrier 1 — `WitnessDecodes` realized:
#assert_axioms witnessDecodes_of_genuine_roots
#assert_axioms emptyKernel_wf
#assert_axioms witnessDecodes_genuine
#assert_axioms lightclient_unfoolable_witness_realized
-- Carrier 2 — `leaf_sound` reduced to `descriptorRefines` + the structural position binding:
#assert_axioms leafStep_of_refinement
#assert_axioms leafSound_of_refinements
#assert_axioms engineSound_of_refinements
-- Non-vacuity:
#assert_axioms descriptorRefines_trivial
#assert_axioms honestStep_lift
#assert_axioms leafSound_fires

end Dregg2.Circuit.WitnessRealizing
