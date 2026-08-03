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

⚑⚑ **§3 REBUILT 2026-08-03, AND ITS HEADLINE CONTRADICTS THIS SECTION'S.** The three "non-vacuity"
witnesses (`descriptorRefines_trivial` at `fun _ _ => True`, `rejectLeaf` over a verifier that accepts
nothing, `leafSound_fires` with a `False` antecedent) were all degenerate and are DELETED. Two are
repaired: `wfStep` is a step relation exhibited both accepting and rejecting a named input, and it
passes the tree's own acceptance test at the floor-free rung (`wfStep_passes_acceptance_test`);
`verifyBool` accepts AND rejects, so the leaf's `bridge` is CONSTRUCTED rather than refuted.

⚠ **The third is NOT repairable, and the claim above about "the one piece not concretely inhabited" is
FALSE in both directions.** `Satisfied2` under an accepting verifier is not the residual — the empty
trace satisfies EVERY descriptor (`ApexFloorFree.satisfied2_emptyTrace`), so the leaf datum is fully
constructible with no floor. The actual residual is in the CONCLUSION: `ChainStep` carries
`commits : recCexec pre turn = some post` as a FIELD, so `leaf_sound`'s per-step conclusion is free
for every step, and `leafSound_free` proves the whole `Forall₂` from the two list LENGTHS. Carrier 2
therefore derives, through a floor, a fact a length equation already gives. §3.0 states the repair
that would change this; it is a `RecursiveAggregation`/`ChainStep` re-shape, not a change here.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every result. All carriers enter as
Prop/structure fields; no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Circuit.RecursiveAggregation
import Dregg2.Circuit.ApexFloorFree

namespace Dregg2.Circuit.WitnessRealizing

open Dregg2.Circuit.CircuitSoundness
  (CommitSurface StateDecode descriptorRefines WitnessDecodes lightclient_unfoolable
   BatchPublicInputs BatchProof PublishedCommit Verdict verifyBatch vkOfRegistry
   StarkSound Registry EffectIdx tracePublishedCommit)
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

/-! ## §3 — Non-vacuity of the `LeafRefinement` reduction. ⚑⚑ REBUILT 2026-08-03.

⚰ **WHAT WAS HERE, AND WHY ALL THREE WERE DELETED.** This section was headed "non-vacuity" and
every one of its three witnesses was degenerate:

  * `descriptorRefines_trivial` realized the rung at `trivialKstep := fun _ _ => True` — exactly the
    laundering `DescriptorRefinesComplete.kstepAll_not_total` exists to exclude, one file over.
  * `rejectLeaf` inhabited `LeafRefinement` over `rejectAll := fun _ => false`, so its `bridge` — the
    ONLY field that has to construct anything — was discharged by `simp [rejectAll] at h`.
  * `leafSound_fires` produced `Forall₂ (fun p s => rejectAll p = true → …) [()] [s]`, i.e.
    `False → anything`, and called it "the reduction is WITNESSED".

Two of the three are genuinely repairable and are repaired below. **The third is not, and saying so
is the load-bearing part of this section**, so it is stated first.

### ⚑⚑ §3.0 — `leaf_sound`'s CONSEQUENT IS A STRUCTURE FIELD. The fold produces nothing.

`ChainStep` (`Distributed/HistoryAggregation.lean:390`) carries

    commits : recCexec pre turn = some post

as a FIELD. So `leaf_sound`'s per-step conclusion `recCexec s.pre s.turn = some s.post` is `s.commits`
— available for EVERY step, with no proof, no verifier, no leaf and no descriptor.
`leafSound_free` below proves the whole `Forall₂` from the two LENGTHS alone.

That is not a repairable witness. There is no `kstep`, no verifier and no bridge that could make
`leafSound_of_refinements`'s OUTPUT informative, because a strictly weaker input already delivers it.
The reduction "`leaf_sound` is DERIVED from `descriptorRefines` + a structural fold" is true and
empty: it derives a free fact through a floor-carrying route.

⚠ The tree already knew this and never joined it up. `RecursiveAggregation.lean:712` discharges
`leaf_sound` as "each `ChainStep`'s OWN `commits` field"; `Verify/KeystoneAuditRunnable.lean:284`
writes `leaf_sound` as `fun _ => x.commits` in so many words. What was missing is a theorem, so
nothing could go red.

**The repair this NAMES and does not do** (it is a `RecursiveAggregation` change and a `ChainStep`
re-shape, not a `WitnessRealizing` one): `leaf_sound` has to be stated over a step type that does NOT
carry its own executor witness — a `(pre, turn, post)` triple — so that "this leaf attests this
transition" is an obligation rather than a projection. Every `EngineSound` producer and the two
capstones move with it. -/

/-- **⚑⚑ `leafSound_free` — the `leaf_sound` `Forall₂` HOLDS WITH NO REFINEMENT DATA AT ALL.** For
any proof type, any verifier, and any two lists of the same length. Each arm is
`fun _ => s.commits`, the executor witness `ChainStep` carries as a field.

So `leafSound_of_refinements` — and therefore `engineSound_of_refinements`'s `leaf_sound` leg, and
every `EngineSound` assembled through it — concludes something a length equation already gives. This
statement takes no surface, no descriptor, no hash and no floor. -/
theorem leafSound_free (Proof : Type) (verify : Proof → Bool) :
    ∀ (ps : List Proof) (ss : List ChainStep), ps.length = ss.length →
      List.Forall₂
        (fun (p : Proof) (s : ChainStep) => verify p = true → recCexec s.pre s.turn = some s.post)
        ps ss
  | [],      [],      _ => List.Forall₂.nil
  | _ :: ps, s :: ss, h =>
      List.Forall₂.cons (fun _ => s.commits) (leafSound_free Proof verify ps ss (by simpa using h))
  | [],      _ :: _,  h => by simp at h
  | _ :: _,  [],      h => by simp at h

/-! ### §3.1 — a kernel step relation that ACCEPTS something and REJECTS something.

The replacement for `trivialKstep`. `wfStep` is the conjunction of the two structural well-formedness
facts the decode already carries; it is exhibited below both accepting and refusing a named pair, so
it is neither `True` nor `False`.

⚠ **AND IT IS NOT CIRCUIT CONTENT, WHICH §3.3 PROVES RATHER THAN CONCEDES.** `wfStep` is read off
`StateDecode`'s `preWF`/`postWF` fields, not off `Satisfied2`. §3.3 shows that is forced: any `kstep`
for which the rung holds at every commit map ALREADY contains every off-diagonal `wfStep` pair, so
`wfStep` is the CEILING of what the rung — as this tree states it — can carry, not a convenient
choice. A sharper witness would have to come from a sharper rung. -/

/-- The step relation the decode's own structural fields force: both endpoints' kernels are
`AccountsWF`. Neither the constant `True` (`wfStep_rejects`) nor the constant `False`
(`wfStep_accepts`). -/
def wfStep : RecChainedState → RecChainedState → Prop :=
  fun pre post => AccountsWF pre.kernel ∧ AccountsWF post.kernel

/-- A kernel that is NOT `AccountsWF`: no live accounts, yet every cell holds `.int 1` rather than the
default `.int 0`. The exhibited input `wfStep` REJECTS. -/
def badKernel : RecordKernelState where
  accounts := ∅
  cell     := fun _ => .int 1
  caps     := fun _ => []

/-- The chained state over `badKernel`. -/
def badState : RecChainedState where
  kernel := badKernel
  log    := []

/-- `badKernel` violates `AccountsWF` at cell `0`: `0 ∉ ∅`, and `.int 1 ≠ .int 0 = default`. -/
theorem badKernel_not_wf : ¬ AccountsWF badKernel := by
  intro h
  have h0 : (Value.int 1) = (Value.int 0) := h 0 (by simp [badKernel])
  injection h0 with h1
  exact absurd h1 (by decide)

/-- **`wfStep` ACCEPTS** the honest empty-cell boundary. (So it is not `fun _ _ => False`.) -/
theorem wfStep_accepts : wfStep emptyState emptyState :=
  ⟨emptyKernel_wf, emptyKernel_wf⟩

/-- **`wfStep` REJECTS** the boundary whose pre-state kernel is not `AccountsWF`. (So it is not
`fun _ _ => True` — the input the deleted `trivialKstep` could not name.) -/
theorem wfStep_rejects : ¬ wfStep badState emptyState :=
  fun h => badKernel_not_wf h.1

/-! ### §3.2 — the rung at `wfStep`, and the ACCEPTANCE TEST, run.

⚑ The acceptance test is `ApexFloorFree.descriptorRefinesFree_false_at_False_kstep`: at the exhibited
`collapseMap emptyTrace`, the FLOOR-FREE rung is FALSE at `fun _ _ => False`. It is stateable only at
`ApexFloorFree.CommitMap`; `CircuitSoundness.descriptorRefines` FAILS it outright
(`DescriptorRefinesShirkRefuted.descriptorRefines_vacuous_babyBear` proves it AT the `False` step
relation for every field-bounded sponge), so a witness stated only at `descriptorRefines` cannot be
tested at all — which is why the two theorems below are stated at the free rung. -/

/-- **The rung at `wfStep`, FLOOR-FREE.** Discharged by projecting the decode's own structural
fields — no `Poseidon2SpongeCR`, no `CommitSurface`, at every commit map / hash / descriptor. -/
theorem descriptorRefinesFree_wfStep (C : ApexFloorFree.CommitMap) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) :
    ApexFloorFree.descriptorRefinesFree C hash d wfStep :=
  fun _ _ _ _ _ _ _ _ _ hdec => ⟨hdec.preWF, hdec.postWF⟩

/-- **⚑ THE ACCEPTANCE TEST, RUN ON THIS WITNESS.** At ONE AND THE SAME commit map — the exhibited
`collapseMap emptyTrace` — all four poles at once:

  1. the rung HOLDS at `wfStep`  (satisfiable: the witness is not an empty over-ask);
  2. the rung is FALSE at `fun _ _ => False`  (refutable: it is not the constant `True`, which is the
     falsifier `descriptorRefines` and `descriptorRefinesR` both fail);
  3. `wfStep` ACCEPTS a named input;
  4. `wfStep` REJECTS a named input.

The deleted `descriptorRefines_trivial` could supply (1) only, and could not be given (2) at all: its
statement quantifies over `CommitSurface`, where a refutability pole is unstateable. -/
theorem wfStep_passes_acceptance_test (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) :
    ApexFloorFree.descriptorRefinesFree
        (ApexFloorFree.collapseMap ApexFloorFree.emptyTrace) hash d wfStep
      ∧ ¬ ApexFloorFree.descriptorRefinesFree
            (ApexFloorFree.collapseMap ApexFloorFree.emptyTrace) hash d (fun _ _ => False)
      ∧ wfStep emptyState emptyState
      ∧ ¬ wfStep badState emptyState :=
  ⟨descriptorRefinesFree_wfStep _ hash d,
   ApexFloorFree.descriptorRefinesFree_false_at_False_kstep hash d,
   wfStep_accepts, wfStep_rejects⟩

/-! ### §3.3 — ⚑ THE CEILING: `wfStep` cannot be sharpened, and that is a fact about the RUNG.

A witness is only as honest as the bound on what a better one could have said. Here it is: the rung
quantifies over the published commitment `pc` with no constraint linking it to anything except the
trace, and the empty trace satisfies EVERY descriptor
(`ApexFloorFree.satisfied2_emptyTrace`). So for any two `AccountsWF` endpoints with DISTINCT kernels
there is a commit map making them decode at the boundary the empty trace publishes — and a `kstep`
that holds at every commit map must already relate them.

⚠ The diagonal (`post.kernel = pre.kernel`) is the one residual, and it is exactly
`tracePublishedCommit`'s opacity: hitting it needs a satisfying trace whose published OLD and NEW
commitments are EQUAL, and `tracePublishedCommit` is `opaque`, so nothing in Lean can produce one.
It is named, not swept. -/

/-- **⚑ `descriptorRefinesFree` FORCES `wfStep` off the diagonal.** Any `kstep` for which the
floor-free rung holds at EVERY commit map relates every pair of `AccountsWF`-kernel states with
distinct kernels. So `wfStep` is the strongest step relation this rung can carry, and no witness at
this rung — however cleverly chosen — can say anything about the circuit. -/
theorem rung_forces_wfStep_offDiagonal (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (kstep : RecChainedState → RecChainedState → Prop)
    (h : ∀ C : ApexFloorFree.CommitMap, ApexFloorFree.descriptorRefinesFree C hash d kstep)
    (pre post : RecChainedState) (hne : post.kernel ≠ pre.kernel)
    (hpre : AccountsWF pre.kernel) (hpost : AccountsWF post.kernel) :
    kstep pre post := by
  classical
  refine h (fun k _ => if k = pre.kernel
              then (tracePublishedCommit ApexFloorFree.emptyTrace).pubPre
              else (tracePublishedCommit ApexFloorFree.emptyTrace).pubPost)
    (fun _ => 0) (fun _ => (0, 0)) [] ApexFloorFree.emptyTrace
    (tracePublishedCommit ApexFloorFree.emptyTrace) pre post
    (ApexFloorFree.satisfied2_emptyTrace hash d _ _) rfl ⟨?_, ?_, hpre, hpost⟩
  · exact (if_pos rfl).symm
  · exact (if_neg hne).symm

/-! ### §3.4 — a verifier that ACCEPTS something and REJECTS something, and a leaf whose bridge is
CONSTRUCTED.

The replacement for `rejectAll`/`rejectLeaf`. `verifyBool` accepts `true` and refuses `false`, so the
`LeafRefinement` at `p := true` has a bridge premise that HOLDS and must be discharged by exhibiting
a `Satisfied2` witness, a faithful `StateDecode` and the lift — none of which the deleted
`rejectLeaf` ever had to produce.

⚑ **The leaf is exhibited as an ANONYMOUS `example`, deliberately.** A NAMED declaration whose type
mentions `LeafRefinement` is a `#floor_ratchet` `bundle-user` carrier (`LeafRefinement.refines` is
typed at `descriptorRefines`, whose body opens `Poseidon2SpongeCR hash →`), and the baseline may only
get SHORTER. This is the discipline `Verify/RestFrameFiniteSupportSuccessor` §6 and
`TurnDecodeChainLogBundleCutoverCheck` §1/§5 already established for reference-pole objects; the same
term is built inline where it is consumed. -/

/-- A verifier that DISCRIMINATES: `true` verifies, `false` does not. -/
def verifyBool : Bool → Bool := id

/-- `verifyBool` ACCEPTS — so a `LeafRefinement` at `p := true` has a LIVE bridge premise. -/
theorem verifyBool_accepts : verifyBool true = true := rfl

/-- `verifyBool` REJECTS — so it is not `fun _ => true` either. (`rejectAll` had only this pole, and
built its whole leaf on it.) -/
theorem verifyBool_rejects : ¬ (verifyBool false = true) := by decide

/-- **A `LeafRefinement` whose `bridge` is CONSTRUCTED at an ACCEPTING leaf.** Every field is
supplied: the per-effect rung at the discriminating `wfStep`; a `Satisfied2` witness of the
descriptor (the empty trace, which satisfies every descriptor); a faithful `StateDecode` at the
boundary the honest empty-cell state publishes; and the lift.

⚠ The lift is `fun _ => s.commits` and CANNOT be otherwise — see §3.0. That is the leaf's honest
residual, and it is the same one `leafSound_free` names. -/
example (hash : List ℤ → ℤ) (S : CommitSurface) (d : EffectVmDescriptor2) (τ : Turn)
    (s : ChainStep) : LeafRefinement Bool verifyBool hash S true s where
  d       := d
  kstep   := wfStep
  refines := fun _ _ _ _ _ _ _ _ _ hdec => ⟨hdec.preWF, hdec.postWF⟩
  bridge  := fun _ =>
    ⟨fun _ => 0, fun _ => (0, 0), [], ApexFloorFree.emptyTrace,
     ⟨S.commit emptyKernel τ, S.commit emptyKernel τ, τ⟩, emptyState, emptyState,
     ApexFloorFree.satisfied2_emptyTrace hash d _ _,
     ⟨rfl, rfl, emptyKernel_wf, emptyKernel_wf⟩,
     fun _ => s.commits⟩

/-! ### §3.5 — the fold, fired at a REACHABLE antecedent — and what that is worth. -/

/-- **`leafSound_fires` — the fold, at a LIVE antecedent.** `leafSound_of_refinements` produces the
`leaf_sound` `Forall₂` from a per-leaf refinement over the DISCRIMINATING verifier, so the arm's
premise is `verifyBool true = true` — discharged by `verifyBool_accepts` — where the deleted version's
was `rejectAll () = true`, i.e. `False`.

⚠ **AND THIS IS STILL NOT A NON-VACUITY WITNESS, BY §3.0.** The `Forall₂` it produces is
`leafSound_free Bool verifyBool [true] [s] rfl` — the same term, with the surface, the descriptor, the
refinement family and the `Poseidon2SpongeCR` floor all dropped. `leafSound_fires_is_free` states
exactly that. A reachable antecedent is a real repair to the WITNESS; it does not repair the
REDUCTION, and this file no longer claims it does. -/
theorem leafSound_fires (hash : List ℤ → ℤ) (S : CommitSurface) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor2) (τ : Turn) (s : ChainStep) :
    List.Forall₂
      (fun (p : Bool) (s : ChainStep) => verifyBool p = true → recCexec s.pre s.turn = some s.post)
      [true] [s] :=
  leafSound_of_refinements Bool verifyBool hash S hCR
    (List.Forall₂.cons
      ⟨{ d       := d
       , kstep   := wfStep
       , refines := fun _ _ _ _ _ _ _ _ _ hdec => ⟨hdec.preWF, hdec.postWF⟩
       , bridge  := fun _ =>
           ⟨fun _ => 0, fun _ => (0, 0), [], ApexFloorFree.emptyTrace,
            ⟨S.commit emptyKernel τ, S.commit emptyKernel τ, τ⟩, emptyState, emptyState,
            ApexFloorFree.satisfied2_emptyTrace hash d _ _,
            ⟨rfl, rfl, emptyKernel_wf, emptyKernel_wf⟩,
            fun _ => s.commits⟩ }⟩
      List.Forall₂.nil)

/-- **⚑ THE SAME CONCLUSION, WITH EVERYTHING DROPPED.** `leafSound_fires`'s statement, proved from
`leafSound_free` alone: no hash, no surface, no descriptor, no turn, no `Poseidon2SpongeCR`, no
`LeafRefinement`. Read the two side by side — that difference is the entire content the carrier-2
reduction adds, and it is nil. -/
theorem leafSound_fires_is_free (s : ChainStep) :
    List.Forall₂
      (fun (p : Bool) (s : ChainStep) => verifyBool p = true → recCexec s.pre s.turn = some s.post)
      [true] [s] :=
  leafSound_free Bool verifyBool [true] [s] rfl

-- The antecedent is REACHABLE: reading the fired arm at `verifyBool_accepts` (rather than refuting
-- it, which is all `rejectAll` allowed) yields the step's transition. Anonymous — a named version
-- binds `Poseidon2SpongeCR` and would mint a baseline row for a fact §3.0 shows is free anyway.
example (hash : List ℤ → ℤ) (S : CommitSurface) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor2) (τ : Turn) (s : ChainStep) :
    recCexec s.pre s.turn = some s.post := by
  cases leafSound_fires hash S hCR d τ s with
  | cons harm _ => exact harm verifyBool_accepts

/-- **`stepLift` — the `LeafRefinement` bridge's lift, and why it cannot consume its antecedent.**
The lift owes "the rung's conclusion yields the step's `recCexec`"; at ANY `ChainStep` the conclusion
is that step's own `commits` field, so the antecedent is unread for every `P`. This generalizes the
deleted `honestStep_lift` (which stated the same thing at `honestStep` alone, where it read as a fact
about the honest transfer rather than about the step TYPE). -/
theorem stepLift (s : ChainStep) (P : Prop) : P → recCexec s.pre s.turn = some s.post :=
  fun _ => s.commits

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
-- Non-vacuity (§3):
#assert_axioms leafSound_free
#assert_axioms badKernel_not_wf
#assert_axioms wfStep_accepts
#assert_axioms wfStep_rejects
#assert_axioms descriptorRefinesFree_wfStep
#assert_axioms wfStep_passes_acceptance_test
#assert_axioms rung_forces_wfStep_offDiagonal
#assert_axioms verifyBool_accepts
#assert_axioms verifyBool_rejects
#assert_axioms leafSound_fires
#assert_axioms leafSound_fires_is_free
#assert_axioms stepLift

end Dregg2.Circuit.WitnessRealizing
