/-
# Dregg2.Circuit.LightClientFusion — FUSING the deployed model into the abstract UC floor.

This module is ADDITIVE: it edits nothing. It instantiates the abstract, carrier-generic
light-client unfoolability reduction of `Dregg2.Crypto.LightClientUC` at the DEPLOYED circuit-soundness
model of `Dregg2.Circuit.CircuitSoundness`, and connects the resulting fooling event to the DEPLOYED
Poseidon2 domain-separation collision-resistance floor of `Dregg2.Circuit.Poseidon2KeyedBridge`.

## The two mature tracks, fused

  * TRACK A — the DEPLOYED model. `verifyBatch` (the FRI/p3 batch verifier at the KAT-validated deployed
    config) with `StarkSound.extract` (accept ⇒ a `Satisfied2` witness publishing `pi`), `WitnessDecodes`
    (a publishing witness decodes to real kernel states), and `descriptorRefines` (the AIR→kernel rung).
    Their composition is `CircuitSoundness.lightclient_unfoolable` (the apex).

  * TRACK B — the abstract CRYPTO floor. `LightClientUC.unfoolable_of_floor`
    (`ExtractsTo` + `SatBindsProduced` ⇒ `Unfoolable`) over ANY `{State Proof Witness}`, and
    `LightClientUC.fooling_breaks_floor` (a fooling breaks `ExtractsTo`); plus the deployed Negl bounds
    `Poseidon2KeyedBridge.deployed_*_advantage_bound` under `DomainSeparatedCR`.

## The instantiation (`u := 0`; every deployed type is `Type`)

  | abstract slot | deployed value                                                              |
  |---------------|-----------------------------------------------------------------------------|
  | `State`       | `BatchPublicInputs` (the full PI — `verifyBatch`/`R pi.effect` need it)      |
  | `Proof`       | `BatchProof`                                                                |
  | `Witness`     | `(ℤ→ℤ) × (ℤ→ℤ×ℕ) × List ℤ × VmTrace` (the memory boundary bundle `+` trace) |
  | `verify`      | `dVerify R := fun pi π => decide (verifyBatch (vkOfRegistry R) pi π = accept)` |
  | `Sat`         | `dSat hash R := Satisfied2 … ∧ tracePublishedCommit t = pi.toPublished`      |
  | `Produced`    | `dProduced S kstep := ∃ pre post, StateDecode ∧ kstep ∧ commit-eqs` (the apex ∃-body) |

`deployed_ExtractsTo ⟸ StarkSound.extract`; `deployed_SatBindsProduced ⟸ WitnessDecodes + descriptorRefines`;
`deployed_unfoolable := unfoolable_of_floor …` is DEFINITIONALLY the single-transition apex.

## The residual (NAMED, not forced — see §5)

The Negl connection re-exports the deployed advantage bound over a SUPPLIED equivocator. The map from an
actual `p2Commit` state-equivocation to the concrete `CollisionFinder (poseidon2KeyedFamily D)` — the
`p2Commit`/`spongeCompress` root-unwinding into a distinct sponge-preimage pair — is NOT wired in Lean
(`FinBindsKernel.recStateCommit_binds_kernel_fin` proves only the positive forward direction). We name
that seam rather than instantiate a vacuous `Sat`/`Produced` that quietly builds the finder.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/`native_decide`/
fresh `axiom`. Non-vacuity: `dProduced` is refutable at `kstep := fun _ _ _ => False` (§4), so the
`kstep` conjunct is load-bearing, not a laundered `True`.
-/
import Dregg2.Tactics
import Dregg2.Crypto.LightClientUC
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Circuit.Poseidon2KeyedBridge

namespace Dregg2.Circuit.LightClientFusion

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.HashFloorHonesty (CollisionFinder CollisionResistant collisionAdv)
open Dregg2.Circuit.Poseidon2KeyedBridge
  (DomainSeparatedSponge DomainSeparatedCR poseidon2KeyedFamily)
open Dregg2.Exec (RecChainedState)
open Verdict

/-! ## §1 — the deployed instantiation of the abstract `{State, Proof, Witness}` slots.

`State := BatchPublicInputs`, `Proof := BatchProof`. The `Witness` is the FOUR-tuple the extraction and
`WitnessDecodes` quantify (`minit, mfin, maddrs, t`) — NOT bare `VmTrace`; the memory boundary is part of
`Satisfied2`. Everything is `Type`, so the single-universe constraint of `LightClientUC` is trivial. -/

/-- The deployed witness: the memory boundary `(minit, mfin, maddrs)` bundled with the trace `t`. -/
abbrev DWitness : Type := (ℤ → ℤ) × (ℤ → ℤ × Nat) × List ℤ × VmTrace

/-- **`dVerify R` — the deployed `verify` curried to the light-client surface.** The state IS the whole
`BatchPublicInputs pi` (so the accept condition genuinely depends on the state), the VK is fixed at
`vkOfRegistry R`, and the `Verdict` accept is wrapped to `Bool` via `decide`. -/
abbrev dVerify (R : Registry) (pi : BatchPublicInputs) (π : BatchProof) : Bool :=
  decide (verifyBatch (vkOfRegistry R) pi π = accept)

/-- **`dSat hash R` — the deployed `Sat`.** The `Satisfied2` circuit-satisfaction body over the four-tuple
witness, CONJOINED with the `s`-linking fact that the trace publishes `pi.toPublished`. The linking
conjunct is inside `Sat` (never dropped) so `SatBindsProduced` can fire. -/
abbrev dSat (hash : List ℤ → ℤ) (R : Registry) (pi : BatchPublicInputs) (w : DWitness) : Prop :=
  Satisfied2 hash (R pi.effect) w.1 w.2.1 w.2.2.1 w.2.2.2 ∧
    tracePublishedCommit w.2.2.2 = pi.toPublished

/-- **`dProduced S kstep` — the deployed `Produced`.** Literally the apex ∃-body: the executor genuinely
produced the state — a decoded kernel boundary `(pre, post)` carrying a `kstep` transition whose endpoints
commit to the published `pi.pre`/`pi.post`. NOT `True`: the `kstep` conjunct is load-bearing (§4). -/
abbrev dProduced (S : CommitSurface)
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (pi : BatchPublicInputs) : Prop :=
  ∃ pre post : RecChainedState,
    StateDecode S pi.toPublished pre post ∧
    kstep pi.effect pre post ∧
    pi.pre = S.commit pre.kernel pi.turn ∧
    pi.post = S.commit post.kernel pi.turn

/-- `dVerify` is exactly the deployed verifier's accept verdict over the state `pi` and proof `π` — the
adapter adds nothing, and the state is genuinely tied into the accept condition. -/
theorem dVerify_true_iff (R : Registry) (pi : BatchPublicInputs) (π : BatchProof) :
    dVerify R pi π = true ↔ verifyBatch (vkOfRegistry R) pi π = accept := by
  simp only [dVerify, decide_eq_true_eq]

/-! ## §2 — the two floor carriers, at the deployed types.

`deployed_ExtractsTo ⟸ StarkSound.extract`; `deployed_SatBindsProduced ⟸ WitnessDecodes + descriptorRefines`
— exactly the derivation chain inside `lightclient_unfoolable`, but factored into the two abstract halves. -/

/-- **`ExtractsTo` at the deployed model ⟸ the audited STARK extraction.** An accepting batch yields the
`Satisfied2` four-tuple witness publishing `pi.toPublished` — bundled into the single `DWitness`. -/
theorem deployed_ExtractsTo (hash : List ℤ → ℤ) (R : Registry) [StarkSound hash R] :
    Dregg2.Crypto.LightClientUC.ExtractsTo (dVerify R) (dSat hash R) := by
  intro pi π hacc
  rw [dVerify_true_iff] at hacc
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ :=
    (inferInstance : StarkSound hash R).extract pi π hacc
  exact ⟨(minit, mfin, maddrs, t), hsat, hpub⟩

/-- **`SatBindsProduced` at the deployed model ⟸ the witness→state existence rung + the per-effect rung.**
A satisfying witness for `pi` (which publishes `pi.toPublished`) decodes to `(pre, post)` via
`WitnessDecodes`, the carried per-effect `descriptorRefines` (fed the named CR carrier) forces the
`kstep`, and the decode's binding re-exports the commitment endpoints. This is the honest content: the
carriers are passed EXPLICITLY, none is faked. -/
theorem deployed_SatBindsProduced (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hCR : Poseidon2SpongeCR hash)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (hwitdec : ∀ pi, WitnessDecodes hash R S pi) :
    Dregg2.Crypto.LightClientUC.SatBindsProduced (dSat hash R) (dProduced S kstep) := by
  intro pi h
  obtain ⟨w, hsat, hpub⟩ := h
  obtain ⟨pre, post, hdecode⟩ := hwitdec pi w.1 w.2.1 w.2.2.1 w.2.2.2 hsat hpub
  have hstep : kstep pi.effect pre post :=
    hrefines pi.effect hCR w.1 w.2.1 w.2.2.1 w.2.2.2 pi.toPublished pre post hsat hdecode
  refine ⟨pre, post, hdecode, hstep, ?_, ?_⟩
  · simpa using hdecode.preBinds
  · simpa using hdecode.postBinds

/-! ## §3 — THE FUSION: `unfoolable_of_floor` at the deployed model.

`deployed_unfoolable` is `LightClientUC.Unfoolable (dVerify R) (dProduced S kstep)` — definitionally the
single-transition apex `lightclient_unfoolable`, obtained through the abstract reduction. -/

/-- **THE FUSED APEX.** The deployed light client is `Unfoolable`: under the named floors (STARK
extractability via `[StarkSound]`, the hash CR carrier `hCR`, the per-effect rung `hrefines`, the
witness→state existence rung `hwitdec`), whenever `verifyBatch` accepts `(pi, π)`, the executor genuinely
produced `pi` (a real kernel transition committing to `pi.pre`/`pi.post`). Derived by instantiating the
abstract `LightClientUC.unfoolable_of_floor` at the deployed `verify`/`Sat`/`Produced`. -/
theorem deployed_unfoolable (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hCR : Poseidon2SpongeCR hash)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (hwitdec : ∀ pi, WitnessDecodes hash R S pi) :
    Dregg2.Crypto.LightClientUC.Unfoolable (dVerify R) (dProduced S kstep) :=
  Dregg2.Crypto.LightClientUC.unfoolable_of_floor (dVerify R) (dSat hash R) (dProduced S kstep)
    (deployed_ExtractsTo hash R)
    (deployed_SatBindsProduced hash S R kstep hCR hrefines hwitdec)

/-- The fused apex, spelled out at the deployed surface: an accepting batch proof forces the deployed
`Produced` predicate. This is the honest light-client-soundness headline read off the abstract
`Unfoolable`. -/
theorem deployed_accept_produces (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hCR : Poseidon2SpongeCR hash)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (hwitdec : ∀ pi, WitnessDecodes hash R S pi)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyBatch (vkOfRegistry R) pi π = accept) :
    dProduced S kstep pi :=
  deployed_unfoolable hash S R kstep hCR hrefines hwitdec pi π ((dVerify_true_iff R pi π).2 hacc)

/-! ## §4 — NON-VACUITY: `dProduced` is not `True`; the `kstep` conjunct is load-bearing.

If the deployed `Produced` were vacuously `True`, `Unfoolable` would be free. It is not: at a kernel step
relation that never holds (`fun _ _ _ => False`), `dProduced` is REFUTABLE — the `kstep` conjunct kills
it. So the good branch is real, exactly the sharpness the `descriptorRefines_constHash_vacuous` warning
one rung down demands. -/

/-- **NON-VACUITY.** `dProduced` at the always-false step relation is refutable for every `pi`: the
`kstep` conjunct is load-bearing, so `dProduced` is not identically `True`. -/
theorem dProduced_not_vacuous (S : CommitSurface) (pi : BatchPublicInputs) :
    ¬ dProduced S (fun _ _ _ => False) pi := by
  rintro ⟨_pre, _post, _hdec, hstep, _⟩
  exact hstep

/-- And with `kstep := fun _ _ _ => False`, the deployed `Produced` is refuted at EVERY state, so the
fused `Unfoolable` at that instance would force `verifyBatch` to reject everything — the reduction only
delivers `Unfoolable` because `Produced` is a genuine, satisfiable predicate for real `kstep`. -/
theorem dProduced_false_everywhere (S : CommitSurface) :
    ∀ pi, ¬ dProduced S (fun _ _ _ => False) pi :=
  fun pi => dProduced_not_vacuous S pi

/-! ## §5 — the CONTRAPOSITIVE and the Negl connection (with the residual NAMED).

`fooling_breaks_floor` at the deployed model: a fooling of the deployed client BREAKS deployed
extractability. Combined with §2 that means, under the honest carriers, NO deployed fooling exists.
The Negl half re-exports `Poseidon2KeyedBridge.deployed_recStateCommit_advantage_bound`: a
state-equivocation, PACKAGED as a `CollisionFinder (poseidon2KeyedFamily D)`, has negligible advantage
under `DomainSeparatedCR D`. -/

/-- **The contrapositive at the deployed model.** If the deployed carriers hold (so `SatBindsProduced`)
yet the deployed client is `Foolable`, then deployed STARK extractability is FALSE — a concrete accepting
proof of a state with no satisfying witness. A real attack on the light client is a real attack on the
floor. -/
theorem deployed_fooling_breaks_floor (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hCR : Poseidon2SpongeCR hash)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (hwitdec : ∀ pi, WitnessDecodes hash R S pi)
    (hFool : Dregg2.Crypto.LightClientUC.Foolable (dVerify R) (dProduced S kstep)) :
    ¬ Dregg2.Crypto.LightClientUC.ExtractsTo (dVerify R) (dSat hash R) :=
  Dregg2.Crypto.LightClientUC.fooling_breaks_floor (dVerify R) (dSat hash R) (dProduced S kstep)
    (deployed_SatBindsProduced hash S R kstep hCR hrefines hwitdec) hFool

/-- Under `[StarkSound]` the two §2 halves CONTRADICT any fooling: deployed extractability HOLDS
(`deployed_ExtractsTo`), so `deployed_fooling_breaks_floor` refutes the assumed fooling. Hence — with the
honest carriers in hand — the deployed client is UNFOOLABLE, restated as impossibility of a fooling. -/
theorem deployed_not_foolable (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hCR : Poseidon2SpongeCR hash)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (hwitdec : ∀ pi, WitnessDecodes hash R S pi) :
    ¬ Dregg2.Crypto.LightClientUC.Foolable (dVerify R) (dProduced S kstep) := by
  rw [← Dregg2.Crypto.LightClientUC.unfoolable_iff_not_foolable]
  exact deployed_unfoolable hash S R kstep hCR hrefines hwitdec

/-- **A state-equivocation finder** built from a distinct sponge-preimage pair `(xs, xs')` (the pair a
`p2Commit` root-collision would unwind to). This is the object the Negl bound bounds. -/
def foolingRootEquivocator (D : DomainSeparatedSponge) (xs xs' : List ℤ) :
    CollisionFinder (poseidon2KeyedFamily D) where
  find := fun _ _ => (xs, xs')

/-- The equivocator WINS at tag `t` exactly when `(xs, xs')` is a genuine collision of the DEPLOYED
domain-separated sponge at `t` — the game measures finding a real collision, via
`Poseidon2KeyedBridge.wins_iff_deployed_collision`. -/
theorem foolingRootEquivocator_wins_iff (D : DomainSeparatedSponge) (xs xs' : List ℤ)
    (n : ℕ) (t : D.Tag) :
    (foolingRootEquivocator D xs xs').wins n t = true ↔
      xs ≠ xs' ∧ D.hashAt t xs = D.hashAt t xs' := by
  simpa [foolingRootEquivocator] using
    Poseidon2KeyedBridge.wins_iff_deployed_collision D (foolingRootEquivocator D xs xs') n t

/-- **The Negl connection (deployed floor).** Under the DEPLOYED Poseidon2 domain-separation CR
(`DomainSeparatedCR D`), the state-equivocation finder has NEGLIGIBLE advantage — re-exporting
`deployed_recStateCommit_advantage_bound` at the concrete finder. So a deployed fooling that violates
`SatBindsProduced` (which can only happen via a `recStateCommit` root-equivocation) wins with negligible
probability: deployed light-client fooling is negligible under the deployed sponge's domain separation. -/
theorem deployed_fooling_advantage_negl (D : DomainSeparatedSponge) (hD : DomainSeparatedCR D)
    (xs xs' : List ℤ) :
    Dregg2.Crypto.ConcreteSecurity.Negl
      (collisionAdv (poseidon2KeyedFamily D) (foolingRootEquivocator D xs xs')) :=
  Poseidon2KeyedBridge.deployed_recStateCommit_advantage_bound D hD (foolingRootEquivocator D xs xs')

/-! ### THE RESIDUAL (named, NOT forced).

The Negl connection above bounds the advantage of a SUPPLIED `foolingRootEquivocator D xs xs'`. What is
NOT wired in Lean is the map that PRODUCES that concrete `(xs, xs')` FROM an actual deployed fooling:
unwinding a `p2Commit sponge (denote f) t = p2Commit sponge (denote f') t` with `f ≠ f'` (through
`spongeCompress`/`sponge`) into the distinct sponge-preimage pair. `FinBindsKernel`'s
`recStateCommit_binds_kernel_fin` proves only the POSITIVE forward direction (equal root ⇒ equal state);
the contrapositive collision EXTRACTION is a prose seam, not a Lean term. A second, definitional
alignment obligation: the commitment's bare `sponge` must be instantiated at `D.deployedHash` (so the
tag prefix is baked in) and identified with the family instance via `deployed_hash_is_family_instance`
(`rfl`). We NAME both rather than instantiate a vacuous `Sat`/`Produced` that would make the
fooling→finder link `True`. The fusion delivered here is therefore: the ABSTRACT reduction fired at the
deployed types (real, §3), the fooling→floor-break contrapositive (real, §5), and the Negl bound over the
packaged finder (real, §5) — with the finder-CONSTRUCTION-from-fooling map named as the residual. -/

/-! ## §6 — axiom hygiene. -/

#assert_axioms dVerify_true_iff
#assert_axioms deployed_ExtractsTo
#assert_axioms deployed_SatBindsProduced
#assert_axioms deployed_unfoolable
#assert_axioms deployed_accept_produces
#assert_axioms dProduced_not_vacuous
#assert_axioms dProduced_false_everywhere
#assert_axioms deployed_fooling_breaks_floor
#assert_axioms deployed_not_foolable
#assert_axioms foolingRootEquivocator_wins_iff
#assert_axioms deployed_fooling_advantage_negl

end Dregg2.Circuit.LightClientFusion
