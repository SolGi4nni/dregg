/-
# Dregg2.Circuit.DescriptorRefinesReduce — the REDUCTION-FORM twin of `descriptorRefines`.

`CircuitSoundness.descriptorRefines` (the AIR→kernel per-effect rung) takes `Poseidon2SpongeCR hash`
— sponge INJECTIVITY, false at real Poseidon2 params — as its antecedent, so at the deployed hash the
original is satisfied only vacuously. This module builds its reduction-form twin on the
`CollisionReduce` infra:

  `descriptorRefinesR S hash d kstep` — DROPS the `Poseidon2SpongeCR hash` premise and concludes, for
  each satisfying + decoded witness, `OrBreak (SpongeCollision hash) (kstep pre post)`: the kernel
  step holds UNLESS a concrete sponge collision is exhibited. Valid (non-vacuous) at the real hash.

The two bridges make the twin interchangeable with the original:

  * `descriptorRefines_of_R` — the twin + injectivity resolve back to the original (nothing already
    downstream of `descriptorRefines` is lost);
  * `descriptorRefinesR_of_refines` — the original + the unconditional collision dichotomy
    (`by_cases` on `SpongeCollision hash`) give the twin.

FIRE teeth:

  * `lightclient_unfoolableR` — the twin COMPOSES through the real apex: the reduction-form family
    threads `StarkSound` + `WitnessDecodes` into the full `lightclient_unfoolable` conclusion, with
    NO `Poseidon2SpongeCR` hypothesis anywhere — the collision branch propagates to the apex verdict.
  * `descriptorRefinesR_constHash` vs `descriptorRefines_constHash_vacuous` — at a concretely broken
    hash (`constHash`, collision exhibited) the ORIGINAL holds for ANY `kstep` purely by its
    impossible premise (the vacuity), while the twin holds by EXHIBITING the real collision — the
    break branch is load-bearing, not decorative.
-/
import Dregg2.Circuit.CollisionReduce
import Dregg2.Circuit.CircuitSoundness

namespace Dregg2.Circuit.DescriptorRefinesReduce

open Dregg2.Circuit
open Dregg2.Circuit.CollisionReduce
open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec (RecChainedState)

/-! ## §1 — the sponge dichotomy: `Poseidon2SpongeCR` vs `SpongeCollision`

The two faces of the same coin: injectivity is exactly the absence of a collision. The `←` direction
is the unconditional dichotomy the second bridge rides on (constructive here — `List ℤ` has decidable
equality via `spongeN_orBreak`). -/

/-- Injectivity refutes every concrete collision. -/
theorem no_collision_of_spongeCR {hash : List ℤ → ℤ} (hCR : Poseidon2SpongeCR hash) :
    ¬ SpongeCollision hash :=
  fun ⟨xs, ys, hne, heq⟩ => hne (hCR xs ys heq)

/-- No collision forces injectivity (the `spongeN_orBreak` leaf, resolved). -/
theorem spongeCR_of_no_collision {hash : List ℤ → ℤ} (hNo : ¬ SpongeCollision hash) :
    Poseidon2SpongeCR hash :=
  fun _ _ heq => OrBreak.resolve hNo (spongeN_orBreak hash heq)

/-- The dichotomy, packaged. -/
theorem spongeCR_iff_no_collision (hash : List ℤ → ℤ) :
    Poseidon2SpongeCR hash ↔ ¬ SpongeCollision hash :=
  ⟨no_collision_of_spongeCR, spongeCR_of_no_collision⟩

/-! ## §2 — the reduction-form rung -/

/-- **`descriptorRefinesR S hash d kstep`** — the reduction-form twin of
`CircuitSoundness.descriptorRefines`. NO injectivity premise: every `Satisfied2` witness of `d` whose
published commitments decode to `pre`/`post` forces the kernel step `kstep pre post` UNLESS a concrete
sponge collision (`SpongeCollision hash`) is exhibited. The good branch is the REAL `kstep`
conclusion; the break branch is a REAL collision — a family of these is a non-vacuous floor at the
deployed (non-injective) Poseidon2. -/
def descriptorRefinesR (S : CommitSurface) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (kstep : RecChainedState → RecChainedState → Prop) : Prop :=
  ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pc : PublishedCommit) (pre post : RecChainedState),
    Satisfied2 hash d minit mfin maddrs t →
    StateDecode S pc pre post →
    OrBreak (SpongeCollision hash) (kstep pre post)

/-! ## §3 — the two bridges -/

/-- **Bridge 1 (twin ⟹ original).** Under the injectivity carrier the twin RESOLVES to the
original `descriptorRefines`: injectivity refutes the break branch, leaving the bare kernel step. So
everything downstream that already consumes `descriptorRefines` (the apex `lightclient_unfoolable`,
`stepsRefine_of_descriptorRefines`, …) is reachable from a `descriptorRefinesR` family unchanged. -/
theorem descriptorRefines_of_R (S : CommitSurface) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (kstep : RecChainedState → RecChainedState → Prop)
    (hR : descriptorRefinesR S hash d kstep) :
    descriptorRefines S hash d kstep := by
  intro hCR minit mfin maddrs t pc pre post hsat hdec
  exact OrBreak.resolve (no_collision_of_spongeCR hCR)
    (hR minit mfin maddrs t pc pre post hsat hdec)

/-- **Bridge 2 (original ⟹ twin).** The original + the unconditional collision dichotomy give the
reduction form: either a collision exists (the break branch, verbatim) or the hash is injective
(`spongeCR_of_no_collision`) and the original fires. -/
theorem descriptorRefinesR_of_refines (S : CommitSurface) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (kstep : RecChainedState → RecChainedState → Prop)
    (h : descriptorRefines S hash d kstep) :
    descriptorRefinesR S hash d kstep := by
  intro minit mfin maddrs t pc pre post hsat hdec
  by_cases hcol : SpongeCollision hash
  · exact OrBreak.broke hcol
  · exact OrBreak.ok
      (h (spongeCR_of_no_collision hcol) minit mfin maddrs t pc pre post hsat hdec)

/-- The two bridges, packaged: the twin and the original are interchangeable (classically) — but the
twin's STATEMENT never presupposes injectivity, so it is the honest floor to state at the real hash. -/
theorem descriptorRefinesR_iff_refines (S : CommitSurface) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (kstep : RecChainedState → RecChainedState → Prop) :
    descriptorRefinesR S hash d kstep ↔ descriptorRefines S hash d kstep :=
  ⟨descriptorRefines_of_R S hash d kstep, descriptorRefinesR_of_refines S hash d kstep⟩

/-- The family-level Bridge 1: a registry-wide `descriptorRefinesR` family resolves (under the CR
carrier) to exactly the `hrefines` family the apex `lightclient_unfoolable` consumes. -/
theorem descriptorRefines_family_of_R (S : CommitSurface) (hash : List ℤ → ℤ) (R : Registry)
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hR : ∀ e, descriptorRefinesR S hash (R e) (kstep e)) :
    ∀ e, descriptorRefines S hash (R e) (kstep e) :=
  fun e => descriptorRefines_of_R S hash (R e) (kstep e) (hR e)

/-! ## §4 — FIRE tooth 1: the twin composes through the real apex

The reduction-form family threads the ACTUAL apex derivation chain of `lightclient_unfoolable`
(STARK extraction → witness decode → per-effect rung → commitment re-export) with NO
`Poseidon2SpongeCR` hypothesis anywhere: the collision branch propagates via `OrBreak.imp` to the
apex verdict. The good branch is the full original conclusion, verbatim. -/

/-- **`lightclient_unfoolableR`** — the reduction-form apex. From a verifying batch, `StarkSound`,
`WitnessDecodes`, and a `descriptorRefinesR` family (NO injectivity carrier): either the full
`lightclient_unfoolable` conclusion holds — a decoded kernel boundary, the kernel step, and the
published commitments as genuine endpoint commitments — or a concrete sponge collision is exhibited. -/
theorem lightclient_unfoolableR
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefinesR : ∀ e, descriptorRefinesR S hash (R e) (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    OrBreak (SpongeCollision hash)
      (∃ pre post : RecChainedState,
        StateDecode S pi.toPublished pre post ∧
        kstep pi.effect pre post ∧
        pi.pre = S.commit pre.kernel pi.turn ∧
        pi.post = S.commit post.kernel pi.turn) := by
  -- (1) STARK soundness extracts a Satisfied2 witness publishing `pi.toPublished`.
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ :=
    (inferInstance : StarkSound hash R).extract pi π hacc
  -- (2) the carried existence rung supplies the decoded kernel boundary.
  obtain ⟨pre, post, hdecode⟩ := hwitdec minit mfin maddrs t hsat hpub
  -- (3) the reduction-form rung: the step, unless a collision — mapped into the apex conclusion.
  refine OrBreak.imp (fun hstep => ⟨pre, post, hdecode, hstep, ?_, ?_⟩)
    (hrefinesR pi.effect minit mfin maddrs t pi.toPublished pre post hsat hdecode)
  · simpa using hdecode.preBinds
  · simpa using hdecode.postBinds

/-- Round trip through the apex: under the CR carrier the reduction-form apex RESOLVES to the exact
original `lightclient_unfoolable` conclusion — the twin loses nothing downstream. -/
theorem lightclient_unfoolable_of_R
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefinesR : ∀ e, descriptorRefinesR S hash (R e) (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn :=
  OrBreak.resolve (no_collision_of_spongeCR hCR)
    (lightclient_unfoolableR hash S R kstep hrefinesR pi π hwitdec hacc)

/-! ## §5 — FIRE tooth 2: the break branch is load-bearing at a concretely broken hash

At `constHash` (everything hashes to `0`) a collision is EXHIBITED, `Poseidon2SpongeCR` is REFUTED,
and the contrast is sharp: the ORIGINAL rung holds for an ARBITRARY `kstep` purely through its
impossible premise (the vacuity this campaign removes), while the TWIN holds by producing the real
collision — its `∨` genuinely takes the break branch, it does not fake the step. -/

/-- A concretely broken sponge: constant `0`. -/
def constHash : List ℤ → ℤ := fun _ => 0

/-- The exhibited collision: `[] ≠ [0]`, equal hashes. -/
theorem constHash_collision : SpongeCollision constHash :=
  ⟨[], [0], by simp, rfl⟩

/-- `constHash` refutes the injectivity carrier — the original rung's premise is FALSE here. -/
theorem constHash_not_CR : ¬ Poseidon2SpongeCR constHash :=
  fun hCR => no_collision_of_spongeCR hCR constHash_collision

/-- **The vacuity, exhibited.** The ORIGINAL `descriptorRefines` holds at `constHash` for EVERY
`kstep` — including `fun _ _ => False` — because its injectivity premise is impossible. This is
exactly the vacuous floor the reduction form replaces. -/
theorem descriptorRefines_constHash_vacuous (S : CommitSurface) (d : EffectVmDescriptor2)
    (kstep : RecChainedState → RecChainedState → Prop) :
    descriptorRefines S constHash d kstep :=
  fun hCR => absurd hCR constHash_not_CR

/-- **The twin at the broken hash.** `descriptorRefinesR` also holds at `constHash` — but ONLY by
EXHIBITING the concrete collision (`OrBreak.broke constHash_collision`): the break branch carries a
real break event an adversary/auditor can inspect, not an impossible premise. -/
theorem descriptorRefinesR_constHash (S : CommitSurface) (d : EffectVmDescriptor2)
    (kstep : RecChainedState → RecChainedState → Prop) :
    descriptorRefinesR S constHash d kstep :=
  fun _ _ _ _ _ _ _ _ _ => OrBreak.broke constHash_collision

#assert_axioms no_collision_of_spongeCR
#assert_axioms spongeCR_of_no_collision
#assert_axioms spongeCR_iff_no_collision
#assert_axioms descriptorRefines_of_R
#assert_axioms descriptorRefinesR_of_refines
#assert_axioms descriptorRefinesR_iff_refines
#assert_axioms descriptorRefines_family_of_R
#assert_axioms lightclient_unfoolableR
#assert_axioms lightclient_unfoolable_of_R
#assert_axioms constHash_collision
#assert_axioms constHash_not_CR
#assert_axioms descriptorRefines_constHash_vacuous
#assert_axioms descriptorRefinesR_constHash

end Dregg2.Circuit.DescriptorRefinesReduce
