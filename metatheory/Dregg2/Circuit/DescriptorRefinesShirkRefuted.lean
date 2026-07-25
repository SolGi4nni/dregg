/-
# `Dregg2.Circuit.DescriptorRefinesShirkRefuted` — the `descriptorRefines` keystone and its
"reduction-form twin" are EQUALLY VACUOUS at deployed parameters.

`CircuitSoundness.descriptorRefines S hash d kstep` is one of the three Prop-def keystones that hide a
refuted floor in the DEF BODY rather than in a binder:

    def descriptorRefines … : Prop := Poseidon2SpongeCR hash → ∀ …, Satisfied2 … → StateDecode … → kstep pre post

Because the floor is in the body, a theorem that merely MENTIONS `descriptorRefines` carries it with no
floor binder anywhere in its type — invisible to every binder-keyed ruler, which is why this keystone
was the highest-leverage porting target on the board.

`DescriptorRefinesReduce` offered the port: `descriptorRefinesR`, which DROPS the
`Poseidon2SpongeCR hash` antecedent and concludes `OrBreak (SpongeCollision hash) (kstep pre post)`
instead — "the kernel step, unless a concrete sponge collision is exhibited". Its module documents the
break branch as "load-bearing, not decorative" and the twin as "a non-vacuous floor at the deployed
(non-injective) Poseidon2".

**Both claims are false, and this file proves it.** `SpongeCollision hash` is a GLOBAL existential, and
the very pigeonhole that refutes `Poseidon2SpongeCR` at BabyBear ESTABLISHES it
(`SpongeCollisionShirk.spongeCollision_of_fieldBounded`). So at every deployed-shaped sponge the break
branch is unconditionally available and the twin holds for EVERY `kstep` — including
`fun _ _ => False`, a step relation nothing can satisfy. The original holds there too, by its refuted
antecedent. §1 proves both, side by side, at the same hash.

The two are not merely both vacuous; the tree already contained the proof that they are
INTERCHANGEABLE (`descriptorRefinesR_iff_refines`, an `↔`). An equivalence cannot remove content that
one side lacks — that theorem was the standing evidence that the twin bought nothing, and it was read
as a compatibility result instead.

## Consequence for the campaign

The B-class ("unpaired bare disjunctions", 103 sites at this commit by
`scripts/binding_surface_complete.py`) is not a partially-completed re-grounding. Every one of its
members whose break event is a GLOBAL collision existential is refuted wholesale by
`SpongeCollisionShirk.bareDisjunction_is_not_a_regrounding`, with no per-site inspection. Porting
`descriptorRefines` ONTO `descriptorRefinesR` — the move the DAG's shape recommends, since the twin and
both bridges are already built and green — would have moved ~250 invisible carriers from one vacuous
floor to another and reported it as progress.

The honest target is `SpongeCollisionShirk.SpongeColl` — the collision AT THE PAIR IN PLAY — reached
through the bridge `noSpongeColl_of_spongeCR`, exactly as the landed `logHashInjective` /
`cellLeafInjective` cutovers reached theirs.
-/
import Dregg2.Circuit.DescriptorRefinesReduce
import Dregg2.Circuit.SpongeCollisionShirk

namespace Dregg2.Circuit.DescriptorRefinesShirkRefuted

open Dregg2.Circuit.CollisionReduce (SpongeCollision OrBreak)
open Dregg2.Circuit.CircuitSoundness (CommitSurface descriptorRefines)
open Dregg2.Circuit.DescriptorRefinesReduce (descriptorRefinesR)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.SpongeCollisionShirk (FieldBounded spongeCollision_of_fieldBounded)
open Dregg2.Exec (RecChainedState)

/-! ## §1 — both keystones hold at the WORST `kstep`, at the same deployed-shaped sponge -/

/-- **The ORIGINAL keystone is vacuous at deployed parameters.** At a field-bounded sponge the body's
`Poseidon2SpongeCR hash` antecedent is refuted, so `descriptorRefines` holds for EVERY `kstep` and every
descriptor — the circuit⟹kernel refinement obligation is discharged by the parameters, not by the
circuit. -/
theorem descriptorRefines_vacuous_babyBear (S : CommitSurface) {hash : List ℤ → ℤ}
    (hb : FieldBounded hash) (d : EffectVmDescriptor2)
    (kstep : RecChainedState → RecChainedState → Prop) :
    descriptorRefines S hash d kstep :=
  fun hCR => absurd hCR (Dregg2.Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear hash hb)

/-- **⚑ THE TWIN IS EXACTLY AS VACUOUS.** `descriptorRefinesR` drops the refuted antecedent, but its
break event is the GLOBAL `SpongeCollision hash`, which HOLDS at every field-bounded sponge. So the
twin, too, is satisfied for EVERY `kstep` — by the break branch alone, with the good branch never
touched. Dropping the antecedent moved the vacuity from the hypothesis into the conclusion; it did not
remove it. -/
theorem descriptorRefinesR_vacuous_babyBear (S : CommitSurface) {hash : List ℤ → ℤ}
    (hb : FieldBounded hash) (d : EffectVmDescriptor2)
    (kstep : RecChainedState → RecChainedState → Prop) :
    descriptorRefinesR S hash d kstep :=
  fun _ _ _ _ _ _ _ _ _ => OrBreak.broke (spongeCollision_of_fieldBounded hb)

/-- **⚑⚑ THE ACCEPTANCE TEST, FAILED BY BOTH.** At one and the same deployed-shaped sponge, BOTH the
keystone and its replacement hold with `kstep := fun _ _ => False` — a step relation no pair of states
satisfies. A refinement obligation that is discharged at an unsatisfiable conclusion constrains the
circuit in no way at all. This is the falsifier any candidate re-grounding of `descriptorRefines` must
survive; neither of the two currently in the tree does. -/
theorem both_hold_at_False_kstep (S : CommitSurface) {hash : List ℤ → ℤ} (hb : FieldBounded hash)
    (d : EffectVmDescriptor2) :
    descriptorRefines  S hash d (fun _ _ => False) ∧
    descriptorRefinesR S hash d (fun _ _ => False) :=
  ⟨descriptorRefines_vacuous_babyBear S hb d _, descriptorRefinesR_vacuous_babyBear S hb d _⟩

/-- **The whole registry-wide family is free, too.** The apex `lightclient_unfoolable` consumes
`∀ e, descriptorRefines S hash (R e) (kstep e)`; at deployed parameters that entire family is inhabited
with no circuit content, for any `kstep` family. The apex's per-effect rung is not what is holding the
soundness argument up. -/
theorem descriptorRefines_family_vacuous_babyBear (S : CommitSurface) {hash : List ℤ → ℤ}
    (hb : FieldBounded hash) (R : Dregg2.Circuit.CircuitSoundness.Registry)
    (kstep : Dregg2.Circuit.CircuitSoundness.EffectIdx →
      RecChainedState → RecChainedState → Prop) :
    ∀ e, descriptorRefines S hash (R e) (kstep e) :=
  fun e => descriptorRefines_vacuous_babyBear S hb (R e) (kstep e)

/-! ## §2 — why the twin could never have helped

`descriptorRefinesR_iff_refines` was already in the tree: the twin and the original are equivalent.
Restating it here against the vacuity makes the reading explicit — an `↔` between a re-grounding
candidate and the object it re-grounds is not a compatibility result, it is a REFUTATION of the
candidate. Any proposed replacement that is provably equivalent to the vacuous original inherits its
vacuity, and this is checkable before any porting work is scheduled. -/

/-- **The standing test for a `descriptorRefines` re-grounding.** If a candidate is equivalent to the
original at a deployed-shaped sponge, it holds at `fun _ _ => False` and is refused. `descriptorRefinesR`
is refused by this via `descriptorRefinesR_iff_refines`; a genuine port must FAIL this equivalence. -/
theorem equivalent_candidate_is_refused (S : CommitSurface) {hash : List ℤ → ℤ}
    (hb : FieldBounded hash) (d : EffectVmDescriptor2)
    (Cand : (RecChainedState → RecChainedState → Prop) → Prop)
    (hiff : ∀ kstep, Cand kstep ↔ descriptorRefines S hash d kstep) :
    Cand (fun _ _ => False) :=
  (hiff _).mpr (descriptorRefines_vacuous_babyBear S hb d _)

#assert_all_clean [descriptorRefines_vacuous_babyBear, descriptorRefinesR_vacuous_babyBear,
  both_hold_at_False_kstep, descriptorRefines_family_vacuous_babyBear,
  equivalent_candidate_is_refused]

end Dregg2.Circuit.DescriptorRefinesShirkRefuted
