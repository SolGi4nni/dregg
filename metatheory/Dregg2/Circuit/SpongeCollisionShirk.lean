/-
# `Dregg2.Circuit.SpongeCollisionShirk` — the BARE-DISJUNCTION SHIRK, refuted; and the per-instance
condition that actually carries content.

## What this file is about

The vacuity campaign's job is to move theorems off `Poseidon2Binding.Poseidon2SpongeCR hash`
(`∀ xs ys, hash xs = hash ys → xs = ys`), which `HashFloorHonesty.poseidon2SpongeCR_false_babyBear`
PROVES FALSE for any sponge landing in a BabyBear field element: the domain `List ℤ` is infinite, the
codomain is `~2³¹` values, pigeonhole. A theorem whose antecedent is that floor says nothing about the
deployed system.

One re-grounding shape already in the tree is the **reduction-form twin**: replace the antecedent with
a disjunctive conclusion,

    Poseidon2SpongeCR hash → … → P        ⟿        … → OrBreak (SpongeCollision hash) P

reading "`P`, unless a concrete hash collision was exhibited". `CircuitSoundness.descriptorRefines`
has exactly such a twin (`DescriptorRefinesReduce.descriptorRefinesR`), and its module documents the
break branch as "load-bearing, not decorative".

**It is decorative.** `CollisionReduce.SpongeCollision hash` is a GLOBAL existential
(`∃ xs ys, xs ≠ ys ∧ hash xs = hash ys`) and `OrBreak B P` is a bare disjunction (`P ∨ B`). The very
pigeonhole argument that refutes `Poseidon2SpongeCR` at deployed parameters *establishes*
`SpongeCollision`, so at every deployed-shaped sponge the break branch is simply TRUE and the
disjunction holds for EVERY good branch — including `False`. §2 proves this. The twin is exactly as
vacuous as the floor it replaced, which is what `descriptorRefinesR_iff_refines` (an `↔` between the
two, already in the tree) was telling us all along.

This matters beyond one def: the same `OrBreak (SpongeCollision …)` / `OrBreak (CompressCollision …)`
shape is the campaign's whole B-class. §2 is stated over an ARBITRARY good branch `P`, so it refutes
every member of that class at once, and no per-site inspection is needed.

## What replaces it

§3 gives the object the landed cutovers already use (`LogCommitRegrounded.noLogColl_of_inj` is the
same pattern one level down): the **per-instance** no-collision condition

    SpongeColl hash xs ys := xs ≠ ys ∧ hash xs = hash ys

carried at the EXACT pair a proof feeds the floor, never globally. `noSpongeColl_of_spongeCR` is the
bridge — the old carrier IMPLIES the new condition — so a theorem re-grounded on `¬ SpongeColl` keeps
its conclusion and is strictly STRONGER than the original, and any not-yet-ported consumer can be
re-pointed through one uniform application (the `ConePort` `AppRule` shape).

§4 is the teeth, and §4's crown is the SEPARATION that makes this a real port rather than a relabeling:
at one and the SAME field-bounded (deployed-shaped) sponge, the bare disjunction holds with good branch
`False` while the per-instance condition genuinely HOLDS at a pair. The per-instance form therefore
says something the disjunctive form provably cannot.

## What this file does NOT claim

It does not port `descriptorRefines` itself. It refutes the shape that port was aimed at and builds the
target the port must land on instead. The remaining work is named precisely in the lane report.
-/
import Dregg2.Circuit.CollisionReduce
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Tactics

namespace Dregg2.Circuit.SpongeCollisionShirk

open Dregg2.Circuit.CollisionReduce (SpongeCollision OrBreak)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## §1 — deployed-shaped sponges, and the collision they provably have -/

/-- **`FieldBounded hash`** — the DEPLOYED shape: every output is a BabyBear field element
(`p = 2³¹ − 2²⁷ + 1 = 2013265921`). Every real Poseidon2 `hash_many` is `FieldBounded`; this is the
exact hypothesis `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` refutes the injective floor
under. -/
def FieldBounded (hash : List ℤ → ℤ) : Prop :=
  ∀ xs, 0 ≤ hash xs ∧ hash xs < (2013265921 : ℤ)

/-- **The collision EXISTS at deployed parameters.** A field-bounded sponge is non-injective
(pigeonhole: infinite `List ℤ` into `~2³¹` values), and non-injectivity IS a `SpongeCollision`. This is
the same fact as `poseidon2SpongeCR_false_babyBear`, stated positively — and it is what makes the
break branch of every `OrBreak (SpongeCollision hash) _` unconditionally available. -/
theorem spongeCollision_of_fieldBounded {hash : List ℤ → ℤ} (hb : FieldBounded hash) :
    SpongeCollision hash := by
  by_contra hno
  refine Dregg2.Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear hash hb ?_
  intro xs ys heq
  by_contra hne
  exact hno ⟨xs, ys, hne, heq⟩

/-! ## §2 — THE SHIRK, REFUTED

Stated over an ARBITRARY good branch `P`, so it applies to every `OrBreak (SpongeCollision hash) _`
in the tree at once — the campaign's whole B-class — with no per-site inspection. -/

/-- **⚑ THE BARE-DISJUNCTION SHIRK.** At ANY deployed-shaped sponge, `OrBreak (SpongeCollision hash) P`
holds for EVERY proposition `P`, by the break branch alone. A "reduction-form twin" whose break event is
the GLOBAL collision existential therefore carries no information about `P` whatsoever at the parameters
we deploy at. -/
theorem orBreak_spongeCollision_trivial {hash : List ℤ → ℤ} (hb : FieldBounded hash) (P : Prop) :
    OrBreak (SpongeCollision hash) P :=
  OrBreak.broke (spongeCollision_of_fieldBounded hb)

/-- **⚑⚑ THE SHIRK AT ITS WORST BRANCH.** The dichotomy holds with the good branch `False`. Nothing
survives: a theorem of this shape is satisfied without its conclusion being satisfiable at all. -/
theorem orBreak_spongeCollision_False {hash : List ℤ → ℤ} (hb : FieldBounded hash) :
    OrBreak (SpongeCollision hash) False :=
  orBreak_spongeCollision_trivial hb False

/-- **The shirk, as an equivalence.** At a deployed-shaped sponge the dichotomy is literally `True` —
the good branch is unreachable from the statement. This is the crisp form to cite when refusing a
`OrBreak (SpongeCollision …)` re-grounding. -/
theorem orBreak_spongeCollision_iff_True {hash : List ℤ → ℤ} (hb : FieldBounded hash) (P : Prop) :
    OrBreak (SpongeCollision hash) P ↔ True :=
  ⟨fun _ => trivial, fun _ => orBreak_spongeCollision_trivial hb P⟩

/-! ## §3 — the PER-INSTANCE condition (the honest replacement)

The pattern the landed cutovers use (`LogCommitRegrounded.noLogColl_of_inj` / `noLogColl_self` /
`logHash_binds_of_noLogColl`), at the sponge level. -/

/-- **`SpongeColl hash xs ys`** — a collision AT THE NAMED PAIR. Not an existential over all pairs: the
side condition a proof actually needs is that the TWO lists it is comparing do not collide, and that
condition is not settled by pigeonhole. -/
def SpongeColl (hash : List ℤ → ℤ) (xs ys : List ℤ) : Prop :=
  xs ≠ ys ∧ hash xs = hash ys

/-- **THE BRIDGE — no strength lost.** The old (refuted) carrier IMPLIES the new per-instance condition
at every pair. So each theorem re-grounded on `¬ SpongeColl` is IMPLIED BY its original: the port is
strictly STRONGER, conclusions unchanged, and a not-yet-ported consumer re-points through exactly one
application of this lemma. -/
theorem noSpongeColl_of_spongeCR {hash : List ℤ → ℤ} (hCR : Poseidon2SpongeCR hash)
    (xs ys : List ℤ) : ¬ SpongeColl hash xs ys :=
  fun h => h.1 (hCR xs ys h.2)

/-- The identity at the bridge's type, so a ported site's side condition passes through unchanged —
the `ConePort` `AppRule` replacement target (cf. `LogCommitRegrounded.noLogColl_self`). -/
theorem noSpongeColl_self {hash : List ℤ → ℤ} {xs ys : List ℤ}
    (hno : ¬ SpongeColl hash xs ys) : ¬ SpongeColl hash xs ys := hno

/-- **THE S3 FORM** — the SAME conclusion every old endpoint application drew (`xs = ys` from equal
digests), now from the per-instance side condition instead of the global floor. -/
theorem spongeBinds_of_noSpongeColl {hash : List ℤ → ℤ} (xs ys : List ℤ)
    (hno : ¬ SpongeColl hash xs ys) (heq : hash xs = hash ys) : xs = ys := by
  by_contra hne
  exact hno ⟨hne, heq⟩

/-- The old carrier still reaches the S3 conclusion, through the bridge — nothing downstream of the
original floor is lost by the port. -/
theorem spongeBinds_of_carrier {hash : List ℤ → ℤ} (hCR : Poseidon2SpongeCR hash) (xs ys : List ℤ)
    (heq : hash xs = hash ys) : xs = ys :=
  spongeBinds_of_noSpongeColl xs ys (noSpongeColl_of_spongeCR hCR xs ys) heq

/-! ## §4 — TEETH -/

/-- `[0] ≠ [1]` in `List ℤ` — the witness both polarity teeth ride on. -/
theorem list01_ne : ([0] : List ℤ) ≠ [1] := by decide

/-- **`headHash`** — a concrete DEPLOYED-SHAPED sponge: the head of the list, reduced mod the BabyBear
prime. Field-bounded exactly as a real Poseidon2 output is. -/
def headHash (xs : List ℤ) : ℤ := (xs.headD 0) % (2013265921 : ℤ)

/-- `headHash` really is deployed-shaped. -/
theorem headHash_fieldBounded : FieldBounded headHash := by
  intro xs
  exact ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩

/-- **TOOTH (REFUTABLE).** The per-instance condition genuinely FIRES: at the constant sponge the named
pair really does collide, so `¬ SpongeColl` is not a tautology. -/
theorem spongeColl_refutable : SpongeColl (fun _ => (0 : ℤ)) [0] [1] :=
  ⟨list01_ne, rfl⟩

/-- **TOOTH (SATISFIABLE).** And it is not unsatisfiable either: at `headHash` the named pair does not
collide. So `¬ SpongeColl` separates hashes — which is precisely what the global existential cannot do
once the sponge is field-bounded. -/
theorem noSpongeColl_satisfiable : ¬ SpongeColl headHash [0] [1] := by
  rintro ⟨-, heq⟩
  norm_num [headHash] at heq

/-- **TOOTH (LOAD-BEARING).** Delete the side condition and the S3 statement is FALSE — so `hno` is
carrying the argument, not decorating it. -/
theorem spongeBinds_unconditional_false :
    ¬ (∀ (hash : List ℤ → ℤ) (xs ys : List ℤ), hash xs = hash ys → xs = ys) :=
  fun h => list01_ne (h (fun _ => (0 : ℤ)) [0] [1] rfl)

/-- **⚑⚑ THE CROWN — the port is NOT a relabeling.** At ONE AND THE SAME deployed-shaped sponge:
the bare disjunction holds with good branch `False` (it says nothing), while the per-instance condition
HOLDS at a pair (it says something). A theorem re-grounded on `¬ SpongeColl` at the pair in play
therefore carries content that no `OrBreak (SpongeCollision …)` form can carry at deployed parameters.
This is the acceptance test for the B-class rebuild: the replacement must survive here, and the
disjunctive twin provably does not. -/
theorem perInstance_strictly_sharper_than_bareDisjunction :
    ∃ hash : List ℤ → ℤ,
      FieldBounded hash ∧ OrBreak (SpongeCollision hash) False ∧ ¬ SpongeColl hash [0] [1] :=
  ⟨headHash, headHash_fieldBounded,
    orBreak_spongeCollision_False headHash_fieldBounded, noSpongeColl_satisfiable⟩

/-- **THE STANDING REFUSAL.** Any candidate re-grounding presented as `OrBreak (SpongeCollision hash) P`
is refused by this: it is equivalent to `True` at every deployed-shaped sponge. Cite this, not a
doc-comment, when a lane offers a disjunctive twin as a vacuity fix. -/
theorem bareDisjunction_is_not_a_regrounding :
    ∀ (hash : List ℤ → ℤ), FieldBounded hash → ∀ P : Prop,
      OrBreak (SpongeCollision hash) P ↔ True :=
  fun _ hb P => orBreak_spongeCollision_iff_True hb P

#assert_all_clean [spongeCollision_of_fieldBounded, orBreak_spongeCollision_trivial,
  orBreak_spongeCollision_False, orBreak_spongeCollision_iff_True, noSpongeColl_of_spongeCR,
  noSpongeColl_self, spongeBinds_of_noSpongeColl, spongeBinds_of_carrier, headHash_fieldBounded,
  spongeColl_refutable, noSpongeColl_satisfiable, spongeBinds_unconditional_false,
  perInstance_strictly_sharper_than_bareDisjunction, bareDisjunction_is_not_a_regrounding]

-- The refutation must not secretly route through the floors the campaign is draining.
-- POSITIVE CONTROL, same root and therefore the same walk as the rejector below: the refutation
-- reaches these two ONLY through its proof term, so a value-blind walk reds here.
#assert_depends_on perInstance_strictly_sharper_than_bareDisjunction
  [orBreak_spongeCollision_False, noSpongeColl_satisfiable]

#assert_not_depends_on perInstance_strictly_sharper_than_bareDisjunction
  [Dregg2.Circuit.StateCommit.logHashInjective, Dregg2.Circuit.StateCommit.cellLeafInjective]

end Dregg2.Circuit.SpongeCollisionShirk
