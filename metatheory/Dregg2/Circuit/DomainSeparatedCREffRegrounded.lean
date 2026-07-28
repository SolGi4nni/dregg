/-
# `Dregg2.Circuit.DomainSeparatedCREffRegrounded` — `DomainSeparatedCR` IS FALSE AT THE DEPLOYED
SPONGE, and the deployed apex consumers re-grounded onto the `Eff`-carrying floor.

## ⚑ The finding: the BRIDGE TO THE REAL OBJECT does not reach the real object

`Poseidon2KeyedBridge` is the file that was supposed to close the "abstract `F`" gap — to connect the
DEPLOYED unkeyed Poseidon2 (`babyBearD4W16`, a `List ℤ → ℤ` PaddingFreeSponge) to the keyed floor the
whole STARK/FRI/apex chain rests on. Its named floor is

    DomainSeparatedCR D := CollisionResistant (poseidon2KeyedFamily D)

and its own docstring calls that "a GENUINE floor ... SATISFIABLE and REFUTABLE ... NOT an
injectivity/existence-refutation". But `FloorGames` (07-16) proved the load-bearing result that lands
squarely on it:

    CollisionResistant F  ↔  HashCRHardQuant F ⊤        (collisionResistant_iff_hashCRHardQuant_top)
    Hard G ⊤              ↔  Negl (solvableFrac G)      (hard_top_iff_solvableFrac_negl)

⚑ 2026-07-28 — BOTH NAMES ON THE LEFT ARE NOW GONE, and the display above is history, kept because it
is the argument. `CollisionResistant` was DELETED (it was the right-hand side under a name that hid
the `⊤`) and the `↔` went with its subject; `DomainSeparatedCR D` now reads
`HashCRHardQuant (poseidon2KeyedFamily D) (fun _ => True)` directly, so
`domainSeparatedCREff_top_iff_old` below is `Iff.rfl`. Nothing in this file's finding changed — what
changed is that a reader no longer needs a lemma to see the adversary class that makes it true.

The old `CollisionResistant` **was** a floor at the UNRESTRICTED adversary class, so it **is** the probabilistic
EXISTENCE floor, so it is FALSE wherever collisions merely EXIST — and at a BabyBear-bounded sponge
they exist at every tag, by the same pigeonhole that killed `Poseidon2SpongeCR`. §1 proves it:
`domainSeparatedCR_false_babyBear`. `Classical.choice` is the adversary; the domain-separation tag
cannot see it coming.

**And the satisfiability witness is the tell.** `Poseidon2KeyedBridge.refDomainSep_CR` discharges the
floor at `Reference.refSponge` — a provably INJECTIVE stand-in. Toy witness satisfiable, real hash
false: *the exact pattern `HashFloorHonesty`'s header diagnosed in its own predecessor*, now recurring
at the file written to cure it. `domainSeparatedCR_forces_unbounded_sponge` (§1) states this as sharply
as it can be stated: **anything satisfying `DomainSeparatedCR` has an INFINITE-range sponge — i.e. is
not a field hash at all.** That is why `refDomainSep` satisfies it and why the deployed Poseidon2
cannot.

⚑ **HONEST SCOPE — no theorem in the tree is WRONG.** `Poseidon2KeyedBridge`'s consumers are all true;
they are true *vacuously* at deployed parameters, so they transport no security. Nothing deployed
becomes unsafe today. The bridge's REAL contributions stand and are not disturbed: the keyed family,
the faithfulness lemmas (`deployed_hash_is_family_instance`, `wins_iff_deployed_collision` — the game
genuinely is about the deployed function), and the domain-separation model. What fails is only the
adversary CLASS the floor quantifies over.

## The repair (§2-§4): the `Eff` parameter, exactly as `FloorGames` §8 prescribes

`DomainSeparatedCREff D Eff := HashCRHardQuant (poseidon2KeyedFamily D) Eff` — the SAME game over the
SAME deployed keyed family (so every faithfulness lemma still applies verbatim), at an EXPLICIT
adversary class. §2 proves the bridge `domainSeparatedCREff_top_iff_old` (the old floor IS this one at
`⊤`), which is what makes §1 a statement ABOUT the deployed floor rather than a different claim.

§3 re-grounds the deployed consumers `Poseidon2KeyedBridge` ships — the `FinBindsKernel` root binder,
the OOD/Merkle/trace binders, the multi-round FRI/STARK fold, and the APEX two-hash light-client
forgery advantage — onto the `Eff`-carrying floor. Each keeps its exact conclusion; what changes is
that the hypothesis is now a floor a real Poseidon2 could satisfy, and each carries its `hEff`
obligation in the open.

⚑ **THE `hEff` OBLIGATIONS ARE UNDISCHARGED AND THAT IS THE HONEST STATE.** This tree has no general
cost model (`FloorGames` §8). ⚑ But this carrier is the one place a REAL `Eff` is already in-tree and
should be named: `RomQueryFloor.RomEff` (query-bounded ROM adversaries) prices hash/oracle adversaries
and proves an UNCONDITIONAL birthday bound — a floor that is PROVED, not assumed. §5 records that this
is the natural landing site for the deployed sponge and states precisely what it would take.

## Non-fake

The `Eff` floor is priced at BOTH poles (§4): `⊤` FALSE at the deployed sponge (§1, the whole point),
`⊥` vacuous. The canary proves the re-grounded consumers do NOT follow from the floor applied at other
adversaries. `#assert_all_clean`; no `sorry`, no fresh `axiom`. `Poseidon2KeyedBridge` is NOT edited —
its consumers are KEPT untouched and doc-marked; siblings ADDED here.

## Coordination

This is the DEPLOYED-SPONGE floor lane. `KeySetCR` is `Apps.PreRotationKeySetRegrounded`; the queue
carriers are `Apps.QueueRootFloorRegrounded`; `RosterCR` is `Circuit.CouncilRosterRegrounded`; the
commit-reveal side is `Crypto.HermineHashCRRegrounded`.
-/
import Dregg2.Circuit.Poseidon2KeyedBridge
import Dregg2.Crypto.FloorGames

namespace Dregg2.Circuit.DomainSeparatedCREffRegrounded

open Dregg2.Circuit.Poseidon2KeyedBridge
  (DomainSeparatedSponge poseidon2KeyedFamily DomainSeparatedCR)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv not_injective_of_finite_range
   finite_range_of_field_bound)
open Dregg2.Crypto.ProbCrypto (negl_of_le)
open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_add negl_finset_sum)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv Hard hashGame hashGame_wins_iff finderToAdv collisionAdv_eq_gameAdv
   HashCRHardQuant hashCRHardQuant_top_false_of_compressing hard_bot_vacuous)

set_option autoImplicit false

/-! ## §1 — `DomainSeparatedCR` IS FALSE AT THE DEPLOYED SPONGE.

The counting core, one level up from where `HashFloorHonesty` left it. The old injective floor
`Poseidon2SpongeCR` was refuted because injectivity fails; the "proper computational" floor that
replaced it is refuted because that floor quantifies over an adversary class that CONTAINS
`Classical.choice` — and at the unrestricted class, `FloorGames` proves, a game floor IS the existence
floor. Same pigeonhole, one `Classical.choice` later. -/

/-- **THE COLLISION AT EVERY TAG.** The deployed domain-separated sponge `xs ↦ sponge (tagCode t ++
xs)` maps the INFINITE `List ℤ` into the sponge's range; if that range is finite, a genuine collision
EXISTS at every domain-separation tag. Domain separation does not help: prefixing is injective, but the
prefixed map still lands in the same bounded field. -/
theorem exists_collision_at_tag (D : DomainSeparatedSponge)
    (hfin : (Set.range D.sponge).Finite) (n : ℕ) (t : (poseidon2KeyedFamily D).Key n) :
    ∃ x y : (poseidon2KeyedFamily D).Input, x ≠ y ∧
      (poseidon2KeyedFamily D).H n t x = (poseidon2KeyedFamily D).H n t y := by
  have hsub : (Set.range (fun xs : List ℤ => D.sponge (D.tagCode t ++ xs))).Finite := by
    refine hfin.subset ?_
    rintro _ ⟨xs, rfl⟩
    exact ⟨D.tagCode t ++ xs, rfl⟩
  have hni := not_injective_of_finite_range (fun xs : List ℤ => D.sponge (D.tagCode t ++ xs)) hsub
  rw [Function.not_injective_iff] at hni
  obtain ⟨x, y, heq, hne⟩ := hni
  exact ⟨x, y, hne, heq⟩

/-- **⚑ TOOTH — `DomainSeparatedCR` is FALSE for any range-bounded deployed sponge.** The floor is
the collision floor at the UNRESTRICTED adversary class — since 2026-07-28 its body says so literally
(`HashCRHardQuant (poseidon2KeyedFamily D) (fun _ => True)`; the `CollisionResistant` def that used to
spell it, and the `↔` that used to be needed to see through the name, are both DELETED) — and
`hard_top_iff_solvableFrac_negl` proves that class's floor IS the existence floor. Collisions exist at
every tag (`exists_collision_at_tag`), so the floor is FALSE. The file that was written to bridge the
consumers to the REAL deployed hash rests on a hypothesis the real deployed hash refutes. -/
theorem domainSeparatedCR_false_of_finite_range (D : DomainSeparatedSponge)
    (hfin : (Set.range D.sponge).Finite) : ¬ DomainSeparatedCR D :=
  hashCRHardQuant_top_false_of_compressing (poseidon2KeyedFamily D) ⟨([] : List ℤ)⟩
    (fun l k => exists_collision_at_tag D hfin l k)

/-- **⚑ TOOTH (deployed form) — `DomainSeparatedCR` is FALSE at the REAL BabyBear parameters.** A
sponge whose output is a genuine BabyBear field element (`0 ≤ · < p`, `p = 2³¹ − 2²⁷ + 1`) — i.e. every
real Poseidon2 `hash_many`, the `babyBearD4W16` object `Poseidon2KeyedBridge` names as the deployed
one — REFUTES the floor. So the deployed apex chain (`deployed_lightclientUnfoolable_advantage_bound`
and its siblings) is VACUOUS at deployed parameters: true, and transporting nothing. -/
theorem domainSeparatedCR_false_babyBear (D : DomainSeparatedSponge)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) : ¬ DomainSeparatedCR D :=
  domainSeparatedCR_false_of_finite_range D (finite_range_of_field_bound D.sponge _ hb)

/-- **⚑ THE SHARPEST FORM — satisfying `DomainSeparatedCR` FORCES an infinite-range sponge.**
Contrapositive of §1: anything that discharges the floor is not a field hash at all. This explains
BOTH poles of `Poseidon2KeyedBridge`'s own non-vacuity argument at once: `refDomainSep_CR` succeeds
precisely because `Reference.refSponge` is an injective `Encodable`-style map into ALL of `ℤ` (infinite
range), and the deployed BabyBear sponge fails precisely because its range is one bounded field. Toy
witness satisfiable, real hash false — `HashFloorHonesty`'s header's own diagnosis of its own
predecessor, recurring at the file written to cure it. -/
theorem domainSeparatedCR_forces_unbounded_sponge (D : DomainSeparatedSponge)
    (h : DomainSeparatedCR D) : ¬ (Set.range D.sponge).Finite :=
  fun hfin => domainSeparatedCR_false_of_finite_range D hfin h

/-! ## §2 — the repair: the SAME game over the SAME deployed family, at an EXPLICIT class. -/

/-- **`DomainSeparatedCREff D Eff`** — the honest deployed-sponge floor: every adversary IN THE CLASS
`Eff` finds a collision of the deployed domain-separated sponge, under a uniformly sampled tag, only
with negligible probability.

This is the SAME `hashGame` over the SAME `poseidon2KeyedFamily D`, so every faithfulness lemma
`Poseidon2KeyedBridge` proved still applies verbatim — `deployed_hash_is_family_instance` (the deployed
fixed function IS the family instance at the deployed tag) and `wins_iff_deployed_collision` (a win IS
a collision of the real function). The game was never the problem. The CLASS was. -/
def DomainSeparatedCREff (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop) : Prop :=
  HashCRHardQuant (poseidon2KeyedFamily D) Eff

/-- **THE BRIDGE TO THE OLD FLOOR — this is what makes §1 a statement about the DEPLOYED floor.** The
old `DomainSeparatedCR` IS the new floor at the unrestricted class. So §1 refutes exactly the object
`Poseidon2KeyedBridge` ships, and the `Eff` parameter is the ONLY thing that changes.

⚑ As of 2026-07-28 this is `Iff.rfl`, and that is the finding, not a simplification: it used to route
through `collisionResistant_iff_hashCRHardQuant_top`, a real lemma whose only job was to see through a
NAME. With `CollisionResistant` deleted and `DomainSeparatedCR`'s body written as `HashCRHardQuant …
(fun _ => True)`, the two sides are the same statement and the bridge is definitional. Kept — deleting
it would take the sentence "the old floor IS this one at `⊤`" out of the tree, and that sentence is
the reason §1's teeth are about the DEPLOYED object. -/
theorem domainSeparatedCREff_top_iff_old (D : DomainSeparatedSponge) :
    DomainSeparatedCREff D (fun _ => True) ↔ DomainSeparatedCR D :=
  Iff.rfl

/-- **THE PROBLEM IS IN THE STATEMENT** — an `Eff`-floor win is a genuine collision of the DEPLOYED
domain-separated sponge, by `Iff.rfl`, at the family whose instance at `deployedTag` IS the function
the prover computes. -/
theorem effFloor_wins_iff (D : DomainSeparatedSponge) (n : ℕ)
    (t : (poseidon2KeyedFamily D).Key n) (p : List ℤ × List ℤ) :
    (hashGame (poseidon2KeyedFamily D)).wins n t p ↔
      (p.1 ≠ p.2 ∧ D.sponge (D.tagCode t ++ p.1) = D.sponge (D.tagCode t ++ p.2)) :=
  Iff.rfl

/-! ## §3 — the DEPLOYED consumers, re-grounded onto the `Eff`-carrying floor.

Each keeps `Poseidon2KeyedBridge`'s exact conclusion. What changes is the hypothesis: a floor a real
Poseidon2 could satisfy, with its `hEff` obligation in the open at the use site. -/

/-- The single-finder bound: an equivocator in the class `Eff` has negligible collision advantage at
the DEPLOYED sponge. `collisionAdv_eq_gameAdv` is the only step — the `CollisionFinder` advantage the
old consumers state IS the game advantage the honest floor bounds. -/
theorem deployed_collision_advantage_bound_eff (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : CollisionFinder (poseidon2KeyedFamily D)) (hEff : Eff (finderToAdv A))
    (hD : DomainSeparatedCREff D Eff) :
    Negl (collisionAdv (poseidon2KeyedFamily D) A) := by
  rw [collisionAdv_eq_gameAdv]
  exact hD _ hEff

/-- **`FinBindsKernel` root binder, re-grounded.** The full-state-root-equivocation adversary (two
distinct kernel states committing to one root) has negligible advantage under the DEPLOYED sponge's
`Eff`-carrying domain-separation floor. Replaces
`Poseidon2KeyedBridge.deployed_recStateCommit_advantage_bound`, whose floor the deployed sponge
refutes (§1). -/
theorem deployed_recStateCommit_advantage_bound_eff (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (rootEquivocator : CollisionFinder (poseidon2KeyedFamily D))
    (hEff : Eff (finderToAdv rootEquivocator)) (hD : DomainSeparatedCREff D Eff) :
    Negl (collisionAdv (poseidon2KeyedFamily D) rootEquivocator) :=
  deployed_collision_advantage_bound_eff D Eff rootEquivocator hEff hD

/-- **OOD / Merkle-opening binder, re-grounded.** -/
theorem deployed_oodCommitmentOpening_advantage_bound_eff (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (opener : CollisionFinder (poseidon2KeyedFamily D))
    (hEff : Eff (finderToAdv opener)) (hD : DomainSeparatedCREff D Eff) :
    Negl (collisionAdv (poseidon2KeyedFamily D) opener) :=
  deployed_collision_advantage_bound_eff D Eff opener hEff hD

/-- **FRI oracle binder, re-grounded.** -/
theorem deployed_friOracle_binding_advantage_bound_eff (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (oracleEquivocator : CollisionFinder (poseidon2KeyedFamily D))
    (hEff : Eff (finderToAdv oracleEquivocator)) (hD : DomainSeparatedCREff D Eff) :
    Negl (collisionAdv (poseidon2KeyedFamily D) oracleEquivocator) :=
  deployed_collision_advantage_bound_eff D Eff oracleEquivocator hEff hD

/-- **AIR trace-digest binder, re-grounded.** -/
theorem deployed_committedTrace_pinned_advantage_bound_eff (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (traceEquivocator : CollisionFinder (poseidon2KeyedFamily D))
    (hEff : Eff (finderToAdv traceEquivocator)) (hD : DomainSeparatedCREff D Eff) :
    Negl (collisionAdv (poseidon2KeyedFamily D) traceEquivocator) :=
  deployed_collision_advantage_bound_eff D Eff traceEquivocator hEff hD

/-- **Multi-round FRI/STARK fold, re-grounded.** The total binding-failure advantage across the
`rounds` Merkle checks is a finite SUM of per-round collision advantages, negligible under the deployed
`Eff`-carrying floor by `negl_finset_sum`. Every round's equivocator carries its own `hEff`. -/
theorem deployed_friStark_fold_advantage_bound_eff (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop) (rounds : Finset ℕ)
    (roundEquivocator : ℕ → CollisionFinder (poseidon2KeyedFamily D))
    (hEff : ∀ r ∈ rounds, Eff (finderToAdv (roundEquivocator r)))
    (hD : DomainSeparatedCREff D Eff) :
    Negl (fun n => ∑ r ∈ rounds, collisionAdv (poseidon2KeyedFamily D) (roundEquivocator r) n) :=
  negl_finset_sum rounds
    (fun r hr => deployed_collision_advantage_bound_eff D Eff (roundEquivocator r) (hEff r hr) hD)

/-- **⚑ APEX two-hash forgery advantage, re-grounded.** The light-client forgery advantage —
trace-commitment equivocation PLUS OOD-commitment equivocation — is negligible under the DEPLOYED
sponge's `Eff`-carrying domain-separation floor. This is the apex bound `Poseidon2KeyedBridge` ships as
`deployed_lightclientUnfoolable_advantage_bound`; its floor is refuted by the deployed sponge (§1),
this one is not. -/
theorem deployed_lightclientUnfoolable_advantage_bound_eff (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (traceEquivocator oodEquivocator : CollisionFinder (poseidon2KeyedFamily D))
    (hEffT : Eff (finderToAdv traceEquivocator)) (hEffO : Eff (finderToAdv oodEquivocator))
    (hD : DomainSeparatedCREff D Eff) :
    Negl (fun n => collisionAdv (poseidon2KeyedFamily D) traceEquivocator n
        + collisionAdv (poseidon2KeyedFamily D) oodEquivocator n) :=
  negl_add (deployed_collision_advantage_bound_eff D Eff traceEquivocator hEffT hD)
    (deployed_collision_advantage_bound_eff D Eff oodEquivocator hEffO hD)

/-! ## §4 — the `Eff` parameter, PRICED, and the CANARY. -/

/-- **⚑ (TOOTH — `Eff := ⊤` is FALSE at the DEPLOYED sponge.)** §1 transported through the §2 bridge:
at the unrestricted class the honest floor IS the old `DomainSeparatedCR`, which the BabyBear-bounded
deployed sponge refutes. This is the price of every `hEff` above, stated as a theorem instead of a
promise — and it is the whole reason the class cannot be left implicit. -/
theorem effFloor_top_false_babyBear (D : DomainSeparatedSponge)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ DomainSeparatedCREff D (fun _ => True) :=
  fun h => domainSeparatedCR_false_babyBear D hb ((domainSeparatedCREff_top_iff_old D).mp h)

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty class the floor holds for ANY
sponge, including a completely broken one. Recorded HONESTLY: a satisfiability witness is worth nothing
without the refutation beside it, and the two poles together are what make `Eff` a dial, not a costume. -/
theorem effFloor_bot_vacuous (D : DomainSeparatedSponge) :
    DomainSeparatedCREff D (fun _ => False) :=
  hard_bot_vacuous _

/-- **(CANARY — the apex bound does NOT follow from the floor applied at OTHER adversaries.)** Strip
the connection — try to conclude the trace/OOD equivocators' negligibility from the floor applied at
some OTHER adversary `B` — and the proof does not go through: the floor bounds `B`, and only
`collisionAdv_eq_gameAdv` at the EXTRACTED finders connects it to the apex sum. -/
example (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (traceEquivocator oodEquivocator : CollisionFinder (poseidon2KeyedFamily D))
    (B : Adversary (hashGame (poseidon2KeyedFamily D))) (hB : Eff B)
    (hD : DomainSeparatedCREff D Eff) : True := by
  fail_if_success
    (have : Negl (fun n => collisionAdv (poseidon2KeyedFamily D) traceEquivocator n
        + collisionAdv (poseidon2KeyedFamily D) oodEquivocator n) := negl_add (hD B hB) (hD B hB))
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge the apex.** A gate that refuses everything is
a broken keystone, not a fixed one. With the floor at the EXTRACTED finders the apex bound fires. -/
theorem the_repaired_apex_fires_on_the_right_floor (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (traceEquivocator oodEquivocator : CollisionFinder (poseidon2KeyedFamily D))
    (hEffT : Eff (finderToAdv traceEquivocator)) (hEffO : Eff (finderToAdv oodEquivocator))
    (hD : DomainSeparatedCREff D Eff) :
    Negl (fun n => collisionAdv (poseidon2KeyedFamily D) traceEquivocator n
        + collisionAdv (poseidon2KeyedFamily D) oodEquivocator n) :=
  deployed_lightclientUnfoolable_advantage_bound_eff D Eff traceEquivocator oodEquivocator
    hEffT hEffO hD

/-! ## §5 — ⚑ THE LANDING SITE, NAMED (this residual has an address, unlike the lattice one).

`FloorGames` §8's residual is "the tree has no cost model", and for LATTICE floors that is still true.
But this carrier is a HASH, and the tree already has a real, PROVED `Eff` for hashes:
`Dregg2.Crypto.RomQueryFloor` — `RomEff F Q`, the adversaries that factor through a `QueryBounded Q`
decision tree, with `romCollision_hard` proving the UNCONDITIONAL birthday bound `(Q² + 1)/|R|`. Both
escapes are proved there: the class is not `⊤` (`choiceAdv_not_romEff` — `Classical.choice`'s adversary
is EXCLUDED) and not `⊥` (`twoPointAdv_in_romEff` exhibits a genuine query-using member).

So `Eff := RomEff` is the honest landing site for the DEPLOYED sponge, and what it needs is stated
precisely rather than hand-waved: `RomQueryFloor`'s game samples a uniformly random ORACLE, whereas
`poseidon2KeyedFamily` is a FIXED function keyed by a domain-separation tag. Landing the deployed
sponge there is therefore a modelling step — the standard random-oracle idealization of Poseidon2 — NOT
a derivation, and it must be taken deliberately and labelled, not smuggled. That step is not taken
here; taking it silently would be exactly the laundering this whole sweep exists to stop.

Until it is taken, `Eff` stays a parameter, and §4 prices it at both poles. -/

/-- **(TOOTH — the residual is a CLASS, not a game.)** The honest floor at ANY class whatsoever is
still a floor over the DEPLOYED sponge's own collision game — the win relation is a genuine collision
of `xs ↦ sponge (tagCode t ++ xs)` (`effFloor_wins_iff`, `Iff.rfl`) no matter which `Eff` is chosen. So
the open work is exactly to name a class with content, and nothing else: the problem is in the
statement already. -/
theorem effFloor_game_is_deployed_regardless (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop) (n : ℕ)
    (t : (poseidon2KeyedFamily D).Key n) (p : List ℤ × List ℤ)
    (_h : DomainSeparatedCREff D Eff) :
    (hashGame (poseidon2KeyedFamily D)).wins n t p ↔
      (p.1 ≠ p.2 ∧ D.sponge (D.tagCode t ++ p.1) = D.sponge (D.tagCode t ++ p.2)) :=
  Iff.rfl

#assert_all_clean [
  exists_collision_at_tag,
  domainSeparatedCR_false_of_finite_range,
  domainSeparatedCR_false_babyBear,
  domainSeparatedCR_forces_unbounded_sponge,
  domainSeparatedCREff_top_iff_old,
  effFloor_wins_iff,
  deployed_collision_advantage_bound_eff,
  deployed_recStateCommit_advantage_bound_eff,
  deployed_oodCommitmentOpening_advantage_bound_eff,
  deployed_friOracle_binding_advantage_bound_eff,
  deployed_committedTrace_pinned_advantage_bound_eff,
  deployed_friStark_fold_advantage_bound_eff,
  deployed_lightclientUnfoolable_advantage_bound_eff,
  effFloor_top_false_babyBear,
  effFloor_bot_vacuous,
  the_repaired_apex_fires_on_the_right_floor,
  effFloor_game_is_deployed_regardless
]

end Dregg2.Circuit.DomainSeparatedCREffRegrounded
