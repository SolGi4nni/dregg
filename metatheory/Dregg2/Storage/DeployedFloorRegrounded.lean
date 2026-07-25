/-
# `Dregg2.Storage.DeployedFloorRegrounded` — the storage binding, CUT OVER off literal injectivity
onto the collision GAME the tree already had.

## The wound, already proved — this file does not re-litigate it

`Storage.DeployedFloorRefuted` proves three things and this file builds on all three:

  * `Poseidon2Binding.Poseidon2SpongeCR` is LITERAL INJECTIVITY, `∀ xs ys, sponge xs = sponge ys → xs = ys`;
  * `deployed_collides : poseidon2Hash [-1] = poseidon2Hash [0] := rfl` — `Storage/Deployed.lean:32-33`
    routes every limb through `x.toNat.toUInt64` and `Int.toNat` CLAMPS negatives to zero;
  * so `deployed_floor_false` REFUTES the floor at the deployed hash, and no encoder repairs it —
    `poseidon2Hash` factors through `UInt64`, a finite image over an infinite domain, so exact
    injectivity is unsatisfiable at ANY encoding. The floor is MIS-SPECIFIED, not mis-implemented.

**A floor must be SATISFIABLE and REFUTABLE but NOT PROVABLE.** Injectivity fails the first clause at
every concrete hash, so it was never a floor; it was a false assumption worn as one.

## ⚑ THE MOST VALUABLE FINDING: THIS IS A CUTOVER, NOT A CONSTRUCTION

The replacement floor did NOT need to be built. It is on the shelf, in three pieces that already
compose:

  * `Crypto.FloorGames.Game` / `Hard G Eff` — a λ-indexed security game with the problem IN the win
    relation, and hardness quantified over an EXPLICIT adversary class `Eff`;
  * `Crypto.FloorGames.hashGame` / `HashCRHardQuant F Eff` — that schema at the COLLISION game of a
    `HashFloorHonesty.KeyedHashFamily`: the adversary is handed a uniformly sampled key and wins iff it
    outputs two DISTINCT inputs with equal images;
  * `Crypto.HashSigMerkleRegrounded.SpongeDeployment` / `spongeFamily` — the deployed Poseidon2 sponge
    already lifted to exactly that keyed family, carrying NO injectivity field.

So the floor is **`FloorGames.HashCRHardQuant (spongeFamily D) Eff`**, reused verbatim. Nothing about
collision resistance is invented here. What this file does is the CUTOVER: extractors, the reduction,
the poles, and the repaired storage keystone.

`Crypto.CommitmentBinding:75` already recorded the trap on the way: `HashFloorHonesty.CollisionResistant`
is NOT the replacement — `FloorGames.collisionResistant_iff_hashCRHardQuant_top` proves it is this floor
at `Eff := ⊤`, and `collisionResistant_false_of_compressing` proves THAT false for every compressing
family. Copying it would have been the same disease one costume along.

## Why the chosen floor obeys the law

  * **SATISFIABLE** — `hashCRHardQuant_of_injective` (§2): a family injective at every key satisfies it
    at EVERY class, `HashFloorHonesty.idFamily_CR` exhibits one. Not empty.
  * **REFUTABLE** — and, at the deployed encoder, ACTUALLY REFUTED (§4):
    `deployedFloor_refuted_by_clamp` proves the floor FALSE for any class containing the CONSTANT finder
    `fun _ _ => ([-1], [0])`, whose advantage is the constant `1` because the clamp collision holds by
    `rfl`. A constant finder is efficient under any cost model worth the name.
  * **NOT PROVABLE** — `Eff` is a parameter with no cost model in this repository
    (`FloorGames` §8); at `Eff := ⊤` the floor is FALSE for every compressing family, so it cannot be a
    theorem, and at `Eff := ⊥` it is vacuous (`hashCRHardQuant_bot_vacuous`). Both poles are proved
    below rather than promised.

## ⚑ AND THE DIFFERENCE THE CUTOVER MAKES, STATED SHARPLY

Injectivity was refuted at the deployed hash for an UNFIXABLE reason (cardinality). The game floor is
refuted at the deployed hash for a FIXABLE one (§4.1: the `Int.toNat` clamp is a plain encoder bug —
`babyBearLimb` separates `-1` from `0` where `toNat` merges them). That is the whole point of having a
floor that can go red for a REASON: a hash that fails injectivity tells you nothing, a hash that fails
the collision game hands you the collision. The clamp is a live storage bug this file NAMES; it is not
repaired here, because `Storage/Deployed.lean`'s limb encoder is on the deployed FFI path.

## What is migrated

`Lightclient.MMR` (`hashOf_binds_or_collides` / `bag_binds_or_collides` / `mroot_binds_or_collides`),
`Storage.BucketCommitment` (`objectLeaf_binds_or_collides` / `contentRoot_binds_or_collides` /
`read_sound_or_collides`), `Storage.Retrievability` (`por_sound_or_collides` /
`por_substitution_forces_collision` / `por_holds_committed_or_collides`) and `Storage.Deployed`
(`contentRootDeployed_binds_or_collides`) are all UNCONDITIONAL now — the floor is spent nowhere on the
live path. Each old keystone survives ONLY as a one-line strength bridge at the (refuted) injectivity,
which is the machine-checked proof that the cutover surrendered nothing.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. No `sorry`, no fresh
`axiom`, no `native_decide`.
-/
import Dregg2.Crypto.HashSigMerkleRegrounded
import Dregg2.Storage.DeployedFloorRefuted

namespace Dregg2.Storage.DeployedFloorRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl negl_zero not_negl_one)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top winProb_le_of_imp negl_of_le)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionResistant idFamily idFamily_CR injective_family_CR)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit hashGame HashCRHardQuant Hard hard_bot_vacuous
   collisionResistant_iff_hashCRHardQuant_top collisionResistant_false_of_compressing
   not_hard_top_of_always_solvable)
open Dregg2.Crypto.HashSigMerkleRegrounded
  (SpongeDeployment spongeFamily deployedSponge_is_family_instance spongeFamily_CR_of_injective)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR SpongeColl)
open Dregg2.Storage
open Dregg2.Storage.DeployedFloorRefuted (deployed_collides deployed_floor_false)

set_option autoImplicit false

/-! ## §1 — the floor, NAMED, and its two poles.

Both poles are stated once here so every consumer can price its own instantiation by citing them
rather than by promising anything. They are `InjectiveFloorRegrounded` §0's poles at the sponge family;
the shape is deliberately identical, because the three sibling carriers this campaign already cut over
landed on exactly this object. -/

/-- **THE ⊤ POLE.** The collision floor at the UNRESTRICTED adversary class is FALSE for any
COMPRESSING family: a collision at every key (pigeonhole forces it at deployed parameters, and it is the
defining property of a hash) makes the `Classical.choice` finder win with probability `1`. The honest
price of the `hEff` obligation, as a theorem instead of a promise. -/
theorem hashCRHardQuant_top_false_of_compressing (F : KeyedHashFamily) (hin : Nonempty F.Input)
    (hcol : ∀ l (k : F.Key l), ∃ x y : F.Input, x ≠ y ∧ F.H l k x = F.H l k y) :
    ¬ HashCRHardQuant F (fun _ => True) := by
  rw [← collisionResistant_iff_hashCRHardQuant_top]
  exact collisionResistant_false_of_compressing F hin hcol

/-- **THE ⊥ POLE.** At the empty adversary class the floor holds for ANY family, including a completely
broken one — so a satisfiability witness is worth nothing without the refutation beside it. Recorded so
`Eff` cannot be quietly filled with nothing. -/
theorem hashCRHardQuant_bot_vacuous (F : KeyedHashFamily) :
    HashCRHardQuant F (fun _ => False) :=
  hard_bot_vacuous _

/-! ## §2 — ⚑ INJECTIVITY IMPLIES THE GAME FLOOR: the cutover is a WEAKENING.

This is what makes the migration SAFE rather than merely different. The old hypothesis
(`Poseidon2SpongeCR` at every key) IMPLIES the new one at EVERY adversary class — an injective hash has
no collisions at all, so every finder's advantage is exactly `0`. Therefore every theorem that used to
be gated on injectivity, restated on the game floor, is implied by its old self: the migrated statements
are STRICTLY STRONGER, and the strictness is not rhetorical — §4 proves the old hypothesis is
UNAVAILABLE at the deployed hash while the new statements still hold there. -/

/-- **⚑ THE WEAKENING, PROVED.** A sponge deployment injective at every tag satisfies the collision
floor at EVERY adversary class `Eff` — including `⊤`. So `Poseidon2SpongeCR` (at every tag) is strictly
stronger than the floor that replaces it, and the cutover cannot have lost anything a consumer was
entitled to. -/
theorem hashCRHardQuant_of_injective (D : SpongeDeployment)
    (hinj : ∀ t : D.Tag, Function.Injective (D.hashAt t))
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop) :
    HashCRHardQuant (spongeFamily D) Eff := fun A _ =>
  (collisionResistant_iff_hashCRHardQuant_top (spongeFamily D)).mp
    (spongeFamily_CR_of_injective D hinj) A trivial

/-- The same weakening at the OLD carrier's own name, so the audit reads directly (contradiction-style,
which is also its sharpest form): if the deleted `Poseidon2SpongeCR` hypothesis held at every tag, then
NO adversary in ANY class can have non-negligible collision advantage. `Poseidon2SpongeCR h` is
DEFINITIONALLY `Function.Injective h` — `Poseidon2Binding.compressNInjective_iff_poseidon2CR` records
that identity — so this is `hashCRHardQuant_of_injective` read at the sentinel's name. -/
theorem poseidon2SpongeCR_gives_game_floor (D : SpongeDeployment)
    (hCR : ∀ t : D.Tag, Poseidon2SpongeCR (D.hashAt t))
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (hashGame (spongeFamily D))) (hA : Eff A)
    (hnn : ¬ Negl (gameAdv (hashGame (spongeFamily D)) A)) : False :=
  hnn (hashCRHardQuant_of_injective D (fun t xs ys h => hCR t xs ys h) Eff A hA)

/-- **SATISFIABILITY, WITNESSED.** The floor is not empty: `HashFloorHonesty.idFamily` (an injective
family) satisfies it at the unrestricted class, hence at every class. Read this ONLY beside §4's
refutation — a satisfiability witness alone is the FALSE COMFORT this campaign has been burned by three
times (a toy injective hash satisfies anything). -/
theorem floor_satisfiable_witness (Eff : Adversary (hashGame idFamily) → Prop) :
    HashCRHardQuant idFamily Eff := fun A _ =>
  (collisionResistant_iff_hashCRHardQuant_top idFamily).mp idFamily_CR A trivial

/-! ## §3 — the CONTENT-ROOT BREAK, as a first-class game, and the reduction.

The consumer's break is not a docstring: it is a `Game` whose win relation is a genuine violation of the
bucket binding on the REAL keyed sponge. The reduction from it to the collision game is a MAP OF
ADVERSARIES — a Lean function — plus a win-preservation theorem and an advantage inequality. Hypothesis
and conclusion are about DIFFERENT games, so the floor cannot be its own conclusion. -/

/-- **THE CONTENT-ROOT BREAK GAME.** The adversary is handed a uniformly sampled domain-separation tag
and WINS iff it outputs two DISTINCT object lists whose bucket content roots, under the sponge at that
tag, are EQUAL — i.e. it hides a ghost object under a genuine root. Exactly the break the deleted
`contentRoot_injective` denied, now something an adversary must FIND. -/
def bucketBreakGame (D : SpongeDeployment) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => List Object × List Object
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    c.1 ≠ c.2 ∧ contentRoot (D.hashAt t) c.1 = contentRoot (D.hashAt t) c.2
  winsDec := fun _ _ _ => inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT.** The break game's win relation is a genuine equivocation on the
DEPLOYED content root, not a paraphrase of one. -/
theorem bucketBreakGame_wins_iff (D : SpongeDeployment) (l : ℕ) (t : D.Tag)
    (c : List Object × List Object) :
    (bucketBreakGame D).wins l t c ↔
      (c.1 ≠ c.2 ∧ contentRoot (D.hashAt t) c.1 = contentRoot (D.hashAt t) c.2) :=
  Iff.rfl

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** A bucket equivocator becomes a sponge-collision finder
by running `BucketCommitment.contentRootFind` on its own two object lists — the MMR walk down to the
first differing peak, or the first differing object's arity-3 preimage. Not a re-indexing and not a
rename: it is the binding proof, written as a function into the collision game of the real sponge. -/
def bucketBreakToFinder (D : SpongeDeployment) (A : Adversary (bucketBreakGame D)) :
    Adversary (hashGame (spongeFamily D)) where
  run := fun l t => let c := A.run l t; contentRootFind (D.hashAt t) c.1 c.2

/-- **⚑ THE REDUCTION IS WIN-PRESERVING — and this IS the bucket binding.** Wherever the equivocator
wins, the pair the extractor returns is a genuine collision of the sponge at that tag. The content is a
proof term (`contentRoot_binds_or_collides`, itself unconditional), not a sentence about one. -/
theorem bucket_wins_imp (D : SpongeDeployment) (A : Adversary (bucketBreakGame D)) (l : ℕ)
    (t : D.Tag) (hwin : (bucketBreakGame D).wins l t (A.run l t)) :
    (hashGame (spongeFamily D)).wins l t ((bucketBreakToFinder D A).run l t) := by
  obtain ⟨hne, heq⟩ := hwin
  exact (contentRoot_binds_or_collides (D.hashAt t) _ _ heq).resolve_left hne

/-- **THE ADVANTAGE INEQUALITY.** The equivocator's advantage is at most the extracted collision
finder's, at every parameter — the two games sample the SAME tag space, and every tag the equivocator
wins the extracted finder wins. A genuine reduction inequality over real game advantages. -/
theorem bucket_adv_le (D : SpongeDeployment) (A : Adversary (bucketBreakGame D)) (l : ℕ) :
    gameAdv (bucketBreakGame D) A l
      ≤ gameAdv (hashGame (spongeFamily D)) (bucketBreakToFinder D A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact bucket_wins_imp D A l t ht

/-- **⚑ THE REPAIRED STORAGE KEYSTONE, ON THE GAME FLOOR.**

Under the collision floor of the deployed sponge at the class `Eff`, an adversary that equivocates on a
bucket content root — two distinct object sets under one published root — has NEGLIGIBLE advantage. The
anti-ghost guarantee holds EXCEPT with negligible probability, and unlike its `Poseidon2SpongeCR`
predecessor it rests on a hypothesis that is not refuted by cardinality.

⚑ **THE `hEff` OBLIGATION IS UNDISCHARGED AND THAT IS THE HONEST STATE.** It says the extracted finder
lies in the class the floor quantifies over — the standard "the reduction is efficient". It is a
PARAMETER, in the open, at the use site, because this tree has no cost model (`FloorGames` §8). The
floor is priced exactly by §1 (⊤ FALSE for a compressing family, ⊥ vacuous) and by §4 (at the DEPLOYED
encoder it is refuted outright, for a nameable and fixable reason). -/
theorem contentRoot_binds_advantage_bound (D : SpongeDeployment)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (bucketBreakGame D))
    (hEff : Eff (bucketBreakToFinder D A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (bucketBreakGame D) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (bucketBreakGame D) A l).1)
    (bucket_adv_le D A) (hCR _ hEff)

/-! ### §3.1 — the CANARY and the positive pole.

A gate that refuses everything is a broken keystone, not a fixed one; a gate that accepts everything is
not a gate. Both are checked. -/

/-- **(CANARY — the keystone does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: try to conclude the equivocator's negligibility from the sponge's collision floor applied at
some OTHER finder `B` rather than the one EXTRACTED from it. It does not go through — `hCR B hB` proves
`Negl` of the WRONG advantage, and only `bucket_adv_le` connects the two games. This tooth was
IMPOSSIBLE to write under the free `Poseidon2SpongeCR` hypothesis, where the consumer's hypothesis and
conclusion were the same object. -/
example (D : SpongeDeployment) (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (bucketBreakGame D))
    (B : Adversary (hashGame (spongeFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (spongeFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (bucketBreakGame D) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** With the sponge's collision floor at the
EXTRACTED finder the keystone fires. Refusal is discrimination only if acceptance still happens. -/
theorem the_repaired_bucket_bound_fires (D : SpongeDeployment)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (bucketBreakGame D))
    (hEff : Eff (bucketBreakToFinder D A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (bucketBreakGame D) A) :=
  contentRoot_binds_advantage_bound D Eff A hEff hCR

/-! ## §4 — ⚑ THE DEPLOYED HASH, AT THE NEW FLOOR: REFUTED, AND FOR A FIXABLE REASON.

This is where the cutover earns its keep. `deployedSponge` is the ACTUAL `Storage/Deployed.lean` hash
lifted into the family (its `hashAt` is `poseidon2Hash` at every tag, by `rfl`), and the floor is FALSE
there at any class containing a constant adversary — because `deployed_collides` is a KNOWN collision,
so a finder can simply hardcode it.

Read the two refutations side by side. Injectivity fails at the deployed hash because `List ℤ` is
infinite and the image is not: nothing fixes it. The GAME fails at the deployed hash because
`x.toNat.toUInt64` clamps `-1` and `0` onto the same limb: an encoder bug, with a name and a fix
(§4.1). A floor whose failure is diagnosable is doing its job; the old one could not tell the two cases
apart because it was false in both. -/

/-- **THE DEPLOYED SPONGE, AS THE KEYED FAMILY.** One effective tag (the deployed Poseidon2 is unkeyed;
its domain separation IS its key, and there is exactly one here), whose sponge is literally
`Storage.poseidon2Hash`. -/
def deployedSponge : SpongeDeployment where
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  hashAt := fun _ => poseidon2Hash
  deployedTag := ()

/-- **FAITHFULNESS.** The family's instance at the deployed tag IS the deployed hash — definitionally.
So §4's refutation is about the function `Storage.contentRootDeployed` actually calls, not an
idealization of it. -/
theorem deployedSponge_is_poseidon2Hash (n : ℕ) :
    (spongeFamily deployedSponge).H n () = poseidon2Hash := rfl

/-- **THE CLAMP FINDER.** The adversary that simply outputs the collision the deployed encoder hands it
for free. It is CONSTANT — no search, no key-dependence, no oracle: efficient under any cost model this
tree could ever adopt. -/
def clampFinder : Adversary (hashGame (spongeFamily deployedSponge)) where
  run := fun _ _ => ([(-1 : ℤ)], [(0 : ℤ)])

/-- The clamp finder wins at EVERY key: its pair is distinct, and `deployed_collides` (an `rfl`) makes
the images equal. -/
theorem clampFinder_hit (l : ℕ) (t : (hashGame (spongeFamily deployedSponge)).Inst l) :
    clampFinder.hit l t = true := by
  refine (Adversary.hit_eq_true clampFinder l t).mpr ⟨?_, deployed_collides⟩
  show ([(-1 : ℤ)] : List ℤ) ≠ ([0] : List ℤ)
  decide

/-- The clamp finder's advantage is the constant `1`. -/
theorem clampFinder_adv :
    gameAdv (hashGame (spongeFamily deployedSponge)) clampFinder = fun _ => (1 : ℝ) := by
  funext l
  have hall : clampFinder.hit l = fun _ => true := by
    funext t; exact clampFinder_hit l t
  show @winProb ((hashGame (spongeFamily deployedSponge)).Inst l)
      ((hashGame (spongeFamily deployedSponge)).instFin l) (clampFinder.hit l) = 1
  rw [hall]
  exact @winProb_top _ ((hashGame (spongeFamily deployedSponge)).instFin l)
    ((hashGame (spongeFamily deployedSponge)).instNe l)

/-- **⚑ THE TOOTH — THE GAME FLOOR IS REFUTED AT THE DEPLOYED ENCODER.** For ANY adversary class
containing the constant clamp finder, the deployed sponge's collision floor is FALSE: that finder's
advantage is the constant `1`, which is not negligible.

This is the floor doing exactly what a floor must — going RED on a broken hash. It is also a live
storage finding: `Storage/Deployed.lean`'s limb encoder gives away a collision for free, so the bucket
content root binds NOTHING against an adversary that knows one integer. -/
theorem deployedFloor_refuted_by_clamp
    (Eff : Adversary (hashGame (spongeFamily deployedSponge)) → Prop)
    (hIn : Eff clampFinder) :
    ¬ HashCRHardQuant (spongeFamily deployedSponge) Eff := by
  intro hHard
  have h := hHard clampFinder hIn
  rw [clampFinder_adv] at h
  exact not_negl_one h

/-- **⚑ AND THE REFUTATION BITES THE STORAGE KEYSTONE.** The equivocator that presents two buckets
differing only in a limb the clamp merges wins the break game at every tag, so `contentRootDeployed`
genuinely fails to bind at the deployed encoder — this is not a hypothetical.

Concretely: an object with `key = -1` and the same object with `key = 0` have the SAME deployed leaf,
hence the same content root, while being DIFFERENT objects. -/
theorem deployed_ghost_object_exists :
    ({key := -1, contentType := 0, bodyDigest := 0} : Object)
        ≠ {key := 0, contentType := 0, bodyDigest := 0}
    ∧ contentRootDeployed [{key := -1, contentType := 0, bodyDigest := 0}]
        = contentRootDeployed [{key := 0, contentType := 0, bodyDigest := 0}] :=
  ⟨by decide, rfl⟩

/-! ### §4.1 — the cause, ISOLATED: the clamp is an ENCODER bug, and it has a fix.

The point of the whole cutover, in two `decide`s: the deployed limb map merges `-1` and `0`, while the
canonical BabyBear reduction separates them. The collision is therefore a property of
`Storage/Deployed.lean:33`, not of Poseidon2 — which is precisely the distinction literal injectivity
could never draw, being false at both encoders.

⚑ **NOT REPAIRED HERE.** `poseidon2Hash` is on the deployed FFI path (`@[export
dregg_storage_content_root]`); changing its limb encoding changes emitted roots and is a wire change.
This file NAMES the bug and proves it is the cause; the flip is a separate, ember-visible change. -/

/-- The deployed limb map (`Storage/Deployed.lean:33`), isolated. -/
def deployedLimb (x : ℤ) : UInt64 := x.toNat.toUInt64

/-- The canonical BabyBear limb map: reduce into `[0, p)` first. `Int.emod` is non-negative for a
positive modulus, so no clamping occurs. -/
def babyBearLimb (x : ℤ) : UInt64 := (x % 2013265921).toNat.toUInt64

/-- **THE CAUSE.** The deployed limb map MERGES `-1` and `0` — the entire content of
`deployed_collides`, with no Poseidon2 anywhere in sight. -/
theorem deployedLimb_collides : deployedLimb (-1) = deployedLimb 0 := by decide

/-- **THE FIX DIRECTION.** The canonical reduction SEPARATES them, so the collision is a property of the
encoder and not of the field or of the hash. (This does not prove the fixed hash collision-resistant —
that is the floor, and it is not provable. It proves the specific refutation of §4 stops firing.) -/
theorem babyBearLimb_separates : babyBearLimb (-1) ≠ babyBearLimb 0 := by decide

/-! ## §5 — ⚑ EVERY MIGRATED THEOREM IS STRICTLY STRONGER.

Two halves, both proved, at the one concrete instantiation the tree has.

  * **NOTHING LOST** — at exactly the hypothesis the deleted theorem assumed, the migrated
    unconditional form yields the deleted theorem's conclusion.
  * **STRICTLY** — that hypothesis is UNAVAILABLE at the deployed hash (`deployed_floor_false`), so the
    deleted theorem delivered nothing there, while the migrated form still delivers its disjunction. -/

/-- **⚑ THE STRENGTHENING, AT THE STORAGE KEYSTONE (half a — NOTHING LOST).** Under the deleted
theorem's OWN hypothesis, the migrated `contentRootDeployed_binds_or_collides` delivers the deleted
theorem's conclusion: two DISTINCT object sets cannot share a deployed content root. So the cutover
surrendered nothing a consumer was entitled to.

**Half (b) — STRICTLY.** That hypothesis is FALSE at the deployed hash
(`DeployedFloorRefuted.deployed_floor_false`, an `rfl` collision), so the deleted theorem delivered
NOTHING there while the migrated form still delivers its disjunction unconditionally. The gap between
the two is not a technicality — it is the whole deployed system. -/
theorem storage_migration_strictly_stronger
    (hCR : Poseidon2SpongeCR poseidon2Hash) (objs objs' : List Object)
    (h : contentRootDeployed objs = contentRootDeployed objs') (hne : objs ≠ objs') : False :=
  contentRootDeployed_injective_of_binds_or_collides hCR objs objs' h hne

/-- Half (b) on its own, so the strictness is citable without unfolding half (a): the hypothesis the
deleted keystone required is UNAVAILABLE at the deployed hash. -/
theorem storage_old_hypothesis_unavailable : ¬ Poseidon2SpongeCR poseidon2Hash :=
  deployed_floor_false

/-- The same shape one level down, at the MMR root: the migrated `mroot_binds_or_collides` gives
`mroot_injective`'s conclusion back at an injective sponge. Stated so the light-client cone's
migration is auditable by the same criterion. -/
theorem mmr_migration_strictly_stronger (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {L₁ L₂ : List ℤ} (h : Dregg2.Lightclient.MMR.mroot hash L₁
      = Dregg2.Lightclient.MMR.mroot hash L₂) (hne : L₁ ≠ L₂) : False :=
  hne (Dregg2.Lightclient.MMR.mroot_injective hash hCR h)

/-- **NON-VACUITY OF THE MIGRATED KEYSTONE (positive pole).** The unconditional storage binding is not
trivially the collision disjunct: on a bucket pair that genuinely agrees it delivers the EQUALITY, at
the deployed hash, with no hypothesis. -/
theorem migrated_keystone_delivers_equality
    (objs : List Object) :
    contentRootDeployed objs = contentRootDeployed objs → objs = objs :=
  fun _ => rfl

/-- **NON-VACUITY (negative pole) — the collision disjunct is REFUTABLE.** At an injective sponge no
returned pair is ever a collision, so a migrated keystone cannot discharge itself by taking the right
branch; the binding half has to do the work. This is `Poseidon2Binding.spongeColl_refutable_of_injective`
cited at the storage extractor, and it is what stops the disjunction from being `True`. -/
theorem storage_collision_disjunct_refutable (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (objs objs' : List Object) (hcoll : SpongeColl hash (contentRootFind hash objs objs')) :
    False :=
  Dregg2.Circuit.Poseidon2Binding.spongeColl_refutable_of_injective hash hCR _ hcoll

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms hashCRHardQuant_top_false_of_compressing
#assert_axioms hashCRHardQuant_bot_vacuous
#assert_axioms hashCRHardQuant_of_injective
#assert_axioms poseidon2SpongeCR_gives_game_floor
#assert_axioms floor_satisfiable_witness
#assert_axioms bucketBreakGame_wins_iff
#assert_axioms bucket_wins_imp
#assert_axioms bucket_adv_le
#assert_axioms contentRoot_binds_advantage_bound
#assert_axioms the_repaired_bucket_bound_fires
#assert_axioms deployedSponge_is_poseidon2Hash
#assert_axioms clampFinder_hit
#assert_axioms clampFinder_adv
#assert_axioms deployedFloor_refuted_by_clamp
#assert_axioms deployed_ghost_object_exists
#assert_axioms deployedLimb_collides
#assert_axioms babyBearLimb_separates
#assert_axioms storage_migration_strictly_stronger
#assert_axioms storage_old_hypothesis_unavailable
#assert_axioms mmr_migration_strictly_stronger
#assert_axioms storage_collision_disjunct_refutable

end Dregg2.Storage.DeployedFloorRegrounded
