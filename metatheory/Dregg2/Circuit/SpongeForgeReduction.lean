/-
# `Dregg2.Circuit.SpongeForgeReduction` — the DEPLOYED sponge-digest bindings, as SECURITY REDUCTIONS.

## The sin this module retires, at its root

Across the circuit tower ~20 exported bindings had the shape

    theorem foo_binds (hCR : Poseidon2SpongeCR sponge) {a b} (h : digest a = digest b) : a = b

`Poseidon2SpongeCR sponge := ∀ xs ys, sponge xs = sponge ys → xs = ys` is INJECTIVITY of a map from
the infinite `List ℤ` into a bounded BabyBear field element. It is PROVED FALSE at deployed parameters
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so every such theorem is **VACUOUSLY TRUE at
the deployed hash** — clean `#assert_axioms`, zero transported security. `StateCommit.compressNInjective`
is literally the same predicate, refuted by the same tooth (`compressNInjective_false_of_finite_range`).

The cure is NOT a `binds ∨ collides` disjunction. That is true at deployed parameters, but a collision
EXISTS there by pigeonhole, so the disjunction is satisfiable through the `collides` branch WITHOUT
`binds` ever holding: it quantifies over SOLUTIONS, where cryptographic hardness quantifies over
EFFICIENT ADVERSARIES. The cure is the standard one:

  * the forgery is a first-class `FloorGames.Game` (the deployed digest equivocation IS the win
    relation, at a uniformly sampled domain-separation tag),
  * the extractor is a MAP OF ADVERSARIES into the deployed sponge's collision game,
  * the advantage inequality is UNCONDITIONAL — it quantifies over ALL adversaries, the class `Eff`
    does NOT appear in it,
  * the security conclusion is `Negl` under the NAMED floor
    `DomainSeparatedCREffRegrounded.DomainSeparatedCREff D Eff`
    = `FloorGames.HashCRHardQuant (poseidon2KeyedFamily D) Eff`,
  * and `Eff` is instantiated at `CostAdversary.IsPolyTime`, where the efficiency obligation is
    DISCHARGED by `CostTactics.poly_time` rather than carried as a floating parameter.

## What this module is

The GENERIC layer, so the ~20 sites do not each re-derive it. Every deployed site absorbs a `List ℤ`
CODE of its own object and publishes the sponge of it; the only per-site data is that code. So:

  * **§1** `codeForgeGame D A code` — the forgery game at an arbitrary domain `A` with an absorption
    code `code : A → List ℤ`. The adversary wins iff it outputs two objects whose CODES DIFFER yet
    whose domain-separated sponge digests AGREE at the sampled tag. `codeForgeGame_wins_iff` pins that
    the problem is in the statement; `deployed_forgery_is_break` ties a deployed-tag equivocation of
    the real function to a game win.
  * **§2** `codeForgeToFinder` — the extractor as a map of adversaries (a pure output reshaping: read
    off the two codes). `code_wins_imp` / `code_adv_le` — win-preservation and the UNCONDITIONAL
    advantage inequality.
  * **§3** `codeForge_advantage_bound` — the reduction under the named floor at an arbitrary class.
  * **§4** `codeForge_binds_from_polyTime` — `hEff` DISCHARGED at `Eff := IsPolyTime` via `poly_time`.
    The ONLY per-site input is the domain's output-size fact (the `hout` slot), supplied here in the
    generic `codeAnsSize`/`hashAnsSize` encodings where it is `rfl`-shaped.
  * **§5** the poles, PRICED: `⊤` FALSE at the deployed BabyBear sponge, `⊥` vacuous, the class at
    `IsPolyTime` INHABITED, and the canary that the bound does not follow from the floor at another
    finder.
  * **§6** `injective_code_forgery_is_break` — the bridge every site with an INJECTIVE code uses: an
    equivocation of the site's OBJECTS is a game win, because distinct objects have distinct codes.

## ⚑ ONE CARRIER, ONE FLOOR — no mirror

An earlier revision of this module declared its OWN `DeployedSponge` / `spongeFamily` /
`DeployedSpongeCRHard` — field-for-field the same objects as `Poseidon2KeyedBridge`'s
`DomainSeparatedSponge` / `poseidon2KeyedFamily` and `DomainSeparatedCREffRegrounded`'s
`DomainSeparatedCREff`. That mirror is DELETED, not bridged: this module is typed directly over
`Poseidon2KeyedBridge.DomainSeparatedSponge`, its floor IS `DomainSeparatedCREff`, and the §5 poles
are the Regrounded file's `effFloor_top_false_babyBear` / `effFloor_bot_vacuous`, re-exported under
this module's names. So every faithfulness lemma the bridge proves
(`deployed_hash_is_family_instance`, `wins_iff_deployed_collision`) applies verbatim to the games
below, and there is exactly ONE deployed-sponge carrier in the tree for consumers to speak.

## What this does NOT buy (stated at current resolution)

The floor is FALSE at `Eff := ⊤` and vacuous at `Eff := ⊥`; both are proved in the Regrounded file and
re-exported below. What the reduction buys is that the residual is ONE named parameter with both poles
proved and its `IsPolyTime` instantiation's efficiency obligation DISCHARGED — in place of a hypothesis
the deployed hash REFUTES. It does not make the deployed BabyBear sponge collision-resistant; nothing
can.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no fresh `axiom`, no
`native_decide`, no `decide` on an opaque prop. Cost stays SYNTACTIC (`poly_time` only ever applies
`isPolyTime_postMap`, whose cost is derived from the reduction program's syntax).
-/
import Dregg2.Circuit.DomainSeparatedCREffRegrounded
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.CostTactics
import Dregg2.Tactics

namespace Dregg2.Circuit.SpongeForgeReduction

open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit hashGame)
open Dregg2.Circuit.Poseidon2KeyedBridge
  (DomainSeparatedSponge poseidon2KeyedFamily)
open Dregg2.Circuit.DomainSeparatedCREffRegrounded
  (DomainSeparatedCREff effFloor_top_false_babyBear effFloor_bot_vacuous)
open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime)
open Dregg2.Crypto.CostTactics

set_option autoImplicit false

/-! ## §0 — THE DEPLOYED SPONGE, AND THE NAMED FLOOR THIS MODULE REDUCES TO.

The deployed Poseidon2 is a FIXED, UNKEYED `List ℤ → ℤ`. Its effective KEY is the domain-separation
tag — the per-use prefix the deployment absorbs ahead of the message — which is the standard
keyed-from-unkeyed model. `Poseidon2KeyedBridge.DomainSeparatedSponge` bundles exactly that, and
`poseidon2KeyedFamily` lifts it to a `HashFloorHonesty.KeyedHashFamily`, so the floor below is
`DomainSeparatedCREff D Eff = FloorGames.HashCRHardQuant (poseidon2KeyedFamily D) Eff` at the family
whose instance AT THE DEPLOYED TAG **is** the function the prover computes
(`Poseidon2KeyedBridge.deployed_hash_is_family_instance` — a definitional equality, no idealization).

⚑ This module deliberately routes through the SINGLE owner of that carrier —
`Poseidon2KeyedBridge` (the bundle + family) and `DomainSeparatedCREffRegrounded` (the `Eff`-carrying
floor with both poles priced) — instead of declaring a mirror. There is nothing to keep in sync. -/

/-! ## §1 — THE FORGERY, AS A GAME.

The deployed shape at every site: an object `a : A` is absorbed as the field-element list `code a` and
published as `sponge (tagCode t ++ code a)`. A BINDING FORGERY is therefore exactly: two objects with
DIFFERENT absorbed codes carrying the SAME published digest. That is the win relation below — not a
docstring about it, and not the existence of a collision somewhere. -/

/-- **THE GENERIC SPONGE-DIGEST FORGERY GAME.** The adversary is handed a uniformly sampled
domain-separation tag and WINS iff it outputs two objects of the site's domain `A` whose absorbed
CODES DIFFER yet whose domain-separated sponge digests AGREE — i.e. it breaks the binding of the
deployed digest `a ↦ D.hashAt t (code a)`.

The break is IN the win relation. `code` is the only per-site datum: it is how the deployed circuit
absorbs the object, so a win here is a forgery of the deployed publication, not of an abstraction. -/
def codeForgeGame (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => A × A
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p =>
    code p.1 ≠ code p.2 ∧
      D.hashAt t (code p.1) = D.hashAt t (code p.2)
  winsDec := fun _ _ _ => inferInstance

/-- **THE DEPLOYED SPONGE'S COLLISION GAME, in the `codeForgeGame` presentation** (`code := id`). A win
here IS a collision of the deployed domain-separated function, by `Iff.rfl` — it is the same `Prop` as
`hashGame (poseidon2KeyedFamily D)`'s win. This is the COMMON TARGET every multi-absorb site's
chain-walk extractor lands in, so a fold site composes two `postMap` hops (fold forgery → collision
pair → the collision game) exactly as the `Market.WideCommitBoundary` spine does. -/
abbrev spongeCollGame (D : DomainSeparatedSponge) : Game := codeForgeGame D (List ℤ) id

/-- A `spongeCollGame` win IS a collision of the deployed domain-separated sponge at the sampled tag. -/
theorem spongeCollGame_wins_iff (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag) (p : List ℤ × List ℤ) :
    (spongeCollGame D).wins l t p ↔ (p.1 ≠ p.2 ∧ D.hashAt t p.1 = D.hashAt t p.2) :=
  Iff.rfl

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation unfolds, by `Iff.rfl`, to a genuine
equivocation of the deployed domain-separated digest at the sampled tag. -/
theorem codeForgeGame_wins_iff (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ)
    (l : ℕ) (t : D.Tag) (p : A × A) :
    (codeForgeGame D A code).wins l t p ↔
      (code p.1 ≠ code p.2 ∧
        D.hashAt t (code p.1) = D.hashAt t (code p.2)) :=
  Iff.rfl

/-- **⚑ THE FORGERY IS THE DEPLOYED OBJECT.** Two objects whose codes differ but whose digest under
the DEPLOYED fixed function `D.deployedHash` agrees ARE a game win at the deployed tag. This is what
ties the abstract game to the very publication the circuit computes: the game is not free-floating. -/
theorem deployed_forgery_is_break (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ)
    (a b : A) (hne : code a ≠ code b)
    (heq : D.deployedHash (code a) = D.deployedHash (code b)) :
    (codeForgeGame D A code).wins 0 D.deployedTag (a, b) :=
  ⟨hne, heq⟩

/-! ## §2 — THE EXTRACTOR, AS A MAP OF ADVERSARIES, and the UNCONDITIONAL advantage inequality.

`Eff` does NOT appear in `code_adv_le`. It is a statement about EVERY adversary — which is what makes
the §3 domination step a reduction rather than a re-assertion. -/

/-- **THE EXTRACTOR.** A digest forger becomes a collision finder of the DEPLOYED domain-separated
sponge by reading off the two absorbed codes. A pure output reshaping, tag passed through — which is
what makes §4's efficiency preservation a theorem rather than an assumption. -/
def codeForgeToFinder (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ)
    (adv : Adversary (codeForgeGame D A code)) :
    Adversary (hashGame (poseidon2KeyedFamily D)) where
  run := fun l t => (code (adv.run l t).1, code (adv.run l t).2)

/-- **⚑ WIN-PRESERVATION — the reduction, at the game level.** Every tag on which the forger wins, the
extracted finder wins the DEPLOYED sponge's collision game: distinct codes, equal
`sponge (tagCode t ++ ·)`. Definitional, because `poseidon2KeyedFamily`'s instance at `t` IS
`D.hashAt t`. -/
theorem code_wins_imp (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ)
    (adv : Adversary (codeForgeGame D A code)) (l : ℕ) (t : D.Tag)
    (hwin : (codeForgeGame D A code).wins l t (adv.run l t)) :
    (hashGame (poseidon2KeyedFamily D)).wins l t ((codeForgeToFinder D A code adv).run l t) :=
  hwin

/-- **THE ADVANTAGE INEQUALITY — UNCONDITIONAL, over ALL adversaries.** The forger's advantage is at
most the extracted collision finder's, at every parameter, over the SAME sampled tag space. No class
appears; this is the load-bearing content of the reduction. -/
theorem code_adv_le (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ)
    (adv : Adversary (codeForgeGame D A code)) (l : ℕ) :
    gameAdv (codeForgeGame D A code) adv l
      ≤ gameAdv (hashGame (poseidon2KeyedFamily D)) (codeForgeToFinder D A code adv) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact code_wins_imp D A code adv l t ht

/-! ## §3 — THE REDUCED BINDING, at an arbitrary adversary class. -/

/-- **⚑ THE REDUCED DIGEST BINDING — from the DEPLOYED sponge's collision floor, VIA the reduction.**

Under `DomainSeparatedCREff D Eff` (the deployed domain-separated sponge's collision floor at the class
`Eff`), a digest forger whose EXTRACTED finder is in that class has NEGLIGIBLE advantage: the published
digest binds the absorbed code except with negligible probability.

This is what replaces `(hCR : Poseidon2SpongeCR sponge) → a = b` as the exported headline. That form
was VACUOUS at deployed parameters; this one is not, and its residual is the single named `Eff` whose
two poles are proved in §5.

⚑ `hEff` is a PARAMETER here — the honest name for "the reduction is efficient" at an ARBITRARY class.
§4 DISCHARGES it at `Eff := IsPolyTime`. -/
theorem codeForge_advantage_bound (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (adv : Adversary (codeForgeGame D A code))
    (hEff : Eff (codeForgeToFinder D A code adv))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (codeForgeGame D A code) adv) :=
  negl_of_le (fun l => (gameAdv_mem_unit (codeForgeGame D A code) adv l).1)
    (code_adv_le D A code adv) (hCR _ hEff)

/-! ## §4 — `hEff` DISCHARGED at `Eff := IsPolyTime`, with the overhead DERIVED.

The reduction is `Adversary.postMap` of a pure reshaping, so `CostAdversary.isPolyTime_postMap` proves
it preserves `IsPolyTime`: an EFFICIENT forger yields an EFFICIENT collision finder. The reshaper's
declared work `cw · (input size) + bw` is the honest modelling input (a Lean `fun` has no runtime, and
`CostAdversary` charges work in the PROGRAM'S SYNTAX, never as an assertable field). Everything else —
including the poly-ness of the composed overhead — is derived. -/

/-- **THE FORGERY GAME'S ANSWER ENCODING.** A forged pair costs, to write down, the two absorbed codes.
Concrete on purpose: the size measure belongs to the GAME, and leaving it open would let a degenerate
`sz := 0` make output free again. -/
def codeAnsSize (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ) :
    AnsSize (codeForgeGame D A code) :=
  fun _ p => (code p.1).length + (code p.2).length

/-- **THE COLLISION GAME'S ANSWER ENCODING** — the two claimed preimages of the deployed sponge. -/
def hashAnsSize (D : DomainSeparatedSponge) : AnsSize (hashGame (poseidon2KeyedFamily D)) :=
  fun _ p => p.1.length + p.2.length

/-- **THE EXTRACTOR DOES NOT BLOW UP ITS INPUT** — it emits exactly the two codes it was handed, so its
output size under the collision game's encoding EQUALS its input size under the forgery game's. The
`hout` obligation of `isPolyTime_postMap`, discharged by `rfl`-shaped arithmetic rather than assumed. -/
theorem codeForge_out_le (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ)
    (l : ℕ) (t : D.Tag) (p : A × A) :
    hashAnsSize D l (code p.1, code p.2)
      ≤ 1 * codeAnsSize D A code l p + 0 := by
  show (code p.1).length + (code p.2).length
    ≤ 1 * ((code p.1).length + (code p.2).length) + 0
  omega

/-- **⚑ `hEff` DISCHARGED — the reduced binding at `Eff := IsPolyTime`.** A digest forger that is
EFFICIENT at the game's own answer encoding, put through the extractor, is still efficient — so the
deployed sponge's collision floor at `IsPolyTime` applies to it and the forger's advantage is
negligible. NO floating polynomial: the reshaper's declared work `(cw, bw)` is the only modelling
input, and the output growth is PROVED (`codeForge_out_le`). -/
theorem codeForge_binds_from_polyTime (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ)
    (adv : Adversary (codeForgeGame D A code))
    (hA : IsPolyTime (codeAnsSize D A code) adv) (cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (hashAnsSize D))) :
    Negl (gameAdv (codeForgeGame D A code) adv) := by
  have hEff : IsPolyTime (hashAnsSize D) (codeForgeToFinder D A code adv) := by
    poly_time (codeAnsSize D A code) (hashAnsSize D)
      (fun _ _ (p : A × A) => (code p.1, code p.2))
      cw bw 1 0 hA
    intro l t p
    exact codeForge_out_le D A code l t p
  exact codeForge_advantage_bound D A code (IsPolyTime (hashAnsSize D)) adv hEff hCR

/-! ## §5 — the `Eff` residual, PRICED AT BOTH POLES, plus the canary and the positive pole.

The poles are PROVED ONCE, at the floor's single owner (`DomainSeparatedCREffRegrounded` §4); the two
theorems below are that file's teeth re-exported under this module's names, kept so every consumer of
the reduction sees the price beside the bound. -/

/-- **⚑ THE ⊤ POLE — the floor is FALSE at the REAL BabyBear parameters** (the honest price of `hEff`).
A sponge whose output is a BabyBear field element has finite range while `List ℤ` is infinite, so a
collision exists at every tag and the floor at `Eff := ⊤` is FALSE. What the reduction buys is NOT a
floor the deployed sponge satisfies at ⊤ — no such floor exists — it is that the residual is ONE named
parameter with both poles proved, in place of a hypothesis the deployed hash outright REFUTES.
Re-export of `DomainSeparatedCREffRegrounded.effFloor_top_false_babyBear`. -/
theorem forge_floor_top_false_babyBear (D : DomainSeparatedSponge)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ DomainSeparatedCREff D (fun _ => True) :=
  effFloor_top_false_babyBear D hb

/-- **THE ⊥ POLE — vacuous.** Recorded so the floor's satisfiability cannot be mistaken for evidence.
Re-export of `DomainSeparatedCREffRegrounded.effFloor_bot_vacuous`. -/
theorem forge_floor_bot_vacuous (D : DomainSeparatedSponge) :
    DomainSeparatedCREff D (fun _ => False) :=
  effFloor_bot_vacuous D

/-- **(TOOTH — the class the floor is instantiated at is NOT EMPTY.)** `IsPolyTime (hashAnsSize D)` is
not the vacuous `Eff := ⊥`: the constant finder is in it, because the answer it writes has size `0`
under the game's own encoding. Together with `CostAdversary.bruteForce_not_polyTime` (the ⊤-collapse
witness is excluded) this pins the instantiated floor strictly between the two poles. -/
theorem hashFloor_isPolyTime_inhabited (D : DomainSeparatedSponge) :
    IsPolyTime (hashAnsSize D)
      (Dregg2.Crypto.CostAdversary.idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  Dregg2.Crypto.CostAdversary.isPolyTime_inhabited _ _
    ⟨0, 0, fun _ _ => by simp [hashAnsSize]⟩

/-- **(CANARY — the bound does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: try to conclude the forger's negligibility from the collision floor applied at some OTHER
finder `B`, not the one EXTRACTED from the forger. It does not go through — only `code_adv_le`
connects the extracted finder to the forgery game. This tooth reds if a future edit disconnects them. -/
example (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (adv : Adversary (codeForgeGame D A code))
    (B : Adversary (hashGame (poseidon2KeyedFamily D))) (hB : Eff B)
    (hCR : DomainSeparatedCREff D Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (codeForgeGame D A code) adv) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one: with the deployed sponge's collision floor at the EXTRACTED finder,
the digest binding fires. -/
theorem the_reduced_forge_bound_fires (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (adv : Adversary (codeForgeGame D A code))
    (hEff : Eff (codeForgeToFinder D A code adv))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (codeForgeGame D A code) adv) :=
  codeForge_advantage_bound D A code Eff adv hEff hCR

/-! ## §6 — the INJECTIVE-CODE bridge: an OBJECT equivocation IS a game win.

Most deployed sites publish `sponge (code a)` for a code that is STRUCTURALLY injective (a canonical
serialization). For those the site's forgery — two DISTINCT OBJECTS with one digest — is a game win
directly. `hcode` is a STRUCTURAL fact about the serializer, never a crypto floor: it is exactly the
`serializeFin_injective` / `List.map_injective_iff` / cons-injectivity content the old proofs already
carried BESIDE the refuted `hCR`, and unlike `hCR` it is TRUE at deployed parameters. -/

/-- **⚑ THE OBJECT-LEVEL FORGERY IS A GAME WIN.** Under a structurally injective absorption code, two
DISTINCT objects publishing the SAME deployed digest are a `codeForgeGame` win at the deployed tag. So
"the digest binds the object" and "the digest binds the code" are the same forgery, and §3/§4's bounds
apply to the site's own equivocation. -/
theorem injective_code_forgery_is_break (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ)
    (hcode : Function.Injective code) (a b : A) (hne : a ≠ b)
    (heq : D.deployedHash (code a) = D.deployedHash (code b)) :
    (codeForgeGame D A code).wins 0 D.deployedTag (a, b) :=
  deployed_forgery_is_break D A code a b (fun h => hne (hcode h)) heq

/-- **THE EXACT-PROP SKELETON (the reduction's INTERNAL witness, NOT the headline).** Two objects with
equal deployed digests are EQUAL — or exhibit a genuine collision of the deployed domain-separated
sponge. This is the honest deterministic residue of the old `(hCR : Poseidon2SpongeCR sponge) → a = b`:
the refuted injectivity hypothesis is GONE, and the collision branch is what §3/§4 price. It is
retained ONLY as the extractor; it is NOT the exported binding, because a collision EXISTS at deployed
parameters, so its right branch is unconditionally available. -/
theorem digest_binds_or_collides (D : DomainSeparatedSponge) (A : Type) (code : A → List ℤ)
    (hcode : Function.Injective code) (a b : A)
    (heq : D.deployedHash (code a) = D.deployedHash (code b)) :
    a = b ∨ (code a ≠ code b ∧
      D.hashAt D.deployedTag (code a) = D.hashAt D.deployedTag (code b)) := by
  by_cases h : a = b
  · exact Or.inl h
  · exact Or.inr (injective_code_forgery_is_break D A code hcode a b h heq)

/-! ## §7 — axiom hygiene. -/

#assert_all_clean [
  codeForgeGame_wins_iff,
  spongeCollGame_wins_iff,
  deployed_forgery_is_break,
  code_wins_imp,
  code_adv_le,
  codeForge_advantage_bound,
  codeForge_out_le,
  codeForge_binds_from_polyTime,
  forge_floor_top_false_babyBear,
  forge_floor_bot_vacuous,
  hashFloor_isPolyTime_inhabited,
  the_reduced_forge_bound_fires,
  injective_code_forgery_is_break,
  digest_binds_or_collides
]

end Dregg2.Circuit.SpongeForgeReduction
