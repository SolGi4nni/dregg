/-
# `Dregg2.Circuit.Blake3FloorReduce` — the BLAKE3 floors, falsified as injectivity and rebuilt as
reduction twins over `CollisionReduce`.

## The disease (same as the Poseidon2 floors, previously toothless here)

Two BLAKE3 carriers in the tree are stated as **injectivity**:

  * `PortalFloor.Blake3Kernel.noCollision : collisionHard → ∀ x y, hash x = hash y → x = y`
    (`Dregg2/Crypto/PortalFloor.lean:178`) — the transcript/attribute hash.
  * `ThresholdDecrypt.Blake3Prf : ∀ key s₁ i₁ s₂ i₂, blake3Mac key s₁ i₁ = blake3Mac key s₂ i₂ →
    s₁ = s₂ ∧ i₁ = i₂` (`Dregg2/Distributed/ThresholdDecrypt.lean:289`) — the share-MAC carrier.

Both force an *infinite* message space (`List Nat`; `Nat × Nat` per key) into a digest. The real
BLAKE3 digest is 32 bytes — a FINITE space — so the injectivity these carriers assert is false by
pigeonhole: collisions EXIST; collision-resistance only means they are hard to FIND. Every theorem
conditioned on such a carrier is vacuously true at real parameters. `HashFloorHonesty` bit the
Poseidon2 floors (`poseidon2SpongeCR_false_babyBear`); the BLAKE3 floors had no tooth. This file
closes both, then builds the honest replacement.

## What this file provides

  * **§1 — FALSIFICATION.** `Blake3NoCollision` names the exact carrier shape; it is proved FALSE
    for any hash into a finite digest type (`blake3_noCollision_false_of_finite_digest`) and for any
    range-bounded `Nat`-valued hash (`blake3_noCollision_false_bounded`, the ≤ 2²⁵⁶ deployed form).
    Lifted to the class: any `Blake3Kernel` instance over a finite `Digest` has an UNSATISFIABLE
    `collisionHard` carrier (`blake3Kernel_collisionHard_false`). Same for the MAC:
    `macPrfShape_false_of_bounded` and its `Blake3Prf` corollary. MODELING NOTE, stated honestly:
    `blake3Mac` is `opaque`, so nothing about its range is provable in Lean; the `Blake3Prf`
    falsification is CONDITIONAL on the range bound (`∀ s i, blake3Mac key s i < B`) — which is
    exactly the honest model of a 32-byte tag (`B = 2²⁵⁶`). The kernel-level tooth needs only
    `Finite Digest`, which every real digest type satisfies.

  * **§2 — REDUCTION TWINS** (the `CollisionReduce` de-vacuation). Break events `Blake3Collision`
    / `MacCollision`; dichotomy leaves `blake3_orBreak` / `mac_orBreak` (mirroring
    `spongeN_orBreak` / `compress_orBreak`); the committed-opening twin
    `blake3_commit_opens_orBreak` (the de-vacuated `blake3_floor_cr`); the share-MAC twin
    `share_mac_detects_tamper_orBreak` over the REAL `opaque blake3Mac` (the de-vacuated
    `share_mac_detects_tamper` — same conclusion, NO `Blake3Prf` hypothesis); `_of_no_collision`
    recoveries; and the apex `Blake3Break` with a composed transcript+share theorem via
    `OrBreak.map₂`/`weaken`. `blake3Prf_implies_no_macCollision` pins that the twin is a strict
    weakening: the old carrier implies the no-break side, so nothing downstream is lost.

  * **§3 — FIRE, both directions.** A colliding toy mac (`collidingMac`) on which the twin, fed a
    concrete pass equality between DIFFERENT shares, is forced into the Break branch and delivers a
    genuine `MacCollision`; a colliding toy hash (`toyHash2`, parity — plus a `Blake3Kernel Bool`
    instance whose carrier §1 refutes); and an injective toy (`injToyHash = id`) on which
    `¬ Blake3Collision` is proved and `resolve` recovers binding verbatim on a concrete opening.
    The good branch and the break branch are both exercised on closed terms — the dichotomy is
    load-bearing in both directions.

## Axiom hygiene

`#assert_axioms` on every theorem: ⊆ {propext, Classical.choice, Quot.sound}. No sorry/admit,
no native_decide, no new axiom. This file EDITS NOTHING — PortalFloor and ThresholdDecrypt keep
their record; the falsification + twins live here over the same shapes.
-/
import Dregg2.Circuit.CollisionReduce
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Crypto.PortalFloor
import Dregg2.Distributed.ThresholdDecrypt

namespace Dregg2.Circuit.Blake3FloorReduce

open Dregg2.Circuit.CollisionReduce
open Dregg2.Circuit.HashFloorHonesty (not_injective_of_finite_range)
open Dregg2.Crypto.PortalFloor (Blake3Kernel)
open Dregg2.Distributed.ThresholdDecrypt (blake3Mac Blake3Prf)

set_option autoImplicit false

universe u

/-! ## §1 — FALSIFICATION: the BLAKE3 injectivity carriers are FALSE at any finite digest. -/

/-- The exact carrier shape `Blake3Kernel.noCollision` unpacks to (`PortalFloor.lean:178`): equal
BLAKE3 digests force equal preimages — injectivity of `hash : List Nat → Digest`. -/
def Blake3NoCollision {Digest : Type u} (hash : List Nat → Digest) : Prop :=
  ∀ x y : List Nat, hash x = hash y → x = y

/-- **TOOTH — `Blake3NoCollision` is FALSE for any hash of finite range.** `List Nat` is infinite;
an injection into a finite range is impossible (the `HashFloorHonesty` pigeonhole core). -/
theorem blake3_noCollision_false_of_finite_range {Digest : Type u} (hash : List Nat → Digest)
    (hfin : (Set.range hash).Finite) : ¬ Blake3NoCollision hash :=
  fun hinj => not_injective_of_finite_range hash hfin (fun _ _ h => hinj _ _ h)

/-- **TOOTH (deployed form) — FALSE whenever the digest TYPE is finite.** The real BLAKE3 digest is
32 bytes, a finite type; any faithful `Digest` model is `Finite`. No bound hypothesis needed: the
range of a map into a finite type is finite outright. -/
theorem blake3_noCollision_false_of_finite_digest {Digest : Type u} [Finite Digest]
    (hash : List Nat → Digest) : ¬ Blake3NoCollision hash :=
  blake3_noCollision_false_of_finite_range hash (Set.toFinite _)

/-- **TOOTH (bounded-`Nat` form)** — for a `Nat`-valued digest model, a range bound (the honest
model of a 32-byte tag is `B = 2^256`) refutes the carrier. Mirror of
`poseidon2SpongeCR_false_babyBear`. -/
theorem blake3_noCollision_false_bounded (hash : List Nat → Nat) (B : Nat)
    (hb : ∀ x, hash x < B) : ¬ Blake3NoCollision hash := by
  refine blake3_noCollision_false_of_finite_range hash ?_
  refine (Set.finite_lt_nat B).subset ?_
  rintro _ ⟨x, rfl⟩
  exact hb x

/-- **THE KERNEL-LEVEL TOOTH — any `Blake3Kernel` over a finite digest has an UNSATISFIABLE
`collisionHard` carrier.** `noCollision` says `collisionHard` implies injectivity; injectivity is
false at a finite digest; so `collisionHard` is false. Every `blake3_floor_cr` consumer over such an
instance is vacuous — the disease `HashFloorHonesty` documented for Poseidon2, now pinned for
BLAKE3. -/
theorem blake3Kernel_collisionHard_false {Digest : Type u} [Finite Digest]
    (K : Blake3Kernel Digest) : ¬ K.collisionHard :=
  fun hcr => blake3_noCollision_false_of_finite_digest K.hash (fun x y h => K.noCollision hcr x y h)

/-- The exact `Blake3Prf` shape (`ThresholdDecrypt.lean:289`), parametric in the mac: matching tags
under one key force matching `(share, idx)` messages — per-key injectivity on `Nat × Nat`. -/
def MacPrfShape (mac : Nat → Nat → Nat → Nat) : Prop :=
  ∀ key s₁ i₁ s₂ i₂, mac key s₁ i₁ = mac key s₂ i₂ → (s₁ = s₂ ∧ i₁ = i₂)

/-- `Blake3Prf` IS `MacPrfShape blake3Mac` — definitionally. Pins that the falsification below hits
the real carrier, not a paraphrase. -/
theorem blake3Prf_eq_shape : Blake3Prf = MacPrfShape blake3Mac := rfl

/-- **TOOTH — `MacPrfShape` is FALSE for any mac that is range-bounded at even ONE key.** The
message space `Nat × Nat` is infinite; the tag space under the bound is finite; pigeonhole. Mirror
of `compressInjective_false_of_finite_range` (uncurry, refute injectivity of the pair map). -/
theorem macPrfShape_false_of_bounded (mac : Nat → Nat → Nat → Nat) (key B : Nat)
    (hb : ∀ s i, mac key s i < B) : ¬ MacPrfShape mac := by
  intro hprf
  have hfin : (Set.range (fun p : Nat × Nat => mac key p.1 p.2)).Finite := by
    refine (Set.finite_lt_nat B).subset ?_
    rintro _ ⟨p, rfl⟩
    exact hb p.1 p.2
  refine not_injective_of_finite_range (fun p : Nat × Nat => mac key p.1 p.2) hfin ?_
  rintro ⟨s₁, i₁⟩ ⟨s₂, i₂⟩ heq
  obtain ⟨h1, h2⟩ := hprf key s₁ i₁ s₂ i₂ heq
  simp [h1, h2]

/-- **TOOTH (deployed carrier) — `Blake3Prf` is FALSE if `blake3Mac` is range-bounded anywhere.**
MODELING NOTE (honest): `blake3Mac` is `opaque`, so the bound is not provable in Lean — but it is
exactly what a 32-byte BLAKE3 tag satisfies (`B = 2^256`). CONDITIONAL on that faithful-model bound,
the carrier `share_mac_detects_tamper` conditions on is unsatisfiable. -/
theorem blake3Prf_false_of_bounded (key B : Nat) (hb : ∀ s i, blake3Mac key s i < B) :
    ¬ Blake3Prf :=
  blake3Prf_eq_shape ▸ macPrfShape_false_of_bounded blake3Mac key B hb

/-! ## §2 — REDUCTION TWINS: the same conclusions, injectivity replaced by a concrete Break. -/

/-- Break event: a concrete BLAKE3 collision — two distinct byte lists, one digest. The BLAKE3
analogue of `SpongeCollision` (which is pinned to `List ℤ → ℤ`). -/
def Blake3Collision {Digest : Type u} (hash : List Nat → Digest) : Prop :=
  ∃ x y : List Nat, x ≠ y ∧ hash x = hash y

/-- Break event: a concrete keyed-MAC collision — one key, two distinct `(share, idx)` messages,
one tag. -/
def MacCollision (mac : Nat → Nat → Nat → Nat) : Prop :=
  ∃ (key : Nat) (p q : Nat × Nat), p ≠ q ∧ mac key p.1 p.2 = mac key q.1 q.2

/-- **The BLAKE3 dichotomy leaf** (mirror of `spongeN_orBreak`): equal digests give equal preimages,
OR the two preimages ARE a concrete collision. Valid at the real hash — no injectivity assumed. -/
theorem blake3_orBreak {Digest : Type u} (hash : List Nat → Digest) {x y : List Nat}
    (heq : hash x = hash y) : OrBreak (Blake3Collision hash) (x = y) := by
  by_cases h : x = y
  · exact OrBreak.ok h
  · exact OrBreak.broke ⟨x, y, h, heq⟩

/-- **The keyed-MAC dichotomy leaf** (mirror of `compress_orBreak`): equal tags under one key give
equal messages, OR the two messages are a concrete `MacCollision`. -/
theorem mac_orBreak (mac : Nat → Nat → Nat → Nat) {key s₁ i₁ s₂ i₂ : Nat}
    (heq : mac key s₁ i₁ = mac key s₂ i₂) :
    OrBreak (MacCollision mac) (s₁ = s₂ ∧ i₁ = i₂) := by
  by_cases h : (s₁, i₁) = (s₂, i₂)
  · exact OrBreak.ok ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · exact OrBreak.broke ⟨key, (s₁, i₁), (s₂, i₂), h, heq⟩

/-- **The committed-opening twin — `blake3_floor_cr`, de-vacuated.** A transcript opened against a
BLAKE3 commitment BINDS (the opened bytes are the committed bytes), or the opening exhibits a
concrete BLAKE3 collision. Same conclusion as `blake3_floor_cr`; the unsatisfiable `collisionHard`
hypothesis is gone. -/
theorem blake3_commit_opens_orBreak {Digest : Type u} (hash : List Nat → Digest)
    {commitment : Digest} {xCommitted xOpened : List Nat}
    (hCommitted : hash xCommitted = commitment) (hOpened : hash xOpened = commitment) :
    OrBreak (Blake3Collision hash) (xOpened = xCommitted) :=
  blake3_orBreak hash (hOpened.trans hCommitted.symm)

/-- Recovery: with no BLAKE3 collision the injective original (`Blake3Kernel.noCollision`'s
conclusion) is recovered verbatim — nothing downstream is lost. -/
theorem blake3_binds_of_no_collision {Digest : Type u} (hash : List Nat → Digest)
    (hNo : ¬ Blake3Collision hash) {x y : List Nat} (heq : hash x = hash y) : x = y :=
  OrBreak.resolve hNo (blake3_orBreak hash heq)

/-- The carrier shape and the no-break side are the SAME proposition — the twin's break event is
exactly the negation of the old carrier's content, no slack in either direction. -/
theorem blake3NoCollision_iff_no_break {Digest : Type u} (hash : List Nat → Digest) :
    Blake3NoCollision hash ↔ ¬ Blake3Collision hash := by
  constructor
  · rintro hinj ⟨x, y, hne, heq⟩
    exact hne (hinj x y heq)
  · exact fun hNo _ _ heq => blake3_binds_of_no_collision hash hNo heq

/-- **Collisions EXIST at any finite digest** — §1 and §2 close the loop: since the no-break side
is exactly the falsified carrier, the Break side is a THEOREM for the real (finite-digest) hash.
The twin's break branch is not decorative. -/
theorem blake3Collision_of_finite_digest {Digest : Type u} [Finite Digest]
    (hash : List Nat → Digest) : Blake3Collision hash := by
  by_contra hNo
  exact blake3_noCollision_false_of_finite_digest hash
    ((blake3NoCollision_iff_no_break hash).mpr hNo)

/-- **The share-MAC twin — `share_mac_detects_tamper`, de-vacuated, over the REAL `blake3Mac`.**
A presented share passing MAC verification at a held index equals the dealer's honest share, OR the
pass equality exhibits a concrete `blake3Mac` collision. Same conclusion as the original
(`ThresholdDecrypt.lean:295`); the `Blake3Prf` hypothesis (false at any range-bounded mac, §1)
is gone. -/
theorem share_mac_detects_tamper_orBreak (key sHonest sBad idx : Nat)
    (hpass : blake3Mac key sBad idx = blake3Mac key sHonest idx) :
    OrBreak (MacCollision blake3Mac) (sBad = sHonest) :=
  OrBreak.imp And.left (mac_orBreak blake3Mac hpass)

/-- Recovery: with no `blake3Mac` collision, tamper detection is recovered verbatim. -/
theorem share_mac_detects_tamper_of_no_collision (hNo : ¬ MacCollision blake3Mac)
    (key sHonest sBad idx : Nat)
    (hpass : blake3Mac key sBad idx = blake3Mac key sHonest idx) : sBad = sHonest :=
  OrBreak.resolve hNo (share_mac_detects_tamper_orBreak key sHonest sBad idx hpass)

/-- The twin is a STRICT WEAKENING of the old carrier: `Blake3Prf` implies the no-break side, so
every `Blake3Prf` consumer factors through the twin + recovery. (The converse direction is where
the old carrier over-claimed.) -/
theorem blake3Prf_implies_no_macCollision (hprf : Blake3Prf) : ¬ MacCollision blake3Mac := by
  rintro ⟨key, ⟨s₁, i₁⟩, ⟨s₂, i₂⟩, hne, heq⟩
  obtain ⟨h1, h2⟩ := hprf key s₁ i₁ s₂ i₂ heq
  exact hne (by simp [h1, h2])

/-- **Apex break** for a flow using BOTH BLAKE3 roles — the transcript hash and the share MAC. Per
the `CollisionReduce` discipline: one coarse event the per-hash leaves `weaken` into. -/
def Blake3Break {Digest : Type u} (hash : List Nat → Digest)
    (mac : Nat → Nat → Nat → Nat) : Prop :=
  Blake3Collision hash ∨ MacCollision mac

/-- **Composition at the apex**: a transcript opening AND a share-MAC pass both bind, or the apex
`Blake3Break` holds — the two leaves `weaken`ed into one break and zipped with `OrBreak.map₂`.
This is the shape a threshold-decrypt session actually consumes: transcript pinned AND share
untampered, unless a concrete BLAKE3 collision (in either role) is in hand. -/
theorem transcript_and_share_bind_orBreak {Digest : Type u} (hash : List Nat → Digest)
    (mac : Nat → Nat → Nat → Nat) {commitment : Digest} {xCommitted xOpened : List Nat}
    {key sHonest sBad idx : Nat}
    (hCommitted : hash xCommitted = commitment) (hOpened : hash xOpened = commitment)
    (hpass : mac key sBad idx = mac key sHonest idx) :
    OrBreak (Blake3Break hash mac) (xOpened = xCommitted ∧ sBad = sHonest) :=
  OrBreak.map₂ And.intro
    (OrBreak.weaken Or.inl (blake3_commit_opens_orBreak hash hCommitted hOpened))
    (OrBreak.weaken Or.inr (OrBreak.imp And.left (mac_orBreak mac hpass)))

/-! ## §3 — FIRE: both branches of the dichotomy exercised on closed terms. -/

/-- A colliding toy mac — the constant tag. Every distinct message pair collides at every key. -/
def collidingMac : Nat → Nat → Nat → Nat := fun _ _ _ => 0

/-- **FIRE (break branch)** — fed a concrete pass equality between DIFFERENT shares (`0` vs `1`) at
one index, the twin cannot take the good branch, so it DELIVERS the concrete `MacCollision`. The
break branch is reachable and productive on a closed instance. -/
theorem collidingMac_twin_forces_break : MacCollision collidingMac := by
  have h := mac_orBreak collidingMac (key := 0) (s₁ := 0) (i₁ := 0) (s₂ := 1) (i₂ := 0) rfl
  rcases h with ⟨hs, _⟩ | hb
  · exact absurd hs (by decide)
  · exact hb

/-- **FIRE (§1 on the toy)** — the colliding mac is range-bounded (`< 1`), so the pigeonhole tooth
refutes its PRF shape outright, matching the collision the twin just delivered. -/
theorem collidingMac_prfShape_false : ¬ MacPrfShape collidingMac :=
  macPrfShape_false_of_bounded collidingMac 0 1 (fun _ _ => Nat.one_pos)

/-- A colliding toy transcript hash into the FINITE digest `Bool` — parity of the byte sum. -/
def toyHash2 : List Nat → Bool := fun xs => decide (xs.sum % 2 = 0)

/-- **FIRE (break branch, transcript role)** — a concrete equivocating opening against the
commitment `true` (`[0]` committed, `[2]` opened; distinct lists, equal digests): the twin is forced
into the Break branch and delivers the concrete `Blake3Collision`. -/
theorem toyHash2_commit_twin_forces_break : Blake3Collision toyHash2 := by
  have h := blake3_commit_opens_orBreak toyHash2 (commitment := true)
      (xCommitted := ([0] : List Nat)) (xOpened := ([2] : List Nat)) (by decide) (by decide)
  rcases h with heq | hb
  · exact absurd heq (by decide)
  · exact hb

/-- A toy `Blake3Kernel` instance over the finite digest `Bool`, with `collisionHard` set to
exactly what `noCollision` unpacks it to — the strongest honest choice for the shape. -/
@[reducible] def toyKernel : Blake3Kernel Bool where
  hash := toyHash2
  collisionHard := Blake3NoCollision toyHash2
  noCollision := fun h => h

/-- **FIRE (§1 at the class)** — the toy kernel's `collisionHard` carrier is UNSATISFIABLE, by the
kernel-level tooth alone (`Finite Bool`). Any `blake3_floor_cr` consumer over `toyKernel` is
vacuous — the concrete demonstration of the disease. -/
theorem toyKernel_collisionHard_false : ¬ toyKernel.collisionHard :=
  blake3Kernel_collisionHard_false toyKernel

/-- An injective toy hash — identity on byte lists (an "infinite digest": injectivity is actually
satisfiable here, which is exactly what a REAL digest space is not). -/
def injToyHash : List Nat → List Nat := id

/-- The injective toy genuinely has NO collision — the no-break side is satisfiable, so the twins
are not vacuously always-broken. -/
theorem injToyHash_no_collision : ¬ Blake3Collision injToyHash := by
  rintro ⟨x, y, hne, heq⟩
  exact hne heq

/-- **FIRE (good branch)** — on the injective toy, `resolve` recovers binding verbatim from the
twin: the good branch is reachable and delivers the original injective conclusion. -/
theorem injToyHash_twin_resolves {x y : List Nat} (heq : injToyHash x = injToyHash y) : x = y :=
  OrBreak.resolve injToyHash_no_collision (blake3_orBreak injToyHash heq)

/-- **FIRE (good branch, closed instance)** — the committed-opening twin composed end-to-end on a
concrete non-equivocating opening, resolved through `¬ Blake3Collision injToyHash`. -/
theorem injToyHash_opening_binds :
    ([3, 1, 4] : List Nat) = [3, 1, 4] :=
  OrBreak.resolve injToyHash_no_collision
    (blake3_commit_opens_orBreak injToyHash
      (commitment := ([3, 1, 4] : List Nat)) (xCommitted := [3, 1, 4]) (xOpened := [3, 1, 4])
      rfl rfl)

/-! ## §4 — axiom-hygiene tripwires. -/

#assert_axioms blake3_noCollision_false_of_finite_range
#assert_axioms blake3_noCollision_false_of_finite_digest
#assert_axioms blake3_noCollision_false_bounded
#assert_axioms blake3Kernel_collisionHard_false
#assert_axioms blake3Prf_eq_shape
#assert_axioms macPrfShape_false_of_bounded
#assert_axioms blake3Prf_false_of_bounded
#assert_axioms blake3_orBreak
#assert_axioms mac_orBreak
#assert_axioms blake3_commit_opens_orBreak
#assert_axioms blake3_binds_of_no_collision
#assert_axioms blake3NoCollision_iff_no_break
#assert_axioms blake3Collision_of_finite_digest
#assert_axioms share_mac_detects_tamper_orBreak
#assert_axioms share_mac_detects_tamper_of_no_collision
#assert_axioms blake3Prf_implies_no_macCollision
#assert_axioms transcript_and_share_bind_orBreak
#assert_axioms collidingMac_twin_forces_break
#assert_axioms collidingMac_prfShape_false
#assert_axioms toyHash2_commit_twin_forces_break
#assert_axioms toyKernel_collisionHard_false
#assert_axioms injToyHash_no_collision
#assert_axioms injToyHash_twin_resolves
#assert_axioms injToyHash_opening_binds

end Dregg2.Circuit.Blake3FloorReduce
