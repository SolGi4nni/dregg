/-
# `Dregg2.Circuit.MapOpWideDigest8` — the wide-key map root MIGRATED OFF the one-felt digest, and
the birthday bar re-derived at the codomain it actually lands in.

## What this file is for, stated as the correction it makes

`MapOpWideKeyGate` ported the whole wide-key family off the refuted `Poseidon2SpongeCR` floor onto
per-instance non-collision residuals, and in doing so made the honest number VISIBLE for the first
time. The number is bad. `leafOfW hash E : K × ℤ → ℤ` and `mapRootW hash E d : List (K × ℤ) → ℤ`
return **ONE BabyBear felt at every key width**, so `Crypto.RomQueryFloor.birthday_bound`'s
`(Q² + 1)/‖R‖` reads `‖R‖ = babyBearP ≈ 2^30.9` and the bar is **≈ 2^15.5 queries — a break, not a
bound** — at `wideEnc` exactly as at `narrowEnc`.

⚑ **The kind-D epoch widened the ABSORBED PREIMAGE (map leaf arity 2 → 9, IMT leaf 3 → 17) and NOT
the DIGEST, and that buys ZERO bits.** `romBar` (§1) is a function of `Q` and the CODOMAIN
cardinality only; the domain does not occur in it. Every theorem in §1 is stated over an ARBITRARY
finite domain for exactly that reason — the arity-9 absorb and the arity-2 absorb are the same
instance of the same bound.

**The number that moves is `‖R‖`.** This file moves it: `leafOfW8` / `mapRootW8` are the SAME
objects with the SAME absorbed preimages, squeezed into `Digest8` (`Fin 8 → ℤ`) instead of one felt,
riding the `Heap8Scheme.chipAbsorb8` chip and `MapMerkleRoot` §5b's `perfectRoot8` fold. The bar
goes from `2^15.5` to `2^123.63`, and §1 proves BOTH endpoints and the exact break points rather
than asserting them in a docstring — the failure mode `docs/INJECTIVITY-FLOOR-CLASS.md` §7 names
(the wound that was documented in prose and therefore undetected).

## Substrate — say it out loud

**This is a MODEL module, not an AIR.** Nothing here authors a constraint, a gadget, or an
`air_accepts` predicate, in Lean or anywhere else: it defines a digest fold and proves binding
facts about it. The AIR/emit consequences of the widening are PRICED in §5 as arithmetic on
deployed constants and are a Rust re-emit (a VK epoch), not a claim made here.

## What is NOT closed here — read this before citing

  * **Nothing deployed is touched.** No descriptor is registered, no emit path changed, no byte
    moved. `MapOpWideKeyGate`'s ℤ-valued family is left STANDING and is still what the deployed
    narrow objects are `rfl`-equal to; this file is the wide-codomain sibling, and §6 states the
    remaining migration explicitly rather than implying it happened.
  * **The ROM idealisation is a modelling step, and it is the same one
    `Crypto.RomCarrierSites`' header labels.** §1's bars are theorems about a uniformly sampled
    `H : D → R`. They are NOT statements about the fixed deployed Poseidon2 chip; collision
    resistance of a fixed public function is a conjecture, not a Lean theorem. What §1 buys is that
    the *width* now has a price attached, so a widening can be shown to buy something.
  * **`Heap8Scheme` carries no floor**, by construction (its `chip8CR` field was deleted 07-20), so
    every binding below is a DISJUNCTION `binding ∨ Coll8 chipAbsorb8 (the pair a TOTAL extractor
    returned)`. No global `∀ p q, ¬ Coll` side condition appears anywhere — that shape is
    pigeonhole-refuted exactly like the injectivity it would replace.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `native_decide`.
-/
import Dregg2.Circuit.MapOpWideKeyGate
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Dregg2.Circuit.MapOpWideDigest8

open Dregg2.Substrate
open Dregg2.Circuit.MapOpWideKeyGate (LaneEnc leafPreW leafPreW_inj
  mapLeafWFind mapLeafWFind_self)
open Dregg2.Circuit.DeployedCapTree (Digest8 Coll8 Compress8CR)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8 coll8_refutable_of_injective)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.MapMerkleRoot (perfectRoot8 perfectRoot8Find
  perfectRoot8_binds_or_collides HEAP_TREE_DEPTH)
open Dregg2.Crypto.RomCarrierSites (babyBearP babyBearP_pos)
open Dregg2.Crypto.RomQueryFloor (collWin birthday_bound)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.ProbCrypto (winProb)

set_option autoImplicit false

/-! ## §1 — THE PRICE OF A CODOMAIN, as theorems.

`RomQueryFloor.birthday_bound` is width-agnostic — it has no width hypothesis — so instantiating it
is an arithmetic choice, not new mathematics. What was missing is that nobody had instantiated it at
the two widths the tree actually deploys, so the numbers `2^15.5` and `2^123.5` lived only in
docstrings. Here they are objects. -/

/-- **`romBar Q N`** — the bound `birthday_bound` delivers at a digest space of cardinality `N`
against a `Q`-query adversary. ⚑ **The DOMAIN does not occur.** That is the whole content of "widen
the digest, not the preimage": `romBar` cannot tell an arity-2 absorb from an arity-9 one. -/
noncomputable def romBar (Q N : ℕ) : ℝ := ((Q : ℝ) * (Q : ℝ) + 1) / (N : ℝ)

/-- **`NarrowDigest`** — the DEPLOYED-SHAPED one-felt digest space. This is the codomain of
`leafOfW`, `mapRootW`, `imtLeafHash8` and `mapNode` at every key width.

⚑ The MODEL types are `ℤ` and `Digest8 = Fin 8 → ℤ`, both INFINITE. `NarrowDigest` / `WideDigest8`
are their deployed-shaped finite restrictions — every lane a BabyBear element, which is what the
Rust chip actually emits (`DeployedCapTree.deployedShapedChip8`). §1's counting is therefore about
the DEPLOYED SHAPE, not about the model's carrier type; saying otherwise would be the conflation
this campaign exists to catch. Bounding the lanes is also what makes `Compress8CR` refutable at
all (`VacuitySweepTeeth.compress8CR_false_babyBear`), so this is the same restriction the teeth
already use. -/
abbrev NarrowDigest : Type := Fin babyBearP

/-- **`WideDigest8`** — the deployed-shaped EIGHT-felt digest space. See `NarrowDigest` for the
model-vs-deployed caveat that applies equally here. -/
abbrev WideDigest8 : Type := Fin 8 → Fin babyBearP

instance : NeZero babyBearP := ⟨by norm_num [babyBearP]⟩

theorem card_narrowDigest : Fintype.card NarrowDigest = babyBearP := Fintype.card_fin _

theorem card_wideDigest8 : Fintype.card WideDigest8 = babyBearP ^ 8 := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **THE ONE-FELT BAR.** A `Q`-query adversary against a random oracle whose range is a single
BabyBear felt collides with probability at most `romBar Q babyBearP`.

⚑ Stated over an **arbitrary finite domain `D`** — deliberately. The wide-key epoch's arity-9 leaf
absorb and the deployed arity-2 one are two instances of this one theorem with the same conclusion,
which is the kind-D error in its exact form. -/
theorem narrow_birthday_bar {D : Type} [Fintype D] [DecidableEq D]
    (Q : ℕ) (M : OracleComp D NarrowDigest (D × D)) (hM : QueryBounded Q M) :
    winProb (collWin M) ≤ romBar Q babyBearP := by
  have h := birthday_bound (D := D) (R := NarrowDigest) Q M hM
  rwa [card_narrowDigest] at h

/-- **THE EIGHT-FELT BAR.** The identical theorem at the `Digest8` codomain — the ONLY change is
`‖R‖`, and the whole security delta of this file lives in that change. -/
theorem wide8_birthday_bar {D : Type} [Fintype D] [DecidableEq D]
    (Q : ℕ) (M : OracleComp D WideDigest8 (D × D)) (hM : QueryBounded Q M) :
    winProb (collWin M) ≤ romBar Q (babyBearP ^ 8) := by
  have h := birthday_bound (D := D) (R := WideDigest8) Q M hM
  rwa [card_wideDigest8] at h

/-! ### §1a — the two bars READ, at the numbers. -/

theorem cast_babyBearP_pos : (0 : ℝ) < (babyBearP : ℝ) := by exact_mod_cast babyBearP_pos

theorem cast_babyBearP_pow8_pos : (0 : ℝ) < ((babyBearP ^ 8 : ℕ) : ℝ) := by
  have : 0 < babyBearP ^ 8 := pow_pos babyBearP_pos 8
  exact_mod_cast this

/-- A bar below `1` is the only kind that says anything: `winProb ≤ 1` holds for free. -/
theorem romBar_lt_one_iff {Q N : ℕ} (hN : 0 < N) : romBar Q N < 1 ↔ Q * Q + 1 < N := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [romBar, div_lt_one hNR]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- **⚑ THE ONE-FELT BAR IS VACUOUS AT 2^16 QUERIES.** `(2^16)² + 1 > babyBearP`, so the bound is
`> 1` and states nothing a probability does not state for free. This is the "break, not a bound". -/
theorem narrow_bar_vacuous_at_2pow16 : (1 : ℝ) ≤ romBar (2 ^ 16) babyBearP := by
  rw [romBar, le_div_iff₀ cast_babyBearP_pos, one_mul]
  have h : babyBearP ≤ 2 ^ 16 * 2 ^ 16 + 1 := by norm_num [babyBearP]
  exact_mod_cast h

/-- **THE EXACT ONE-FELT BREAK POINT.** `44870² + 1 ≥ babyBearP` while `44869² + 1 < babyBearP`, so
the bar dies at `Q = 44870 ≈ 2^15.45`. The docstring number `≈ 2^15.5` is this integer. -/
theorem narrow_break_exactly_at_44870 :
    romBar 44869 babyBearP < 1 ∧ (1 : ℝ) ≤ romBar 44870 babyBearP := by
  refine ⟨(romBar_lt_one_iff babyBearP_pos).mpr (by norm_num [babyBearP]), ?_⟩
  rw [romBar, le_div_iff₀ cast_babyBearP_pos, one_mul]
  have h : babyBearP ≤ 44870 * 44870 + 1 := by norm_num [babyBearP]
  exact_mod_cast h

/-- **AND THE ONE-FELT BAR AT A REAL ATTACKER BUDGET SAYS NOTHING AT ALL.** At `Q = 2^64` the bound
is above `1` by a factor of about `2^97`. -/
theorem narrow_bar_says_nothing_at_2pow64 : (1 : ℝ) ≤ romBar (2 ^ 64) babyBearP := by
  rw [romBar, le_div_iff₀ cast_babyBearP_pos, one_mul]
  have h : babyBearP ≤ 2 ^ 64 * 2 ^ 64 + 1 := by norm_num [babyBearP]
  exact_mod_cast h

/-- **⚑ THE EIGHT-FELT BAR AT THE SAME REAL BUDGET.** At `Q = 2^64` the `Digest8` bound is below
`2^-119` — the difference between "no statement" and "a statement no adversary can approach". -/
theorem wide8_bar_at_2pow64 : romBar (2 ^ 64) (babyBearP ^ 8) ≤ 1 / (2 : ℝ) ^ 119 := by
  rw [romBar, div_le_div_iff₀ cast_babyBearP_pow8_pos (by positivity)]
  have h : (2 ^ 64 * 2 ^ 64 + 1) * 2 ^ 119 ≤ babyBearP ^ 8 * 1 := by norm_num [babyBearP]
  exact_mod_cast h

/-- **THE EXACT EIGHT-FELT BREAK POINT, AND IT IS AN INTEGER.** `‖R‖ = babyBearP^8` is a perfect
square, so the birthday threshold is exactly `babyBearP^4 = 16428751811598850197311699254593454081
≈ 2^123.63`: at `babyBearP^4 - 1` queries the bar still binds, at `babyBearP^4` it does not. The
docstring number `≈ 2^123.5` is this integer. -/
theorem wide8_bar_binds_below_p4 {Q : ℕ} (hQ : Q < babyBearP ^ 4) :
    romBar Q (babyBearP ^ 8) < 1 := by
  have hp8 : 0 < babyBearP ^ 8 := pow_pos babyBearP_pos 8
  refine (romBar_lt_one_iff hp8).mpr ?_
  have hQ' : Q + 1 ≤ babyBearP ^ 4 := hQ
  have hn2 : 2 ≤ babyBearP ^ 4 := by norm_num [babyBearP]
  have hpow : babyBearP ^ 4 * babyBearP ^ 4 = babyBearP ^ 8 := by ring
  rcases Nat.eq_zero_or_pos Q with hz | hpos
  · subst hz
    have : 2 * 2 ≤ babyBearP ^ 4 * babyBearP ^ 4 := Nat.mul_le_mul hn2 hn2
    omega
  · have hstep : Q * Q + 1 < (Q + 1) * (Q + 1) := by nlinarith [hpos]
    have hmono : (Q + 1) * (Q + 1) ≤ babyBearP ^ 4 * babyBearP ^ 4 := Nat.mul_le_mul hQ' hQ'
    omega

theorem wide8_bar_dies_at_p4 : (1 : ℝ) ≤ romBar (babyBearP ^ 4) (babyBearP ^ 8) := by
  rw [romBar, le_div_iff₀ cast_babyBearP_pow8_pos, one_mul]
  have hpow : babyBearP ^ 4 * babyBearP ^ 4 = babyBearP ^ 8 := by ring
  have h : babyBearP ^ 8 ≤ babyBearP ^ 4 * babyBearP ^ 4 + 1 := by rw [hpow]; exact Nat.le_succ _
  exact_mod_cast h

/-- The break point, as ONE statement: the bar binds at every budget strictly below `babyBearP^4`
and is dead at `babyBearP^4`. -/
theorem wide8_break_exactly_at_p4 :
    romBar (babyBearP ^ 4 - 1) (babyBearP ^ 8) < 1
      ∧ (1 : ℝ) ≤ romBar (babyBearP ^ 4) (babyBearP ^ 8) := by
  refine ⟨wide8_bar_binds_below_p4 ?_, wide8_bar_dies_at_p4⟩
  have hn2 : 2 ≤ babyBearP ^ 4 := by norm_num [babyBearP]
  omega

/-- **THE MIGRATION'S PAYOFF, AS ONE IDENTITY.** At EVERY query budget the eight-felt bar is
`babyBearP^7 ≈ 2^216` times smaller than the one-felt bar. Nothing about the preimage enters: the
factor is exactly the ratio of the two codomains. -/
theorem wide8_bar_ratio (Q : ℕ) :
    romBar Q (babyBearP ^ 8) * ((babyBearP : ℝ) ^ 7) = romBar Q babyBearP := by
  have hp : (babyBearP : ℝ) ≠ 0 := ne_of_gt cast_babyBearP_pos
  rw [romBar, romBar]
  push_cast
  field_simp

/-- **THE BAR IS ANTITONE IN THE CODOMAIN — and that is the ONLY lever.** Widening `‖R‖` is the one
move that lowers the bound; the domain never appears. -/
theorem romBar_antitone_in_codomain (Q : ℕ) {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) :
    romBar Q M ≤ romBar Q N := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast lt_of_lt_of_le hN hNM
  have hle : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  rw [romBar, romBar]
  exact div_le_div_of_nonneg_left (by positivity) hNR hle

section Generic

variable {K : Type} [LinearOrder K]

/-! ## §2 — THE MIGRATED LEAF: the same absorbed preimage, an eight-felt image.

`leafOfW8` is `leafOfW` with `hash : List ℤ → ℤ` replaced by `S8.chipAbsorb8 : List ℤ → Digest8`.
The preimage is BYTE-IDENTICAL (`leafPreW E e`, arity `E.width + 1` — 2 narrow, 9 wide), which is
the point: this migration does not touch what is absorbed, only where it lands. -/

/-- **`leafOfW8 S8 E e`** — the map-tree leaf digest at the deployed 8-output chip:
`chipAbsorb8 [key-lanes ‖ value]`. Definitionally `S8.chipAbsorb8 (leafPreW E e)`. -/
def leafOfW8 (S8 : Heap8Scheme) (E : LaneEnc K) (e : K × ℤ) : Digest8 :=
  S8.chipAbsorb8 (leafPreW E e)

/-- The absorbed preimage is UNCHANGED by the migration — the same list, at the same arity. Stated
as a theorem because it is the claim that would be false if this were another preimage widening. -/
theorem leafOfW8_absorbs_leafPreW (S8 : Heap8Scheme) (E : LaneEnc K) (e : K × ℤ) :
    leafOfW8 S8 E e = S8.chipAbsorb8 (leafPreW E e) := rfl

/-- **THE HYPOTHESIS-FREE WIDE-DIGEST LEAF BINDING.** Equal 8-felt leaf digests force equal entries
OR name a genuine collision of the deployed chip at the two absorbed `E.width + 1`-felt preimages.
Same proof as `MapOpWideKeyGate.leafOfW_binds_or_collides` — `leafPreW_inj` is pure layout
combinatorics and carries no crypto — and now priced at `romBar Q (babyBearP^8)`. -/
theorem leafOfW8_binds_or_collides (S8 : Heap8Scheme) (E : LaneEnc K) {e₁ e₂ : K × ℤ}
    (h : leafOfW8 S8 E e₁ = leafOfW8 S8 E e₂) :
    e₁ = e₂ ∨ Coll8 S8.chipAbsorb8 (leafPreW E e₁, leafPreW E e₂) := by
  by_cases hpre : leafPreW E e₁ = leafPreW E e₂
  · exact Or.inl (leafPreW_inj E hpre)
  · exact Or.inr ⟨hpre, h⟩

/-- **★ THE WIDENED LEAF BINDS THE WHOLE KEY AND THE VALUE, AT AN 8-FELT DIGEST.** The endpoint
`MapOpWideKeyGate.leafOfW_injective` migrated. Statement shape identical; the residual is now a
collision of a map into `Digest8` rather than into one felt, so the query cost of exhibiting it
moves from `≈ 2^15.45` (`narrow_break_exactly_at_44870`) to `≈ 2^123.63`
(`wide8_break_exactly_at_p4`). -/
theorem leafOfW8_injective (S8 : Heap8Scheme) (E : LaneEnc K) {e₁ e₂ : K × ℤ}
    (hno : ¬ Coll8 S8.chipAbsorb8 (leafPreW E e₁, leafPreW E e₂))
    (h : leafOfW8 S8 E e₁ = leafOfW8 S8 E e₂) : e₁ = e₂ :=
  (leafOfW8_binds_or_collides S8 E h).resolve_right hno

/-- **THE LEAF-VECTOR BINDING.** The extractor is REUSED verbatim: `mapLeafWFind` scans the two
heaps' absorbed preimages and is hash-independent, so it serves both widths unchanged. -/
theorem map_leafOfW8_binds_or_collides (S8 : Heap8Scheme) (E : LaneEnc K) :
    ∀ h₁ h₂ : List (K × ℤ),
      h₁.map (leafOfW8 S8 E) = h₂.map (leafOfW8 S8 E) →
      h₁ = h₂ ∨ Coll8 S8.chipAbsorb8 (mapLeafWFind E h₁ h₂) := by
  intro h₁
  induction h₁ with
  | nil =>
    intro h₂ h
    cases h₂ with
    | nil => exact Or.inl rfl
    | cons b s => simp at h
  | cons a t ih =>
    intro h₂ h
    cases h₂ with
    | nil => simp at h
    | cons b s =>
      simp only [List.map_cons, List.cons.injEq] at h
      by_cases hpre : leafPreW E a = leafPreW E b
      · rcases ih s h.2 with hts | hc
        · exact Or.inl (by rw [leafPreW_inj E hpre, hts])
        · refine Or.inr ?_
          show Coll8 S8.chipAbsorb8 (mapLeafWFind E (a :: t) (b :: s))
          rw [mapLeafWFind, if_pos hpre]
          exact hc
      · refine Or.inr ?_
        show Coll8 S8.chipAbsorb8 (mapLeafWFind E (a :: t) (b :: s))
        rw [mapLeafWFind, if_neg hpre]
        exact ⟨hpre, h.1⟩

/-! ## §3 — THE MIGRATED ROOT: `perfectRoot8` in place of `perfectRoot`.

`mapRootW` folded the leaf digests with `perfectRoot hash` — a 1-felt `mapNode hash l r = hash [l,r]`
per level, so even a `Digest8` leaf would have been crushed back to one felt at the first node.
`mapRootW8` folds with `MapMerkleRoot` §5b's `perfectRoot8`, whose node is the arity-16
`heapNodeOf8 = chipAbsorb8 (pack8 l r)` and whose image is `Digest8` all the way to the root. The
§5b machinery is REUSED, not re-authored: `perfectRoot8_binds_or_collides` already exists and is
hypothesis-free. -/

/-- **`mapRootW8 S8 E d h`** — the depth-`d` binary-Merkle root of a heap whose leaves absorb the key
at `E`'s width, at the DEPLOYED 8-felt chip end to end: 8-felt leaves, arity-16 nodes, `Digest8`
root. -/
def mapRootW8 (S8 : Heap8Scheme) (E : LaneEnc K) (d : Nat) (h : List (K × ℤ)) : Digest8 :=
  perfectRoot8 S8 d (h.map (leafOfW8 S8 E))

/-- **`mapRootW8Find`** — the ROOT extractor, the exact twin of `MapOpWideKeyGate.mapRootWFind`:
resolve the equivocation at the level it actually happens. If the two heaps already agree on their
leaf-digest VECTORS the collision is at a LEAF (`mapLeafWFind`); otherwise it is in the node fold
(`perfectRoot8Find`). Total, decidable, and independent of any hypothesis on the chip. -/
def mapRootW8Find (S8 : Heap8Scheme) (E : LaneEnc K) (d : Nat)
    (h₁ h₂ : List (K × ℤ)) : List ℤ × List ℤ :=
  if h₁.map (leafOfW8 S8 E) = h₂.map (leafOfW8 S8 E) then mapLeafWFind E h₁ h₂
  else perfectRoot8Find S8 d (h₁.map (leafOfW8 S8 E)) (h₂.map (leafOfW8 S8 E))

/-- **`MapRootCollW8 S8 E d h₁ h₂`** — the pair `mapRootW8Find` RETURNS on this heap equivocation is
a genuine collision of the deployed arity-16 chip.

Deliberately NOT `∃ a b, chipAbsorb8 a = chipAbsorb8 b ∧ a ≠ b`: at deployed parameters that
existence claim is unconditionally true by pigeonhole
(`VacuitySweepTeeth.compress8CR_false_babyBear`), so a disjunct of that shape carries no more content
than `True`. And deliberately NOT a global `∀ p q, ¬ Coll8` side condition, refuted for the same
reason. This one is about the SPECIFIC pair a total extractor hands back — DISCHARGEABLE (§3a),
REFUTABLE (§3a), and PRICED (§1) at `romBar Q (babyBearP ^ 8)`. -/
def MapRootCollW8 (S8 : Heap8Scheme) (E : LaneEnc K) (d : Nat)
    (h₁ h₂ : List (K × ℤ)) : Prop :=
  Coll8 S8.chipAbsorb8 (mapRootW8Find S8 E d h₁ h₂)

/-- **★ THE WIDENED ROOT BINDS THE WHOLE HEAP AT AN 8-FELT DIGEST, FLOOR-FREE.** Two `2^d`-leaf
heaps publishing the SAME `Digest8` root are EITHER the same heap, OR the deployed chip genuinely
collides at the named pair. No hypothesis on the chip. -/
theorem mapRootW8_binds_or_collides (S8 : Heap8Scheme) (E : LaneEnc K) (d : Nat)
    {h₁ h₂ : List (K × ℤ)} (hlen₁ : h₁.length = 2 ^ d) (hlen₂ : h₂.length = 2 ^ d)
    (h : mapRootW8 S8 E d h₁ = mapRootW8 S8 E d h₂) :
    h₁ = h₂ ∨ MapRootCollW8 S8 E d h₁ h₂ := by
  by_cases hEq : h₁.map (leafOfW8 S8 E) = h₂.map (leafOfW8 S8 E)
  · rcases map_leafOfW8_binds_or_collides S8 E h₁ h₂ hEq with hh | hc
    · exact Or.inl hh
    · refine Or.inr ?_
      show Coll8 S8.chipAbsorb8 (mapRootW8Find S8 E d h₁ h₂)
      rw [mapRootW8Find, if_pos hEq]
      exact hc
  · rcases perfectRoot8_binds_or_collides S8 d (by rw [List.length_map, hlen₁])
      (by rw [List.length_map, hlen₂]) h with hmap | hc
    · exact absurd hmap hEq
    · refine Or.inr ?_
      show Coll8 S8.chipAbsorb8 (mapRootW8Find S8 E d h₁ h₂)
      rw [mapRootW8Find, if_neg hEq]
      exact hc

/-- **★★ THE MIGRATED ENDPOINT.** `MapOpWideKeyGate.mapRootW_injective` at an eight-felt digest.
Same hypotheses, same conclusion; the ONLY change is that the residual is a collision of a map into
`Digest8` rather than into one BabyBear felt, and therefore costs `≈ 2^123.63` queries to exhibit
instead of `≈ 2^15.45`. -/
theorem mapRootW8_injective (S8 : Heap8Scheme) (E : LaneEnc K) (d : Nat)
    {h₁ h₂ : List (K × ℤ)} (hno : ¬ MapRootCollW8 S8 E d h₁ h₂)
    (hlen₁ : h₁.length = 2 ^ d) (hlen₂ : h₂.length = 2 ^ d)
    (h : mapRootW8 S8 E d h₁ = mapRootW8 S8 E d h₂) : h₁ = h₂ :=
  (mapRootW8_binds_or_collides S8 E d hlen₁ hlen₂ h).resolve_right hno

/-! ### §3a — three poles for the eight-felt root residual.

A side condition that can never FIRE is `True` in disguise; one that can never be DISCHARGED is a
broken keystone rather than a repaired one; and one that does not REFUTE the premise it replaced is
a change of subject. All three, as for the ℤ half. -/

/-- **DISCHARGEABLE.** The honest prover, who commits ONE heap, pays nothing — for EVERY chip, with
no cryptographic assumption whatsoever. -/
theorem mapRootCollW8_dischargeable (S8 : Heap8Scheme) (E : LaneEnc K) (d : Nat)
    (h : List (K × ℤ)) : ¬ MapRootCollW8 S8 E d h h := by
  intro hc
  have hcc : Coll8 S8.chipAbsorb8 (mapRootW8Find S8 E d h h) := hc
  rw [show mapRootW8Find S8 E d h h = mapLeafWFind E h h by rw [mapRootW8Find, if_pos rfl],
    mapLeafWFind_self E h] at hcc
  exact hcc.1 rfl

/-- **A REFUTATION, NOT A NEW FLOOR (leaf side).** Exhibiting the leaf residual refutes
`Compress8CR` outright, so the port is a strict WEAKENING of the premise the 8-felt tree used to
carry in its deleted `chip8CR` field. Stated contrapositively, so it assumes no floor content. -/
theorem leafCollW8_refutes_compress8CR {S8 : Heap8Scheme} {E : LaneEnc K} {e₁ e₂ : K × ℤ}
    (hc : Coll8 S8.chipAbsorb8 (leafPreW E e₁, leafPreW E e₂)) :
    ¬ Compress8CR S8.chipAbsorb8 :=
  fun hCR => hc.1 (hCR _ _ hc.2)

/-- **A REFUTATION, NOT A NEW FLOOR (root side).** -/
theorem mapRootCollW8_refutes_compress8CR {S8 : Heap8Scheme} {E : LaneEnc K} {d : Nat}
    {h₁ h₂ : List (K × ℤ)} (hc : MapRootCollW8 S8 E d h₁ h₂) :
    ¬ Compress8CR S8.chipAbsorb8 :=
  fun hCR => hc.1 (hCR _ _ hc.2)

end Generic

/-! ### §3b — SATISFIABLE. The residual can FIRE, so the endpoint is not secretly unconditional.

A side condition proved dischargeable and never shown to hold would mean `mapRootW8_injective` binds
with no hypothesis at all — an over-claim, and the shape the whole floor campaign exists to catch.
Exhibited instead: a chip that really does equivocate, and the pair the extractor hands back.

⚑ Deliberately NOT stated as `Compress8CR → ¬ MapRootCollW8`. That form takes a REFUTED floor as a
hypothesis (`VacuitySweepTeeth.compress8CR_false_babyBear`) and would be a new baselined carrier for
no content: `mapRootCollW8_refutes_compress8CR` above is its contrapositive and assumes nothing. -/

/-- A chip that maps everything to the zero digest — deployed-shaped in type, maximally colliding in
behaviour. -/
def constChip8 : Heap8Scheme := ⟨fun _ => fun _ => 0⟩

/-- **SATISFIABLE.** Two DISTINCT one-leaf heaps publish the SAME eight-felt root under the constant
chip, and `mapRootW8Find` hands back exactly the colliding absorbed pair `([0,0], [1,0])`. So the
residual is inhabited: the binding really is conditional on the chip, as it must be. -/
theorem mapRootCollW8_fires_on_constant_chip :
    MapRootCollW8 constChip8 Dregg2.Circuit.MapOpWideKeyGate.narrowEnc 0 [(0, 0)] [(1, 0)] := by
  refine ⟨?_, rfl⟩
  decide

section Generic

variable {K : Type} [LinearOrder K]

/-! ## §4 — the OPENING layer at eight felts, so the migration reaches a consumer.

A root that binds and is never opened has moved no consumer. These are the widened
`opensToMerkleW` / `writesToMerkleW` with a `Digest8` commitment, and their anti-ghosts over
EXPLICIT witness heaps — the existential hides the heap, so the residual must name the witnesses. -/

/-- **`opensToMerkleW8 S8 E d r k o`** — some admissible `2^d`-leaf heap, keyed at `K` and committed
by the depth-`d` EIGHT-FELT binary root `r`, reads `o` at `k`. -/
def opensToMerkleW8 (S8 : Heap8Scheme) (E : LaneEnc K) (d : Nat) (r : Digest8) (k : K)
    (o : Option ℤ) : Prop :=
  ∃ h : List (K × ℤ), E.HeapOk h ∧ h.length = 2 ^ d ∧ mapRootW8 S8 E d h = r
    ∧ Heap.get h k = o

/-- **`writesToMerkleW8 S8 E d r k v r'`** — the sorted insert-or-update of `(k, v)` moves the
committed EIGHT-FELT root `r` to `r'`, at key width `E`. -/
def writesToMerkleW8 (S8 : Heap8Scheme) (E : LaneEnc K) (d : Nat) (r : Digest8) (k : K) (v : ℤ)
    (r' : Digest8) : Prop :=
  ∃ h : List (K × ℤ), E.HeapOk h ∧ h.length = 2 ^ d
    ∧ (Heap.set h k v).length = 2 ^ d
    ∧ mapRootW8 S8 E d h = r ∧ r' = mapRootW8 S8 E d (Heap.set h k v)

/-- **EIGHT-FELT OPENINGS ARE FUNCTIONAL, UNCONDITIONAL.** Two witness heaps behind the SAME 8-felt
root read the SAME value at a key — OR the deployed chip genuinely collides at the named pair. -/
theorem opensToMerkleW8_functional_or_collides (S8 : Heap8Scheme) (E : LaneEnc K) (d : Nat)
    {r : Digest8} {k : K} {o₁ o₂ : Option ℤ} {m₁ m₂ : List (K × ℤ)}
    (hl₁ : m₁.length = 2 ^ d) (hr₁ : mapRootW8 S8 E d m₁ = r) (hg₁ : Heap.get m₁ k = o₁)
    (hl₂ : m₂.length = 2 ^ d) (hr₂ : mapRootW8 S8 E d m₂ = r) (hg₂ : Heap.get m₂ k = o₂) :
    o₁ = o₂ ∨ MapRootCollW8 S8 E d m₁ m₂ := by
  rcases mapRootW8_binds_or_collides S8 E d hl₁ hl₂ (hr₁.trans hr₂.symm) with hm | hc
  · exact Or.inl (by rw [← hg₁, ← hg₂, hm])
  · exact Or.inr hc

/-- **THE EIGHT-FELT NULLIFIER / NON-MEMBERSHIP TOOTH, UNCONDITIONAL.** A prover cannot exhibit one
witness heap reading `some v` and another reading `none` at the same key behind the same 8-felt
root without thereby EXHIBITING a genuine chip collision at the named pair. This is the double-spend
refusal, and at an eight-felt digest the exhibition costs `≈ 2^123.63` queries rather than
`≈ 2^15.45`. -/
theorem opensToMerkleW8_some_excludes_none_or_collides (S8 : Heap8Scheme) (E : LaneEnc K) (d : Nat)
    {r : Digest8} {k : K} {v : ℤ} {m₁ m₂ : List (K × ℤ)}
    (hl₁ : m₁.length = 2 ^ d) (hr₁ : mapRootW8 S8 E d m₁ = r) (hg₁ : Heap.get m₁ k = some v)
    (hl₂ : m₂.length = 2 ^ d) (hr₂ : mapRootW8 S8 E d m₂ = r) (hg₂ : Heap.get m₂ k = none) :
    MapRootCollW8 S8 E d m₁ m₂ := by
  rcases opensToMerkleW8_functional_or_collides S8 E d hl₁ hr₁ hg₁ hl₂ hr₂ hg₂ with heq | hc
  · exact absurd heq (by simp)
  · exact hc

/-- **WRITES ARE FUNCTIONAL AT EIGHT FELTS, UNCONDITIONAL.** -/
theorem writesToMerkleW8_functional_or_collides (S8 : Heap8Scheme) (E : LaneEnc K) (d : Nat)
    {r : Digest8} {k : K} {v : ℤ} {r₁ r₂ : Digest8} {m₁ m₂ : List (K × ℤ)}
    (hl₁ : m₁.length = 2 ^ d) (hr₁ : mapRootW8 S8 E d m₁ = r)
    (hw₁ : r₁ = mapRootW8 S8 E d (Heap.set m₁ k v))
    (hl₂ : m₂.length = 2 ^ d) (hr₂ : mapRootW8 S8 E d m₂ = r)
    (hw₂ : r₂ = mapRootW8 S8 E d (Heap.set m₂ k v)) :
    r₁ = r₂ ∨ MapRootCollW8 S8 E d m₁ m₂ := by
  rcases mapRootW8_binds_or_collides S8 E d hl₁ hl₂ (hr₁.trans hr₂.symm) with hm | hc
  · exact Or.inl (by rw [hw₁, hw₂, hm])
  · exact Or.inr hc

end Generic

/-! ## §5 — THE COST, as arithmetic on deployed constants. A wider digest is NOT free.

Stated at the resolution actually available: these are COLUMN and ARITY counts on the model objects,
which is what the Rust re-emit (`circuit/src/lean_descriptor_air.rs`) turns into AIR width. They are
not a measured proof-size delta and are not offered as one. -/

/-- The deployed one-felt map node absorbs `[l, r]` — arity 2. -/
def MAP_NODE_ARITY_NARROW : Nat := 2
/-- The eight-felt map node absorbs `pack8 l r = L8 ‖ R8` — arity 16. -/
def MAP_NODE_ARITY_WIDE8 : Nat := 16

/-- The node absorb arity is what a `mapNode` and a `heapNodeOf8` actually take. Kernel-checked
rather than asserted: `mapNode hash l r = hash [l, r]` has a length-2 preimage, and `pack8` is
`List.ofFn l ++ List.ofFn r` at width 8. -/
theorem mapNode_arity (l r : ℤ) :
    ([l, r] : List ℤ).length = MAP_NODE_ARITY_NARROW := rfl

theorem pack8_arity (l r : Digest8) : (pack8 l r).length = MAP_NODE_ARITY_WIDE8 := by
  simp [pack8, MAP_NODE_ARITY_WIDE8]

/-- The number of felts a depth-`d` perfect tree COMMITS at one felt per node: `2^d` leaf digests
plus `2^d - 1` internal nodes. -/
def digestFeltsNarrow (d : Nat) : Nat := 2 ^ (d + 1) - 1
/-- The same tree at eight felts per node. -/
def digestFeltsWide8 (d : Nat) : Nat := 8 * (2 ^ (d + 1) - 1)

/-- **THE PRICE, EXACTLY.** The eight-felt tree commits `8×` the digest felts — `+7` per node and
per leaf. At the deployed `HEAP_TREE_DEPTH = 16` that is `917_497` extra felts of committed digest
across a full tree (`7 · (2^17 − 1)`), against a bar that improves by `babyBearP^7 ≈ 2^216`.
The trade is stated, not hidden; whether it is worth paying at every site is §6's question. -/
theorem digest_felts_delta (d : Nat) : digestFeltsWide8 d = 8 * digestFeltsNarrow d := rfl

theorem digest_felts_extra_at_deployed_depth :
    digestFeltsWide8 HEAP_TREE_DEPTH - digestFeltsNarrow HEAP_TREE_DEPTH = 917497 := by
  norm_num [digestFeltsWide8, digestFeltsNarrow, HEAP_TREE_DEPTH]

/-- The leaf absorb arity is UNCHANGED by this migration (`E.width + 1` — 2 narrow, 9 wide), which
is the honest separation from the kind-D epoch: that one moved this number and not the codomain;
this one moves the codomain and not this number. -/
theorem leafPreW_arity_unchanged {K : Type} [LinearOrder K] (E : LaneEnc K) (e : K × ℤ) :
    (leafPreW E e).length = E.width + 1 := by
  simp [leafPreW, E.enc_length]

/-! ## §6 — WHAT REMAINS, named rather than implied.

  * `MapOpWideKeyGate`'s ℤ-valued family is UNTOUCHED and still what the deployed narrow objects are
    `rfl`-equal to. This file does not delete it, because deleting it needs the deployed
    `MapOp.holdsAt` denotation, `DescriptorIR2.opensTo`, and the Rust `map_root` to move together —
    a VK epoch, which is the flag day `docs/DIGEST-WIDENING-PLAN.md` sequences.
  * The four `MapOpWideKeyGate` theorems that still carry `Poseidon2SpongeCR`
    (`reconcileGatesW_force_openingW`, `mapOpW_gates_force_holds`, `aafiInsertW_forces_imtInsertW`,
    `aafiGatesW_force_imtAbsentW`) are UNAFFECTED: their obstruction is that the gate data's heap and
    path steps are existentially bound, which widening does not address.
  * `imtLeafHash8` (arity 17, ONE felt) is a SECOND one-felt endpoint in the same family and is not
    migrated here. It is the next move and it is the same move.
  * `MapOp`'s VALUE stays one felt. Widening it is a separate site.
-/

/-! ## §AXIOM HYGIENE -/

#assert_axioms card_narrowDigest
#assert_axioms card_wideDigest8
#assert_axioms narrow_birthday_bar
#assert_axioms wide8_birthday_bar
#assert_axioms romBar_lt_one_iff
#assert_axioms narrow_bar_vacuous_at_2pow16
#assert_axioms narrow_break_exactly_at_44870
#assert_axioms narrow_bar_says_nothing_at_2pow64
#assert_axioms wide8_bar_at_2pow64
#assert_axioms wide8_bar_binds_below_p4
#assert_axioms wide8_bar_dies_at_p4
#assert_axioms wide8_break_exactly_at_p4
#assert_axioms wide8_bar_ratio
#assert_axioms romBar_antitone_in_codomain
#assert_axioms leafOfW8_binds_or_collides
#assert_axioms leafOfW8_injective
#assert_axioms map_leafOfW8_binds_or_collides
#assert_axioms mapRootW8_binds_or_collides
#assert_axioms mapRootW8_injective
#assert_axioms mapRootCollW8_dischargeable
#assert_axioms mapRootCollW8_fires_on_constant_chip
#assert_axioms leafCollW8_refutes_compress8CR
#assert_axioms mapRootCollW8_refutes_compress8CR
#assert_axioms opensToMerkleW8_functional_or_collides
#assert_axioms opensToMerkleW8_some_excludes_none_or_collides
#assert_axioms writesToMerkleW8_functional_or_collides
#assert_axioms pack8_arity
#assert_axioms digest_felts_delta
#assert_axioms digest_felts_extra_at_deployed_depth
#assert_axioms leafPreW_arity_unchanged

end Dregg2.Circuit.MapOpWideDigest8
