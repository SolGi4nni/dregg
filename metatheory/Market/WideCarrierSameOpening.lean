/-
# Market.WideCarrierSameOpening — C5 same-opening INSTANTIATED on the deployed wide carrier
  (D2 Bazaar-apex lane; builds ON `Dregg2.Circuit.ShieldedWideJoinPin`, re-derives nothing).

`ShieldedWideJoinPin` (`2ca3ca47f7`) states the C5 wound abstractly: the deployed ring↔wide
value-join is felt-equality on a ~31-bit `legacy_binding` squeeze, and any value-distinct collision
of the squeeze decouples the carrier's advertised dark value from the value the ring conserves.
Its binds are ABSTRACT functions. This module INSTANTIATES those theorems on the REAL deployed
carrier shapes (`circuit-prove/src/shielded/wide_value_binding.rs` at HEAD), with two sharpenings
the abstract module could not state:

  * **THE COLLISION IS FREE, not birthday.** The deployed legacy squeeze is
    `hash_fact(value mod p, [asset mod p, randomness, 0])` — it REDUCES `value`/`asset` mod
    BabyBear `p` BEFORE hashing (`u64_recompose(_, VALUE_MOD_P)`, `wide_value_binding.rs`). So for
    ANY hash function — the real Poseidon2 `hash_fact` included — the distinct `u64` values `v` and
    `v + p` produce LITERALLY IDENTICAL hash inputs (`legacy_input_aliases`): the value-distinct
    collision the abstract falsifier consumes is DETERMINISTIC, cost ZERO, and requires NO
    collision-resistance break of anything. The "~2^15.5 birthday / ~2^31 chosen" framing was an
    over-estimate of the attacker's cost; the mod-p pre-reduction hands the alias over structurally
    (`wide_value_binding.rs`'s own doc: "values separated by the BabyBear modulus alias before
    hashing"). `deployed_squeeze_join_decouples` fires the LANDED abstract falsifier at this real
    shape with the free collision.
  * **FIX B's floor DECOMPOSES — one named CR floor, the rest proved.** The wide carrier hashes
    the assembly `[domain, value limbs 0-3, asset limbs 0-2] ++ [asset limb 3, randomness,
    blind 0-5]` through two domain-separated `node8` sponges (`wide_input_columns`). Injectivity
    of the 16-lane image on `(value, asset)` splits into:
      - limb decomposition is injective on the `u64` domain (`limbs_recompose`/`limbs_inj`) — PROVED,
        pure arithmetic (this is what the AIR's bit-constraints + `limb_recompose` gates enforce);
      - the sponge-input assembly is injective on witnesses (`spongeInput_faithful`) — PROVED,
        structural (fixed lanes, no overlap);
      - ONE named CR floor: the `node8` sponge under `DOMAIN_A` is collision-free on assembled
        carrier inputs (`SpongeCROnCarrier`, injectivity-style, the same idealization as
        `WideCarrierFaithful` / `Poseidon2SpongeCR`). Only ONE floor is needed even though the
        carrier publishes two sponges: both absorb the SAME payload, so lane-A collision-freeness
        already forces the payload (`real_wide_join_forces_same_opening` uses only `laneA`).
    `real_wide_join_rejects_the_free_alias` closes the loop: the very alias pair the legacy squeeze
    hands over for free is SEPARATED by the wide join under that one floor.

**Fix A at the real shape** (`fws1_one_opening_is_fix_a`) is DISPATCHED THROUGH the abstract
theorem, not re-proved: the FWS1 whole-note-swap substrate (`f540ed95a1`,
`shielded-whole-note-swap-substrate-v1` — one selected hidden opening supplies nullifier, wide
binding, swap rule, output notes, and the exact transition in ONE witness) is architecturally
`shared_witness_forbids_decouple`: with one opening cell there is no second opening to decouple.
The v4 apex must keep that architecture while adding the FXC4/output-note/committee legs.

**Scope (honest).** Model resolution: lanes are `ℤ` (the per-lane BabyBear width is priced
elsewhere — `ShieldedValueLinkPin` / felt-width campaign); hashes are abstract functions of the
exact deployed input assemblies; the CR floor is named as injectivity on the carrier's input
space, the standing idealization of Poseidon2 collision resistance (the reduction of such floors
to adversary games is `WideCommitBoundary` §R's program, not this module's). Nothing here touches
deployed code, descriptors, or VKs.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
-/
import Dregg2.Circuit.ShieldedWideJoinPin
import Dregg2.Tactics

set_option autoImplicit false

namespace Market.WideCarrierSameOpening

open Dregg2.Circuit.ShieldedWideJoinPin

/-! ## 1. The real carrier shapes: BabyBear modulus, u64 domain, limbs, the witness. -/

/-- The BabyBear modulus `2^31 - 2^27 + 1` (`BABYBEAR_P`, `circuit/src/field.rs:12`). -/
def p : ℕ := 2013265921

theorem p_eq_deployed : p = 2 ^ 31 - 2 ^ 27 + 1 := by norm_num [p]

/-- The `u64` value/asset domain bound. -/
def u64Bound : ℕ := 2 ^ 64

/-- The full private witness of the deployed wide carrier: full-`u64` value and asset, the legacy
randomness felt, and the six extra blinding lanes (`BINDING_BLIND_LANES = 6`). -/
structure WideWitness where
  value : ℕ
  asset : ℕ
  randomness : ℤ
  blind : Fin 6 → ℤ
  value_lt : value < u64Bound
  asset_lt : asset < u64Bound

/-- Canonical 16-bit limb `k` of a `u64` (the AIR's bit-constrained `limb_recompose` columns). -/
def limb (v k : ℕ) : ℕ := v / 2 ^ (16 * k) % 2 ^ 16

/-- The four limbs recompose to the exact `u64` — what the AIR's `u64_recompose` gate enforces. -/
theorem limbs_recompose (v : ℕ) (hv : v < u64Bound) :
    limb v 0 + 65536 * limb v 1 + 4294967296 * limb v 2 + 281474976710656 * limb v 3 = v := by
  simp only [limb, u64Bound] at *
  norm_num
  omega

/-- Limb decomposition is INJECTIVE on the `u64` domain: agreeing limbs force equal values.
This is the PROVED leg of Fix B's injectivity — no hash assumption. -/
theorem limbs_inj {v w : ℕ} (hv : v < u64Bound) (hw : w < u64Bound)
    (h0 : limb v 0 = limb w 0) (h1 : limb v 1 = limb w 1)
    (h2 : limb v 2 = limb w 2) (h3 : limb v 3 = limb w 3) : v = w := by
  have Hv := limbs_recompose v hv
  have Hw := limbs_recompose w hw
  rw [h0, h1, h2, h3] at Hv
  omega

/-! ## 2. The deployed sponge-input assembly (`wide_input_columns`, faithful lane-for-lane).

`left = [domain, value limbs 0-3, asset limbs 0-2]`, `right = [asset limb 3, randomness,
blind 0-5]`; the sponge absorbs `left ++ right`. Two in-band domain separators. -/

/-- `"VBN0"` (`DOMAIN_A`, `wide_value_binding.rs:47`). -/
def DOMAIN_A : ℤ := 0x56424e30
/-- `"VBN1"` (`DOMAIN_B`, `wide_value_binding.rs:48`). -/
def DOMAIN_B : ℤ := 0x56424e31

/-- The exact 16-lane sponge input the deployed carrier absorbs under domain `dom`. -/
def spongeInput (dom : ℤ) (w : WideWitness) : List ℤ :=
  [dom,
   (limb w.value 0 : ℤ), (limb w.value 1 : ℤ), (limb w.value 2 : ℤ), (limb w.value 3 : ℤ),
   (limb w.asset 0 : ℤ), (limb w.asset 1 : ℤ), (limb w.asset 2 : ℤ),
   (limb w.asset 3 : ℤ), w.randomness,
   w.blind 0, w.blind 1, w.blind 2, w.blind 3, w.blind 4, w.blind 5]

/-- **The assembly is faithful**: equal sponge inputs force the ENTIRE witness equal — value,
asset (via limb injectivity), randomness, and every blinding lane. PROVED, structural: the lanes
are fixed and disjoint. This is the second proved leg of Fix B. -/
theorem spongeInput_faithful (dom : ℤ) {w₁ w₂ : WideWitness}
    (h : spongeInput dom w₁ = spongeInput dom w₂) :
    w₁.value = w₂.value ∧ w₁.asset = w₂.asset ∧
    w₁.randomness = w₂.randomness ∧ w₁.blind = w₂.blind := by
  simp only [spongeInput, List.cons.injEq, Nat.cast_inj, and_true, true_and] at h
  obtain ⟨h0, h1, h2, h3, a0, a1, a2, a3, hr, b0, b1, b2, b3, b4, b5⟩ := h
  refine ⟨limbs_inj w₁.value_lt w₂.value_lt h0 h1 h2 h3,
          limbs_inj w₁.asset_lt w₂.asset_lt a0 a1 a2 a3, hr, ?_⟩
  funext i
  fin_cases i <;> assumption

/-! ## 3. The deployed legacy squeeze — and its FREE structural collision.

`hash_fact(value mod p, [asset mod p, randomness, 0])` — the mod-p reduction happens BEFORE the
hash (`u64_recompose(_, VALUE_MOD_P)` / `u64_recompose(_, ASSET_MOD_P)`), so `v` and `v + p`
present IDENTICAL inputs to the hash. No CR break, no birthday search: the alias is handed over
by the squeeze's own arithmetic. -/

/-- The exact 4-lane legacy hash input (`[VALUE_MOD_P, ASSET_MOD_P, RANDOMNESS, ZERO]`). -/
def legacyInput (w : WideWitness) : List ℤ :=
  [((w.value % p : ℕ) : ℤ), ((w.asset % p : ℕ) : ℤ), w.randomness, 0]

/-- The legacy one-felt binding, for an ABSTRACT hash `H1` (the real Poseidon2 `hash_fact`
included — the aliasing below holds for EVERY `H1`). -/
def legacyBind (H1 : List ℤ → ℤ) (w : WideWitness) : ℤ := H1 (legacyInput w)

/-- Shift a witness's value by the modulus (staying inside `u64`). The canonical alias partner. -/
def bump (w : WideWitness) (h : w.value + p < u64Bound) : WideWitness :=
  { w with value := w.value + p, value_lt := h }

/-- **THE FREE COLLISION**: the bumped witness presents the LITERALLY IDENTICAL legacy hash
input. Deterministic, for any hash, zero cost. -/
theorem legacy_input_aliases (w : WideWitness) (h : w.value + p < u64Bound) :
    legacyInput (bump w h) = legacyInput w := by
  simp [legacyInput, bump, Nat.add_mod_right]

/-- Hence the legacy BINDING aliases — for EVERY hash function `H1`, the real one included. -/
theorem legacy_binding_aliases (H1 : List ℤ → ℤ) (w : WideWitness)
    (h : w.value + p < u64Bound) : legacyBind H1 (bump w h) = legacyBind H1 w :=
  congrArg H1 (legacy_input_aliases w h)

/-- …while the values genuinely DIFFER (by exactly the modulus). -/
theorem bump_changes_value (w : WideWitness) (h : w.value + p < u64Bound) :
    (bump w h).value ≠ w.value := by
  simp only [bump]
  unfold p
  omega

/-- …and the WIDE sponge input SEPARATES the alias pair: the full limbs see `v ≠ v + p`.
(The wide carrier's whole point, proved rather than narrated.) -/
theorem bump_separated_by_wide (w : WideWitness) (h : w.value + p < u64Bound) :
    spongeInput DOMAIN_A (bump w h) ≠ spongeInput DOMAIN_A w := by
  intro hEq
  have hval := (spongeInput_faithful DOMAIN_A hEq).1
  exact bump_changes_value w h hval

/-! ## 4. FIRING THE LANDED FALSIFIER at the real squeeze shape.

`ShieldedWideJoinPin` quantifies over abstract `Opening`/`Narrow`. We project the real shape into
it and DISCHARGE its collision hypothesis constructively — the abstract falsifier fires at the
deployed squeeze with the free `(0, p)` alias, for ANY hash `H1` and any randomness `r`. -/

/-- Project the real witness to the abstract `Opening` the landed C5 theorems quantify over. -/
def toOpening (w : WideWitness) : Opening := ⟨(w.value : ℤ), (w.asset : ℤ)⟩

/-- The deployed squeeze as an abstract `Narrow` bind at fixed randomness `r`: reduce the value
and asset coordinates mod `p`, then hash. Faithful to `hash_fact(value mod p, [asset mod p, r, 0])`. -/
def narrowOf (H1 : List ℤ → ℤ) (r : ℤ) : Narrow :=
  fun o => H1 [o.value % (p : ℤ), o.asset % (p : ℤ), r, 0]

/-- The projection commutes: the abstract bind at the projected opening IS the real legacy bind
(so the abstract theorems below are ABOUT the deployed object, not a mirror). -/
theorem narrowOf_faithful (H1 : List ℤ → ℤ) (w : WideWitness) :
    narrowOf H1 w.randomness (toOpening w) = legacyBind H1 w := by
  simp only [narrowOf, legacyBind, legacyInput, toOpening]
  push_cast
  rfl

/-- **The real squeeze HAS a value-distinct collision — constructively, for every hash.**
`⟨0, 0⟩` and `⟨p, 0⟩` differ in value yet reduce to identical hash inputs. This discharges the
abstract falsifier's `hcol` hypothesis with NO cryptographic assumption. -/
theorem real_squeeze_collides (H1 : List ℤ → ℤ) (r : ℤ) :
    ∃ o₁ o₂ : Opening, o₁.value ≠ o₂.value ∧ narrowOf H1 r o₁ = narrowOf H1 r o₂ := by
  refine ⟨⟨0, 0⟩, ⟨(p : ℤ), 0⟩, ?_, ?_⟩
  · show (0 : ℤ) ≠ ((p : ℕ) : ℤ)
    norm_num [p]
  · simp [narrowOf]

/-- **THE LANDED FALSIFIER FIRES ON THE DEPLOYED SQUEEZE** — `narrow_join_admits_dark_value_decouple`
instantiated: the deployed narrow join accepts a ring/carrier pair whose values differ, and the
collision it needs is the FREE mod-p alias, not a birthday search. -/
theorem deployed_squeeze_join_decouples (H1 : List ℤ → ℤ) (r : ℤ) :
    ∃ ringOpen wideOpen : Opening,
      joinedNarrow (narrowOf H1 r) ringOpen wideOpen ∧ ringOpen.value ≠ wideOpen.value :=
  narrow_join_admits_dark_value_decouple (narrowOf H1 r) (real_squeeze_collides H1 r)

/-- The theft form (`dark_value_decouples` instantiated): distinct openings, accepted join,
decoupled values — at the deployed squeeze, for free. -/
theorem deployed_dark_value_decouples_free (H1 : List ℤ → ℤ) (r : ℤ) :
    ∃ ringOpen wideOpen : Opening,
      joinedNarrow (narrowOf H1 r) ringOpen wideOpen ∧
      ringOpen.value ≠ wideOpen.value ∧ ¬(ringOpen = wideOpen) :=
  dark_value_decouples (narrowOf H1 r) (real_squeeze_collides H1 r)

/-! ## 5. FIX B on the real carrier — ONE named CR floor; everything else proved.

The wide binding is the pair of 8-lane sponge images. Joining on it forces the SAME `(value,
asset)` under a single named floor: `node8`-under-`DOMAIN_A` collision-free on assembled carrier
inputs. Lane B buys domain-separated redundancy, not additional binding: both sponges absorb the
same payload. -/

/-- The 16-lane wide binding: the two domain-separated 8-lane sponge images
(`WIDE_A ++ WIDE_B`). -/
structure WideBinding where
  laneA : Fin 8 → ℤ
  laneB : Fin 8 → ℤ

/-- The deployed wide bind for an abstract 8-lane sponge `H8` (the real `node8` Poseidon2
included). -/
def wideBind (H8 : List ℤ → Fin 8 → ℤ) (w : WideWitness) : WideBinding :=
  ⟨H8 (spongeInput DOMAIN_A w), H8 (spongeInput DOMAIN_B w)⟩

/-- **THE ONE NAMED FLOOR** — `node8` under `DOMAIN_A` is collision-free ON THE CARRIER'S INPUT
SPACE (injectivity-style, the standing idealization of Poseidon2 CR — same register as
`WideCarrierFaithful` and `Poseidon2SpongeCR`; its game-theoretic grounding is the
`WideCommitBoundary` §R program, not assumed here). -/
def SpongeCROnCarrier (H8 : List ℤ → Fin 8 → ℤ) : Prop :=
  ∀ w₁ w₂ : WideWitness,
    H8 (spongeInput DOMAIN_A w₁) = H8 (spongeInput DOMAIN_A w₂) →
    spongeInput DOMAIN_A w₁ = spongeInput DOMAIN_A w₂

/-- **FIX B, REAL CARRIER**: joining on the 16-lane wide binding forces the same `(value, asset)`
opening — under the ONE named floor; the limb and assembly legs are the proved theorems above.
Note only `laneA` is consulted: one sponge already binds the whole payload. -/
theorem real_wide_join_forces_same_opening (H8 : List ℤ → Fin 8 → ℤ)
    (floor : SpongeCROnCarrier H8) {w₁ w₂ : WideWitness}
    (h : wideBind H8 w₁ = wideBind H8 w₂) :
    w₁.value = w₂.value ∧ w₁.asset = w₂.asset := by
  have hA : H8 (spongeInput DOMAIN_A w₁) = H8 (spongeInput DOMAIN_A w₂) :=
    congrArg WideBinding.laneA h
  have hfull := spongeInput_faithful DOMAIN_A (floor w₁ w₂ hA)
  exact ⟨hfull.1, hfull.2.1⟩

/-- Fix B forces the ABSTRACT same-opening too — the bridge back to `ShieldedWideJoinPin`'s
vocabulary: the projected openings are equal. -/
theorem real_wide_join_forces_abstract_same_opening (H8 : List ℤ → Fin 8 → ℤ)
    (floor : SpongeCROnCarrier H8) {w₁ w₂ : WideWitness}
    (h : wideBind H8 w₁ = wideBind H8 w₂) : toOpening w₁ = toOpening w₂ := by
  obtain ⟨hv, ha⟩ := real_wide_join_forces_same_opening H8 floor h
  simp [toOpening, hv, ha]

/-- **The two halves meet on the real carrier**: the very alias pair the legacy squeeze accepts
for free is REJECTED by the wide join — under the one named floor, the bumped witness cannot
share a wide binding with the original. -/
theorem real_wide_join_rejects_the_free_alias (H8 : List ℤ → Fin 8 → ℤ)
    (floor : SpongeCROnCarrier H8) (w : WideWitness) (h : w.value + p < u64Bound) :
    wideBind H8 (bump w h) ≠ wideBind H8 w := by
  intro hEq
  exact bump_changes_value w h (real_wide_join_forces_same_opening H8 floor hEq).1

/-! ## 6. FIX A at the real shape — FWS1's architecture, dispatched THROUGH the landed theorem.

The FWS1 substrate feeds ONE selected hidden opening to the nullifier, the wide binding, the swap
rule, the output notes, and the exact transition. That architecture IS Fix A: with one witness
cell there is no second opening to decouple. Stated by APPLYING `shared_witness_forbids_decouple`
at the projected openings — reuse, not re-derivation. -/

theorem fws1_one_opening_is_fix_a (w ringW wideW : WideWitness)
    (hr : ringW = w) (hw : wideW = w) :
    (toOpening ringW).value = (toOpening wideW).value :=
  shared_witness_forbids_decouple (toOpening w) (toOpening ringW) (toOpening wideW)
    (congrArg toOpening hr) (congrArg toOpening hw)

/-! ## 7. NON-VACUITY — the free alias on concrete numbers. A false `#guard` is a build error. -/

/-- A concrete witness: value 1, asset 7, randomness 3, zero blinds. -/
def demoBase : WideWitness where
  value := 1
  asset := 7
  randomness := 3
  blind := fun _ => 0
  value_lt := by norm_num [u64Bound]
  asset_lt := by norm_num [u64Bound]

/-- Its free alias partner: value `1 + p` — a DIFFERENT `u64` that the legacy squeeze cannot
distinguish. -/
def demoAlias : WideWitness where
  value := 1 + p
  asset := 7
  randomness := 3
  blind := fun _ => 0
  value_lt := by norm_num [u64Bound, p]
  asset_lt := by norm_num [u64Bound]

-- The two values genuinely differ…
#guard decide (demoAlias.value ≠ demoBase.value) = true
-- …yet their legacy hash inputs are LITERALLY IDENTICAL (the free collision, on real numbers):
#guard decide (legacyInput demoAlias = legacyInput demoBase) = true
-- …and the WIDE sponge input tells them apart (limb 0: 2 vs 1; limb 1 also differs):
#guard decide (spongeInput DOMAIN_A demoAlias ≠ spongeInput DOMAIN_A demoBase) = true

/-- The demo pair witnesses the free collision as a theorem (non-vacuity of §4's hypothesis
discharge). -/
theorem demo_alias_is_free_collision :
    demoAlias.value ≠ demoBase.value ∧ legacyInput demoAlias = legacyInput demoBase :=
  ⟨by decide, by decide⟩

/-! ## 8. Axiom hygiene. -/

#assert_all_clean [
  Market.WideCarrierSameOpening.limbs_recompose,
  Market.WideCarrierSameOpening.limbs_inj,
  Market.WideCarrierSameOpening.spongeInput_faithful,
  Market.WideCarrierSameOpening.legacy_input_aliases,
  Market.WideCarrierSameOpening.legacy_binding_aliases,
  Market.WideCarrierSameOpening.bump_changes_value,
  Market.WideCarrierSameOpening.bump_separated_by_wide,
  Market.WideCarrierSameOpening.narrowOf_faithful,
  Market.WideCarrierSameOpening.real_squeeze_collides,
  Market.WideCarrierSameOpening.deployed_squeeze_join_decouples,
  Market.WideCarrierSameOpening.deployed_dark_value_decouples_free,
  Market.WideCarrierSameOpening.real_wide_join_forces_same_opening,
  Market.WideCarrierSameOpening.real_wide_join_forces_abstract_same_opening,
  Market.WideCarrierSameOpening.real_wide_join_rejects_the_free_alias,
  Market.WideCarrierSameOpening.fws1_one_opening_is_fix_a,
  Market.WideCarrierSameOpening.demo_alias_is_free_collision]

end Market.WideCarrierSameOpening
