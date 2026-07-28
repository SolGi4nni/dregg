/-
# `Dregg2.Circuit.Emit.AttestedFactsRootRegrounded` — the tooth for `Hash4Injective`.

`AttestedFactsRootModel.Hash4Injective` asks the deployed arity-4 compression `hash_4_to_1`
(four field elements in, ONE out) to be injective in all four arguments at once. Its own
docstring called it "the honest collision-resistance floor". It is not a floor: it is FALSE at
every finite carrier, and the argument is pigeonhole with nothing cryptographic in it.

Fix two of the four arguments and the floor hands you an injection `F × F ↪ F`, so it forces
`|F|² ≤ |F|`, so `|F| ≤ 1`. The deployed field is BabyBear (`p = 2^31 − 2^27 + 1`), so the
floor is false there, and every theorem conditioned on it was vacuously true at deployed
parameters. No Poseidon2 collision is exhibited and none is needed — the same counting core as
`HashFloorHonesty.compressNInjective_false_of_finite_range` and
`AutomataflRevealRefine.hash4NoCollision_false_babyBear`.

⚑ WIDENING DOES NOT SAVE IT, and that is the point worth carrying away. `Hash4Injective`
mentions no width, so it is exactly as false at 8 output lanes as at 1 — an assumption stated
as injectivity gives a wider encoding nothing to improve. The repair is not a bigger codomain
but a different SHAPE: restrict to the preimages actually presented and price the collision.
That is `AttestedFactsRootModel.Coll4`, and the bound that discharges it is
`Crypto.RomQueryFloor.birthday_bound`, which is PROVED and assumes nothing. The tree already
has the both-moves-at-once version worked end to end in exactly one place —
`Emit.ShieldedWideValueLinkDescriptor.WideBindingCR`, injectivity restricted to the CANONICAL
encoding domain at 8 lanes, which is INHABITED (`wideBindingCR_satisfiable`) precisely because
the domain is ~2^159 against a ~2^248 range.

⚑ DO NOT "repair" a consumer by swapping in the unrestricted-class collision floor —
`HashFloorHonesty.CollisionResistant`, DELETED 2026-07-28 precisely because it was
refuted too (`FloorGames.hashCRHardQuant_top_false_of_compressing`, 57 carriers), for the same reason at one
level up: it is the floor at the UNRESTRICTED adversary class, where `Classical.choice` is a
perfectly good collision finder. Rung 2 is `HashCRHardQuant F Eff`; rung 3 is
`RomQueryFloor.birthday_bound`.

This module holds ONLY the refutation. The port lives in the model file, which keeps its
bare-`lean` no-imports property; a cardinality argument needs Mathlib and therefore lives here.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Dregg2.Circuit.Emit.AttestedFactsRootModel
import Dregg2.Tactics

set_option autoImplicit false

namespace Dregg2.Circuit.Emit.AttestedFactsRootRegrounded

open Dregg2.Circuit.Emit.AttestedFactsRootModel

/-- **⚑ THE TOOTH — `Hash4Injective` is FALSE at every finite carrier with more than one
element.** Pigeonhole, no hash collision exhibited: fixing the last two arguments at a constant
`x` embeds `F × F` into `F`, so the floor forces `|F| * |F| ≤ |F|`, which fails as soon as
`1 < |F|`. Nothing about Poseidon2, arity 4, or the tree shape is used — only that a compression
compresses. -/
theorem hash4Injective_false_of_finite {F : Type} [Fintype F]
    (hcard : 1 < Fintype.card F) (hash4 : F → F → F → F → F) :
    ¬ Hash4Injective hash4 := by
  intro hinj
  -- `1 < card F` gives an element to freeze the last two arguments at.
  obtain ⟨x⟩ : Nonempty F := Fintype.card_pos_iff.mp (by omega)
  -- The floor makes `(a, b) ↦ hash4 a b x x` injective: an embedding `F × F ↪ F`.
  have hemb : Function.Injective (fun p : F × F => hash4 p.1 p.2 x x) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨ha, hb, _, _⟩ := hinj a b x x a' b' x x h
    simp only [Prod.mk.injEq]
    exact ⟨ha, hb⟩
  have hcards : Fintype.card (F × F) ≤ Fintype.card F :=
    Fintype.card_le_of_injective _ hemb
  rw [Fintype.card_prod] at hcards
  -- `card F * card F ≤ card F` with `2 ≤ card F` is a linear contradiction once the square is
  -- bounded below by the doubling.
  have hdouble : Fintype.card F * 2 ≤ Fintype.card F * Fintype.card F :=
    Nat.mul_le_mul (Nat.le_refl _) hcard
  omega

/-- **The tooth at DEPLOYED parameters.** BabyBear is `Fin p` for `p = 2^31 − 2^27 + 1 =
2013265921`, so the floor is false in the field the circuits actually run over. This is the
statement that makes `attested_member_is_committed`'s old form vacuous — not a statement about
a hypothetical small field. -/
theorem hash4Injective_false_babyBear
    (hash4 : Fin 2013265921 → Fin 2013265921 → Fin 2013265921 → Fin 2013265921 →
      Fin 2013265921) :
    ¬ Hash4Injective hash4 :=
  hash4Injective_false_of_finite (by rw [Fintype.card_fin]; omega) hash4

/-- **The refutation is not an artifact of arity 4.** The same pigeonhole kills the floor at
`Bool`, the smallest carrier that can carry it at all — recorded so the boundary of the tooth is
explicit: `1 < |F|` is exactly the condition, and `|F| = 1` is the only escape (a one-element
field, where every function is injective and nothing is committed). -/
theorem hash4Injective_false_bool (hash4 : Bool → Bool → Bool → Bool → Bool) :
    ¬ Hash4Injective hash4 :=
  hash4Injective_false_of_finite (by rw [Fintype.card_bool]; omega) hash4

/-! ### The boundary of the tooth, and why it is not stated as a theorem here

`1 < |F|` is SHARP. On a subsingleton carrier the floor does hold, vacuously — everything is
equal to everything, and nothing is committed. So the only finite escape is a one-element field.
That fact is deliberately NOT written as `[Subsingleton F] → Hash4Injective hash4`: a
declaration whose TYPE names a refuted floor is a `#floor_ratchet` carrier no matter which
position the name sits in, so stating the degenerate positive case would cost a permanent
baseline entry to record something with no security content. The same reasoning retired
`hash4Injective_is_satisfiable` from the model file in favour of the floor-free
`ftreeNode_injective`. -/

#assert_axioms hash4Injective_false_of_finite
#assert_axioms hash4Injective_false_babyBear
#assert_axioms hash4Injective_false_bool

end Dregg2.Circuit.Emit.AttestedFactsRootRegrounded
