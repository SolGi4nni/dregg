/-
# Dregg2.Verify.FloorRatchetBaselineInline — the INLINE-SPELLED grandfathered carriers.

GENERATED, and kept SEPARATE from `FloorRatchetBaseline.lean` on purpose. Two reasons:

* **Provenance.** Every name here became visible on one day, from one cause: `#floor_ratchet`
  learned to read a floor spelled `Function.Injective f` instead of by name
  (`Dregg2/Verify/InjSpelling.lean`). None of them is a new theorem. Each was ALREADY vacuous and
  ALREADY uncounted — the gate's own log printed the size of the hole on every run ("N
  `Function.Injective`-spelled sites ungated (known residual)") and nobody could act on a number.
  Keeping the raise in its own file keeps that cause readable instead of dissolving it into a
  2000-line list.
* **Co-tenancy.** The main baseline is edited by other lanes in the same working tree. A
  several-hundred-line append to the same generated file is exactly the clobber
  `CLAUDE.md` forbids.

⚑ WHAT EACH LINE MEANS. The declaration takes `Function.Injective f` as a HYPOTHESIS at a
signature this tree REFUTES — either because the inline spelling is definitionally a named refuted
floor (`Poseidon2SpongeCR` at `List ℤ → ℤ`), or because an in-tree theorem proves NO function of
that type is injective at all. The second kind is the majority and is the worse one: a
whole-function digest `(CellId → AssetId → ℤ) → ℤ` maps an UNCOUNTABLE domain into a countable one,
so the hypothesis is a CARDINALITY IMPOSSIBILITY — false at every parameter set, for every hash, in
every field (`Dregg2/Verify/InjSpelledFloors.lean`). These are not optimistic assumptions about
Poseidon2; they are assumptions with no models.

The PORT is structural, not cryptographic: digest the FINITE support actually touched (the
`accounts : Finset CellId` rows), never the whole function. A finite-support digest has a countable
domain and is back at the ordinary deployed-parameter CR bar, where the campaign's per-instance
`…Coll` side conditions apply.

Only ever gets SHORTER. The next `#floor_ratchet_emit` folds surviving entries into
`FloorRatchetBaseline.lean`'s chunks; when that happens this file's array goes empty and stays.
-/
set_option autoImplicit false

namespace Dregg2.Verify.FloorRatchetBaselineInline

/-- The inline-spelled grandfathered carriers. -/
def inlineSpelled : Array String := #[]

end Dregg2.Verify.FloorRatchetBaselineInline
