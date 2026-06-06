/-
# Dregg2.Circuit.KeyedCommit — the keyed-function commitment carrier (v2, the FUNCTION-field shape).

`StateCommit.frameDigest`/`FrameDigestBindsCells` commit a `cell : CellId → Value` function over a
`Finset CellId` carrier and bind it. But other FUNCTION fields change too: `bal : CellId → AssetId → ℤ`
(mint/burn/transfer) and `caps : Label → …` (the authority effects). They are the SAME shape — a total
function from a finite-domain key to a value — only the KEY TYPE and the leaf differ. This module is the
state-free, key-polymorphic lift: `keyedDigest`/`KeyedDigestBindsKeys` over any `LinearOrder` key, so
`FrameDigestBindsCells` becomes the `κ = CellId` instance and `bal` (key `CellId × AssetId`) / `caps`
(key `Label`) are bound with the SAME proof, zero new crypto beyond `compressNInjective`.

`#assert_axioms` whitelists `{propext, Classical.choice, Quot.sound}` (the injectivity is a hypothesis).
-/
import Dregg2.Circuit.StateCommit

namespace Dregg2.Circuit.KeyedCommit

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit

universe u

/-- **`keyedDigest KL compressN S`** — the Poseidon sponge of the leaves `KL k` over the SORTED keys of
the finite carrier `S : Finset κ`. The key-polymorphic generalization of `StateCommit.frameDigest`
(which is the `κ = CellId`, `KL k = CH k (state.cell k)` instance). -/
def keyedDigest {κ : Type u} [LinearOrder κ] (KL : κ → ℤ) (compressN : List ℤ → ℤ)
    (S : Finset κ) : ℤ :=
  compressN ((S.sort (· ≤ ·)).map KL)

/-- **`KeyedDigestBindsKeys` — the function-field binder.** Two leaf-readings whose keyed digests over
the SAME carrier `S` agree must agree at every key of `S`. Binds `bal`-debit/credit (key `CellId ×
AssetId`) and `caps` edge-add/remove (key `Label`) with the same proof as `FrameDigestBindsCells`:
`compressN`-injective ⇒ the mapped leaf-lists are equal; equal `List.map`s over the same list ⇒
pointwise equal on it. -/
theorem KeyedDigestBindsKeys {κ : Type u} [LinearOrder κ] (KL KL' : κ → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (S : Finset κ)
    (h : keyedDigest KL cN S = keyedDigest KL' cN S) :
    ∀ k ∈ S, KL k = KL' k := by
  intro k hk
  unfold keyedDigest at h
  have hmap : (S.sort (· ≤ ·)).map KL = (S.sort (· ≤ ·)).map KL' := hN _ _ h
  exact (List.map_inj_left.mp hmap) k ((Finset.mem_sort _).mpr hk)

/-- Completeness dual: agree at every key of `S` ⇒ equal keyed digests. -/
theorem keyedDigest_congr {κ : Type u} [LinearOrder κ] {KL KL' : κ → ℤ} (cN : List ℤ → ℤ)
    (S : Finset κ) (h : ∀ k ∈ S, KL k = KL' k) :
    keyedDigest KL cN S = keyedDigest KL' cN S := by
  unfold keyedDigest
  refine congrArg cN (List.map_inj_left.mpr ?_)
  intro k hk; exact h k ((Finset.mem_sort _).mp hk)

/-! ## Non-vacuity over a concrete key (`Nat × Nat`, the `bal` key shape) + leaf. -/

private def cNC : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000000 + x) (xs.length : ℤ)

-- agree-everywhere ⇒ equal; differ at a key ⇒ unequal (the bind gate would reject the wrong value):
#guard decide (keyedDigest (fun k : Nat => (k : ℤ)) cNC {0, 1, 2}
             = keyedDigest (fun k : Nat => (k : ℤ)) cNC {0, 1, 2})                              -- true
#guard decide (keyedDigest (fun k : Nat => (k : ℤ)) cNC {0, 1, 2}
             = keyedDigest (fun k : Nat => if k = 1 then 99 else (k : ℤ)) cNC {0, 1, 2}) == false -- differ @1

#assert_axioms KeyedDigestBindsKeys
#assert_axioms keyedDigest_congr

end Dregg2.Circuit.KeyedCommit
