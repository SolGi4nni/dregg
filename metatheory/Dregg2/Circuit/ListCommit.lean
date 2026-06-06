/-
# Dregg2.Circuit.ListCommit — the list-side-table commitment carrier (the v2 bottleneck-breaker).

The generic `EffectCommit` framework (v1) binds CELL-changing effects: `StateCommit.frameDigest` +
`FrameDigestBindsCells` commit a function-field (`cell : CellId → Value`) and bind it. But ~12 of the
remaining effects change a **`List` side-table** instead — `nullifiers`/`commitments`/`escrows`/
`queues`/`swiss`/`sealedBoxes`/`revoked`/`factories` — by a `cons`/insert. Binding a list change needs
ONE new carrier: a Poseidon list-sponge whose injectivity pins the WHOLE post-list (so a forgery that
drops/reorders an existing entry, not just adds the new one, is rejected).

This is the list analog of `StateCommit.frameDigest`/`FrameDigestBindsCells`, proved the same way
(compressN-injective ⇒ mapped lists equal; injective leaf ⇒ the lists equal). The only carried crypto
assumptions are the SAME realizable Poseidon injectivities (`compressNInjective` + an injective leaf
encoder) — never an axiom. `#assert_axioms` whitelists `{propext, Classical.choice, Quot.sound}`.

`ListDigestBindsList` is the single new lemma the whole list-effect family (~12 effects) instantiates.
-/
import Dregg2.Circuit.StateCommit

namespace Dregg2.Circuit.ListCommit

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit

universe u

/-! ## §1 — the list digest + its CR carriers. -/

/-- **`listDigest LE compressN xs`** — the Poseidon sponge of a `List α` under a leaf encoder
`LE : α → ℤ`. The list analog of `frameDigest` (which sponges the sorted leaves of a `Finset`). -/
def listDigest {α : Type u} (LE : α → ℤ) (compressN : List ℤ → ℤ) (xs : List α) : ℤ :=
  compressN (xs.map LE)

/-- The leaf encoder is injective (REALIZABLE — Poseidon over a canonical per-entry serialization;
the list analog of `cellLeafInjective`). Carried, never proved here. -/
def listLeafInjective {α : Type u} (LE : α → ℤ) : Prop := Function.Injective LE

/-! ## §2 — the binding lemma (PROVED from the realizable Poseidon-CR set). -/

/-- **`ListDigestBindsList` — the bottleneck-breaker.** Equal list digests force the WHOLE lists
equal: `compressNInjective` ⇒ the mapped leaf-lists are equal; the injective leaf encoder ⇒ the
source lists are equal. So a list-bind gate pins not just "grew by the new entry" but the entire
ordered post-list — a forgery that drops or reorders an existing entry is REJECTED. The list analog of
`StateCommit.FrameDigestBindsCells`, and the single lemma the ~12 list-changing effects instantiate. -/
theorem ListDigestBindsList {α : Type u} (LE : α → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (xs ys : List α)
    (h : listDigest LE cN xs = listDigest LE cN ys) : xs = ys := by
  unfold listDigest at h
  have hmap : xs.map LE = ys.map LE := hN _ _ h
  exact List.map_injective_iff.mpr hLE hmap

/-- Completeness dual: equal lists ⇒ equal digests (by `congrArg`). -/
theorem listDigest_congr {α : Type u} (LE : α → ℤ) (cN : List ℤ → ℤ) {xs ys : List α}
    (h : xs = ys) : listDigest LE cN xs = listDigest LE cN ys := by rw [h]

/-! ## §3 — non-vacuity: the digest distinguishes a `cons` from a drop (the anti-ghost shape). -/

/-- A concrete injective leaf encoder + concrete injective `compressN` (a positional Horner fold,
seeded by length) over which the binding is DECIDABLY exhibited. -/
private def leafC : Nat → ℤ := fun n => (n : ℤ)
private def cNC : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000000 + x) (xs.length : ℤ)

-- A grown list and a dropped list have DIFFERENT digests (the gate would reject the drop):
#guard decide (listDigest leafC cNC [7, 3, 1] = listDigest leafC cNC [7, 3, 1])           -- true
#guard decide (listDigest leafC cNC [9, 7, 3, 1] = listDigest leafC cNC [7, 3, 1]) == false -- cons ≠ base
#guard decide (listDigest leafC cNC [7, 1] = listDigest leafC cNC [7, 3, 1]) == false       -- drop ≠ base
#guard decide (listDigest leafC cNC [3, 7, 1] = listDigest leafC cNC [7, 3, 1]) == false     -- reorder ≠ base

#assert_axioms ListDigestBindsList
#assert_axioms listDigest_congr

end Dregg2.Circuit.ListCommit
