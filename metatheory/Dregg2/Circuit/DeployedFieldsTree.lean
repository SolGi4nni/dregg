import Dregg2.Circuit.DeployedCapTree
import Dregg2.Circuit.CapMerkleGeneric

/-!
# `DeployedFieldsTree` — the native 8-felt user-field-MAP tree spine (Phase H-FIELDS-8).

The THIRD and LAST faithful root's Lean spine, the exact twin of `DeployedHeapTree`'s `Heap8Scheme`
(and of `DeployedCapTree`'s `Cap8Scheme`). The deployed fields tree is a sorted-Poseidon2 binary
Merkle map over `(addr, value)` leaves (`addr = openable_fields_root::field_key_hash key`,
`value = fold_bytes32 v`) — the SAME `HeapLeaf` / `node8` scheme `heap_root.rs::compute_canonical_heap_root_8`
folds, over the `fields_root_leaves` set. The historical commitment projected each node/leaf to a SINGLE
felt (`hash : List ℤ → ℤ`, ~2^31), well below the deployed FRI/STARK ~124-bit soundness floor: two
genuinely-different field maps can collide on the 1-felt root while topping different 8-felt roots (the
fields GENTIAN tooth `circuit/tests/fields_root_gentian_weld.rs` exhibits a concrete pair). This module
gives the FAITHFUL 8-felt fields tree — every node absorbs full 8-felt children through the arity-16
`node8` chip and emits a full 8-felt digest — and the ONE new width-specific obligation its anti-ghost
needs.

REUSE (the Option-A payoff, exactly as for cap and heap): the membership-recompose anti-ghost spine
(`CapMerkleGeneric.recomposeG_inj_of_path`) is digest-type-AGNOSTIC and already proved once, so the
fields 8-felt migration collapses to `fieldsNodeOf8_injective` (the sole width-specific lemma) plus a
pure re-instantiation of the generic. `Digest8`, `Compress8CR`, and `pack8`/`pack8_inj` are shared
verbatim from `DeployedCapTree` — cap/heap/fields all ride the ONE `node8` compression
(`descriptor_ir2::chip_absorb_all_lanes` at `CHIP_NODE8_ARITY = 16`).
-/

namespace Dregg2.Circuit.DeployedFieldsTree

open Dregg2.Circuit.DeployedCapTree (Digest8 Compress8CR)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8 pack8_inj)

/-- **`Fields8Scheme`** — the native-8-felt fields-tree's SINGLE Poseidon2 carrier: the 8-output chip
absorb `chipAbsorb8 : List ℤ → Digest8` (`descriptor_ir2::chip_absorb_all_lanes`, all 8 squeezed
lanes). BOTH the leaf (`fieldsLeafDigest8`, arity 2) and the node (`fieldsNodeOf8`, arity 16) ride it;
the input lists are length-disjoint (2 vs 16), so the chip's per-row `(arity, padded inputs)` seeding
separates the two domains for free. The exact twin of `DeployedHeapTree.Heap8Scheme` — indeed the SAME
carrier (one `node8` chip serves cap/heap/fields). -/
structure Fields8Scheme where
  /-- The single 8-output chip-absorb compression (`heap_root.rs::heap_node8`/`HeapLeaf::digest8`, the
  carrier `compute_canonical_fields_root_8` folds). -/
  chipAbsorb8 : List ℤ → Digest8
  /-- CRYPTO CARRIER: the arity-16 chip's per-row collision-resistance (primitive #4 at 8-felt width). -/
  chip8CR : Compress8CR chipAbsorb8

namespace Fields8Scheme

variable (S8 : Fields8Scheme)

/-- **`fieldsLeafDigest8 S8 e`** — the 8-felt deployed fields leaf digest, the SINGLE 8-output chip
absorb over the 2 leaf fields `[addr, value]` (`addr = field_key_hash key`, `value = fold_bytes32 v`).
BYTE-IDENTICAL to `heap_root.rs::HeapLeaf::digest8` over a `fields_root_leaves` entry. The 8-felt
faithful twin of the 1-felt fields leaf. -/
def fieldsLeafDigest8 (e : ℤ × ℤ) : Digest8 := S8.chipAbsorb8 [e.1, e.2]

/-- **`fieldsNodeOf8 S8 l r`** — the native 8-felt internal node, the arity-16 chip absorb over
`pack8 l r = L8 ‖ R8`. BYTE-IDENTICAL to `heap_root.rs::heap_node8`. The SAME `chipAbsorb8` carrier as
the leaf — one fields hash everywhere. The 8-felt faithful twin of `MapMerkleRoot.mapNode`. -/
def fieldsNodeOf8 (l r : Digest8) : Digest8 := S8.chipAbsorb8 (pack8 l r)

/-- **Leaf injectivity at 8-felt width** — distinct `(addr, value)` pairs yield distinct 8-felt
digests, by the 8-output chip CR composed with the `[e.1, e.2]` list being injective in the pair.
The fields twin of `heapLeafDigest8_injective`. -/
theorem fieldsLeafDigest8_injective {e₁ e₂ : ℤ × ℤ}
    (h : fieldsLeafDigest8 S8 e₁ = fieldsLeafDigest8 S8 e₂) : e₁ = e₂ := by
  unfold fieldsLeafDigest8 at h
  have hl : [e₁.1, e₁.2] = [e₂.1, e₂.2] := S8.chip8CR _ _ h
  simp only [List.cons.injEq, and_true] at hl
  exact Prod.ext hl.1 hl.2

/-- **THE ONE NEW OBLIGATION — node injectivity at 8-felt width.** Equal `fieldsNodeOf8` images ⇒ equal
8-felt children. PROVED by the arity-16 chip's collision-resistance (`Compress8CR`) composed with
`pack8` injectivity — the per-level peel the native-8-felt membership recompose's anti-ghost needs.
This is the SOLE width-specific lemma the fields `node8` migration adds; the recompose spine is reused,
not re-proved. The exact twin of `DeployedHeapTree.Heap8Scheme.heapNodeOf8_injective`. -/
theorem fieldsNodeOf8_injective {l₁ r₁ l₂ r₂ : Digest8}
    (h : fieldsNodeOf8 S8 l₁ r₁ = fieldsNodeOf8 S8 l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  unfold fieldsNodeOf8 at h
  exact pack8_inj (S8.chip8CR _ _ h)

/-- **`recomposeUp8 S8 cur path`** — the native-8-felt fields membership recompose, DEFINED as the
generic `CapMerkleGeneric.recomposeG` at `D := Digest8`, `node := fieldsNodeOf8 S8`. No bespoke
recursion — the SAME generic spine cap/heap ride. BYTE-IDENTICAL to `heap_root.rs::recompose_membership_8`
and to the deployed in-circuit `node8` MapOps chain (unified onto `BUS_P2`). -/
def recomposeUp8 (cur : Digest8) (path : List (CapMerkleGeneric.StepG Digest8)) : Digest8 :=
  CapMerkleGeneric.recomposeG (fieldsNodeOf8 S8) cur path

/-- **The native-8-felt fields anti-ghost spine — a PURE RE-INSTANTIATION.** `recomposeUp8` is injective
in its starting digest along a fixed path, by `CapMerkleGeneric.recomposeG_inj_of_path` fed the ONE new
obligation `fieldsNodeOf8_injective`. NO spine re-proof: the SAME generic theorem the 1-felt tree and the
cap/heap trees delegate to. A prover cannot keep the published 8-felt fields root while swapping the
opened leaf along a fixed path. -/
theorem recomposeUp8_inj_of_path (path : List (CapMerkleGeneric.StepG Digest8)) :
    ∀ {a b : Digest8}, recomposeUp8 S8 a path = recomposeUp8 S8 b path → a = b :=
  CapMerkleGeneric.recomposeG_inj_of_path (fieldsNodeOf8 S8)
    (fun hh => fieldsNodeOf8_injective S8 hh) path

/-- **`MembersAt8 S8 root e`** — the native-8-felt deployed fields-tree membership: a sibling/direction
path recomposes the FULL 8-felt `root` from the 8-felt leaf digest of `(addr, value)`. The HONEST
8-felt replacement for the lossy 1-felt opening — opens against ~124-bit of root, not lane-0. The fields
twin of `DeployedHeapTree.Heap8Scheme.MembersAt8`. -/
def MembersAt8 (root : Digest8) (e : ℤ × ℤ) : Prop :=
  ∃ path : List (CapMerkleGeneric.StepG Digest8),
    recomposeUp8 S8 (fieldsLeafDigest8 S8 e) path = root

/-- **The GENTIAN close, in Lean.** Two field leaves opening the SAME 8-felt root along the SAME path
are the SAME leaf: the 8-felt root binds the opened `(addr, value)` at full ~124-bit width, so a
colliding-lane-0 forge (different entry, same 1-felt projection) cannot also open the 8-felt root. The
membership predicate is functional in the leaf along a fixed path. -/
theorem membersAt8_functional_on_path
    (root : Digest8) {e₁ e₂ : ℤ × ℤ}
    (path : List (CapMerkleGeneric.StepG Digest8))
    (h₁ : recomposeUp8 S8 (fieldsLeafDigest8 S8 e₁) path = root)
    (h₂ : recomposeUp8 S8 (fieldsLeafDigest8 S8 e₂) path = root) : e₁ = e₂ :=
  fieldsLeafDigest8_injective S8
    (recomposeUp8_inj_of_path S8 path (h₁.trans h₂.symm))

end Fields8Scheme

end Dregg2.Circuit.DeployedFieldsTree
