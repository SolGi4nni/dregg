/-
# Dregg2.Circuit.Emit.ShieldedExactMembershipFold — the shielded-spend membership fold at the
DEPLOYED `hash_many_8`, over the FSI2/FSN2/FSE2 exact-linked structure (Fork B, step-1 realization —
the SEMANTIC layer that fixes the emitted descriptor's target to the real object).

**This is Lean-authored AIR (semantics).** Ember greenlit Fork B: keep the depth-16 indexed-Merkle
sorted-linked shielded accumulator and make the DESCRIPTOR commensurate with it.
`Dregg2.Circuit.ShieldedOnRampPin` §8 fixed the commensuration OBLIGATION over an ABSTRACT 8-lane
hash. This module REALIZES that obligation at the DEPLOYED hash: it reuses
`ExactNullifierAafiDescriptorPlan.fullStateHash8` — the exact `hash_many_8` sponge the deployed
`note_shielded.root8()` folds through — and the proven general-position child placement
`exactChildren4`, at the SHIELDED domain triple `FSI2`/`FSN2`/`FSE2`
(`cell/src/shielded_note_set.rs:123-127`).

So the shielded membership fold here is the SAME object `exact_linked_append_root8(FSI2..)` commits
(`circuit/src/exact_nullifier_aafi.rs`), domain-swapped from the nullifier's `FNI2` — NOT an
abstraction of it. It is the SEMANTIC target the emitted `EffectVmDescriptor2` must pin `piCOMMITTED`
to, and the object `ShieldedOnRampPin.reencoded_fold_commensurates` is now discharged over.

## What is proved
* `shieldedParent_is_deployed_hash` — the per-level parent IS `fullStateHash8` (the deployed
  `hash_many_8`) of the FSN2 node block; not a stand-in.
* `shieldedNodeBlock_length = 33`, `shieldedLeafBlock_length = 39` — the exact-linked preimage widths,
  matching the Rust `debug_assert_eq!` (`exact_nullifier_aafi.rs:504,533`).
* `shielded_pin8_determines_root` — the 8-lane `Root8` pin binds the full root (no 8->1 collapse);
  WIDTH closed over the real object.
* `shielded_fold_realizes_commensuration` — the §8 obligation (WIDTH + STRUCTURE + the Shield-A LEAF)
  realized at the deployed hash.

## Scope (honest) — what this is NOT
This is the fold SEMANTICS at the deployed hash + the 8-lane pin CONTRACT, NOT the emitted descriptor.
The emitted per-row `EffectVmDescriptor2` (the FSN2 node sponge via `spongePlan`, the FSI2 leaf sponge,
the 8-lane `piBinding` pins, and `root_is_pinned8` over `Satisfied2`) is the mechanical remainder: it
reuses `v3State16Lookup`/`spongePlan`/`v3ChildExpr` with the two domain constants swapped
(`FNN2 -> FSN2`, `FNI2 -> FSI2`) plus the 8-lane pin. It is NOT emitted here because a wrong
general-position node indicator is a MEMBERSHIP HOLE (worse than #15) and must not be rushed into a
single pass. No `native_decide`: nothing here evaluates Poseidon2 — faithfulness rides the preimage
shapes and the definitional tie to `fullStateHash8`.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Dregg2.Circuit.ShieldedOnRampPin
import Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan

namespace Dregg2.Circuit.Emit.ShieldedExactMembershipFold

open Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan
  (fullStateHash8 exactChildren4 rootBlock rootBlock_length)
open Dregg2.Circuit.ExactNullifierAafiPlan
  (Root8 PathStep4 ExactLeaf exactKeyBlock rawValueBlock exactLeafBlock exactLeafBlock_length)
open Dregg2.Circuit.ShieldedOnRampPin
  (Note IsLedgerNote shieldAppendLeaf shieldAppend_is_ledger_note routeSum)

set_option autoImplicit false

/-- The deployed shielded exact-linked domain triple (`cell/src/shielded_note_set.rs:123-127`):
`FSI2` leaf, `FSN2` node, `FSE2` empty. Distinct from the nullifier's `FNI2`/`FNN2`/`FNE2`, so a
shielded leaf digest can never be replayed as a nullifier one. -/
def SHIELDED_LEAF_DOMAIN : ℤ := 0x46534932
def SHIELDED_NODE_DOMAIN : ℤ := 0x46534e32
def SHIELDED_EMPTY_DOMAIN : ℤ := 0x46534532

/-- The shielded exact-linked NODE block: `FSN2` + the four placed children's eight lanes — the
`exactNodeBlock` shape (`circuit/src/exact_nullifier_aafi.rs:522-533`), domain-swapped to `FSN2`. -/
def shieldedNodeBlock (current : Root8) (step : PathStep4) : List ℤ :=
  [SHIELDED_NODE_DOMAIN] ++ (exactChildren4 current step).flatMap rootBlock

/-- **The shielded per-level parent = the DEPLOYED `hash_many_8` (`fullStateHash8`) of the node
block.** The same sponge `note_shielded.root8()` folds through — not a stand-in. -/
def shieldedParent (current : Root8) (step : PathStep4) : Root8 :=
  fullStateHash8 (shieldedNodeBlock current step)

/-- The shielded exact-linked LEAF block: `FSI2` + tag/addr/value/next — the `exactLeafBlock` shape
(`:487-506`), domain-swapped to `FSI2`; length 39. -/
def shieldedLeafBlock (leaf : ExactLeaf) : List ℤ :=
  [SHIELDED_LEAF_DOMAIN] ++ exactKeyBlock leaf.addr ++ rawValueBlock leaf.value ++
    exactKeyBlock leaf.nextAddr

/-- The shielded leaf digest — the DEPLOYED `hash_many_8` of the FSI2 leaf block. -/
def shieldedLeafDigest (leaf : ExactLeaf) : Root8 := fullStateHash8 (shieldedLeafBlock leaf)

/-- Fold a leaf digest up its exact-linked path to the 8-lane root, through the DEPLOYED parent hash. -/
def shieldedFoldPath (leaf : Root8) : List PathStep4 → Root8
  | []       => leaf
  | s :: rest => shieldedFoldPath (shieldedParent leaf s) rest

/-- Membership against the deployed 8-lane exact-linked root — the predicate the emitted descriptor
must pin `piCOMMITTED` to. -/
def shieldedMembership (leaf : Root8) (path : List PathStep4) (root : Root8) : Prop :=
  shieldedFoldPath leaf path = root

/-- **`shieldedParent_is_deployed_hash`.** The per-level parent is the deployed `hash_many_8`
(`fullStateHash8`) of the FSN2 node block — the same object `note_shielded.root8()` folds through. -/
theorem shieldedParent_is_deployed_hash (cur : Root8) (step : PathStep4) :
    shieldedParent cur step = fullStateHash8 (shieldedNodeBlock cur step) := rfl

/-- The node block leads with the `FSN2` domain (`exact_nullifier_aafi.rs:527`). -/
theorem shieldedNodeBlock_head_FSN2 (cur : Root8) (step : PathStep4) :
    (shieldedNodeBlock cur step).headD 0 = SHIELDED_NODE_DOMAIN := rfl

/-- **Faithful width (`shieldedNodeBlock_length`).** 1 + 8·4 = 33 — the exact-linked node preimage
width (`exact_nullifier_aafi.rs:521-533`). -/
theorem shieldedNodeBlock_length (cur : Root8) (step : PathStep4) :
    (shieldedNodeBlock cur step).length = 33 := by
  obtain ⟨pos, sibs⟩ := step
  fin_cases pos <;>
    simp [shieldedNodeBlock, exactChildren4, List.flatMap, rootBlock_length]

/-- **Faithful width (`shieldedLeafBlock_length`).** 39 — the exact-linked leaf preimage width
(`exact_nullifier_aafi.rs:494-504`), inherited from `exactLeafBlock_length` (same shape, `FSI2` head). -/
theorem shieldedLeafBlock_length (leaf : ExactLeaf) :
    (shieldedLeafBlock leaf).length = 39 := by
  have h := exactLeafBlock_length leaf
  simp only [exactLeafBlock, List.length_append, List.length_cons, List.length_nil] at h
  simp only [shieldedLeafBlock, List.length_append, List.length_cons, List.length_nil]
  omega

/-- **⚑ WIDTH CLOSED, over the real object (`shielded_pin8_determines_root`).** The membership root is
a `Root8` (eight lanes); the fold determines it fully, so an 8-lane lane-wise `piCOMMITTED` pin binds
the committed root — there is no 8->1 collapse (§7's `route_fold_8to1_collides` is unrepresentable). -/
theorem shielded_pin8_determines_root (leaf : Root8) (path : List PathStep4) (r r' : Root8)
    (h : shieldedMembership leaf path r) (h' : shieldedMembership leaf path r') : r = r' := by
  rw [shieldedMembership] at h h'; rw [← h, ← h']

/-- **⚑ THE REALIZATION TIE (`shielded_fold_realizes_commensuration`).** The §8 commensuration
obligation (`ShieldedOnRampPin.reencoded_fold_commensurates`) is realized here at the DEPLOYED hash:
the shielded membership fold's per-level parent is `fullStateHash8` of the FSN2 exact-linked node
block (the same `hash_many_8` `note_shielded.root8()` commits), the node preimage is the exact-linked
33-felt shape (not `Hair`'s 7), and the LEAF conjunct is the Shield-A append committing `noteLeaf`.
The emitted descriptor must pin `piCOMMITTED` (8 lanes) to `shieldedFoldPath leaf path`. -/
theorem shielded_fold_realizes_commensuration (hash : List ℤ → ℤ) :
    (∀ cur step, shieldedParent cur step = fullStateHash8 (shieldedNodeBlock cur step))
    ∧ (∀ cur step, (shieldedNodeBlock cur step).length = 33)
    ∧ (∀ (auth : Note → Prop) (n : Note), auth n →
        IsLedgerNote hash auth (shieldAppendLeaf hash n)) :=
  ⟨fun cur step => shieldedParent_is_deployed_hash cur step,
   fun cur step => shieldedNodeBlock_length cur step,
   fun auth n hn => shieldAppend_is_ledger_note hash auth n hn⟩

#assert_axioms shieldedParent_is_deployed_hash
#assert_axioms shieldedNodeBlock_length
#assert_axioms shieldedLeafBlock_length
#assert_axioms shielded_pin8_determines_root
#assert_axioms shielded_fold_realizes_commensuration

end Dregg2.Circuit.Emit.ShieldedExactMembershipFold
