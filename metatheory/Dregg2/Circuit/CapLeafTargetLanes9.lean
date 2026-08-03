/-
# Dregg2.Circuit.CapLeafTargetLanes9 — THE CAP-LEAF TARGET. THE WOUND WAS NOT STATEABLE.

## SUBSTRATE, SAID OUT LOUD

This is Lean-authored AIR material. The encoding and the leaf's absorb shape are decided HERE;
`circuit/src/cap_root.rs` is a twin that must be cut over to what this file fixes, and
`circuit/tests/cap_leaf_target_lanes9_pins.rs` pins the two together by execution. Nothing in this
file is a Rust-authored constraint, and nothing in it is `native_decide`.

## What this file is FOR — the instrument was blind, not wrong

`Dregg2.Circuit.DeployedCapTree` is the authority for the deployed 7-field `CapLeaf`, and it proves
`leafFields_inj`: equal field lists force the whole leaf equal. That theorem is TRUE and it is
**blind to the wound**, because it is a statement about `ℤ`. The deployed leaf's `target` field is
not an `ℤ` a prover chooses — it is the image of a 32-byte `CellId` under
`cap_root.rs::fold_bytes32 = hash_many ∘ bytes32_to_8_limbs`, and `DeployedCapTree` begins ONE STEP
DOWNSTREAM of that map. Lean has never modelled it. Grep `metatheory/` for `foldBytes32`,
`bytes32_to_8_limbs`, `capTarget`: before this file, zero hits.

So the situation on 2026-08-02 was: a Rust docblock (`cap_root.rs:258-268`) said "⚠ **NOT
collision-resistant** … for attacker-chosen `target`/`breadstuff` bytes the pair is CONSTRUCTED, not
searched", a shell gate (`scripts/check-no-degraded-felt.sh`) went red on it, and **no theorem
anywhere could express the sentence**, let alone refute the encoder. `leafFields_inj` reads as
coverage of the leaf and covers everything except the one map that is broken.

§1 makes the deployed map a Lean object and REFUTES its injectivity. §4 fixes the replacement's
shape at an arity the deployed chip actually admits. Both poles are exhibited on the SAME alias
pair: `capFoldLimbs` identifies it (the deployed leaf field lists are EQUAL — accepted), and
`capLeafFields9` separates it (REFUSED).

## The measurement this file encodes, and where the recorded numbers were wrong

`bytes32_to_8_limbs` reads each 4-byte little-endian chunk as a `u32` and reduces it mod
`P = 2013265921`. Its own docblock says a random chunk "needs reducing with probability
`1 - p/2^32 = 53.1%`" — and a reader takes 53.1% for the ALIAS rate. **It is not.** `2·P < 2^32`, so
`[0, 2^32)` covers every residue class at least twice:

  * `2^32 - 2P = 268435454` residues have THREE `u32` representatives,
  * the remaining `1744830467` have TWO,

so **every** chunk value has a sibling, and every 32-byte value has at least `2^8` byte-distinct
siblings with an identical limb vector (`2^8.74` on average: `2^256 / P^8`). The alias rate is
100%, not 53.1%; 53.1% answers a different and more flattering question. Measured by execution in
`circuit/tests/degraded_felt_wound_measure.rs` (`10000/10000`).

That is the ENCODER floor and it is upstream of the sponge, so no hash downstream can undo it.
There is a second, independent floor — the SQUEEZE: `fold_bytes32` emits ONE felt, an image of
`log₂ P = 30.907` bits against a 256-bit source, i.e. `225.09` bits destroyed and a `2^15.45`
birthday. Closing only the encoder leaves the squeeze at `2^30.907`, below this tree's own ~124-bit
bar, and shipping THAT while naming the nonet leaf as a later phase is precisely the move
`Dregg2.Circuit.KeyLanes9`'s header refuses. So §4 widens the leaf, and does not merely re-chunk.

## Why NINE lanes, and why the leaf lands at arity SIXTEEN

Nine is not a preference. `P^8 < 2^256 ≤ P^9` (`FieldLanes9.nine_lanes_is_the_minimum`): no
eight-lane encoding of 32 bytes is injective under ANY chunking, before a line of code is read. The
injective nonet already exists and is proved — `KeyLanes9.keyToLanes9`, base `2^29`, image exactly
`2^256`, `keyToLanes9_injective`, `#assert_axioms`-clean — and a `CellId` is a KEY, so that is the
one to reuse rather than author a third.

The leaf's absorb arity is then FORCED, not chosen. `DescriptorIR2.CHIP_ADMITTED_ARITIES =
[0, 2, 3, 4, 7, 11, 16]` are the roots of the deployed degree-7 admission product; anything else is
UNPROVABLE at that row, and that file forbids widening the list ("pad the absorb block up to the
next admitted arity instead"). Six scalar fields plus a nine-lane target is 15 — not admitted. The
next admitted arity is 16, and the padding lane must be a DOMAIN TAG rather than a zero, because
`Cap8Scheme.nodeOf8` is ALSO an arity-16 chip absorb (`pack8 l r = L8 ‖ R8`). An untagged 16-lane
leaf block would live in the same absorb domain as an internal node. §5 is that separation.

## What this file does NOT do

It does not cut the deployed tree over. `cap_root.rs`'s `CapLeaf` is still 7 fields, the committed
`capability_root` still carries the folded target, and `scripts/check-no-degraded-felt.sh` is still
red at `cell/src/commitment.rs:561` — correctly. The cutover is 45 production Rust sites and six
Lean modules (`DeployedCapOpen`'s `CapOpenCols.leaf : Fin 7 → Nat` and `targetBindGate`,
`InjectiveFloorRegrounded`, `CircuitCompletenessAuthority{,Construct}`, `VacuitySweepTeeth`,
`SortedTreeNonMembership`, `CapHashBundleCutoverCheck`), and half-landing it in a shared tree
breaks it for everyone. **This file is that cutover's specification and its refutation of the
status quo — the first item of the work, not a substitute for it.** No committed byte moves here,
so no epoch rotates here either.
-/

import Mathlib.Tactic
import Dregg2.Circuit.KeyLanes9
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Tactics

namespace Dregg2.Circuit.CapLeafTargetLanes9

open Dregg2.Circuit.FieldLanes9 (P Byte Bytes32 nine_lanes_is_the_minimum)
open Dregg2.Circuit.KeyLanes9 (keyToLanes9 keyToLanes9_injective)

/-! ## §1 — THE DEPLOYED ENCODER, MODELLED, AND REFUTED.

`circuit/src/effect_vm/helpers.rs:78-88`:

```rust
pub fn bytes32_to_8_limbs(b: &[u8; 32]) -> [BabyBear; 8] {
    for i in 0..8 {
        let v = u32::from_le_bytes([b[4i], b[4i+1], b[4i+2], b[4i+3]]);
        out[i] = BabyBear::new(v % crate::field::BABYBEAR_P);
    }
}
```

`cap_root.rs::fold_bytes32` is `hash_many` of THAT, and `cell/src/commitment.rs:561` puts its image
in the deployed cap leaf's `target`. Everything below is about the `% P` step, which is upstream of
`hash_many` and therefore cannot be repaired by anything the sponge does.
-/

/-- The little-endian `u32` value of the `i`-th 4-byte chunk of a 32-byte value — `u32::from_le_bytes`
on the nose. -/
def chunkLE (b : Bytes32) (i : Fin 8) : Nat :=
  (b ⟨4 * i.1, by omega⟩).1
    + 256 * (b ⟨4 * i.1 + 1, by omega⟩).1
    + 65536 * (b ⟨4 * i.1 + 2, by omega⟩).1
    + 16777216 * (b ⟨4 * i.1 + 3, by omega⟩).1

/-- **THE DEPLOYED CAP-TARGET ENCODER.** `bytes32_to_8_limbs`, as a Lean function: eight chunks,
each reduced mod `P`. This is the map `cap_root.rs::fold_bytes32` hashes, and the map every theorem
in `DeployedCapTree` sits downstream of. -/
def capFoldLimbs (b : Bytes32) (i : Fin 8) : Nat := chunkLE b i % P

/-! ### §1a — the alias pair, CONSTRUCTED.

`P = 2013265921 = 0x78000001`, little-endian `01 00 00 78`. So the 32-byte value that is zero
everywhere except `b[3] = 0x78` and `b[0] = 0x01` has first chunk exactly `P`, which reduces to the
same limb as the all-zero chunk. One byte pair, no search. This is byte-identically the canary
already sitting in `circuit/src/exact_cap_root.rs:485-507`. -/

/-- The all-zero 32-byte target. -/
def zeroTarget : Bytes32 := fun _ => 0

/-- The alias of [`zeroTarget`]: chunk 0 carries `P` itself (`01 00 00 78` little-endian). -/
def pTarget : Bytes32 := fun j =>
  if j.1 = 0 then ⟨1, by decide⟩ else if j.1 = 3 then ⟨120, by decide⟩ else ⟨0, by decide⟩

/-- The two targets are DISTINCT 32-byte values — they differ in byte 0. -/
theorem zeroTarget_ne_pTarget : zeroTarget ≠ pTarget := by
  intro h
  have := congrFun h 0
  simp [zeroTarget, pTarget] at this

/-- Chunk 0 of [`pTarget`] is exactly `P`. -/
theorem pTarget_chunk0 : chunkLE pTarget 0 = P := by decide

/-- Chunk 0 of [`zeroTarget`] is `0`. -/
theorem zeroTarget_chunk0 : chunkLE zeroTarget 0 = 0 := by decide

/-- **THE ALIAS, AS AN EQUATION.** Two DISTINCT 32-byte targets with the IDENTICAL deployed limb
vector. Not a birthday bound, not a grind: one byte pair, written down. -/
theorem capFoldLimbs_identifies_the_alias : capFoldLimbs zeroTarget = capFoldLimbs pTarget := by
  funext i
  fin_cases i <;> decide

/-- **THE FLOOR, PROVED FALSE** (`feedback-prove-the-floor-false`). The deployed cap-target encoder
is NOT injective, and the refutation is by exhibit, not by counting. -/
theorem capFoldLimbs_not_injective : ¬ Function.Injective capFoldLimbs := by
  intro h
  exact zeroTarget_ne_pTarget (h capFoldLimbs_identifies_the_alias)

/-! ### §1b — the alias is not one pair. It is a class, and every target has one.

The instance above would be a curiosity if it were special. It is not: `2P < 2^32`, so EVERY `u32`
has a sibling in its residue class, so every 32-byte value has at least `2^8` byte-distinct siblings
with the identical limb vector. §1b proves the general fact the instance is an instance of. -/

/-- `2P < 2^32` — the arithmetic that makes the alias class non-empty at EVERY chunk value, rather
than at 53.1% of them. -/
theorem two_P_lt_two_pow_32 : 2 * P < 2 ^ 32 := by decide

/-- `3P > 2^32` — so a residue class has at most three `u32` representatives, and the class sizes
are exactly 2 or 3. -/
theorem three_P_gt_two_pow_32 : 2 ^ 32 < 3 * P := by decide

/-- **EVERY chunk value has a sibling.** For any `v < 2^32` there is a `w < 2^32` with `w ≠ v` and
`w % P = v % P`. This is the general fact `capFoldLimbs_identifies_the_alias` is one instance of:
the deployed encoder is at least `2`-to-1 in EVERY coordinate, so at least `2^8`-to-1 overall. -/
theorem every_chunk_has_a_sibling (v : Nat) (hv : v < 2 ^ 32) :
    ∃ w, w < 2 ^ 32 ∧ w ≠ v ∧ w % P = v % P := by
  by_cases hlt : v < P
  · refine ⟨v + P, ?_, by omega, ?_⟩
    · have := two_P_lt_two_pow_32; omega
    · simp [Nat.add_mod_right]
  · refine ⟨v - P, by omega, ?_, ?_⟩
    · have : 0 < P := by decide
      omega
    · have hPv : P ≤ v := by omega
      have : v - P + P = v := by omega
      calc (v - P) % P = (v - P + P) % P := by simp [Nat.add_mod_right]
        _ = v % P := by rw [this]

/-- The pigeonhole that makes eight lanes hopeless before any chunking question is asked:
`P^8 < 2^256`. Cited from `FieldLanes9`, not re-proved. -/
theorem eight_lanes_cannot_carry_a_target : P ^ 8 < 2 ^ 256 := nine_lanes_is_the_minimum.1

/-! ## §2 — THE DEPLOYED LEAF ACCEPTS THE ALIAS.

`DeployedCapTree.leafFields` is the list the arity-7 chip absorbs. Its `target` slot is the fold's
image, so for the alias pair the two leaves are not merely hash-equal — they are the SAME LIST.
`leafFields_inj` is not violated; it never had anything to say. This is the ACCEPTED-BEFORE pole,
stated on the object the tree commits.

The deployed leaf is modelled here as the field list directly, so this file does not have to import
`DeployedCapTree`'s whole sponge surface to say what it needs to say. The shape is
`cap_root.rs:115-124` verbatim. -/

/-- The deployed 7-field leaf list, parameterised by the TARGET BYTES rather than by an already-folded
`ℤ` — the shape `DeployedCapTree.leafFields` has once `target` is instantiated at
`fold_bytes32 t`. `foldImage` stands for the `hash_many` the deployed code applies to the limbs; it
is left abstract precisely because the wound does not depend on it. -/
def deployedLeafFields (foldImage : (Fin 8 → Nat) → ℤ)
    (slot_hash auth_tag mask_lo mask_hi expiry breadstuff : ℤ) (t : Bytes32) : List ℤ :=
  [slot_hash, foldImage (capFoldLimbs t), auth_tag, mask_lo, mask_hi, expiry, breadstuff]

/-- **ACCEPTED BEFORE — and for ANY hash.** The deployed leaf field lists of the two DISTINCT
targets are equal, whatever `hash_many` is. The quantifier over `foldImage` is the point: this is
not a Poseidon2 collision and no choice of sponge avoids it, because the two targets reach the
sponge as the SAME input. -/
theorem deployedLeaf_accepts_the_alias
    (foldImage : (Fin 8 → Nat) → ℤ) (slot_hash auth_tag mask_lo mask_hi expiry breadstuff : ℤ) :
    deployedLeafFields foldImage slot_hash auth_tag mask_lo mask_hi expiry breadstuff zeroTarget
      = deployedLeafFields foldImage slot_hash auth_tag mask_lo mask_hi expiry breadstuff pTarget := by
  simp [deployedLeafFields, capFoldLimbs_identifies_the_alias]

/-! ## §3 — THE REPLACEMENT ENCODER.

`KeyLanes9.keyToLanes9` — base `2^29`, nine lanes, image exactly `2^256`, injective with a total
decoder. A `CellId` is an opaque 32-byte KEY, so this is the right one of the two nonets (the other,
`FieldLanes9.fieldToLanes9`, is for numeric field values and keeps the kernel's u64 ABI in lanes 0/1;
a cap target has no such ABI to preserve). Rust twin: `Faithful9::from_key_lanes9`. -/

/-- **THE CAP-TARGET NONET.** The deployed `capFoldLimbs` is replaced by this, and it is
`KeyLanes9.keyToLanes9` unchanged — a third encoder would be a third thing to drift. -/
def capTargetLanes9 (t : Bytes32) : Fin 9 → Nat := keyToLanes9 t

/-- **INJECTIVE**, inherited from `KeyLanes9.keyToLanes9_injective`. Not a hash bound and not a
birthday bound: distinct targets have distinct lane vectors, always. -/
theorem capTargetLanes9_injective : Function.Injective capTargetLanes9 :=
  keyToLanes9_injective

/-- The replacement SEPARATES the pair the deployed encoder identifies. -/
theorem capTargetLanes9_separates_the_alias :
    capTargetLanes9 zeroTarget ≠ capTargetLanes9 pTarget := fun h =>
  zeroTarget_ne_pTarget (capTargetLanes9_injective h)

/-! ## §4 — THE REPLACEMENT LEAF, AT AN ARITY THE DEPLOYED CHIP ADMITS.

Six scalar fields + nine target lanes = 15, and `15 ∉ CHIP_ADMITTED_ARITIES`. `DescriptorIR2` is
explicit that this is not negotiable from the emitter side and that the remedy is to pad up to the
next admitted arity, which is 16. The pad is a DOMAIN TAG (§5). -/

/-- The cap-leaf absorb domain tag, ASCII `CPL9`. It rides lane 0 of the arity-16 leaf block. Its
job is §5: keep the leaf block out of `nodeOf8`'s arity-16 domain. -/
def CAP_LEAF9_DOMAIN : ℤ := 0x43504C39

/-- **THE REPLACEMENT LEAF.** The 7-field `CapLeaf` with `target` widened from one folded felt to the
nine injective lanes. -/
structure CapLeaf9 where
  /-- The sort key: a Poseidon2 image of the (unique) c-list slot. Unchanged. -/
  slot_hash : ℤ
  /-- **The capability's target cell id, as NINE INJECTIVE LANES** — the field this file exists for.
  Was one felt, the image of a `2^8`-to-1 encoder. -/
  target : Fin 9 → ℤ
  /-- The `AuthRequired` tier (+ absorbed vk_hash for `Custom`), one felt. Unchanged. -/
  auth_tag : ℤ
  /-- `EffectMask` low 16 bits. Unchanged. -/
  mask_lo : ℤ
  /-- `EffectMask` high 16 bits. Unchanged. -/
  mask_hi : ℤ
  /-- Optional expiry height. Unchanged. -/
  expiry : ℤ
  /-- Optional breadstuff hash, still folded to one felt. ⚠ NAMED RESIDUAL, not repaired here: this
  field carries the SAME encoder wound as `target` did, at a smaller blast radius (a memo digest, not
  an authority target). The arity budget is spent at 16, so widening it too needs the breadstuff
  digest to be pre-absorbed through its own nonet block rather than inlined. Left one felt, and left
  SAID. -/
  breadstuff : ℤ
  deriving DecidableEq

/-- The nine target lanes as a list, in lane order. -/
def targetList (l : CapLeaf9) : List ℤ := List.ofFn l.target

theorem targetList_length (l : CapLeaf9) : (targetList l).length = 9 := by simp [targetList]

/-- **THE ARITY-16 LEAF ABSORB BLOCK**: `CPL9 ‖ slot_hash ‖ target[0..9] ‖ auth_tag ‖ mask_lo ‖
mask_hi ‖ expiry ‖ breadstuff`. -/
def capLeafFields9 (l : CapLeaf9) : List ℤ :=
  CAP_LEAF9_DOMAIN :: l.slot_hash :: (targetList l
    ++ [l.auth_tag, l.mask_lo, l.mask_hi, l.expiry, l.breadstuff])

/-- The block is exactly 16 lanes. -/
theorem capLeafFields9_length (l : CapLeaf9) : (capLeafFields9 l).length = 16 := by
  simp [capLeafFields9, targetList]

/-- **THE ARITY IS ADMITTED.** 16 is a root of the deployed chip's degree-7 admission product, so a
descriptor absorbing this block is provable at that row. 15 — the un-padded block — is not. -/
theorem capLeafFields9_arity_admitted :
    Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted 16 := by decide

/-- ⚑ And the un-padded block would have been UNPROVABLE. Stated so the pad reads as forced rather
than stylistic. -/
theorem fifteen_is_not_admitted :
    ¬ Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted 15 := by decide

/-- The block determines the whole leaf. The structural twin of `DeployedCapTree.leafFields_inj`, at
the new width. -/
theorem capLeafFields9_inj {l₁ l₂ : CapLeaf9} (h : capLeafFields9 l₁ = capLeafFields9 l₂) :
    l₁ = l₂ := by
  simp only [capLeafFields9, targetList, List.cons.injEq, true_and] at h
  obtain ⟨hslot, hrest⟩ := h
  have hlen : (List.ofFn l₁.target).length = (List.ofFn l₂.target).length := by simp
  obtain ⟨ht, hscalars⟩ := List.append_inj hrest hlen
  have htgt : l₁.target = l₂.target := List.ofFn_inj.mp ht
  simp only [List.cons.injEq, and_true] at hscalars
  cases l₁; cases l₂; simp_all

/-! ### §4a — THE POLE THE DEPLOYED LEAF CANNOT REACH.

§2 showed the deployed leaf list is EQUAL on the alias pair. Here the replacement's list DIFFERS —
on that pair, and on every byte-distinct pair. This is the REFUSED-AFTER, and it is a theorem about
the field list itself, so it holds BEFORE any sponge assumption: the two blocks the chip absorbs are
already distinct, which is strictly stronger than "their digests differ if the chip is collision
resistant" (a premise `VacuitySweepTeeth.compress8CR_false_babyBear` refutes at deployed BabyBear). -/

/-- Build the replacement leaf for a raw 32-byte target. -/
def leafOfTarget (slot_hash auth_tag mask_lo mask_hi expiry breadstuff : ℤ) (t : Bytes32) :
    CapLeaf9 :=
  { slot_hash, auth_tag, mask_lo, mask_hi, expiry, breadstuff
  , target := fun i => ((capTargetLanes9 t i : Nat) : ℤ) }

/-- **THE GENERAL FACT** (not the instance): byte-distinct targets give DISTINCT arity-16 leaf
blocks, for every setting of the other six fields. No hash assumption is used. -/
theorem capLeafFields9_separates_byte_distinct_targets
    (slot_hash auth_tag mask_lo mask_hi expiry breadstuff : ℤ) {t₁ t₂ : Bytes32} (hne : t₁ ≠ t₂) :
    capLeafFields9 (leafOfTarget slot_hash auth_tag mask_lo mask_hi expiry breadstuff t₁)
      ≠ capLeafFields9 (leafOfTarget slot_hash auth_tag mask_lo mask_hi expiry breadstuff t₂) := by
  intro h
  have hl := capLeafFields9_inj h
  have ht : (fun i => ((capTargetLanes9 t₁ i : Nat) : ℤ))
      = (fun i => ((capTargetLanes9 t₂ i : Nat) : ℤ)) := congrArg CapLeaf9.target hl
  refine hne (capTargetLanes9_injective ?_)
  funext i
  have := congrFun ht i
  exact_mod_cast this

/-- **REFUSED AFTER, on the exhibited pre-image.** The same pair §2 shows the deployed leaf accepts. -/
theorem capLeafFields9_refuses_the_alias
    (slot_hash auth_tag mask_lo mask_hi expiry breadstuff : ℤ) :
    capLeafFields9 (leafOfTarget slot_hash auth_tag mask_lo mask_hi expiry breadstuff zeroTarget)
      ≠ capLeafFields9 (leafOfTarget slot_hash auth_tag mask_lo mask_hi expiry breadstuff pTarget) :=
  capLeafFields9_separates_byte_distinct_targets _ _ _ _ _ _ zeroTarget_ne_pTarget

/-! ## §5 — THE PAD IS A DOMAIN TAG, AND IT HAS TO BE.

`Cap8Scheme.nodeOf8 l r = chipAbsorb8 (pack8 l r)` is ALSO an arity-16 absorb (`L8 ‖ R8`, sixteen
lanes). Padding the leaf to 16 with a zero would put a leaf block and an internal-node block in the
same absorb domain, which is how a leaf gets read as a node. Lane 0 of a node block is a digest lane
the tree computes; lane 0 of a leaf block is the fixed tag `CPL9`. Separation is then a lane-0
disequality, and it is decidable. -/

/-- An internal-node block, as `pack8` builds it: sixteen lanes, lane 0 being the left child's lane 0. -/
def nodeBlock (l r : Fin 8 → ℤ) : List ℤ := List.ofFn l ++ List.ofFn r

theorem nodeBlock_length (l r : Fin 8 → ℤ) : (nodeBlock l r).length = 16 := by
  simp [nodeBlock]

/-- **DOMAIN SEPARATION.** A leaf block and a node block whose left child's lane 0 is not the tag are
distinct as blocks — so the two arity-16 populations do not overlap. The hypothesis is the honest
one: it is what a domain tag BUYS, and it is discharged in the deployed tree by the tag being a
fixed constant no digest lane is pinned to. -/
theorem leaf_and_node_blocks_are_separated
    (lf : CapLeaf9) (l r : Fin 8 → ℤ) (h : l 0 ≠ CAP_LEAF9_DOMAIN) :
    capLeafFields9 lf ≠ nodeBlock l r := by
  intro heq
  have : (capLeafFields9 lf).getD 0 0 = (nodeBlock l r).getD 0 0 := by rw [heq]
  simp [capLeafFields9, nodeBlock, List.getD] at this
  exact h this.symm

/-! ## §6 — THE VERDICT, TWO-SIDED.

One theorem carrying both poles on the same pre-image, so a reader cannot take the repair on trust
from the fix's side alone. -/

/-- **THE VERDICT.** There exist two DISTINCT 32-byte cap targets such that

* the DEPLOYED leaf block is the same for both — for EVERY hash, because they reach it as the same
  limb vector — so the committed `capability_root` cannot tell them apart; and
* the REPLACEMENT leaf block differs, with no hash assumption used.

Read the first conjunct as the wound and the second as the repair's specification. Neither is a
statement about `circuit/src/cap_root.rs`, which is a twin and is not cut over yet. -/
theorem cap_target_verdict
    (foldImage : (Fin 8 → Nat) → ℤ) (slot_hash auth_tag mask_lo mask_hi expiry breadstuff : ℤ) :
    zeroTarget ≠ pTarget
    ∧ deployedLeafFields foldImage slot_hash auth_tag mask_lo mask_hi expiry breadstuff zeroTarget
        = deployedLeafFields foldImage slot_hash auth_tag mask_lo mask_hi expiry breadstuff pTarget
    ∧ capLeafFields9 (leafOfTarget slot_hash auth_tag mask_lo mask_hi expiry breadstuff zeroTarget)
        ≠ capLeafFields9 (leafOfTarget slot_hash auth_tag mask_lo mask_hi expiry breadstuff pTarget) :=
  ⟨zeroTarget_ne_pTarget,
   deployedLeaf_accepts_the_alias _ _ _ _ _ _ _,
   capLeafFields9_refuses_the_alias _ _ _ _ _ _⟩

#assert_axioms capFoldLimbs_identifies_the_alias
#assert_axioms capFoldLimbs_not_injective
#assert_axioms every_chunk_has_a_sibling
#assert_axioms deployedLeaf_accepts_the_alias
#assert_axioms capTargetLanes9_injective
#assert_axioms capLeafFields9_length
#assert_axioms capLeafFields9_arity_admitted
#assert_axioms fifteen_is_not_admitted
#assert_axioms capLeafFields9_inj
#assert_axioms capLeafFields9_separates_byte_distinct_targets
#assert_axioms leaf_and_node_blocks_are_separated
#assert_axioms cap_target_verdict

/-! ## §7 — Lean-COMPUTED protocol vectors.

The Rust twin (`circuit/tests/cap_leaf_target_lanes9_pins.rs`) recomputes these from
`Faithful9::from_key_lanes9` and refuses on disagreement. They are the only thing tying the two
sides together — there is no `@[export]` on this path and Rust does not call Lean here. Read the
Rust side as "case-tested against a verified spec", never as "verified". -/

def lanesOf (t : Bytes32) : List Nat := List.ofFn (capTargetLanes9 t)
def bytesOf (t : Bytes32) : List Nat := List.ofFn (fun i => (t i).1)

def ascendingTarget : Bytes32 := fun i => ⟨i.1, by omega⟩
def maxTarget : Bytes32 := fun _ => ⟨255, by decide⟩

end Dregg2.Circuit.CapLeafTargetLanes9
