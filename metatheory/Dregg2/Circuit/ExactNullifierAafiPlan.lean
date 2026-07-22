/-
# Dregg2.Circuit.ExactNullifierAafiPlan -- exact append-at-free-index nullifier plan

This is the additive semantic/geometry beachhead for moving the faithful hidden-note spend's
nullifier successor check INTO the Lean-authored AIR.  It does not modify the deployed descriptor.

The current `NullifierSet.faithful_root8_exact` is a sorted, densely compacted 4-ary tree.  A fresh
key inserted before an existing key shifts the complete suffix, so its successor cannot in general
be proved by one fixed Merkle path.  The efficient replacement is the indexed-Merkle-tree (IMT)
operation already proved generically in `IndexedMerkleTree`, instantiated here at the exact wire:

* real key = an explicit REAL tag followed by all sixteen little-endian `u16` limbs of the raw
  32-byte nullifier, lexicographically ordered (no one-felt or eight-to-one projection); BOT and
  TOP are tagged endpoints, so neither all-zero nor all-`ff` is reserved from the PRF range;
* value = all four little-endian `u16` limbs of the public `u64` value;
* leaf = `domain || addrTag || addr[16] || value[4] || nextTag || next[16]`;
* absence = one authenticated predecessor leaf satisfying `low.key < key < low.nextKey`;
* insert = update that predecessor's link in place, then append the new linked leaf at the
  authenticated free cursor.  These are TWO fixed depth-16 4-ary path rewrites.

The file proves the exact-key semantic spine (freshness, sortedness preservation, exact key-set
growth, and double-spend refusal), the append-at-free-index physical-list facts, and pins an explicit
straight-line state16 descriptor budget.  The additive companion descriptor instantiates these
objects with real domain-separated state16 leaf/node schedules and authenticates the cursor/count;
its rotated-state/runtime cutover remains deliberately gated.  No Rust mirror is made here.
-/

import Dregg2.Circuit.IndexedMerkleTree
import Dregg2.Circuit.FullStateChip
import Mathlib.Data.List.OfFn
import Mathlib.Order.PiLex
import Mathlib.Tactic

namespace Dregg2.Circuit.ExactNullifierAafiPlan

open Dregg2.Circuit.IndexedMerkleTree

set_option autoImplicit false

/-! ## 1. Exact logical IMT schema -/

def KEY_LIMBS : Nat := 16
def TAGGED_KEY_LIMBS : Nat := KEY_LIMBS + 1
def VALUE_LIMBS : Nat := 4
def ROOT_LANES : Nat := 8
def TREE_ARITY : Nat := 4
def TREE_DEPTH : Nat := 16
def U16_BOUND : ℤ := 65536

/-- Raw 32-byte nullifier as sixteen exact little-endian `u16` cells. -/
abbrev RawNullifier : Type := Fin KEY_LIMBS → ℤ

/-- The exact total order used by the pointer bracket; limb zero is most significant for the
ordering relation.  This order is only the map order: byte encoding remains little-endian. -/
abbrev RawNullifierKey : Type := Lex RawNullifier

/-- The IMT order key is one endpoint tag followed by the complete raw nullifier.  Tags are
`BOT = 0`, `REAL = 1`, and `TOP = 2`; endpoint payload lanes are canonically zero. -/
abbrev ExactKey : Type := Lex (Fin TAGGED_KEY_LIMBS → ℤ)

/-- Full public `u64` value as four exact little-endian `u16` cells. -/
abbrev RawValue : Type := Fin VALUE_LIMBS → ℤ

/-- The SAME generic IMT leaf proven in `IndexedMerkleTree`, instantiated at the tagged exact
key/value.
No parallel combinatorics or assumed sortedness is introduced. -/
abbrev ExactLeaf : Type := ImtLeaf ExactKey RawValue
abbrev ExactChain : Type := List ExactLeaf

def U16 (x : ℤ) : Prop := 0 ≤ x ∧ x < U16_BOUND
def CanonicalKey (k : RawNullifierKey) : Prop := ∀ i, U16 (ofLex k i)
def CanonicalValue (v : RawValue) : Prop := ∀ i, U16 (v i)

/-- Insert a tag ahead of all sixteen raw lanes. -/
def taggedKey (tag : ℤ) (raw : RawNullifierKey) : ExactKey :=
  toLex fun i =>
    if h : i.val = 0 then tag
    else ofLex raw ⟨i.val - 1, by
      have hi := i.isLt
      simp [TAGGED_KEY_LIMBS, KEY_LIMBS] at hi ⊢
      omega⟩

def rawZeroKey : RawNullifierKey := toLex (fun _ => 0)
def rawAllFfKey : RawNullifierKey := toLex (fun _ => 65535)

/-- Permanent endpoints.  Their raw payloads are zero by construction; REAL wraps the entire raw
256-bit domain without reservation. -/
def botKey : ExactKey := taggedKey 0 rawZeroKey
def realKey (raw : RawNullifierKey) : ExactKey := taggedKey 1 raw
def topKey : ExactKey := taggedKey 2 rawZeroKey

def CanonicalExactKey (k : ExactKey) : Prop :=
  k = botKey ∨ (∃ raw, k = realKey raw ∧ CanonicalKey raw) ∨ k = topKey

def rawKeyBlock (k : RawNullifierKey) : List ℤ := List.ofFn (ofLex k)
def exactKeyBlock (k : ExactKey) : List ℤ := List.ofFn (ofLex k)
def rawValueBlock (v : RawValue) : List ℤ := List.ofFn v

@[simp] theorem rawKeyBlock_length (k : RawNullifierKey) :
    (rawKeyBlock k).length = KEY_LIMBS := by simp [rawKeyBlock]

@[simp] theorem rawValueBlock_length (v : RawValue) :
    (rawValueBlock v).length = VALUE_LIMBS := by simp [rawValueBlock]

@[simp] theorem exactKeyBlock_length (k : ExactKey) :
    (exactKeyBlock k).length = TAGGED_KEY_LIMBS := by simp [exactKeyBlock]

/-- All 256 key bits survive the logical-to-wire block. -/
theorem rawKeyBlock_injective : Function.Injective rawKeyBlock := by
  intro a b h
  apply ofLex_inj.mp
  exact List.ofFn_injective h

/-- Wrapping a raw key as REAL loses no bit. -/
theorem realKey_injective : Function.Injective realKey := by
  intro a b h
  apply ofLex_inj.mp
  funext i
  let j : Fin TAGGED_KEY_LIMBS := ⟨i.val + 1, by
    have hi := i.isLt
    simp [TAGGED_KEY_LIMBS, KEY_LIMBS] at hi ⊢
    omega⟩
  have hj := congrFun (congrArg ofLex h) j
  simpa [realKey, taggedKey, j] using hj

/-- All 64 value bits survive the logical-to-wire block. -/
theorem rawValueBlock_injective : Function.Injective rawValueBlock :=
  List.ofFn_injective

/-- Domain tag for the exact linked nullifier leaf, ASCII `FNI2`. -/
def EXACT_LINKED_LEAF_DOMAIN : ℤ := 0x464e4932

/-- Exact state16 sponge preimage.  Its arity (39) is protocol geometry: domain, address tag/raw,
value, and successor tag/raw. -/
def exactLeafBlock (leaf : ExactLeaf) : List ℤ :=
  [EXACT_LINKED_LEAF_DOMAIN] ++ exactKeyBlock leaf.addr ++ rawValueBlock leaf.value ++
    exactKeyBlock leaf.nextAddr

@[simp] theorem exactLeafBlock_length (leaf : ExactLeaf) :
    (exactLeafBlock leaf).length = 39 := by
  simp [exactLeafBlock, TAGGED_KEY_LIMBS, KEY_LIMBS, VALUE_LIMBS]

/-- Logical absence brackets the REAL-wrapped full raw key. -/
def ExactAbsent (chain : ExactChain) (key : RawNullifierKey) : Prop :=
  ImtAbsent chain (realKey key)

/-- Logical exact insert is the deployed generic IMT insert at the full raw key/value. -/
noncomputable def exactInsert (chain : ExactChain) (key : RawNullifierKey)
    (value : RawValue) : ExactChain :=
  imtInsert chain (realKey key) value

/-- A valid exact pointer bracket excludes the full raw key from a sorted chain. -/
theorem exact_absent_excludes {chain : ExactChain} (hs : ImtSorted chain)
    {key : RawNullifierKey} (ha : ExactAbsent chain key) : realKey key ∉ imtAddrs chain :=
  imtAbsent_excludes hs ha

/-- The exact raw-key insertion preserves the linked sorted-chain invariant. -/
theorem exact_insert_preserves {chain : ExactChain} (hs : ImtSorted chain)
    {key : RawNullifierKey} {value : RawValue} (ha : ExactAbsent chain key) :
    ImtSorted (exactInsert chain key value) :=
  imtInsert_preserves hs ha

/-- The exact raw-key spine grows by precisely the fresh key: no ghost key and no lost key. -/
theorem mem_exact_insert {chain : ExactChain} {key : RawNullifierKey} {value : RawValue}
    (ha : ExactAbsent chain key) (x : ExactKey) :
    x ∈ imtAddrs (exactInsert chain key value) ↔ x = realKey key ∨ x ∈ imtAddrs chain :=
  mem_imtAddrs_imtInsert ha x

/-- Double-spend refusal at all 256 raw key bits. -/
theorem exact_double_spend_unsat {chain : ExactChain} (hs : ImtSorted chain)
    {key : RawNullifierKey} (hpresent : realKey key ∈ imtAddrs chain)
    (habsent : ExactAbsent chain key) : False :=
  imt_double_spend_unsat hs hpresent habsent

/-! ## 2. Physical AAFI operation: stable predecessor slot + append cursor -/

def lowAfter (low : ExactLeaf) (key : RawNullifierKey) : ExactLeaf :=
  { low with nextAddr := realKey key }

def appendedLeaf (low : ExactLeaf) (key : RawNullifierKey) (value : RawValue) : ExactLeaf :=
  { addr := realKey key, value := value, nextAddr := low.nextAddr }

/-- Physical append-order update.  The predecessor stays at `lowPosition`; the new leaf is placed
at the old list length, which is the free cursor. -/
def physicalInsert (before : List ExactLeaf) (lowPosition : Nat) (low : ExactLeaf)
    (key : RawNullifierKey) (value : RawValue) : List ExactLeaf :=
  before.set lowPosition (lowAfter low key) ++ [appendedLeaf low key value]

/-- The physical layout always grows by one slot; no sorted suffix is shifted. -/
theorem physicalInsert_length (before : List ExactLeaf) (lowPosition : Nat) (low : ExactLeaf)
    (key : RawNullifierKey) (value : RawValue) :
    (physicalInsert before lowPosition low key value).length = before.length + 1 := by
  simp [physicalInsert]

/-- The new leaf lands exactly at the pre-state free cursor (`before.length`). -/
theorem physicalInsert_appends_at_cursor (before : List ExactLeaf) (lowPosition : Nat)
    (low : ExactLeaf) (key : RawNullifierKey) (value : RawValue) :
    (physicalInsert before lowPosition low key value)[before.length]? =
      some (appendedLeaf low key value) := by
  simp [physicalInsert]

/-- When the supplied predecessor position is occupied, that exact physical slot is the only old
slot edited by the first AAFI leg. -/
theorem physicalInsert_updates_low (before : List ExactLeaf) (lowPosition : Nat)
    (low : ExactLeaf) (key : RawNullifierKey) (value : RawValue)
    (hpos : lowPosition < before.length) :
    (physicalInsert before lowPosition low key value)[lowPosition]? = some (lowAfter low key) := by
  have hset : lowPosition < (before.set lowPosition (lowAfter low key)).length := by
    simpa using hpos
  rw [physicalInsert, List.getElem?_append_left hset]
  exact List.getElem?_set_eq_of_lt _ hpos

/-- A compact semantic witness for the physical step.  `lowAt` binds the logical predecessor to an
occupied pre-state slot; `bracket` is exactly the two lexicographic compare gadgets. -/
structure PhysicalAafiStep (before after : List ExactLeaf) (key : RawNullifierKey)
    (value : RawValue) where
  lowPosition : Nat
  low : ExactLeaf
  lowAt : before[lowPosition]? = some low
  bracket : low.addr < realKey key ∧ realKey key < low.nextAddr
  after_eq : after = physicalInsert before lowPosition low key value

theorem PhysicalAafiStep.count_advances {before after : List ExactLeaf}
    {key : RawNullifierKey} {value : RawValue}
    (step : PhysicalAafiStep before after key value) : after.length = before.length + 1 := by
  rw [step.after_eq]
  exact physicalInsert_length _ _ _ _ _

theorem PhysicalAafiStep.appended_at_old_count {before after : List ExactLeaf}
    {key : RawNullifierKey} {value : RawValue}
    (step : PhysicalAafiStep before after key value) :
    after[before.length]? = some (appendedLeaf step.low key value) := by
  rcases step with ⟨lowPosition, low, lowAt, bracket, rfl⟩
  exact physicalInsert_appends_at_cursor _ lowPosition low _ _

/-! ## 3. Two fixed 4-ary depth-16 root rewrites -/

abbrev Root8 : Type := Fin ROOT_LANES → ℤ

structure PathStep4 where
  position : Fin TREE_ARITY
  siblings : Fin (TREE_ARITY - 1) → Root8

structure FixedPath4 where
  levels : List PathStep4
  depth_eq : levels.length = TREE_DEPTH

/-- Abstract one-level 4-ary compressor.  The realization must be the domain-separated 33-input
state16 schedule; keeping it a parameter prevents this semantic file from pretending the chip
correspondence is already wired. -/
abbrev Parent4 : Type := Root8 → PathStep4 → Root8

def recompose4 (parent : Parent4) (leaf : Root8) (path : FixedPath4) : Root8 :=
  path.levels.foldl parent leaf

/-- Interpret sixteen least-significant-first base-4 path digits as their physical leaf index. -/
def decodeBase4 (digits : Fin TREE_DEPTH → Fin TREE_ARITY) : Nat :=
  ∑ i, (digits i).val * TREE_ARITY ^ i.val

/-- One path proves an old leaf opens to `beforeRoot` and the replacement leaf, over the SAME
siblings and position digits, recomposes to `afterRoot`. -/
structure RootRewrite4 (parent : Parent4) (beforeRoot afterRoot : Root8) where
  path : FixedPath4
  oldLeaf : Root8
  newLeaf : Root8
  opens_before : recompose4 parent oldLeaf path = beforeRoot
  opens_after : recompose4 parent newLeaf path = afterRoot

/-- Complete two-path root witness for one exact AAFI insert.

Path one changes only the predecessor pointer and yields `middleRoot`.  Path two opens the empty
leaf at the authenticated free cursor in that middle root and appends the new exact leaf, yielding
`afterRoot`.  `cursor_index` is the explicit seam the state commitment must authenticate; otherwise
an empty but non-canonical physical slot would permit a second root for the same logical set. -/
structure ExactAafiRootWitness (leafDigest : ExactLeaf → Root8) (emptyLeaf : Root8)
    (parent : Parent4) (beforeRoot afterRoot : Root8) (key : RawNullifierKey)
    (value : RawValue) where
  low : ExactLeaf
  key_canonical : CanonicalKey key
  value_canonical : CanonicalValue value
  low_addr_canonical : CanonicalExactKey low.addr
  low_value_canonical : CanonicalValue low.value
  low_next_canonical : CanonicalExactKey low.nextAddr
  bracket : low.addr < realKey key ∧ realKey key < low.nextAddr
  middleRoot : Root8
  predecessorRewrite : RootRewrite4 parent beforeRoot middleRoot
  appendRewrite : RootRewrite4 parent middleRoot afterRoot
  predecessor_old : predecessorRewrite.oldLeaf = leafDigest low
  predecessor_new : predecessorRewrite.newLeaf = leafDigest (lowAfter low key)
  append_old_empty : appendRewrite.oldLeaf = emptyLeaf
  append_new : appendRewrite.newLeaf = leafDigest (appendedLeaf low key value)
  lowPosition : Nat
  lowPosition_in_capacity : lowPosition < TREE_ARITY ^ TREE_DEPTH
  lowPositionDigits : Fin TREE_DEPTH → Fin TREE_ARITY
  lowPosition_eq_digits : lowPosition = decodeBase4 lowPositionDigits
  predecessor_positions_are_lowPosition : ∀ i,
    predecessorRewrite.path.levels[i.val]?.map (·.position) = some (lowPositionDigits i)
  cursor : Nat
  cursor_in_capacity : cursor < TREE_ARITY ^ TREE_DEPTH
  /-- Base-4 digits of `cursor`, least-significant first; the descriptor wires these sixteen digits
  to `appendRewrite.path.position`. -/
  cursorDigits : Fin TREE_DEPTH → Fin TREE_ARITY
  cursor_eq_digits : cursor = decodeBase4 cursorDigits
  append_positions_are_cursor : ∀ i,
    appendRewrite.path.levels[i.val]?.map (·.position) = some (cursorDigits i)

/-- The middle root is not a host seam: it is simultaneously the result of path one and the input
opened by path two. -/
theorem ExactAafiRootWitness.root_chain_is_atomic
    {leafDigest : ExactLeaf → Root8} {emptyLeaf : Root8} {parent : Parent4}
    {beforeRoot afterRoot : Root8} {key : RawNullifierKey} {value : RawValue}
    (w : ExactAafiRootWitness leafDigest emptyLeaf parent beforeRoot afterRoot key value) :
    recompose4 parent w.predecessorRewrite.newLeaf w.predecessorRewrite.path = w.middleRoot ∧
      recompose4 parent w.appendRewrite.oldLeaf w.appendRewrite.path = w.middleRoot ∧
      recompose4 parent w.appendRewrite.newLeaf w.appendRewrite.path = afterRoot := by
  exact ⟨w.predecessorRewrite.opens_after, w.appendRewrite.opens_before,
    w.appendRewrite.opens_after⟩

/-! ## 4. Straight-line descriptor geometry and lookup budget

This is the deliberately simple row-per-tree-level plan, matching the existing FNSP descriptor's
fixed sixteen rows and unguarded lookup grammar.  It is an upper-bound implementation plan, not a
claim that no width/time trade is possible.

Four node chains are necessary on two paths: old/new predecessor roots and empty/new append roots.
Each 4-ary node hashes `domain || children[4][8]` = 33 inputs: nine rate-four absorbs plus squeeze,
ten state16 permutations.  Three nonconstant linked leaves (low-old, low-new, appended) each hash
39 inputs: ten absorbs plus squeeze, eleven permutations.  The empty leaf is a protocol constant.

Because IR2 lookups are currently unguarded, every lookup site fires on all sixteen rows.  Thus the
73 state16 sites below mean 1,168 table events in this straight-line shape.  A segmented/guarded
lookup grammar could trade width for height later without changing the semantics above.
-/

def SPONGE_RATE : Nat := 4
def LEAF_PREIMAGE_INPUTS : Nat := 1 + TAGGED_KEY_LIMBS + VALUE_LIMBS + TAGGED_KEY_LIMBS
def LEAF_SPONGE_STEPS : Nat := (LEAF_PREIMAGE_INPUTS + SPONGE_RATE - 1) / SPONGE_RATE + 1
def NODE_PREIMAGE_INPUTS : Nat := 1 + TREE_ARITY * ROOT_LANES
def NODE_SPONGE_STEPS : Nat := (NODE_PREIMAGE_INPUTS + SPONGE_RATE - 1) / SPONGE_RATE + 1
def ROOT_RECOMPOSITION_CHAINS : Nat := 4
def NONCONSTANT_LEAVES : Nat := 3
def NODE_STATE16_SITES_PER_ROW : Nat := ROOT_RECOMPOSITION_CHAINS * NODE_SPONGE_STEPS
def LEAF_STATE16_SITES_PER_ROW : Nat := NONCONSTANT_LEAVES * LEAF_SPONGE_STEPS
def INCREMENTAL_STATE16_SITES_PER_ROW : Nat :=
  NODE_STATE16_SITES_PER_ROW + LEAF_STATE16_SITES_PER_ROW
def INCREMENTAL_STATE16_EVENTS : Nat := TREE_DEPTH * INCREMENTAL_STATE16_SITES_PER_ROW

/-- A raw-u16 lex compare reuses its two 16-limb operands and adds sixteen one-hot selectors plus
one 16-bit strict-difference witness. -/
def LEX16_AUX_WIDTH : Nat := KEY_LIMBS + 1
def LEX16_GATE_COUNT : Nat := KEY_LIMBS + 1 + (KEY_LIMBS - 1) + 1
def LEX16_RANGE_SITES : Nat := 1
def BRACKET_COMPARE_COUNT : Nat := 2

/-- New unguarded range16 lookup sites: the predecessor's 16+4+16 exact limbs, the four cursor
limbs, and one strict-difference witness for each half of the bracket.  The spend key/value are
already range-bound by FNSP-v2 and therefore are not double-counted. -/
def PREDECESSOR_U16_RANGE_SITES : Nat := KEY_LIMBS + VALUE_LIMBS + KEY_LIMBS
def CURSOR_U16_RANGE_SITES : Nat := 4
def INCREMENTAL_RANGE16_SITES_PER_ROW : Nat :=
  PREDECESSOR_U16_RANGE_SITES + CURSOR_U16_RANGE_SITES +
    BRACKET_COMPARE_COUNT * LEX16_RANGE_SITES
def INCREMENTAL_RANGE16_EVENTS : Nat := TREE_DEPTH * INCREMENTAL_RANGE16_SITES_PER_ROW

/-- Incremental main-trace width upper bound when grafted onto FNSP-v2 without column packing:

* predecessor exact fields: (tag + 16) + 4 + (tag + 16) = 38;
* four running roots: 32;
* two 4-ary paths' siblings and positions: 48 + 4;
* two exact lex-compare auxiliaries: 34;
* three leaf state schedules: 3 * 11 * 16 = 528;
* four node state schedules: 4 * 10 * 16 = 640;
* authenticated cursor limbs: 4.
-/
def INCREMENTAL_TRACE_WIDTH_UPPER : Nat :=
  (TAGGED_KEY_LIMBS + VALUE_LIMBS + TAGGED_KEY_LIMBS) +
  (ROOT_RECOMPOSITION_CHAINS * ROOT_LANES) +
  (2 * (TREE_ARITY - 1) * ROOT_LANES) + 4 +
  (BRACKET_COMPARE_COUNT * LEX16_AUX_WIDTH) +
  (NONCONSTANT_LEAVES * LEAF_SPONGE_STEPS * 16) +
  (ROOT_RECOMPOSITION_CHAINS * NODE_SPONGE_STEPS * 16) + 4

def FNSP_V2_TRACE_WIDTH : Nat := 1023
def FNSP_V2_STATE16_SITES_PER_ROW : Nat := 50
def FNSP_V2_RANGE16_SITES_PER_ROW : Nat := 132
def FNSP_V3_TRACE_WIDTH_UPPER : Nat := FNSP_V2_TRACE_WIDTH + INCREMENTAL_TRACE_WIDTH_UPPER
def FNSP_V3_STATE16_SITES_PER_ROW : Nat :=
  FNSP_V2_STATE16_SITES_PER_ROW + INCREMENTAL_STATE16_SITES_PER_ROW
def FNSP_V3_STATE16_EVENTS : Nat := TREE_DEPTH * FNSP_V3_STATE16_SITES_PER_ROW
def FNSP_V3_RANGE16_SITES_PER_ROW : Nat :=
  FNSP_V2_RANGE16_SITES_PER_ROW + INCREMENTAL_RANGE16_SITES_PER_ROW
def FNSP_V3_RANGE16_EVENTS : Nat := TREE_DEPTH * FNSP_V3_RANGE16_SITES_PER_ROW

#guard KEY_LIMBS == 16
#guard VALUE_LIMBS == 4
#guard TREE_ARITY ^ TREE_DEPTH == 4294967296
#guard LEAF_PREIMAGE_INPUTS == 39
#guard LEAF_SPONGE_STEPS == 11
#guard NODE_PREIMAGE_INPUTS == 33
#guard NODE_SPONGE_STEPS == 10
#guard NODE_STATE16_SITES_PER_ROW == 40
#guard LEAF_STATE16_SITES_PER_ROW == 33
#guard INCREMENTAL_STATE16_SITES_PER_ROW == 73
#guard INCREMENTAL_STATE16_EVENTS == 1168
#guard LEX16_AUX_WIDTH == 17
#guard LEX16_GATE_COUNT == 33
#guard INCREMENTAL_RANGE16_SITES_PER_ROW == 42
#guard INCREMENTAL_RANGE16_EVENTS == 672
#guard INCREMENTAL_TRACE_WIDTH_UPPER == 1328
#guard FNSP_V3_TRACE_WIDTH_UPPER == 2351
#guard FNSP_V3_STATE16_SITES_PER_ROW == 123
#guard FNSP_V3_STATE16_EVENTS == 1968
#guard FNSP_V3_RANGE16_SITES_PER_ROW == 174
#guard FNSP_V3_RANGE16_EVENTS == 2784

/-! ## 5. Non-vacuity and full-domain tagged endpoints -/

def firstKeyLimb : Fin KEY_LIMBS := ⟨0, by decide⟩
def lastKeyLimb : Fin KEY_LIMBS := ⟨15, by decide⟩

def keyOne : RawNullifierKey := toLex (fun i => if i = lastKeyLimb then 1 else 0)
def zeroValue : RawValue := fun _ => 0

def firstTaggedLimb : Fin TAGGED_KEY_LIMBS := ⟨0, by decide⟩

/-- BOT is below every possible raw PRF image because the first compared lane is the tag. -/
theorem botKey_lt_realKey (raw : RawNullifierKey) : botKey < realKey raw := by
  refine ⟨firstTaggedLimb, fun j hj => ?_, ?_⟩
  · have hz : j.val < firstTaggedLimb.val := hj
    simp [firstTaggedLimb] at hz
  · norm_num [botKey, realKey, taggedKey, firstTaggedLimb]

/-- Every possible raw PRF image is below TOP, again solely by the explicit tag. -/
theorem realKey_lt_topKey (raw : RawNullifierKey) : realKey raw < topKey := by
  refine ⟨firstTaggedLimb, fun j hj => ?_, ?_⟩
  · have hz : j.val < firstTaggedLimb.val := hj
    simp [firstTaggedLimb] at hz
  · norm_num [botKey, realKey, topKey, taggedKey, firstTaggedLimb]

theorem botKey_lt_topKey : botKey < topKey :=
  (botKey_lt_realKey rawZeroKey).trans (realKey_lt_topKey rawZeroKey)

/-- Both former raw endpoints are ordinary REAL keys.  No FNF2 output is protocol-reserved. -/
theorem full_raw_domain_between_endpoints :
    (botKey < realKey rawZeroKey ∧ realKey rawZeroKey < topKey) ∧
      (botKey < realKey rawAllFfKey ∧ realKey rawAllFfKey < topKey) := by
  exact ⟨⟨botKey_lt_realKey _, realKey_lt_topKey _⟩,
    ⟨botKey_lt_realKey _, realKey_lt_topKey _⟩⟩

def exactGenesis : ExactChain :=
  [{ addr := botKey, value := zeroValue, nextAddr := topKey }]

theorem exactGenesis_sorted : ImtSorted exactGenesis :=
  botKey_lt_topKey

theorem keyOne_absent_at_genesis : ExactAbsent exactGenesis keyOne := by
  exact ⟨{ addr := botKey, value := zeroValue, nextAddr := topKey }, by simp [exactGenesis],
    botKey_lt_realKey keyOne, realKey_lt_topKey keyOne⟩

theorem rawZero_absent_at_genesis : ExactAbsent exactGenesis rawZeroKey := by
  exact ⟨{ addr := botKey, value := zeroValue, nextAddr := topKey }, by simp [exactGenesis],
    botKey_lt_realKey rawZeroKey, realKey_lt_topKey rawZeroKey⟩

theorem rawAllFf_absent_at_genesis : ExactAbsent exactGenesis rawAllFfKey := by
  exact ⟨{ addr := botKey, value := zeroValue, nextAddr := topKey }, by simp [exactGenesis],
    botKey_lt_realKey rawAllFfKey, realKey_lt_topKey rawAllFfKey⟩

theorem keyOne_insert_is_sorted :
    ImtSorted (exactInsert exactGenesis keyOne zeroValue) :=
  exact_insert_preserves exactGenesis_sorted keyOne_absent_at_genesis

theorem keyOne_present_after_insert :
    realKey keyOne ∈ imtAddrs (exactInsert exactGenesis keyOne zeroValue) := by
  rw [mem_exact_insert keyOne_absent_at_genesis (realKey keyOne)]
  exact Or.inl rfl

/-- The false pole: after the exact 256-bit key is inserted, no valid predecessor bracket can
claim it absent. -/
theorem keyOne_cannot_be_reinserted :
    ¬ ExactAbsent (exactInsert exactGenesis keyOne zeroValue) keyOne := by
  intro ha
  exact exact_double_spend_unsat keyOne_insert_is_sorted keyOne_present_after_insert ha

#assert_axioms rawKeyBlock_injective
#assert_axioms realKey_injective
#assert_axioms rawValueBlock_injective
#assert_axioms full_raw_domain_between_endpoints
#assert_axioms rawZero_absent_at_genesis
#assert_axioms rawAllFf_absent_at_genesis
#assert_axioms exact_absent_excludes
#assert_axioms exact_insert_preserves
#assert_axioms mem_exact_insert
#assert_axioms exact_double_spend_unsat
#assert_axioms physicalInsert_length
#assert_axioms physicalInsert_appends_at_cursor
#assert_axioms PhysicalAafiStep.count_advances
#assert_axioms ExactAafiRootWitness.root_chain_is_atomic
#assert_axioms keyOne_insert_is_sorted
#assert_axioms keyOne_cannot_be_reinserted

end Dregg2.Circuit.ExactNullifierAafiPlan
