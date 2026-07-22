/-
# ExactNullifierAafiRotatedStateHashPathHonest

An independently checkable hash/path witness for the hardest exact-AAFI boundary case:

  canonical BOT-only genesis  --insert REAL(ffff..ffff), value 0-->  successor root.

The two physical rewrites use the genuine domain-separated linked-leaf and four-ary node meanings.
The append proof opens physical slot one: its first sibling is the already-rewritten BOT leaf and
all remaining siblings are the canonical empty-subtree roots.  Thus the predecessor-new root and
append-empty root are not merely assigned the same value; their recompositions are propositionally
equal before either is connected to an FNS3 checkpoint.

No descriptor artifact, registry entry, verifier key, or Rust mirror is emitted here.
-/

import Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateHonest
import Mathlib.Tactic

namespace Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateHashPathHonest

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit
open Dregg2.Circuit.ExactNullifierAafiPlan
open Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan
open Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateRefine
open Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateHonest

set_option autoImplicit false

/-! ## 1. Actual genesis-to-all-ff linked leaves -/

/-- The exact inserted value used by this boundary witness.  Zero is not a projection: it is the
complete four-u16 encoding of the chosen public `u64` value. -/
def ffInsertedValue : RawValue := zeroValue

def ffOldLow : ExactLeaf := exactGenesisLeaf

def ffLowNew : ExactLeaf := lowAfter ffOldLow rawAllFfKey

def ffAppended : ExactLeaf := appendedLeaf ffOldLow rawAllFfKey ffInsertedValue

def ffOldDigest : Root8 := exactLeafDigestReal ffOldLow
def ffLowNewDigest : Root8 := exactLeafDigestReal ffLowNew
def ffAppendedDigest : Root8 := exactLeafDigestReal ffAppended

theorem ff_key_is_strictly_bracketed :
    ffOldLow.addr < realKey rawAllFfKey ∧ realKey rawAllFfKey < ffOldLow.nextAddr := by
  exact ⟨botKey_lt_realKey _, realKey_lt_topKey _⟩

theorem ff_value_is_canonical : CanonicalValue ffInsertedValue := by
  intro i
  simp [ffInsertedValue, zeroValue, U16, U16_BOUND]

/-! ## 2. Canonical physical paths -/

/-- At every level above a leftmost occupied subtree, the other three children are canonical
empty subtrees of exactly that level. -/
def emptyLeftStep (level : Nat) : PathStep4 where
  position := ⟨0, by decide⟩
  siblings := fun _ => exactEmptySubtreeRoot level

/-- The slot-one opening after the predecessor rewrite.  Sibling zero is necessarily the updated
BOT leaf; siblings two and three remain canonical empty leaves. -/
def appendSlotOneStep : PathStep4 where
  position := ⟨1, by decide⟩
  siblings := fun i => if i.val = 0 then ffLowNewDigest else exactEmptySubtreeRoot 0

/-- Bottom-up leftmost path of `depth` levels. -/
def predecessorLevels : Nat → List PathStep4
  | 0 => []
  | depth + 1 => predecessorLevels depth ++ [emptyLeftStep depth]

/-- Bottom-up slot-one path.  After its first level it is the same leftmost path as the updated
predecessor subtree. -/
def appendLevels : Nat → List PathStep4
  | 0 => []
  | 1 => [appendSlotOneStep]
  | depth + 2 => appendLevels (depth + 1) ++ [emptyLeftStep (depth + 1)]

@[simp] theorem predecessorLevels_length (depth : Nat) :
    (predecessorLevels depth).length = depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [predecessorLevels, ih]

@[simp] theorem appendLevels_length (depth : Nat) :
    (appendLevels depth).length = depth := by
  cases depth with
  | zero => rfl
  | succ depth =>
      induction depth with
      | zero => rfl
      | succ depth ih => simp [appendLevels, ih]

def ffPredecessorPath : FixedPath4 where
  levels := predecessorLevels TREE_DEPTH
  depth_eq := predecessorLevels_length TREE_DEPTH

def ffAppendPath : FixedPath4 where
  levels := appendLevels TREE_DEPTH
  depth_eq := appendLevels_length TREE_DEPTH

/-! ## 3. Four genuine root chains and their atomic middle weld -/

def ffPriorRoot : Root8 :=
  recompose4 exactParent4Real ffOldDigest ffPredecessorPath

def ffMiddleRoot : Root8 :=
  recompose4 exactParent4Real ffLowNewDigest ffPredecessorPath

def ffAppendEmptyRoot : Root8 :=
  recompose4 exactParent4Real exactEmptyLeafReal ffAppendPath

def ffSuccessorRoot : Root8 :=
  recompose4 exactParent4Real ffAppendedDigest ffAppendPath

/-- The first append node has exactly the same ordered children as the first updated-predecessor
node: `[lowNew, empty, empty, empty]`. -/
theorem append_first_parent_eq :
    exactParent4Real exactEmptyLeafReal appendSlotOneStep =
      exactParent4Real ffLowNewDigest (emptyLeftStep 0) := by
  apply congrArg fullStateHash8
  simp [exactNodeBlock, exactChildren4, appendSlotOneStep, emptyLeftStep,
    siblingIndex0, siblingIndex1, siblingIndex2, exactEmptySubtreeRoot]

theorem exactParent_emptyLeft_eq (current : Root8) (level : Nat) :
    exactParent4Real current (emptyLeftStep level) =
      exactNodeDigestList [current, exactEmptySubtreeRoot level,
        exactEmptySubtreeRoot level, exactEmptySubtreeRoot level] := by
  apply congrArg fullStateHash8
  simp [exactNodeBlock, exactNodeDigestList, exactChildren4, emptyLeftStep]

theorem append_empty_fold_eq : ∀ depth : Nat,
    (appendLevels (depth + 1)).foldl exactParent4Real exactEmptyLeafReal =
      (predecessorLevels (depth + 1)).foldl exactParent4Real ffLowNewDigest := by
  intro depth
  induction depth with
  | zero =>
      simpa [appendLevels, predecessorLevels] using append_first_parent_eq
  | succ depth ih =>
      simp only [appendLevels, predecessorLevels, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      rw [ih]
      simp [predecessorLevels, List.foldl_append]

theorem predecessor_old_fold_eq_genesis : ∀ depth : Nat,
    (predecessorLevels depth).foldl exactParent4Real ffOldDigest = exactGenesisRoot depth := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [predecessorLevels, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih, exactParent_emptyLeft_eq]
      rfl

/-- The two independently described rewrites meet at one actual middle root. -/
theorem ff_middle_roots_equal : ffAppendEmptyRoot = ffMiddleRoot := by
  simpa [ffAppendEmptyRoot, ffMiddleRoot, ffAppendPath, ffPredecessorPath, recompose4,
    TREE_DEPTH] using append_empty_fold_eq 15

/-- The predecessor-old chain is the canonical physical BOT-only genesis root, not an arbitrary
caller-supplied root. -/
theorem ff_prior_is_logical_genesis : ffPriorRoot = logicalEmptyAccumulatorRoot := by
  simpa [ffPriorRoot, ffPredecessorPath, recompose4, logicalEmptyAccumulatorRoot,
    TREE_DEPTH] using predecessor_old_fold_eq_genesis 16

/-! ## 4. Semantic two-rewrite witness -/

def ffRootWitness : ExactAafiRootWitness exactLeafDigestReal exactEmptyLeafReal
    exactParent4Real ffPriorRoot ffSuccessorRoot rawAllFfKey ffInsertedValue where
  low := ffOldLow
  key_canonical := by
    intro i
    simp [rawAllFfKey, U16, U16_BOUND]
  value_canonical := ff_value_is_canonical
  low_addr_canonical := Or.inl rfl
  low_value_canonical := by
    intro i
    simp [ffOldLow, exactGenesisLeaf, zeroValue, U16, U16_BOUND]
  low_next_canonical := Or.inr (Or.inr rfl)
  bracket := ff_key_is_strictly_bracketed
  middleRoot := ffMiddleRoot
  predecessorRewrite :=
    { path := ffPredecessorPath
      oldLeaf := ffOldDigest
      newLeaf := ffLowNewDigest
      opens_before := rfl
      opens_after := rfl }
  appendRewrite :=
    { path := ffAppendPath
      oldLeaf := exactEmptyLeafReal
      newLeaf := ffAppendedDigest
      opens_before := ff_middle_roots_equal
      opens_after := rfl }
  predecessor_old := rfl
  predecessor_new := rfl
  append_old_empty := rfl
  append_new := rfl
  lowPosition := 0
  lowPosition_in_capacity := by norm_num [TREE_ARITY, TREE_DEPTH]
  lowPositionDigits := fun _ => ⟨0, by decide⟩
  lowPosition_eq_digits := by simp [decodeBase4]
  predecessor_positions_are_lowPosition := by
    intro i
    fin_cases i <;> rfl
  cursor := 1
  cursor_in_capacity := by norm_num [TREE_ARITY, TREE_DEPTH]
  cursorDigits := fun i => if i.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  cursor_eq_digits := by
    decide
  append_positions_are_cursor := by
    intro i
    fin_cases i <;> rfl

theorem ff_root_chain_is_atomic :
    recompose4 exactParent4Real ffRootWitness.predecessorRewrite.newLeaf
        ffRootWitness.predecessorRewrite.path = ffRootWitness.middleRoot ∧
      recompose4 exactParent4Real ffRootWitness.appendRewrite.oldLeaf
        ffRootWitness.appendRewrite.path = ffRootWitness.middleRoot ∧
      recompose4 exactParent4Real ffRootWitness.appendRewrite.newLeaf
        ffRootWitness.appendRewrite.path = ffSuccessorRoot := by
  exact ffRootWitness.root_chain_is_atomic

#assert_axioms ff_middle_roots_equal
#assert_axioms ff_prior_is_logical_genesis
#assert_axioms ff_root_chain_is_atomic

end Dregg2.Circuit.Emit.ExactNullifierAafiRotatedStateHashPathHonest
