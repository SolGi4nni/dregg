/-
# Dregg2.Circuit.CommitmentTreeWide -- faithful wide note-tree authority

This is the Lean-authored semantics of `commit/src/poseidon2_tree.rs`'s
`Poseidon2NoteTree16`:

* a 32-byte commitment is injectively split into sixteen little-endian `u16`
  limbs (each already canonical in BabyBear);
* leaf, empty-leaf, and internal-node hashing use distinct in-band domains;
* every hash absorbs through the deployed rate-4 Poseidon2 sponge and squeezes
  eight rate lanes; no one-felt intermediate exists;
* membership replay rejects a mismatched leaf, malformed path lengths, a
  sibling count other than three, and positions outside `0..3`.

`Poseidon2BabyBearW16.perm` is the existing KAT-locked Lean implementation of
the deployed Rust permutation.  Concrete guards at the bottom are therefore
Lean-computed protocol vectors, not constants copied from the Rust runtime.
-/
import Dregg2.Circuit.Poseidon2BabyBearW16
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Circuit.CommitmentTreeWide

open Dregg2.Circuit.Poseidon2BabyBearW16 (P fadd perm)

set_option autoImplicit false

/-! ## Exact byte carrier -/

abbrev Byte := Fin 256
abbrev Bytes32 := Fin 32 → Byte
abbrev Lanes16 := Fin 16 → Fin P
abbrev Digest8 := List Nat

private def evenByte (i : Fin 16) : Fin 32 := ⟨2 * i.1, by omega⟩
private def oddByte (i : Fin 16) : Fin 32 := ⟨2 * i.1 + 1, by omega⟩

/-- The exact deployed codec: lane `i = b[2i] + 256*b[2i+1]`.
Both bytes are below 256, so the limb is below `2^16 < BabyBear.P`; no field
reduction and hence no `x` / `x+p` alias is possible. -/
def commitmentToLanes16 (bytes : Bytes32) : Lanes16 := fun i =>
  ⟨(bytes (evenByte i)).1 + 256 * (bytes (oddByte i)).1, by
    have hlo := (bytes (evenByte i)).2
    have hhi := (bytes (oddByte i)).2
    simp only [P]
    omega⟩

private def lowByte (lane : Fin P) : Byte :=
  ⟨lane.1 % 256, Nat.mod_lt _ (by decide)⟩

private def highByte (lane : Fin P) : Byte :=
  ⟨(lane.1 / 256) % 256, Nat.mod_lt _ (by decide)⟩

private theorem unpackHigh (lo hi : Byte) :
    (lo.1 + 256 * hi.1) / 256 % 256 = hi.1 := by
  rw [Nat.mul_comm 256 hi.1, Nat.add_mul_div_right lo.1 hi.1 (by decide)]
  rw [Nat.div_eq_of_lt lo.2, Nat.zero_add, Nat.mod_eq_of_lt hi.2]

/-- Explicit inverse of the sixteen-limb codec. -/
def lanes16ToCommitment (lanes : Lanes16) : Bytes32 := fun i =>
  if h : i.1 % 2 = 0 then
    lowByte (lanes ⟨i.1 / 2, by omega⟩)
  else
    highByte (lanes ⟨i.1 / 2, by omega⟩)

/-- The byte-to-limb codec has an actual left inverse, not merely a width
claim.  Consequently the raw 256-bit commitment reaches the hash intact. -/
theorem lanes16ToCommitment_commitmentToLanes16 (bytes : Bytes32) :
    lanes16ToCommitment (commitmentToLanes16 bytes) = bytes := by
  funext i
  fin_cases i <;>
    simp [lanes16ToCommitment, commitmentToLanes16, lowByte, highByte,
      evenByte, oddByte, Fin.ext_iff, Nat.add_mod, unpackHigh]

theorem commitmentToLanes16_injective : Function.Injective commitmentToLanes16 := by
  intro a b h
  have := congrArg lanes16ToCommitment h
  simpa [lanes16ToCommitment_commitmentToLanes16] using this

/-- Canonical list form consumed by the sponge semantics. -/
def lanes16List (lanes : Lanes16) : List Nat := List.ofFn (fun i => (lanes i).1)

theorem lanes16List_length (lanes : Lanes16) : (lanes16List lanes).length = 16 := by
  simp [lanes16List]

/-! ## Deployed eight-lane sponge -/

def NOTE_LEAF_DOMAIN : Nat := 0x4e4c4638
def NOTE_NODE_DOMAIN : Nat := 0x4e4e4438
def NOTE_EMPTY_DOMAIN : Nat := 0x4e454d38

private def initialState (inputLength : Nat) : List Nat :=
  (List.range 16).map (fun i => if i = 4 then inputLength % P else 0)

private def absorbChunk (state chunk : List Nat) : List Nat :=
  perm ((List.range 16).map (fun i =>
    if i < chunk.length then fadd (state.getD i 0) (chunk.getD i 0)
    else state.getD i 0))

private def chunks4 (inputs : List Nat) : List (List Nat) := inputs.toChunks 4

/-- Bit-level semantic image of Rust `hash_many_8`: length in capacity lane 4,
rate-4 additive absorption with one permutation per chunk, then
squeeze-four / permute / squeeze-four. -/
def hashMany8Real (inputs : List Nat) : Digest8 :=
  let final := (chunks4 inputs).foldl absorbChunk (initialState inputs.length)
  final.take 4 ++ (perm final).take 4

def hashTo8 (domain : Nat) (inputs : List Nat) : Digest8 :=
  hashMany8Real (domain :: inputs)

def noteLeaf16 (leaf : Lanes16) : Digest8 :=
  hashTo8 NOTE_LEAF_DOMAIN (lanes16List leaf)

def emptyNoteLeaf8 : Digest8 := hashTo8 NOTE_EMPTY_DOMAIN []

def noteNode8 (children : List Digest8) : Digest8 :=
  hashTo8 NOTE_NODE_DOMAIN children.flatten

/-! ## Tree and fail-closed membership semantics -/

def leafDigestAt (leaves : List Lanes16) (index : Nat) : Digest8 :=
  match leaves[index]? with
  | some leaf => noteLeaf16 leaf
  | none => emptyNoteLeaf8

def nodeAt (leaves : List Lanes16) : Nat → Nat → Digest8
  | 0, index => leafDigestAt leaves index
  | level + 1, index =>
      noteNode8 [nodeAt leaves level (4 * index),
        nodeAt leaves level (4 * index + 1),
        nodeAt leaves level (4 * index + 2),
        nodeAt leaves level (4 * index + 3)]

def root (depth : Nat) (leaves : List Lanes16) : Digest8 := nodeAt leaves depth 0

structure MembershipProof where
  leaf : Lanes16
  siblings : List (List Digest8)
  positions : List Nat

private def insertCurrent (current : Digest8) (siblings : List Digest8)
    (position : Nat) : List Digest8 :=
  siblings.take position ++ [current] ++ siblings.drop position

private def recomposePath : Digest8 → List (List Digest8) → List Nat → Option Digest8
  | current, [], [] => some current
  | current, siblings :: rest, position :: positions =>
      if siblings.length = 3 ∧ position < 4 then
        recomposePath (noteNode8 (insertCurrent current siblings position)) rest positions
      else none
  | _, _, _ => none

def recomposeMembership (leaf : Lanes16) (proof : MembershipProof) : Option Digest8 :=
  if proof.leaf = leaf then
    recomposePath (noteLeaf16 leaf) proof.siblings proof.positions
  else none

def verifyMembership (rootDigest : Digest8) (leaf : Lanes16)
    (proof : MembershipProof) : Bool :=
  recomposeMembership leaf proof = some rootDigest

theorem recompose_mismatched_leaf (claimed : Lanes16) (proof : MembershipProof)
    (h : proof.leaf ≠ claimed) : recomposeMembership claimed proof = none := by
  simp [recomposeMembership, h]

theorem verify_mismatched_leaf (rootDigest : Digest8) (claimed : Lanes16)
    (proof : MembershipProof) (h : proof.leaf ≠ claimed) :
    verifyMembership rootDigest claimed proof = false := by
  simp [verifyMembership, recompose_mismatched_leaf claimed proof h]

private theorem recomposePath_mismatched_lengths (current : Digest8)
    (siblings : List (List Digest8)) (positions : List Nat)
    (h : siblings.length ≠ positions.length) :
    recomposePath current siblings positions = none := by
  induction siblings generalizing positions current with
  | nil => cases positions <;> simp_all [recomposePath]
  | cons s ss ih =>
      cases positions with
      | nil => simp [recomposePath]
      | cons p ps =>
          simp only [recomposePath]
          split
          · apply ih
            intro heq
            apply h
            simpa using congrArg Nat.succ heq
          · rfl

theorem recompose_mismatched_path_lengths (leaf : Lanes16)
    (siblings : List (List Digest8)) (positions : List Nat)
    (h : siblings.length ≠ positions.length) :
    recomposeMembership leaf ⟨leaf, siblings, positions⟩ = none := by
  unfold recomposeMembership
  rw [if_pos rfl]
  exact recomposePath_mismatched_lengths (noteLeaf16 leaf) siblings positions h

/-! ## Lean-computed protocol vectors (mirrored by Rust correspondence tests). -/

def ascendingBytes : Bytes32 := fun i => ⟨i.1, by omega⟩
def zeroBytes : Bytes32 := fun _ => 0
def oneBytes : Bytes32 := fun _ => 1
def twoBytes : Bytes32 := fun _ => 2

#guard lanes16List (commitmentToLanes16 ascendingBytes) =
  [256, 770, 1284, 1798, 2312, 2826, 3340, 3854,
   4368, 4882, 5396, 5910, 6424, 6938, 7452, 7966]

#guard noteLeaf16 (commitmentToLanes16 ascendingBytes) =
  [632237414, 1106963827, 1981485531, 1378889390,
   1941158165, 1606235884, 1135466672, 580799866]
#guard emptyNoteLeaf8 =
  [494407780, 1177177705, 833862924, 528655941,
   1124240900, 1779925736, 349643581, 774482890]
#guard noteNode8 [noteLeaf16 (commitmentToLanes16 zeroBytes),
  noteLeaf16 (commitmentToLanes16 oneBytes),
  noteLeaf16 (commitmentToLanes16 twoBytes), emptyNoteLeaf8] =
  [1629098044, 955608484, 342148490, 1281461710,
   1441002555, 770079181, 1611082324, 749516418]
#guard root 2 [commitmentToLanes16 zeroBytes, commitmentToLanes16 oneBytes,
  commitmentToLanes16 twoBytes] =
  [1872806112, 523477042, 958227429, 1604333445,
   1888739704, 712153370, 1327012915, 1980467199]

def proofAtOne : MembershipProof :=
  { leaf := commitmentToLanes16 oneBytes
    siblings := [[noteLeaf16 (commitmentToLanes16 zeroBytes),
      noteLeaf16 (commitmentToLanes16 twoBytes), emptyNoteLeaf8]]
    positions := [1] }

def depthOneRoot : Digest8 :=
  root 1 [commitmentToLanes16 zeroBytes, commitmentToLanes16 oneBytes,
    commitmentToLanes16 twoBytes]

#guard recomposeMembership (commitmentToLanes16 oneBytes) proofAtOne = some depthOneRoot
#guard verifyMembership depthOneRoot (commitmentToLanes16 oneBytes) proofAtOne
#guard verifyMembership depthOneRoot (commitmentToLanes16 twoBytes) proofAtOne = false
#guard recomposeMembership (commitmentToLanes16 oneBytes)
  { proofAtOne with positions := [] } = none
#guard recomposeMembership (commitmentToLanes16 oneBytes)
  { proofAtOne with positions := [4] } = none

#assert_axioms lanes16ToCommitment_commitmentToLanes16
#assert_axioms commitmentToLanes16_injective
#assert_axioms recompose_mismatched_leaf
#assert_axioms verify_mismatched_leaf
#assert_axioms recompose_mismatched_path_lengths

end Dregg2.Circuit.CommitmentTreeWide
