/-
# Dregg2.Circuit.CommitmentTreeWideHistory -- authenticated faithful-root history

`CommitmentTreeWide` defines the faithful note leaf, node, root, and membership
semantics.  This file defines the *history protocol* that may authenticate those
roots.  A record does not merely publish a successor root: it binds the exact
session/federation/committee epoch, predecessor and successor roots, predecessor
and successor note counts, consecutive finalized heights, and the block identity
that carried the transition.

Authentication is deliberately parameterized as `auth : Record -> Prop`.  The
runtime instantiates it with the existing enrolled-roster hybrid quorum verifier
(Ed25519 AND ML-DSA-65).  Keeping cryptographic verification abstract here makes
the structural theorem independent of any signature implementation without
pretending that structure alone authenticates a record.

The protocol is append-only.  Once a record has advanced the head, replaying it,
or presenting a sibling at the already-consumed height, cannot extend the new
head.  Exact snapshot verification carries an expected record count and head;
dropping a suffix therefore refuses instead of silently accepting a valid prefix.
Rollback of *both* a history and its external expected head is outside this local
model and remains the caller's checkpoint/finality obligation.
-/
import Dregg2.Circuit.CommitmentTreeWide
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Circuit.CommitmentTreeWideHistory

open Dregg2.Circuit.Poseidon2BabyBearW16 (P)
open Dregg2.Circuit.CommitmentTreeWide (Digest8)

set_option autoImplicit false

abbrev Bytes32 := List Nat
abbrev Root8 := Digest8

def zeroBytes : Bytes32 := List.replicate 32 0

def bytesNonzero (bytes : Bytes32) : Prop := bytes ≠ zeroBytes

def canonicalBytes32 (bytes : Bytes32) : Prop :=
  bytes.length = 32 ∧ bytes.all (fun byte => decide (byte < 256)) = true

def canonicalRoot8 (root : Root8) : Prop :=
  root.length = 8 ∧ root.all (fun lane => decide (lane < P)) = true

def U64_BOUND : Nat := 2 ^ 64

def canonicalU64 (value : Nat) : Prop := value < U64_BOUND

/-- The externally trusted head from which a history segment starts. -/
structure Anchor where
  session : Bytes32
  federation : Bytes32
  committeeEpoch : Nat
  height : Nat
  noteCount : Nat
  root : Root8
  deriving DecidableEq

/-- Version-one faithful note-root transition.  The Rust canonical message is a
fixed-width encoding of these fields under the `FNHR`/v1 domain. -/
structure Record where
  version : Nat
  session : Bytes32
  federation : Bytes32
  committeeEpoch : Nat
  previousHeight : Nat
  height : Nat
  previousNoteCount : Nat
  noteCount : Nat
  predecessor : Root8
  successor : Root8
  blockId : Bytes32
  deriving DecidableEq

/-- The history head after accepting `record`. -/
def Record.toAnchor (record : Record) : Anchor :=
  { session := record.session
    federation := record.federation
    committeeEpoch := record.committeeEpoch
    height := record.height
    noteCount := record.noteCount
    root := record.successor }

/-- One record is a structurally valid, context-bound extension of exactly this
head.  Growth must move the root; a no-note finalized height must preserve it.
The latter makes an invented root change without an append fail structurally;
the former treats a same-root append as the hash collision it would be. -/
def Extends (anchor : Anchor) (record : Record) : Prop :=
  record.version = 1 /\
  canonicalBytes32 record.session /\
  canonicalBytes32 record.federation /\
  canonicalBytes32 record.blockId /\
  canonicalRoot8 record.predecessor /\
  canonicalRoot8 record.successor /\
  canonicalU64 record.committeeEpoch /\
  canonicalU64 record.previousHeight /\
  canonicalU64 record.height /\
  canonicalU64 record.previousNoteCount /\
  canonicalU64 record.noteCount /\
  bytesNonzero record.session /\
  bytesNonzero record.federation /\
  bytesNonzero record.blockId /\
  record.session = anchor.session /\
  record.federation = anchor.federation /\
  record.committeeEpoch = anchor.committeeEpoch /\
  record.previousHeight = anchor.height /\
  record.height = anchor.height + 1 /\
  record.previousNoteCount = anchor.noteCount /\
  record.noteCount ≥ anchor.noteCount /\
  record.predecessor = anchor.root /\
  (record.noteCount = anchor.noteCount -> record.successor = anchor.root) /\
  (record.noteCount > anchor.noteCount -> record.successor ≠ anchor.root)

/-- Executable structural admission used by the Rust correspondence tests. -/
def extendsBool (anchor : Anchor) (record : Record) : Bool :=
  let _ : Decidable (Extends anchor record) := by
    unfold Extends canonicalBytes32 canonicalRoot8 canonicalU64 bytesNonzero
    infer_instance
  decide (Extends anchor record)

/-! ## The canonical signed bytes

The runtime signs exactly this layout: `FNHR`, little-endian v1/reserved, the
two exact 32-byte contexts, five little-endian u64 coordinates, two roots as
eight canonical little-endian u32 lanes, and the 32-byte block id. -/

def u16LE (value : Nat) : List Nat := [value % 256, value / 256 % 256]

def u32LE (value : Nat) : List Nat :=
  (List.range 4).map (fun i => value / (256 ^ i) % 256)

def u64LE (value : Nat) : List Nat :=
  (List.range 8).map (fun i => value / (256 ^ i) % 256)

def encodeRoot8 (root : Root8) : List Nat := root.flatMap u32LE

def encodeRecordV1 (record : Record) : List Nat :=
  [0x46, 0x4e, 0x48, 0x52] ++ -- `FNHR`
  u16LE 1 ++ u16LE 0 ++
  record.session ++ record.federation ++
  u64LE record.committeeEpoch ++
  u64LE record.previousHeight ++ u64LE record.height ++
  u64LE record.previousNoteCount ++ u64LE record.noteCount ++
  encodeRoot8 record.predecessor ++ encodeRoot8 record.successor ++
  record.blockId

/-- An authenticated history: every structural edge also satisfies the supplied
authentication predicate. -/
def Valid (auth : Record -> Prop) : Anchor -> List Record -> Prop
  | _, [] => True
  | anchor, record :: rest =>
      auth record /\ Extends anchor record /\ Valid auth record.toAnchor rest

/-- Replay a list to its resulting head.  This is total; [`Valid`] is the gate
that says each step was authenticated and linked. -/
def headAfter : Anchor -> List Record -> Anchor
  | anchor, [] => anchor
  | _, record :: rest => headAfter record.toAnchor rest

/-- A loaded snapshot is accepted only against an externally expected exact
record count, height, note count, and head root.  A locally valid prefix is not
enough. -/
def ExactSnapshot (auth : Record -> Prop) (anchor : Anchor) (records : List Record)
    (expectedRecords expectedHeight expectedNoteCount : Nat) (expectedRoot : Root8) : Prop :=
  Valid auth anchor records /\
  records.length = expectedRecords /\
  (headAfter anchor records).height = expectedHeight /\
  (headAfter anchor records).noteCount = expectedNoteCount /\
  (headAfter anchor records).root = expectedRoot

theorem extends_binds_exact_predecessor (anchor : Anchor) (record : Record)
    (h : Extends anchor record) :
    record.previousHeight = anchor.height /\
    record.previousNoteCount = anchor.noteCount /\
    record.predecessor = anchor.root := by
  unfold Extends at h
  aesop

theorem unchanged_count_preserves_root (anchor : Anchor) (record : Record)
    (h : Extends anchor record) (hcount : record.noteCount = anchor.noteCount) :
    record.successor = anchor.root := by
  unfold Extends at h
  aesop

theorem growth_moves_root (anchor : Anchor) (record : Record)
    (h : Extends anchor record) (hcount : record.noteCount > anchor.noteCount) :
    record.successor ≠ anchor.root := by
  unfold Extends at h
  aesop

/-- After accepting a record, the exact same record cannot be replayed as the
next edge: its previous/current heights are already consumed. -/
theorem replay_rejected_after_append (anchor : Anchor) (record : Record)
    (_h : Extends anchor record) : ¬ Extends record.toAnchor record := by
  intro hreplay
  unfold Extends at hreplay
  simp [Record.toAnchor] at hreplay

/-- A sibling/fork at the height just consumed cannot be appended after the
chosen record, even if it carries a different block id or root. -/
theorem same_height_fork_rejected_after_append (record sibling : Record)
    (hsame : sibling.height = record.height) : ¬ Extends record.toAnchor sibling := by
  intro hfork
  unfold Extends at hfork
  simp [Record.toAnchor, hsame] at hfork

/-- Rebinding a record to another session is structurally refused. -/
theorem session_substitution_rejected (anchor : Anchor) (record : Record)
    (hne : record.session ≠ anchor.session) : ¬ Extends anchor record := by
  intro h
  unfold Extends at h
  aesop

/-- Removing a nonempty suffix changes the record count.  Therefore the exact
snapshot gate cannot accept both the complete list and its strict prefix under
one expected count. -/
theorem strict_prefix_has_wrong_count (initial : List Record) (last : Record) :
    initial.length ≠ (initial ++ [last]).length := by
  simp

theorem exact_snapshot_rejects_truncated_tail
    (auth : Record -> Prop) (anchor : Anchor) (initial : List Record) (last : Record)
    (expectedHeight expectedNoteCount : Nat) (expectedRoot : Root8) :
    ¬ ExactSnapshot auth anchor initial (initial ++ [last]).length
      expectedHeight expectedNoteCount expectedRoot := by
  intro h
  exact strict_prefix_has_wrong_count initial last h.2.1

/-! Concrete executable teeth. -/

def byteTag (tag : Nat) : Bytes32 := tag % 256 :: List.replicate 31 0

def rootTag (tag : Nat) : Root8 := tag % P :: List.replicate 7 0

def demoAnchor : Anchor :=
  { session := byteTag 1
    federation := byteTag 2
    committeeEpoch := 7
    height := 40
    noteCount := 3
    root := rootTag 10 }

def demoRecord : Record :=
  { version := 1
    session := demoAnchor.session
    federation := demoAnchor.federation
    committeeEpoch := demoAnchor.committeeEpoch
    previousHeight := demoAnchor.height
    height := demoAnchor.height + 1
    previousNoteCount := demoAnchor.noteCount
    noteCount := demoAnchor.noteCount + 2
    predecessor := demoAnchor.root
    successor := rootTag 11
    blockId := byteTag 3 }

#guard extendsBool demoAnchor demoRecord
#guard extendsBool demoRecord.toAnchor demoRecord = false
#guard extendsBool demoRecord.toAnchor { demoRecord with blockId := byteTag 4 } = false
#guard extendsBool demoAnchor { demoRecord with predecessor := rootTag 99 } = false
#guard extendsBool demoAnchor { demoRecord with session := byteTag 99 } = false
#guard extendsBool demoAnchor { demoRecord with noteCount := demoAnchor.noteCount } = false

#guard (encodeRecordV1 demoRecord).length = 208
#guard (encodeRecordV1 demoRecord).take 8 = [0x46, 0x4e, 0x48, 0x52, 1, 0, 0, 0]
#guard (encodeRecordV1 demoRecord).getD 8 0 = 1      -- session byte 0
#guard (encodeRecordV1 demoRecord).getD 40 0 = 2     -- federation byte 0
#guard (encodeRecordV1 demoRecord).getD 72 0 = 7     -- epoch LE
#guard (encodeRecordV1 demoRecord).getD 80 0 = 40    -- predecessor height LE
#guard (encodeRecordV1 demoRecord).getD 88 0 = 41    -- successor height LE
#guard (encodeRecordV1 demoRecord).getD 96 0 = 3     -- predecessor count LE
#guard (encodeRecordV1 demoRecord).getD 104 0 = 5    -- successor count LE
#guard (encodeRecordV1 demoRecord).getD 112 0 = 10   -- predecessor root lane 0 LE
#guard (encodeRecordV1 demoRecord).getD 144 0 = 11   -- successor root lane 0 LE
#guard (encodeRecordV1 demoRecord).getD 176 0 = 3    -- block id byte 0

#assert_axioms extends_binds_exact_predecessor
#assert_axioms unchanged_count_preserves_root
#assert_axioms growth_moves_root
#assert_axioms replay_rejected_after_append
#assert_axioms same_height_fork_rejected_after_append
#assert_axioms session_substitution_rejected
#assert_axioms strict_prefix_has_wrong_count
#assert_axioms exact_snapshot_rejects_truncated_tail

end Dregg2.Circuit.CommitmentTreeWideHistory
