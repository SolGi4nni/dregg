/-
# `Dregg2.Circuit.ExactFnspV3DurableAuthority` — the durable FNSP-v3 head/CAS laws.

The runtime persists one authority head `(generation, root8, count, FNS3)` beside a dense
zero-based append image.  This module states that authority protocol over the existing exact
AAFI/FNSP-v3 semantics:

* `Head.Canonical` binds `count = generation + 1` (the permanent BOT leaf) and binds `FNS3`
  with the existing `accumulatorStateCommitReal root count4` definition;
* `Dense` states that record keys/sequences are exactly `0, …, n-1`;
* `replayHead` derives the only authority head from a deterministic replay-root function;
* `Accepts` is the compare-and-swap rule: current prefix replays, expected head matches,
  append sequence equals the current generation, independently replayed successor matches,
  and the current count has room;
* stale comparisons and forged successor heads refuse;
* every accepted append advances generation/count, rebinds FNS3 to successor root/count,
  preserves dense replay, and yields a unique deterministic head.

The Merkle/AAFI replay implementation is deliberately a parameter `replayRoot`.  Reimplementing
the hash tree here would create a second authority.  The existing Lean exact-nullifier modules
define the root/FNS3 semantics; the Rust-to-Lean replay correspondence remains the explicit outer
seam.  This file proves the persistence/CAS laws once, for every deterministic replay root.
-/
import Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan
import Dregg2.Tactics

namespace Dregg2.Circuit.ExactFnspV3DurableAuthority

open Dregg2.Circuit.ExactNullifierAafiPlan
  (RawValue Root8)
open Dregg2.Circuit.Emit.ExactNullifierAafiDescriptorPlan
  (TREE_CAPACITY accumulatorStateCommitReal countOne)

set_option autoImplicit false

/-! ## 1. Canonical count/head semantics. -/

/-- Exact little-endian four-u16 representation of the public count.  FNSP-v3 accepts at most
`2^32` occupied slots.  Nonterminal counts use the low two limbs; the terminal-full count
`2^32` is represented exactly as limb two equal to one.  Four limbs match the existing
`RawValue`/FNS3 ABI without wrap or truncation. -/
def count4 (count : Nat) : RawValue := fun i =>
  Int.ofNat ((count / (65536 ^ i.val)) % 65536)

/-- The durable public authority head.  Canonicity is a predicate rather than proof-carrying
fields so hostile decoded heads can be represented and refused. -/
structure Head where
  generation : Nat
  root : Root8
  count : Nat
  fns3 : Root8
  deriving DecidableEq

namespace Head

/-- A head is canonical exactly when count tracks generation, is within the exact tree capacity,
and FNS3 is recomputed from the head's own root and exact four-limb count. -/
def Canonical (head : Head) : Prop :=
  head.count = head.generation + 1 ∧
  head.count ≤ TREE_CAPACITY ∧
  head.fns3 = accumulatorStateCommitReal head.root (count4 head.count)

end Head

/-- Count one agrees with the already-pinned FNSP-v3 genesis count encoding. -/
theorem count4_one_eq_existing : count4 1 = countOne := by
  funext i
  fin_cases i <;> norm_num [count4, countOne]

/-- The terminal-full count is represented exactly, not truncated to zero. -/
theorem count4_terminal_full :
    count4 TREE_CAPACITY = fun i => if i.val = 2 then 1 else 0 := by
  funext i
  fin_cases i <;> norm_num [count4, TREE_CAPACITY]

/-! ## 2. Dense append image and deterministic replay. -/

/-- The persisted append payload.  `seq` is redundant with the table key on purpose: replay
checks both and refuses truncation/gaps/reordering. -/
structure AppendRecord (Payload : Type) where
  seq : Nat
  payload : Payload
  deriving DecidableEq

/-- Record sequences are exactly the dense zero-based prefix `[0, records.length)`. -/
def Dense {Payload : Type} (records : List (AppendRecord Payload)) : Prop :=
  records.map AppendRecord.seq = List.range records.length

/-- Appending exactly the next sequence preserves density. -/
theorem dense_append {Payload : Type} {records : List (AppendRecord Payload)}
    (hdense : Dense records) (record : AppendRecord Payload)
    (hseq : record.seq = records.length) : Dense (records ++ [record]) := by
  unfold Dense at hdense ⊢
  simp only [List.map_append, List.map_singleton, List.length_append, List.length_singleton]
  rw [hdense, hseq, List.range_succ]

/-- The only head derived from replaying this append image.  `replayRoot` denotes the existing
exact AAFI replay/root implementation at this abstraction boundary; FNS3 itself is not abstract. -/
def replayHead {Payload : Type}
    (replayRoot : List (AppendRecord Payload) → Root8)
    (records : List (AppendRecord Payload)) : Head :=
  let count := records.length + 1
  let root := replayRoot records
  { generation := records.length
    root := root
    count := count
    fns3 := accumulatorStateCommitReal root (count4 count) }

/-- A replayed prefix inside capacity always has a canonical authority head. -/
theorem replayHead_canonical {Payload : Type}
    (replayRoot : List (AppendRecord Payload) → Root8)
    (records : List (AppendRecord Payload)) (hroom : records.length < TREE_CAPACITY) :
    (replayHead replayRoot records).Canonical := by
  refine ⟨rfl, ?_, rfl⟩
  exact Nat.succ_le_iff.mpr hroom

/-- `ReplaysTo` includes density: a head over a gapped/reordered image is not an authority head
even if some root function happens to return the same digest. -/
def ReplaysTo {Payload : Type}
    (replayRoot : List (AppendRecord Payload) → Root8)
    (records : List (AppendRecord Payload)) (head : Head) : Prop :=
  Dense records ∧ head = replayHead replayRoot records

/-- **Deterministic replay yields a unique head.** No hash injectivity is needed: the replay root
is a function, and the head recomputes generation/count/FNS3 from that one result. -/
theorem deterministic_replay_unique {Payload : Type}
    (replayRoot : List (AppendRecord Payload) → Root8)
    (records : List (AppendRecord Payload)) {left right : Head}
    (hleft : ReplaysTo replayRoot records left)
    (hright : ReplaysTo replayRoot records right) : left = right := by
  rw [hleft.2, hright.2]

/-! ## 3. Compare-and-swap acceptance. -/

/-- Store-prepared append candidate.  As in the runtime type, all three fields are checked again
under the writer lock; construction does not grant authority. -/
structure Candidate (Payload : Type) where
  expected : Head
  successor : Head
  append : AppendRecord Payload

/-- The exact durable acceptance relation.  The current dense prefix is replayed first; the
candidate's expected head must compare equal; append sequence must equal generation; and the
candidate successor must equal independent replay of the appended prefix. -/
structure Accepts {Payload : Type}
    (replayRoot : List (AppendRecord Payload) → Root8)
    (records : List (AppendRecord Payload)) (current : Head)
    (candidate : Candidate Payload) : Prop where
  current_replays : ReplaysTo replayRoot records current
  expected_matches : candidate.expected = current
  append_sequence : candidate.append.seq = current.generation
  successor_replays : candidate.successor = replayHead replayRoot (records ++ [candidate.append])
  room : current.count < TREE_CAPACITY

/-- A stale compare token cannot be accepted. -/
theorem stale_expected_head_refused {Payload : Type}
    {replayRoot : List (AppendRecord Payload) → Root8}
    {records : List (AppendRecord Payload)} {current : Head}
    {candidate : Candidate Payload} (hstale : candidate.expected ≠ current) :
    ¬ Accepts replayRoot records current candidate := by
  intro accepted
  exact hstale accepted.expected_matches

/-- A candidate successor differing from independent replay cannot be accepted. -/
theorem forged_successor_head_refused {Payload : Type}
    {replayRoot : List (AppendRecord Payload) → Root8}
    {records : List (AppendRecord Payload)} {current : Head}
    {candidate : Candidate Payload}
    (hforged : candidate.successor ≠ replayHead replayRoot (records ++ [candidate.append])) :
    ¬ Accepts replayRoot records current candidate := by
  intro accepted
  exact hforged accepted.successor_replays

/-- Accepted append records have exactly the next dense sequence number. -/
theorem accepted_append_sequence_eq_length {Payload : Type}
    {replayRoot : List (AppendRecord Payload) → Root8}
    {records : List (AppendRecord Payload)} {current : Head}
    {candidate : Candidate Payload}
    (accepted : Accepts replayRoot records current candidate) :
    candidate.append.seq = records.length := by
  rw [accepted.append_sequence, accepted.current_replays.2]
  rfl

/-- Accepted append preserves the dense durable image. -/
theorem accepted_append_dense {Payload : Type}
    {replayRoot : List (AppendRecord Payload) → Root8}
    {records : List (AppendRecord Payload)} {current : Head}
    {candidate : Candidate Payload}
    (accepted : Accepts replayRoot records current candidate) :
    Dense (records ++ [candidate.append]) :=
  dense_append accepted.current_replays.1 candidate.append
    (accepted_append_sequence_eq_length accepted)

/-- The current accepted prefix is itself canonical. -/
theorem accepted_current_canonical {Payload : Type}
    {replayRoot : List (AppendRecord Payload) → Root8}
    {records : List (AppendRecord Payload)} {current : Head}
    {candidate : Candidate Payload}
    (accepted : Accepts replayRoot records current candidate) : current.Canonical := by
  have hroom := accepted.room
  rw [accepted.current_replays.2] at hroom
  rw [accepted.current_replays.2]
  apply replayHead_canonical
  have hcount : records.length + 1 < TREE_CAPACITY := by
    simpa [replayHead] using hroom
  omega

/-- Every accepted successor remains canonical, including the terminal-full head. -/
theorem accepted_successor_canonical {Payload : Type}
    {replayRoot : List (AppendRecord Payload) → Root8}
    {records : List (AppendRecord Payload)} {current : Head}
    {candidate : Candidate Payload}
    (accepted : Accepts replayRoot records current candidate) :
    candidate.successor.Canonical := by
  have hroom := accepted.room
  rw [accepted.current_replays.2] at hroom
  rw [accepted.successor_replays]
  apply replayHead_canonical
  have hcount : records.length + 1 < TREE_CAPACITY := by
    simpa [replayHead] using hroom
  simpa using hcount

/-- Accepted append increments generation by exactly one. -/
theorem accepted_generation_increments {Payload : Type}
    {replayRoot : List (AppendRecord Payload) → Root8}
    {records : List (AppendRecord Payload)} {current : Head}
    {candidate : Candidate Payload}
    (accepted : Accepts replayRoot records current candidate) :
    candidate.successor.generation = current.generation + 1 := by
  rw [accepted.successor_replays, accepted.current_replays.2]
  simp [replayHead]

/-- Accepted append increments the occupied-slot count by exactly one. -/
theorem accepted_count_increments {Payload : Type}
    {replayRoot : List (AppendRecord Payload) → Root8}
    {records : List (AppendRecord Payload)} {current : Head}
    {candidate : Candidate Payload}
    (accepted : Accepts replayRoot records current candidate) :
    candidate.successor.count = current.count + 1 := by
  rw [accepted.successor_replays, accepted.current_replays.2]
  simp [replayHead]

/-- Accepted successor FNS3 is recomputed from that successor's own root and exact count. -/
theorem accepted_successor_fns3_recomputed {Payload : Type}
    {replayRoot : List (AppendRecord Payload) → Root8}
    {records : List (AppendRecord Payload)} {current : Head}
    {candidate : Candidate Payload}
    (accepted : Accepts replayRoot records current candidate) :
    candidate.successor.fns3 =
      accumulatorStateCommitReal candidate.successor.root (count4 candidate.successor.count) :=
  (accepted_successor_canonical accepted).2.2

/-- The post-CAS dense image replays to exactly the accepted successor. -/
theorem accepted_successor_is_unique_replay {Payload : Type}
    {replayRoot : List (AppendRecord Payload) → Root8}
    {records : List (AppendRecord Payload)} {current : Head}
    {candidate : Candidate Payload}
    (accepted : Accepts replayRoot records current candidate)
    {other : Head}
    (hother : ReplaysTo replayRoot (records ++ [candidate.append]) other) :
    other = candidate.successor := by
  apply deterministic_replay_unique replayRoot (records ++ [candidate.append]) hother
  exact ⟨accepted_append_dense accepted, accepted.successor_replays⟩

/-! ## 4. Prepared-candidate tooth. -/

/-- The canonical candidate produced from an independently replayed prefix. -/
def prepare {Payload : Type}
    (replayRoot : List (AppendRecord Payload) → Root8)
    (records : List (AppendRecord Payload)) (payload : Payload) : Candidate Payload :=
  let append : AppendRecord Payload := { seq := records.length, payload := payload }
  { expected := replayHead replayRoot records
    successor := replayHead replayRoot (records ++ [append])
    append := append }

/-- **FIRE.** A dense prefix with room admits its independently prepared append candidate. -/
theorem prepared_candidate_accepts {Payload : Type}
    (replayRoot : List (AppendRecord Payload) → Root8)
    (records : List (AppendRecord Payload)) (payload : Payload)
    (hdense : Dense records) (hroom : records.length + 1 < TREE_CAPACITY) :
    Accepts replayRoot records (replayHead replayRoot records)
      (prepare replayRoot records payload) := by
  refine ⟨⟨hdense, rfl⟩, rfl, rfl, rfl, ?_⟩
  simpa [replayHead] using hroom

/-! ## 5. Concrete acceptance/refusal teeth. -/

namespace Teeth

/-- Deterministic nonconstant replay root for driving the authority state machine.  This is only
a protocol tooth; no claim is made that it is the exact AAFI Merkle root. -/
def demoRoot (records : List (AppendRecord Unit)) : Root8 := fun lane =>
  Int.ofNat (records.length + lane.val)

def demoCandidate : Candidate Unit := prepare demoRoot [] ()
def demoCurrent1 : Head := replayHead demoRoot [demoCandidate.append]

/-- **FIRE.** Genesis is dense, has room, and accepts its independently prepared first append. -/
theorem demo_prepared_accepts :
    Accepts demoRoot [] (replayHead demoRoot []) demoCandidate := by
  apply prepared_candidate_accepts
  · rfl
  · norm_num [TREE_CAPACITY]

/-- After one append, the genesis compare token is genuinely stale (generation `0 ≠ 1`). -/
theorem demo_expected_is_stale : demoCandidate.expected ≠ demoCurrent1 := by
  intro h
  have hgeneration := congrArg Head.generation h
  norm_num [demoCandidate, demoCurrent1, prepare, replayHead] at hgeneration

/-- **BITE.** Reusing the already-consumed genesis candidate against generation one refuses. -/
theorem demo_replay_refuses_stale :
    ¬ Accepts demoRoot [demoCandidate.append] demoCurrent1 demoCandidate :=
  stale_expected_head_refused demo_expected_is_stale

end Teeth

/-! ## 6. Axiom hygiene. -/

#assert_axioms count4_one_eq_existing
#assert_axioms count4_terminal_full
#assert_axioms dense_append
#assert_axioms replayHead_canonical
#assert_axioms deterministic_replay_unique
#assert_axioms stale_expected_head_refused
#assert_axioms forged_successor_head_refused
#assert_axioms accepted_append_sequence_eq_length
#assert_axioms accepted_append_dense
#assert_axioms accepted_current_canonical
#assert_axioms accepted_successor_canonical
#assert_axioms accepted_generation_increments
#assert_axioms accepted_count_increments
#assert_axioms accepted_successor_fns3_recomputed
#assert_axioms accepted_successor_is_unique_replay
#assert_axioms prepared_candidate_accepts
#assert_axioms Teeth.demo_prepared_accepts
#assert_axioms Teeth.demo_expected_is_stale
#assert_axioms Teeth.demo_replay_refuses_stale

end Dregg2.Circuit.ExactFnspV3DurableAuthority
