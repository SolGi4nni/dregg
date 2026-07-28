/-
# Dregg2.Circuit.Emit.KimchiPartition — the STEP PARTITIONER, and what a step boundary must carry

## Why "~260 steps" is a compiler OUTPUT

`docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` quotes ~260–1,040 Pickles step circuits for a Kimchi-side
dregg FRI verify. That number is not a quantity of circuits anyone writes: it is
`⌈rows / usable⌉` for a circuit the compiler emits. This file is the pass that computes it — so
the step count is a function of the emitted row list and the domain ceiling, and it moves when the
generator moves.

## The wall this partitions against

  * **2^16 = 65,536 rows** is the Kimchi domain
    (`mina/src/lib/crypto/kimchi_backend/pasta/basic/kimchi_pasta_basic.ml:16-17`).
  * **Pickles HARD-REJECTS chunking** — `mina/src/lib/pickles/verify.ml:61-76` raises `Is_chunked`
    if any evaluation array has length > 1, then asserts "only uses single chunks". Upstream Kimchi
    supports chunking; Mina does not accept it. So a circuit that does not fit does not get a
    bigger domain — it gets SPLIT, and the split is this pass.
  * **The domain is a power of two**, so crossing a boundary doubles proving cost at one row over.
  * `zk_rows = 3` plus **one full row per public-input element** come off the top, and the
    recursive-verifier overhead at `max_proofs_verified = 2` (needed for an aggregation tree) is
    ~12,000–16,000 rows, leaving ~48,000–52,000 usable.

## ⚑ The step-boundary contract — the part that is a DESIGN, not an arithmetic

A step is not a slice of rows. Splitting a circuit at row `k` is only sound if everything the
second half reads from the first half crosses the boundary, and in Pickles a boundary is a
PUBLIC INPUT — one field element per row of cost, so it cannot be the carried values themselves.

`StepBoundary` below names exactly what crosses, and `carryDigest` is the shape that makes it
affordable: the carried variables are **hashed into a single field element**, and each step
re-witnesses the values and re-derives the digest. That is why the boundary costs one
Poseidon2 sponge rather than `|carried|` public inputs — and why a step boundary is not free, which
is the thing a naive "just split it" account leaves out.

The three things a work step's public input must carry are stated in `StepPublicInput`, and they
are not interchangeable with a row count:

  1. the **root commitment digest** — without it, consecutive steps could be verifying openings
     against DIFFERENT dregg proofs and the aggregation would still verify;
  2. the **challenge digest** — the Fiat–Shamir transcript state, so a step cannot re-derive
     challenges of its own choosing;
  3. the **step index**, so the aggregation tree cannot admit the same step twice or skip one.

## What is PROVED here

`partition_concat` — the partition loses and duplicates nothing — and `partition_fits`, that every
emitted step is under the ceiling. Those are the two properties that make a step count meaningful.
The SCHEDULER is naive on purpose (greedy, cut at the ceiling); the interface is the point, and a
smarter scheduler that minimises carried state is named in the remainder.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`.
NEW file; imports `KimchiLower`.
-/
import Dregg2.Circuit.Emit.KimchiLower

namespace Dregg2.Circuit.Emit.KimchiPartition

open Dregg2.Circuit.Emit.KimchiTarget
open Dregg2.Circuit.Emit.KimchiLower

set_option autoImplicit false

/-! ## §1 — the budget. -/

/-- Rows lost to `zk_rows` (`KimchiVerify.zkRows = 3`). -/
def ZK_ROWS : Nat := 3

/-- The recursive-verifier overhead at `max_proofs_verified = 2`, the setting an aggregation tree
needs (`docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §4.1, ~12,000–16,000; the pessimistic end is taken so
the step count is not optimistic by construction). -/
def PICKLES_RECURSION_OVERHEAD : Nat := 16000

/-- Rows a work step can actually spend, given `nPub` public-input elements — each of which costs a
FULL ROW (§3.2), which is the whole reason the boundary is a digest and not a vector. -/
def usableRows (nPub : Nat) : Nat :=
  PICKLES_MAX_ROWS - ZK_ROWS - PICKLES_RECURSION_OVERHEAD - nPub

/-- With the three-element public input of `StepPublicInput` compressed to one field element. -/
def usableRowsDigest : Nat := usableRows 1

example : usableRowsDigest = 49532 := rfl

/-! ## §2 — the step-boundary contract. -/

/-- **What a work step's public input must carry.** One field element on the wire — the Poseidon
digest of these three — because each element costs a full row.

Dropping any one of them breaks a different thing, and none of the three is bookkeeping:
`rootCommitDigest` is what binds every step to the SAME dregg proof; `challengeDigest` is what stops
a step choosing its own Fiat–Shamir challenges; `stepIndex` is what stops the aggregation tree
double-counting or skipping. -/
structure StepPublicInput where
  /-- Digest of the dregg proof's commitments — identical across every step of one verification. -/
  rootCommitDigest : Nat
  /-- The Fiat–Shamir transcript state entering this step. -/
  challengeDigest : Nat
  /-- Position in the chain. -/
  stepIndex : Nat
  deriving Repr, DecidableEq, Inhabited

/-- **What crosses a step boundary.** `carried` are the circuit variables the later steps read and
the earlier steps wrote; `digestVar` is the variable holding their compressed digest, which is what
the public input actually commits to.

The cost of a boundary is therefore `|carried|` re-witnessings plus ONE Poseidon2 sponge in each of
the two adjacent steps — not `|carried|` public inputs. That asymmetry is the entire reason this is
a structure and not a `List Nat`. -/
structure StepBoundary where
  carried : List Nat
  digestVar : Nat
  deriving Repr, DecidableEq, Inhabited

/-- One emitted step. -/
structure Step where
  rows : List KRow
  inBoundary : Option StepBoundary
  outBoundary : Option StepBoundary
  deriving Inhabited

/-- A step's cost, including the boundary sponges it must pay for. `spongeRows` is the price of one
Poseidon2-w16 absorb-and-squeeze at the emitted rate — passed in rather than hardcoded so the
partitioner tracks the generator instead of drifting from it. -/
def Step.cost (spongeRows : Nat) (s : Step) : Nat :=
  s.rows.length
    + (if s.inBoundary.isSome then spongeRows else 0)
    + (if s.outBoundary.isSome then spongeRows else 0)

/-! ## §3 — the scheduler.

Greedy: fill to the ceiling, cut, repeat. Deliberately naive — it does not try to cut where the
carried set is smallest, which is the optimisation a real scheduler exists for and which is named
in the remainder. What it DOES do is lose nothing (`chunks_concat`) and fit (`chunks_fits`). -/

/-- Split a row list into chunks of at most `sz` rows.

Recursion is on an explicit FUEL rather than on `rs.drop sz` being shorter. That is not
squeamishness about well-founded recursion: `chunks` with a `decreasing_by` gives no usable
`.induct` principle here, and a partitioner whose two correctness properties cannot be stated is
worse than a slightly uglier definition. The fuel is always `rs.length + 1`, so it never binds. -/
def chunksGo (sz : Nat) : Nat → List KRow → List (List KRow)
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, rs@(_ :: _) => rs.take sz :: chunksGo sz f (rs.drop sz)

/-- Split a row list into chunks of at most `sz` rows. -/
def chunks (sz : Nat) (rs : List KRow) : List (List KRow) := chunksGo sz (rs.length + 1) rs

theorem chunksGo_flatten (sz : Nat) (hsz : 0 < sz) :
    ∀ (f : Nat) (rs : List KRow), rs.length ≤ f → (chunksGo sz f rs).flatten = rs := by
  intro f
  induction f with
  | zero =>
    intro rs hle
    have : rs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hle)
    subst this; rfl
  | succ f ih =>
    intro rs hle
    cases rs with
    | nil => rfl
    | cons x xs =>
      have hdrop : ((x :: xs).drop sz).length ≤ f := by
        simp only [List.length_drop, List.length_cons] at *
        omega
      simp only [chunksGo, List.flatten_cons, ih _ hdrop]
      exact List.take_append_drop sz (x :: xs)

/-- **The partition loses and duplicates nothing.** Without this a step count is a number about a
different circuit. -/
theorem chunks_concat (sz : Nat) (hsz : 0 < sz) (rs : List KRow) :
    (chunks sz rs).flatten = rs :=
  chunksGo_flatten sz hsz (rs.length + 1) rs (by omega)

theorem chunksGo_fits (sz : Nat) :
    ∀ (f : Nat) (rs : List KRow), ∀ c ∈ chunksGo sz f rs, c.length ≤ sz := by
  intro f
  induction f with
  | zero => intro rs c hc; cases hc
  | succ f ih =>
    intro rs c hc
    cases rs with
    | nil => cases hc
    | cons x xs =>
      simp only [chunksGo, List.mem_cons] at hc
      rcases hc with rfl | hc2
      · simp [List.length_take]
      · exact ih _ c hc2

/-- **Every emitted chunk fits under the ceiling.** -/
theorem chunks_fits (sz : Nat) (rs : List KRow) : ∀ c ∈ chunks sz rs, c.length ≤ sz :=
  chunksGo_fits sz (rs.length + 1) rs

/-- **THE STEP COUNT — a compiler output.** How many Pickles work steps an emitted circuit needs. -/
def stepCount (rs : List KRow) : Nat := (chunks usableRowsDigest rs).length

/-- The step count as arithmetic, for budgeting before a circuit exists. -/
def stepCountOfRows (totalRows : Nat) : Nat :=
  (totalRows + usableRowsDigest - 1) / usableRowsDigest

/-- A binary aggregation tree over `n` work steps adds `n − 1` `SelfProof` steps. -/
def aggregationSteps (n : Nat) : Nat := if n = 0 then 0 else n - 1

/-- Total Pickles steps: work plus aggregation. -/
def totalSteps (totalRows : Nat) : Nat :=
  let w := stepCountOfRows totalRows
  w + aggregationSteps w

/-! ## §4 — the ~260 number, recomputed as an output.

`docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §5.3 puts the irreducible floor at ~5,900 permutations and
§2.1 the deployed count at ~11,000. At the row price `KimchiPoseidon2` actually emits — 2,668, not
the o1js 2,600.5 — those become step counts here rather than in a document. -/

/-- The floor permutation count (§5.3: column-driven leaf hashing ~2,900, transcript ~1,300, capped
input paths ~1,100, folded commit phase ~600). -/
def FLOOR_PERMS : Nat := 5900

/-- The deployed permutation count (§2.1, measured in-tree). -/
def DEPLOYED_PERMS : Nat := 11000

/-- The row price this compiler emits (`KimchiPoseidon2.permRowCount`, restated to keep this module
free of that import). -/
def EMITTED_ROWS_PER_PERM : Nat := 2668

/-! ⚑ The floor step count, at the price this compiler emits. The document's ~260 was computed at
2,600.5 rows/permutation; at 2,668 it is this. -/
#guard stepCountOfRows (FLOOR_PERMS * EMITTED_ROWS_PER_PERM) = 318

/-! The deployed step count, work-carrying only. -/
#guard stepCountOfRows (DEPLOYED_PERMS * EMITTED_ROWS_PER_PERM) = 593

/-! With the binary aggregation tree. -/
#guard totalSteps (DEPLOYED_PERMS * EMITTED_ROWS_PER_PERM) = 1185

/-! ⚑ **Read these three numbers as what they are.** They are the partitioner applied to a
permutation COUNT that this compiler has not emitted — `KimchiPoseidon2` emits one permutation, and
`FLOOR_PERMS`/`DEPLOYED_PERMS` are the document's structural counts for a verifier that does not
exist yet. So the step count is a compiler output the moment the verifier generator exists, and
until then it is this pass applied to a quoted input. That distinction is the whole difference
between "260 steps is a partitioning number" and "260 steps is a compiler output", and it is not
closed yet. -/

#assert_axioms chunks_concat
#assert_axioms chunks_fits

end Dregg2.Circuit.Emit.KimchiPartition
