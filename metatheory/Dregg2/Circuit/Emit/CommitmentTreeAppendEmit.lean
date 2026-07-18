/-
# Dregg2.Circuit.Emit.CommitmentTreeAppendEmit — the DEPLOYED note-tree accumulator root,
  COMPUTED IN LEAN over the REAL BabyBear Poseidon2 (not the opaque `H` stand-in).

## What this module delivers (and why it is NOT an `EffectVmDescriptor2`)

Chunk 1 (`Dregg2.Circuit.CommitmentTreeAccumulator`) authored the deployed 4-ary append-only
Poseidon2 note-commitment tree — `nodeAt`/`root`/`append`/`emptyHash` — over an OPAQUE node
compression `H : List ℤ → ℤ`, with the honest collision-extraction binding
(`root_distinct_extracts_collision`) and the incremental-append lemma. That module PROVES the
tree's algebra; it does not compute the deployed BYTES, because `H` is opaque.

This module CLOSES that last gap: it instantiates chunk 1's `root`/`append` at the REAL,
KAT-locked BabyBear Poseidon2-w16 permutation (`Dregg2.Circuit.Poseidon2BabyBearW16.perm`, bit-exact
against the deployed `default_babybear_poseidon2_16().permute`), realizing `hash_4_to_1`
(`circuit/src/poseidon2.rs`) as `hash4to1Real`. The result — `rootReal` — COMPUTES THE DEPLOYED
NOTE-TREE ROOT, byte-for-byte, entirely in Lean. The `#guard` byte-pins below are the EXACT deployed
roots (`Poseidon2MerkleTree::root().0`) for empty/sparse/half/full trees at depths 2–4 and at every
append prefix — the same integers `commit/tests/poseidon2_tree_lean_differential.rs` asserts the
DEPLOYED Rust tree reproduces. Lean `#guard rootReal = golden` ∧ Rust `assert deployed = golden` ⇒
`deployed = rootReal` byte-for-byte: the byte-identical safety gate the cutover requires.

### Why there is no descriptor JSON / `EmitByName` entry here

The other `Emit/*Emit.lean` modules author `EffectVmDescriptor2`s — STARK AIRs that a witness trace
either SATISFIES or not (`Satisfied2`; `prove_vm_descriptor2` takes a caller-supplied `base_trace`).
An AIR descriptor is an ACCEPTOR, not an EVALUATOR: it cannot COMPUTE a tree root from a leaf list.
The deployed precedent confirms this is the intended shape — the sorted-map heap root
(`heap_root.rs::CanonicalHeapTree::root` / `compute_heap_root`) is likewise computed in hand-rolled
Rust, and its Lean-emitted descriptor (`HeapOpenEmit`) only CONSTRAINS the sorted-Merkle write. So
the note-tree ROOT is witness-generation, the analog of `heap_root.rs`'s root computation — it is
legitimately NOT an AIR descriptor, and forcing it into an `EffectVmDescriptor2` shell (an AIR that
computes nothing) would mislabel it. The MEMBERSHIP algebra of the same tree already IS Lean-emitted
(`MerkleMembership4aryEmit` → `merkle-membership-4ary-general.json`, consumed by `circuit::merkle_air`).

This module is the faithful COMPUTED-root author; the differential is the byte-identity proof.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} (inherited from chunk 1); the byte-pins are
computable `#guard`s over the real permutation (interpreter-evaluated, no `native_decide`), exactly
like the `Poseidon2BabyBearW16` KAT.
-/
import Dregg2.Circuit.CommitmentTreeAccumulator
import Dregg2.Circuit.Poseidon2BabyBearW16

namespace Dregg2.Circuit.Emit.CommitmentTreeAppendEmit

open Dregg2.Circuit.CommitmentTreeAccumulator (leafAt nodeAt root append emptyHash EMPTY_LEAF
  root_distinct_extracts_collision append_offpath_unchanged append_length)

set_option autoImplicit false

/-! ## §0 — `hash4to1Real`: the REAL deployed `hash_4_to_1`, over the KAT-locked permutation.

`circuit/src/poseidon2.rs::hash_4_to_1` sets state `[in0, in1, in2, in3, 4, 0…0]` (rate 0..3 = the
four child hashes; position 4 = the arity domain-separation tag `4`; positions 5..15 = 0), applies
the permutation, and returns lane 0. `stateOf` builds exactly that 16-felt state (child hashes are
canonical BabyBear values in `[0, p)`, read via `Int.toNat`); `hash4to1Real` permutes and reads
lane 0. Bit-exact to the deployed hash by the `Poseidon2BabyBearW16.perm` KAT. -/

/-- The 16-felt Poseidon2 state `hash_4_to_1` seeds from a 4-child list (`state[4] = 4` arity tag). -/
def stateOf (xs : List ℤ) : List Nat :=
  [ (xs.getD 0 0).toNat, (xs.getD 1 0).toNat, (xs.getD 2 0).toNat, (xs.getD 3 0).toNat,
    4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ]

/-- **`hash4to1Real`** — the deployed `hash_4_to_1` realized over the real BabyBear Poseidon2-w16
permutation: seed the arity-tagged state, permute, read lane 0. The node compression the DEPLOYED
note tree uses. -/
def hash4to1Real (xs : List ℤ) : ℤ :=
  ((Dregg2.Circuit.Poseidon2BabyBearW16.perm (stateOf xs)).getD 0 0 : ℤ)

-- KAT: `hash4to1Real [0,1,2,3]` equals the deployed `hash_4_to_1([0,1,2,3]).0` byte-for-byte
-- (captured from `circuit/src/poseidon2.rs`). If the Lean permutation diverged from the deployed
-- hash, this `#guard` would fail the build.
#guard decide (hash4to1Real [0, 1, 2, 3] = (319108099 : ℤ))

/-! ## §1 — `rootReal`: chunk 1's proven `root`, instantiated at the REAL hash — computes deployed bytes. -/

/-- **`rootReal depth leaves`** — the DEPLOYED note-tree root, computed in Lean: chunk 1's proven
`CommitmentTreeAccumulator.root` at the real `hash4to1Real`. Byte-identical to
`Poseidon2MerkleTree::root().0` (see the `#guard` goldens below and the Rust differential). -/
def rootReal (depth : Nat) (leaves : List ℤ) : ℤ := root hash4to1Real depth leaves

/-- `rootReal` is definitionally chunk 1's `root` at the real hash — so EVERY chunk-1 theorem
(binding, append locality, additivity) holds of the deployed computed object by instantiation. -/
theorem rootReal_eq (depth : Nat) (leaves : List ℤ) :
    rootReal depth leaves = root hash4to1Real depth leaves := rfl

/-- `[1, 2, …, n]` as an `ℤ` list — the leaf sequences the Rust differential mirrors (`BabyBear::new(i)`). -/
def mkSeq (n : Nat) : List ℤ := (List.range n).map (fun k => ((k + 1 : Nat) : ℤ))

/-! ## §2 — the DEPLOYED-ROOT BYTE-PINS (the golden integers the Rust differential also asserts).

Each `#guard` is `rootReal depth leaves = <deployed Poseidon2MerkleTree::root().0>`. Interpreter-
evaluated over the real permutation (~85 permutations for a depth-4 tree), no `native_decide`. -/

-- depth 2 (capacity 16): empty · sparse · exactly-4 · half · full-1 · full.
#guard decide (rootReal 2 (mkSeq 0)  = (1354085513 : ℤ))
#guard decide (rootReal 2 (mkSeq 3)  = (1895531837 : ℤ))
#guard decide (rootReal 2 (mkSeq 4)  = (1834518077 : ℤ))
#guard decide (rootReal 2 (mkSeq 8)  = (198394206  : ℤ))
#guard decide (rootReal 2 (mkSeq 15) = (983932440  : ℤ))
#guard decide (rootReal 2 (mkSeq 16) = (1501679053 : ℤ))

-- depth 3 (capacity 64): empty · sparse · half · full-1 · full.
#guard decide (rootReal 3 (mkSeq 0)  = (62072511  : ℤ))
#guard decide (rootReal 3 (mkSeq 3)  = (78377282  : ℤ))
#guard decide (rootReal 3 (mkSeq 32) = (746309470 : ℤ))
#guard decide (rootReal 3 (mkSeq 63) = (552841819 : ℤ))
#guard decide (rootReal 3 (mkSeq 64) = (230905478 : ℤ))

-- depth 4 (capacity 256): empty · sparse · half · full.
#guard decide (rootReal 4 (mkSeq 0)   = (1331265460 : ℤ))
#guard decide (rootReal 4 (mkSeq 3)   = (1948100911 : ℤ))
#guard decide (rootReal 4 (mkSeq 128) = (851116238  : ℤ))
#guard decide (rootReal 4 (mkSeq 256) = (524603802  : ℤ))

/-! ### Append prefixes at depth 2 (the incremental-accumulator byte-pins).

`append` is genuinely additive (`append_length`); each prefix root is the deployed root after that
many appends. The Rust differential asserts the DEPLOYED tree reproduces these same integers at every
prefix — the incremental path never diverges from the from-scratch build. -/

#guard decide (rootReal 2 (mkSeq 0) = (1354085513 : ℤ))                  -- k = 0
#guard decide (rootReal 2 (append (mkSeq 0) 1) = (1206744973 : ℤ))       -- k = 1
#guard decide (rootReal 2 (append (mkSeq 1) 2) = (570831052  : ℤ))       -- k = 2
#guard decide (rootReal 2 (append (mkSeq 2) 3) = (1895531837 : ℤ))       -- k = 3
#guard decide (rootReal 2 (append (mkSeq 3) 4) = (1834518077 : ℤ))       -- k = 4
#guard decide (rootReal 2 (append (mkSeq 4) 5) = (895893929  : ℤ))       -- k = 5

-- append is additive on the pinned prefixes (never idempotent): each append grows the length by one.
#guard decide ((append (mkSeq 4) 5).length = 5)

/-! ## §3 — the HONEST BINDING holds at the REAL deployed hash (no floor assumed).

The chunk-1 collision-extraction reduction, instantiated at `hash4to1Real`: a forged DEPLOYED root
does not presuppose injectivity — it EXHIBITS a genuine `hash_4_to_1` collision. This is what an
adversary who publishes a note-tree root for a tampered commitment sequence must actually clear. -/

/-- **`rootReal_distinct_extracts_collision`** — two leaf sequences that differ inside the tree's
capacity `[0, 4^depth)` yet publish the SAME deployed root EXHIBIT a genuine `hash4to1Real`
(= deployed `hash_4_to_1`) collision. Chunk 1's honest binding, at the real deployed hash. -/
theorem rootReal_distinct_extracts_collision (xs ys : List ℤ) (depth : Nat)
    (hroot : rootReal depth xs = rootReal depth ys)
    (hdiff : ∃ j, j < 4 ^ depth ∧ leafAt xs j ≠ leafAt ys j) :
    ∃ l l' : List ℤ, l ≠ l' ∧ hash4to1Real l = hash4to1Real l' :=
  root_distinct_extracts_collision hash4to1Real xs ys depth hroot hdiff

/-- **`rootReal_append_offpath_unchanged`** — appending at `p = leaves.length` recomputes the deployed
root only along the single root-to-leaf path whose windows contain `p`; every off-path subtree root is
reused. Chunk 1's incremental-append lemma, at the real deployed hash. -/
theorem rootReal_append_offpath_unchanged (leaves : List ℤ) (cm : ℤ) (level index : Nat)
    (hoff : ¬ (index * 4 ^ level ≤ leaves.length ∧ leaves.length < (index + 1) * 4 ^ level)) :
    nodeAt hash4to1Real (append leaves cm) level index
      = nodeAt hash4to1Real leaves level index :=
  append_offpath_unchanged hash4to1Real leaves cm level index hoff

/-! ## §4 — the `@[export]` FFI ENTRY (Rust → Lean): the DEPLOYED note-tree root, COMPUTED in Lean.

This is the FIRST cutover step toward retiring the hand-rolled Rust root arithmetic
(`commit/src/poseidon2_tree.rs::compute_node_at_level`/`root`/`append`): expose `rootReal` — the
Lean-authored deployed-byte root — across the established `@[export] String → String` ABI (the
`Dregg2.Crypto.HandlebarsFFI` / `dregg_render_with_proof` precedent, marshalled by the C bridge
`dregg-lean-ffi/src/lib.rs::lean_string_bridge`). Once the C-bridge registration + Rust call site land,
the note-tree root becomes a CALL INTO this verified Lean object rather than a Rust reimplementation
kept byte-equal by a differential — collapsing the two implementations to one.

Wire contract (this export DEFINES it; the Rust caller must match):
  * input  : `"<depth>;<leaf0>,<leaf1>,…,<leafN-1>"` — `depth` a decimal `Nat`; leaves comma-separated
             decimal canonical BabyBear values in `[0, p)`. Empty leaf set is `"<depth>;"`.
  * output : the decimal deployed root (`rootReal depth leaves`), or `"ERR"` on a malformed wire.
Fail CLOSED: any parse failure → `"ERR"` (never a silent zero that could pass for a real root).

SCOPE NOTE (why this is step 1, not the whole cutover): the root is only PART of what the Rust tree
computes. `prove_membership` gathers per-level SIBLINGS via the same `compute_node_at_level` — the
Lean model authors NO membership witness generation. A true single implementation must ALSO export the
membership sibling/position generation from Lean (or that Rust node arithmetic stays for membership and
only the root routes through here). This export lands the root leg; the membership leg is the follow-on. -/

/-- Parse a `"leaf0,leaf1,…"` segment into canonical `ℤ` leaves; `""` is the empty tree. Fail-closed. -/
def parseLeaves (s : String) : Option (List ℤ) :=
  if s = "" then some []
  else (s.splitOn ",").mapM (fun t => t.toNat?.map (fun n => (n : ℤ)))

/-- **`@[export dregg_note_tree_root]`** — the deployed 4-ary Poseidon2 note-tree root, computed by the
verified Lean `rootReal` over the KAT-locked real hash. Wire per §4; malformed → `"ERR"`. -/
@[export dregg_note_tree_root]
def noteTreeRootWire (wire : String) : String :=
  match wire.splitOn ";" with
  | [depthStr, leavesStr] =>
      match depthStr.toNat?, parseLeaves leavesStr with
      | some depth, some leaves => toString (rootReal depth leaves)
      | _, _ => "ERR"
  | _ => "ERR"

-- The export reproduces the deployed goldens byte-for-byte (the same integers the Rust tree emits and
-- the retiring differential asserts) — so the FFI cutover is byte-exact by construction.
#guard noteTreeRootWire "2;" = "1354085513"          -- empty depth-2 tree
#guard noteTreeRootWire "2;1,2,3" = "1895531837"      -- rootReal 2 (mkSeq 3)
#guard noteTreeRootWire "2;1,2,3,4" = "1834518077"    -- rootReal 2 (mkSeq 4)
#guard noteTreeRootWire "3;1,2,3" = "78377282"        -- rootReal 3 (mkSeq 3)
-- Fail-closed on malformed wires (no silent zero root).
#guard noteTreeRootWire "garbage" = "ERR"
#guard noteTreeRootWire "2;1,x,3" = "ERR"
#guard noteTreeRootWire "2;1;3" = "ERR"

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms rootReal_eq
#assert_axioms rootReal_distinct_extracts_collision
#assert_axioms rootReal_append_offpath_unchanged

end Dregg2.Circuit.Emit.CommitmentTreeAppendEmit
