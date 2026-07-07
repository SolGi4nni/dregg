/-
# Dregg2.Circuit.Emit.PredicatesRelationalCompoundEmit — the `predicates-relational-compound`
family emitted into IR-v2, following the `MerkleMembershipEmit.lean` template.

## What this file IS

Two `EffectVmDescriptor2`s, authored in Lean and byte-pinned (`emitVmJson2` `#guard`), that
RE-EXPRESS the hand-written DSL predicate AIRs in the IR-v2 grammar the real prover
(`prove_vm_descriptor2` / `verify_vm_descriptor2`) interprets:

* **`compoundPredicateDesc`** — the twin of `circuit/src/dsl/predicates/compound.rs`
  (`compound_predicate_circuit_descriptor`, `dregg-compound-predicate-dsl-v2`): AND / OR / NOT /
  Threshold / Custom composition of up to 8 binary sub-predicate results, with per-sub-proof
  commitment binding. It is PURE `Base` gates + first-row `PiBinding`s — the compound AIR has NO
  in-circuit hash or range (`tree_hash`/commitments are hashed off-circuit; the in-circuit
  discipline is the boolean gate tree + the `subcommit == expected` equality + the PI pins).

* **`relationalPredicateDesc`** — the twin of `circuit/src/dsl/predicates/relational.rs`
  (`relational_predicate_descriptor`, `dregg-relational-predicate-dsl-v2`): a comparison
  `value_a <op> value_b` over two Poseidon2-committed values. The ONLY non-arithmetic hand-AIR
  constraint is the gated `Hash2to1` commitment binding (C14/C15) — mapped here to an arity-2
  `Poseidon2Chip` lookup (`chip_absorb_all_lanes(2, [v, r])[0] == hash_2_to_1(v, r)`, the arity-2
  face of the arity-4 mapping `MerkleMembershipEmit` KATs). The 30-bit range decomposition
  (C6/C7/C8) is kept in its hand-AIR ARITHMETIC form (gated `Base` gates), matching the hand-AIR's
  `lookup_tables: vec![]` — a `TableSem::Range` lookup is the idiomatic alternative but would change
  the accept-set encoding, so `Base` gates preserve the hand-AIR semantics.

## The gated-hash → unconditional-lookup posture (honest scope statement)

The hand-AIR gates C14/C15 by `commit_verify_flag`; the IR-v2 grammar has no gated lookup, so the
two commitment lookups are emitted UNCONDITIONALLY. This pins the DEPLOYED posture: the production
entry (`relational_predicate_air::prove_value_comparison`) sets `verify_commitments: true`, i.e.
`commit_verify_flag = 1`, so the commitment binding is always live. The unconditional lookup is the
`commit_verify_flag = 1` specialization — a faithful STRENGTHENING (strictly smaller accept-set)
of the hand-AIR toward its own deployed use; the `commit_verify_flag` binary gate (C11) is kept.

## The Rust equality gate

`circuit-prove/tests/predicates_relational_compound_emit_gate.rs` embeds both byte-pinned goldens,
decodes each via `parse_vm_descriptor2`, asserts equality with an independently hand-built
`EffectVmDescriptor2`, proves an HONEST witness through the REAL `prove_vm_descriptor2` (ACCEPT),
and mutates the witness to force real per-constraint UNSAT (the mutation canaries).

## Axiom hygiene

Definitional descriptors + byte-pinned `#guard`s on the wire strings + genuinely-proven,
non-vacuous semantic lemmas (`atLeastOne_zero_iff`, `binBody_zero_iff`, `high_bit_gate_zero_iff`),
each `#assert_axioms`-clean. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.PredicatesRelationalCompoundEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTuple CHIP_RATE CHIP_OUT_LANES
   emitVmJson2)

set_option autoImplicit false

/-! ## §0 — EmittedExpr / VmConstraint2 builder helpers (shared by both descriptors). -/

/-- `a - k` (subtract an integer constant). -/
def subC (a : EmittedExpr) (k : Int) : EmittedExpr := .add a (.const (-k))

/-- `a - x_v` (subtract a column). -/
def subV (a : EmittedExpr) (v : Nat) : EmittedExpr := .add a (.mul (.const (-1)) (.var v))

/-- The binary-check body `x_c · (x_c − 1)` (zero iff `x_c ∈ {0,1}`). -/
def binBody (c : Nat) : EmittedExpr := .mul (.var c) (subC (.var c) 1)

/-- `1 − x_c`. -/
def oneMinus (c : Nat) : EmittedExpr := .add (.const 1) (.mul (.const (-1)) (.var c))

/-- Right-associated product of a nonempty expression list (`[] ↦ 1`). -/
def prodE : List EmittedExpr → EmittedExpr
  | []      => .const 1
  | [x]     => x
  | x :: xs => .mul x (prodE xs)

/-- Right-associated sum of an expression list (`[] ↦ 0`). -/
def sumE : List EmittedExpr → EmittedExpr
  | []      => .const 0
  | [x]     => x
  | x :: xs => .add x (sumE xs)

/-- The `AtLeastOne` body `∏ (1 − x_c)` (zero iff at least one flag is 1). -/
def atLeastOne (cols : List Nat) : EmittedExpr := prodE (cols.map oneMinus)

/-- A per-row `Base` gate `body = 0`. -/
def gate (body : EmittedExpr) : VmConstraint2 := .base (.gate body)

/-- A first-row PI pin `local[col] = pi[k]`. -/
def piFirst (col k : Nat) : VmConstraint2 := .base (.piBinding VmRow.first col k)

/-! ## §1 — The COMPOUND predicate descriptor (`dregg-compound-predicate-dsl-v2` twin).

Column layout (39 cols) mirrors `compound.rs`: `sub_result[0..7]`, five op selectors,
`composed_result`, `tree_hash`, `and_intermediate`, `threshold_k`, `sum_count`,
`sub_proof_commitment[0..7]`, `expected_commitment[0..7]`, custom-gate cols, `commitment_check`. -/

def OP_AND : Nat := 8
def OP_OR : Nat := 9
def OP_NOT : Nat := 10
def OP_THRESHOLD : Nat := 11
def OP_CUSTOM : Nat := 12
def COMPOSED : Nat := 13
def TREE_HASH : Nat := 14
def AND_INT : Nat := 15
def THRESHOLD_K : Nat := 16
def SUBCOMMIT0 : Nat := 18
def EXPCOMMIT0 : Nat := 26
def GATE_OUT : Nat := 37
def COMPOUND_WIDTH : Nat := 39
def COMPOUND_PI : Nat := 11

/-- The compound constraint list (per-row gates first, then the 11 first-row PI pins). -/
def compoundConstraints : List VmConstraint2 :=
  -- C1–C8: sub_result[0..7] binary.
  (List.range 8).map (fun i => gate (binBody i))
  -- C9–C13: the five operator selectors binary.
  ++ [gate (binBody OP_AND), gate (binBody OP_OR), gate (binBody OP_NOT),
      gate (binBody OP_THRESHOLD), gate (binBody OP_CUSTOM)]
  -- C14: at least one operator selected (∏(1−op_i), degree 5).
  ++ [gate (atLeastOne [OP_AND, OP_OR, OP_NOT, OP_THRESHOLD, OP_CUSTOM])]
  -- C15: composed_result binary.
  ++ [gate (binBody COMPOSED)]
  -- C16: AND  — op_and·(composed − and_intermediate).
  ++ [gate (.mul (.var OP_AND) (subV (.var COMPOSED) AND_INT))]
  -- C17: OR   — op_or·(composed + and_intermediate − 1).
  ++ [gate (.mul (.var OP_OR) (sumE [.var COMPOSED, .var AND_INT, .const (-1)]))]
  -- C18: NOT  — op_not·(composed + sub_result_0 − 1).
  ++ [gate (.mul (.var OP_NOT) (sumE [.var COMPOSED, .var 0, .const (-1)]))]
  -- C19: Threshold — op_threshold·(composed − and_intermediate).
  ++ [gate (.mul (.var OP_THRESHOLD) (subV (.var COMPOSED) AND_INT))]
  -- C20: Custom — op_custom·(composed − gate_output).
  ++ [gate (.mul (.var OP_CUSTOM) (subV (.var COMPOSED) GATE_OUT))]
  -- C21: gate_output binary.
  ++ [gate (binBody GATE_OUT)]
  -- C22–C29: sub_proof_commitment[i] == expected_commitment[i].
  ++ (List.range 8).map (fun i => gate (subV (.var (SUBCOMMIT0 + i)) (EXPCOMMIT0 + i)))
  -- Boundaries: composed==pi0, tree_hash==pi1, threshold_k==pi2, expected_commitment[i]==pi[3+i].
  ++ [piFirst COMPOSED 0, piFirst TREE_HASH 1, piFirst THRESHOLD_K 2]
  ++ (List.range 8).map (fun i => piFirst (EXPCOMMIT0 + i) (3 + i))

def compoundPredicateDesc : EffectVmDescriptor2 :=
  { name        := "dregg-compound-predicate-ir2-v1"
  , traceWidth  := COMPOUND_WIDTH
  , piCount     := COMPOUND_PI
  , tables      := []
  , constraints := compoundConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §2 — The RELATIONAL predicate descriptor (`dregg-relational-predicate-dsl-v2` twin).

Base columns 0..44 mirror `relational.rs`; the two Poseidon2 commitment lookups add 7 exposed
permutation-lane columns each (45..51, 52..58), so the IR-v2 trace width is 59. -/

def VALUE_A : Nat := 0
def BLINDING_A : Nat := 1
def VALUE_B : Nat := 2
def BLINDING_B : Nat := 3
def DIFF : Nat := 4
def DIFF_BITS_START : Nat := 5
def NUM_DIFF_BITS : Nat := 30
def NEQ_INV : Nat := 35
def RESULT_BIT : Nat := 36
def RANGE_FLAG : Nat := 37
def EQ_FLAG : Nat := 38
def NEQ_FLAG : Nat := 39
def COMMIT_A : Nat := 41
def COMMIT_B : Nat := 42
def COMMIT_VERIFY : Nat := 43
def ZERO_PAD : Nat := 44
def LANES_A : List Nat := [45, 46, 47, 48, 49, 50, 51]
def LANES_B : List Nat := [52, 53, 54, 55, 56, 57, 58]
def REL_WIDTH : Nat := 59
def REL_PI : Nat := 3

/-- `Σ_{i<30} 2^i · diff_bit_i` — the range recomposition of `diff`. -/
def recomposeExpr : EmittedExpr :=
  sumE ((List.range NUM_DIFF_BITS).map
    (fun i => .mul (.const ((2 ^ i : Nat) : Int)) (.var (DIFF_BITS_START + i))))

/-- Arity-2 `Poseidon2Chip` lookup binding `digestCol = hash_2_to_1(inA, inB)`, exposing lanes 1..7
in `laneCols` — the arity-2 face of `MerkleMembershipEmit.level0Lookup`. -/
def commitLookup (inA inB digestCol : Nat) (laneCols : List Nat) : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTuple [.var inA, .var inB] digestCol laneCols⟩

/-- The relational constraint list. -/
def relationalConstraints : List VmConstraint2 :=
  -- C1: result_bit == pi[2] (first-row pin; the hand-AIR's per-row PiBinding + boundary collapse
  --      to this under the identical-row trace, with C2 forcing result_bit=1 on transition rows).
  [piFirst RESULT_BIT 2]
  -- C2: result_bit == 1.
  ++ [gate (subC (.var RESULT_BIT) 1)]
  -- C3: range_flag / eq_flag / neq_flag binary.
  ++ [gate (binBody RANGE_FLAG), gate (binBody EQ_FLAG), gate (binBody NEQ_FLAG)]
  -- C4: exactly one flag active (range + eq + neq − 1 == 0).
  ++ [gate (sumE [.var RANGE_FLAG, .var EQ_FLAG, .var NEQ_FLAG, .const (-1)])]
  -- C5: at least one flag active.
  ++ [gate (atLeastOne [RANGE_FLAG, EQ_FLAG, NEQ_FLAG])]
  -- C6: 30× diff-bit binary, gated by range_flag.
  ++ (List.range NUM_DIFF_BITS).map
       (fun i => gate (.mul (.var RANGE_FLAG) (binBody (DIFF_BITS_START + i))))
  -- C7: bit recomposition Σ 2^i·bit_i == diff, gated by range_flag.
  ++ [gate (.mul (.var RANGE_FLAG) (subV recomposeExpr DIFF))]
  -- C8: the high diff bit is zero, gated by range_flag (bounds diff < 2^29).
  ++ [gate (.mul (.var RANGE_FLAG) (.var (DIFF_BITS_START + NUM_DIFF_BITS - 1)))]
  -- C9: EQ check diff == 0, gated by eq_flag.
  ++ [gate (.mul (.var EQ_FLAG) (.var DIFF))]
  -- C10: NEQ check diff·neq_inverse == 1, gated by neq_flag.
  ++ [gate (.mul (.var NEQ_FLAG) (subC (.mul (.var DIFF) (.var NEQ_INV)) 1))]
  -- C11: commit_verify_flag binary.
  ++ [gate (binBody COMMIT_VERIFY)]
  -- C12/C13: commitment_a == pi[0], commitment_b == pi[1] (first-row pins).
  ++ [piFirst COMMIT_A 0, piFirst COMMIT_B 1]
  -- C14/C15: commitment == hash_2_to_1(value, blinding) — arity-2 Poseidon2 chip lookups.
  ++ [commitLookup VALUE_A BLINDING_A COMMIT_A LANES_A,
      commitLookup VALUE_B BLINDING_B COMMIT_B LANES_B]
  -- C16: zero_pad == 0.
  ++ [gate (.var ZERO_PAD)]

def relationalPredicateDesc : EffectVmDescriptor2 :=
  { name        := "dregg-relational-predicate-ir2-v1"
  , traceWidth  := REL_WIDTH
  , piCount     := REL_PI
  , tables      := []
  , constraints := relationalConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — The byte-pinned wire goldens (the Rust decoder ingests THESE strings). -/

#guard emitVmJson2 compoundPredicateDesc ==
  "{\"name\":\"dregg-compound-predicate-ir2-v1\",\"ir\":2,\"trace_width\":39,\"public_input_count\":11,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":37}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":31}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":13,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":14,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":16,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":26,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":27,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":28,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":29,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":30,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":31,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":32,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":33,\"pi_index\":10}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 relationalPredicateDesc ==
  "{\"name\":\"dregg-relational-predicate-ir2-v1\",\"ir\":2,\"trace_width\":59,\"public_input_count\":3,\"tables\":[],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":36,\"pi_index\":2},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":37}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":38}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":39}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":34},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":34},\"r\":{\"t\":\"const\",\"v\":-1}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":6}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":7}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":8}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":10}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":11}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":128},\"r\":{\"t\":\"var\",\"v\":12}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":13}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":512},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1024},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2048},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4096},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8192},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16384},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":32768},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"var\",\"v\":21}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":131072},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":262144},\"r\":{\"t\":\"var\",\"v\":23}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":524288},\"r\":{\"t\":\"var\",\"v\":24}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1048576},\"r\":{\"t\":\"var\",\"v\":25}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2097152},\"r\":{\"t\":\"var\",\"v\":26}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4194304},\"r\":{\"t\":\"var\",\"v\":27}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8388608},\"r\":{\"t\":\"var\",\"v\":28}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16777216},\"r\":{\"t\":\"var\",\"v\":29}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":33554432},\"r\":{\"t\":\"var\",\"v\":30}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":67108864},\"r\":{\"t\":\"var\",\"v\":31}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":134217728},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":268435456},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":536870912},\"r\":{\"t\":\"var\",\"v\":34}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"var\",\"v\":34}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"var\",\"v\":4}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":35}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":41,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":42,\"pi_index\":1},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":41},{\"t\":\"var\",\"v\":45},{\"t\":\"var\",\"v\":46},{\"t\":\"var\",\"v\":47},{\"t\":\"var\",\"v\":48},{\"t\":\"var\",\"v\":49},{\"t\":\"var\",\"v\":50},{\"t\":\"var\",\"v\":51}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":42},{\"t\":\"var\",\"v\":52},{\"t\":\"var\",\"v\":53},{\"t\":\"var\",\"v\":54},{\"t\":\"var\",\"v\":55},{\"t\":\"var\",\"v\":56},{\"t\":\"var\",\"v\":57},{\"t\":\"var\",\"v\":58}]},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":44}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — Genuinely-proven, non-vacuous semantic lemmas (the gate teeth). -/

/-- The binary-check body is zero EXACTLY when the column is 0 or 1. -/
theorem binBody_zero_iff (a : Assignment) (c : Nat) :
    (binBody c).eval a = 0 ↔ a c = 0 ∨ a c = 1 := by
  simp only [binBody, subC, EmittedExpr.eval]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rintro (h | h) <;> simp [h]

-- Non-vacuity: the binary body ACCEPTS 1 and REJECTS 2.
#guard decide ((binBody 0).eval (fun _ => 1) = 0)
#guard decide (¬ ((binBody 0).eval (fun _ => 2) = 0))

/-- The `AtLeastOne` body over two flags is zero EXACTLY when at least one is 1. -/
theorem atLeastOne_zero_iff (a : Assignment) (x y : Nat) :
    (atLeastOne [x, y]).eval a = 0 ↔ a x = 1 ∨ a y = 1 := by
  simp only [atLeastOne, oneMinus, prodE, List.map, EmittedExpr.eval]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rintro (h | h) <;> simp [h]

-- Non-vacuity: at-least-one over [x,y] REJECTS (0,0) and ACCEPTS (1,0).
#guard decide (¬ ((atLeastOne [0, 1]).eval (fun _ => 0) = 0))
#guard decide ((atLeastOne [0, 1]).eval (fun i => if i = 0 then 1 else 0) = 0)

/-- The range high-bit gate (`range_flag · diff_bit_29`) is zero EXACTLY when `range_flag = 0`
or the high bit is 0 — the `diff < 2^29` bound. TRUE when the high bit clears, FALSE otherwise. -/
theorem high_bit_gate_zero_iff (a : Assignment) (hr : a RANGE_FLAG = 1) :
    (.mul (.var RANGE_FLAG) (.var (DIFF_BITS_START + NUM_DIFF_BITS - 1)) : EmittedExpr).eval a = 0
      ↔ a (DIFF_BITS_START + NUM_DIFF_BITS - 1) = 0 := by
  simp only [EmittedExpr.eval, hr]
  constructor <;> intro h <;> omega

-- Non-vacuity: with range_flag=1 the high-bit gate REJECTS a set high bit, ACCEPTS a clear one.
#guard decide (¬ ((EmittedExpr.mul (.var RANGE_FLAG) (.var 34)).eval (fun _ => 1) = 0))
#guard decide ((EmittedExpr.mul (.var RANGE_FLAG) (.var 34)).eval
  (fun i => if i = RANGE_FLAG then 1 else 0) = 0)

/-! ## §5 — Shape pins. -/

#guard compoundPredicateDesc.traceWidth == 39
#guard compoundPredicateDesc.piCount == 11
#guard compoundPredicateDesc.constraints.length == 40
#guard relationalPredicateDesc.traceWidth == 59
#guard relationalPredicateDesc.piCount == 3
#guard relationalPredicateDesc.constraints.length == 47
#guard (chipLookupTuple [.var VALUE_A, .var BLINDING_A] COMMIT_A LANES_A).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES

#assert_axioms binBody_zero_iff
#assert_axioms atLeastOne_zero_iff
#assert_axioms high_bit_gate_zero_iff

end Dregg2.Circuit.Emit.PredicatesRelationalCompoundEmit
