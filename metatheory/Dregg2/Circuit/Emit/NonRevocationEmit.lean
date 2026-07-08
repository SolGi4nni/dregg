/-
# Dregg2.Circuit.Emit.NonRevocationEmit — the emit-from-Lean sorted-tree NON-MEMBERSHIP descriptor
(the `revocation` family: prove an item is NOT revoked).

## What this file IS

A REAL `EffectVmDescriptor2` that DECLARES, in the IR-v2 grammar, the non-membership statement the
hand-written non-revocation AIR (`circuit/src/dsl/revocation.rs`,
`non_revocation_circuit_descriptor`) enforces: *a queried item `x` sits STRICTLY between two ADJACENT
committed sorted leaves `L < x < R`, both members of the public revocation-tree root*. An item that is
strictly bracketed by two adjacent present leaves cannot itself be present — that is the freshness
(non-revocation) proof.

It replaces the hand DSL circuit's per-row-selector multi-row layout (a control row + `2·TREE_DEPTH`
Merkle rows, direction-bit gated) with a SINGLE active-row descriptor in the deployed IR-v2 grammar,
proven through the REAL `prove_vm_descriptor2` / `verify_vm_descriptor2`. The emitted JSON
(`emitVmJson2`) is BYTE-PINNED below (`#guard`); the Rust equality gate
(`circuit-prove/tests/non_revocation_emit_gate.rs`) decodes THIS exact string via
`parse_vm_descriptor2`, asserts it equals an independently hand-built descriptor, proves an honest
freshness witness (ACCEPT), and mutation canaries (forged root / de-bracketed item / non-adjacent
neighbors / forged leaf / forged sibling / forged queried item) force real UNSAT.

## The hand-AIR constraints (C1–C12 + boundaries) and how they map (audited against revocation.rs)

  * **C5** node-hash binding `col2 = hash_fact(col0, [col1])` on Merkle rows  →  `Poseidon2Chip`
    lookups. The generic main-side chip lookup is served on `BUS_P2` by the ARITY-TAG seeding
    (`chip_absorb_lanes`), i.e. `hash_2_to_1` (arity 2, `descriptor_ir2.rs:3413 hash2_state_c`), the
    binary-node hash. (`hash_fact`'s `BUS_FACT` marker seeding is reachable only by the internal
    map-ops chains, NOT by a descriptor's generic `TID_P2` lookup — so a faithful binary-Merkle EMIT
    names the arity-2 node hash, exactly as `MerkleMembershipEmit` names the arity-4 node hash.)
  * **C6/C7** ordering `diff_left = x − L − 1`, `diff_right = R − x − 1`  →  Base gates.
  * **C8–C11** the strict half-field ordering bound (`ORDERING_BITS = 30`,
    `HALF_P_MINUS_1 = 1006632959`): `(HALF_P_MINUS_1 − diff)` fits in 30 bits  →  a Base gate binding
    a `range-wire` column to `HALF_P_MINUS_1 − diff`, plus a `TableSem::Range { bits := 30 }` LOOKUP on
    that column. THE non-membership tooth: an item that violates the half-field ordering bound has a
    range-wire ≥ 2^30, which no limb decomposition serves → UNSAT (`descriptor_ir2.rs:3643` refuses to
    build such a trace; the `eval_decomp` reconstruction gate would fail regardless).
  * **C12** adjacency `right_position − left_position − 1 = 0`  →  a Base gate.
  * **Boundaries** revocation-root pin + no-double-spend queried-item pin  →  `PiBinding`.

## The representative single-active-row shape (honest scope statement)

The hand AIR proves membership of the two neighbors along INDEPENDENT direction-bit-gated paths. This
descriptor realizes the adjacent pair as the depth-2 tree's BOTTOM SIBLINGS sharing the path to the
root (`PAR0 = hash_2_to_1(L, R)`, then `root = hash_2_to_1(PAR0, sib1)`) — the canonical even-left-
position case — so the honest witness is CONSTRUCTIBLE (two distinct leaves genuinely reaching one
committed root, which two free independent canonical paths never could). The load-bearing
non-membership content (the strict-ordering bracket, the adjacency gate, both bracketing leaves
committed under the public root, the queried-item binding) is enforced in full; the direction-general
multi-row layout is the hand AIR's, this is its single-active-row IR-v2 realization at the
representative shape — exactly the depth/shape fixing `MerkleMembershipEmit` does for membership.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + genuinely-proven, non-vacuous
semantic lemmas (each gate body is zero iff its intended integer equation holds — TRUE and FALSE
witnessed). `#assert_axioms` on each lemma (pure `omega`). NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.NonRevocationEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTuple rangeTableDef
   CHIP_RATE CHIP_OUT_LANES emitVmJson2)

set_option autoImplicit false

/-! ## §1 — Constants + the single-row column layout. -/

/-- `(p−1)/2 − 1` for BabyBear (`p = 2013265921`) — the deployed `revocation.rs::HALF_P_MINUS_1`. The
strict-ordering bound `diff < (p−1)/2` is proven by decomposing `HALF_P_MINUS_1 − diff` into 30 bits. -/
def HALF_P_MINUS_1 : Int := 1006632959

/-- The half-field ordering-bound limb width (`revocation.rs::ORDERING_BITS`). -/
def ORDERING_BITS : Nat := 30

-- Control columns.
/-- The queried item `x` (control-row `COL_0`), pinned to `pi[QUERIED_ITEM]`. -/
def X : Nat := 0
/-- The left neighbor `L` (leaf 0 of the adjacent bottom-sibling pair). -/
def LEAF_L : Nat := 1
/-- The right neighbor `R` (leaf 1 of the adjacent bottom-sibling pair). -/
def LEAF_R : Nat := 2
/-- The left neighbor's tree position. -/
def LPOS : Nat := 3
/-- The right neighbor's tree position (adjacency forces `RPOS = LPOS + 1`). -/
def RPOS : Nat := 4
/-- `diff_left = x − L − 1` (the lower gap witness). -/
def DIFF_L : Nat := 5
/-- `diff_right = R − x − 1` (the upper gap witness). -/
def DIFF_R : Nat := 6
/-- The left range-wire `HALF_P_MINUS_1 − diff_left` (range-checked to 30 bits). -/
def RL : Nat := 7
/-- The right range-wire `HALF_P_MINUS_1 − diff_right` (range-checked to 30 bits). -/
def RR : Nat := 8

-- Merkle columns (the shared depth-2 path of the adjacent pair).
/-- Level-0 node digest `= hash_2_to_1(L, R)` (out0 of the level-0 chip lookup). -/
def PAR0 : Nat := 9
/-- Level-1 path input (continuity forces `CUR1 = PAR0`). -/
def CUR1 : Nat := 10
/-- Level-1 sibling. -/
def SIB1 : Nat := 11
/-- Level-1 node digest `= hash_2_to_1(CUR1, SIB1)` = the ROOT (out0 of the level-1 chip lookup). -/
def PAR1 : Nat := 12

/-- The seven exposed permutation lane columns 1..7 of the level-0 chip lookup. -/
def LEVEL0_LANES : List Nat := [13, 14, 15, 16, 17, 18, 19]
/-- The seven exposed permutation lane columns 1..7 of the level-1 chip lookup. -/
def LEVEL1_LANES : List Nat := [20, 21, 22, 23, 24, 25, 26]

/-- Total main-trace width: 13 base columns + 7 + 7 chip lanes. -/
def NONREV_WIDTH : Nat := 27

/-- `pi[0]` = the public revocation root. -/
def ROOT_PI : Nat := 0
/-- `pi[1]` = the queried item (the no-double-spend binding "b"). -/
def QUERIED_PI : Nat := 1

/-! ## §2 — Constraint bodies (Base gates as `EmittedExpr`). -/

/-- `x − c` (the twin of the hand AIR's continuity/consistency subtractions). -/
def subBody (a b : Nat) : EmittedExpr := .add (.var a) (.mul (.const (-1)) (.var b))

/-- Continuity: `CUR1 − PAR0` (level 1's path input equals level 0's parent). -/
def contBody : EmittedExpr := subBody CUR1 PAR0

/-- `diff_left − x + L + 1` — zero iff `diff_left = x − L − 1` (hand AIR C6). -/
def diffLBody : EmittedExpr :=
  .add (.add (.add (.var DIFF_L) (.mul (.const (-1)) (.var X))) (.var LEAF_L)) (.const 1)

/-- `diff_right − R + x + 1` — zero iff `diff_right = R − x − 1` (hand AIR C7). -/
def diffRBody : EmittedExpr :=
  .add (.add (.add (.var DIFF_R) (.mul (.const (-1)) (.var LEAF_R))) (.var X)) (.const 1)

/-- `RL + diff_left − HALF_P_MINUS_1` — zero iff `RL = HALF_P_MINUS_1 − diff_left` (hand AIR C10). -/
def rangeLBindBody : EmittedExpr :=
  .add (.add (.var RL) (.var DIFF_L)) (.const (-HALF_P_MINUS_1))

/-- `RR + diff_right − HALF_P_MINUS_1` — zero iff `RR = HALF_P_MINUS_1 − diff_right` (hand AIR C11). -/
def rangeRBindBody : EmittedExpr :=
  .add (.add (.var RR) (.var DIFF_R)) (.const (-HALF_P_MINUS_1))

/-- `RPOS − LPOS − 1` — zero iff the two neighbor positions are consecutive (hand AIR C12). -/
def adjBody : EmittedExpr :=
  .add (.add (.var RPOS) (.mul (.const (-1)) (.var LPOS))) (.const (-1))

/-! ## §3 — The constraint list. -/

/-- Level-0 `L,R → PAR0` step: an arity-2 `Poseidon2Chip` lookup absorbing `[L, R]`, binding out0 to
`PAR0` (the parent of the adjacent bottom-sibling pair). -/
def level0Lookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTuple [.var LEAF_L, .var LEAF_R] PAR0 LEVEL0_LANES⟩

/-- Level-1 `CUR1,SIB1 → PAR1` step: an arity-2 `Poseidon2Chip` lookup absorbing `[CUR1, SIB1]`,
binding out0 to `PAR1` (the root). -/
def level1Lookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTuple [.var CUR1, .var SIB1] PAR1 LEVEL1_LANES⟩

/-- The left range lookup: `RL ∈ [0, 2^30)` (the strict lower-gap half-field bound). -/
def rangeLLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var RL]⟩

/-- The right range lookup: `RR ∈ [0, 2^30)` (the strict upper-gap half-field bound). -/
def rangeRLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var RR]⟩

/-- THE LOWER-BOUND FIX (rung-2 `emitfix` promoted): a DIRECT range lookup on `diff_left` itself.
`RL = HALF − diff_left ∈ [0,2^30)` alone only bounds `diff_left ≤ HALF` — a negative `diff_left`
(`= p − small`, i.e. `x ≤ L`, a member/out-of-bracket) gives `RL = HALF + small < 2^30` and leaks in.
Adding `diff_left ∈ [0,2^30)` intersects to pin `diff_left ∈ [0, HALF]` (a wrapped negative is `≥ p−… > 2^30`,
excluded), forcing the STRICT lower bound `x > L`. Zero new columns (`DIFF_L` already exists). -/
def rangeLDiffLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var DIFF_L]⟩

/-- THE LOWER-BOUND FIX for the upper gap: a DIRECT range lookup on `diff_right`, forcing `x < R`
strictly (closes the `x == R` / `x > R` member-claimed-fresh window). -/
def rangeRDiffLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var DIFF_R]⟩

/-- **`nonRevocationDesc`** — the sorted-tree NON-MEMBERSHIP descriptor.
Constraints (in order): the two child→parent chip lookups, the continuity gate, the two ordering
gates, the two range-wire binding gates, the two range lookups, the adjacency gate, the root pin, and
the queried-item pin. The chip table (`TID_P2`) is IMPLICITLY present (Presence-detected from the
chip lookups); the range table is DECLARED (it carries the `bits`). -/
def nonRevocationDesc : EffectVmDescriptor2 :=
  { name        := "dregg-non-revocation-sorted-tree::poseidon2-v1"
  , traceWidth  := NONREV_WIDTH
  , piCount     := 2
  , tables      := [rangeTableDef ORDERING_BITS]
  , constraints :=
      [ level0Lookup
      , level1Lookup
      , .base (.gate contBody)
      , .base (.gate diffLBody)
      , .base (.gate diffRBody)
      , .base (.gate rangeLBindBody)
      , .base (.gate rangeRBindBody)
      , rangeLLookup
      , rangeRLookup
      , rangeLDiffLookup
      , rangeRDiffLookup
      , .base (.gate adjBody)
      , .base (.piBinding VmRow.first PAR1 ROOT_PI)
      , .base (.piBinding VmRow.first X QUERIED_PI) ]
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — The byte-pinned wire golden (the Rust decoder ingests THIS string). -/

#guard emitVmJson2 nonRevocationDesc ==
  "{\"name\":\"dregg-non-revocation-sorted-tree::poseidon2-v1\",\"ir\":2,\"trace_width\":27,\"public_input_count\":2,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":30}],\"constraints\":[{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":24},{\"t\":\"var\",\"v\":25},{\"t\":\"var\",\"v\":26}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"var\",\"v\":1}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"const\",\"v\":-1006632959}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":6}},\"r\":{\"t\":\"const\",\"v\":-1006632959}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":7}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":8}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":5}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":6}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":12,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":1}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §5 — Genuinely-proven, non-vacuous semantic lemmas (the gate teeth). -/

/-- The continuity gate body is zero EXACTLY when the levels chain (`CUR1 = PAR0`). -/
theorem cont_body_zero_iff (a : Assignment) :
    contBody.eval a = 0 ↔ a CUR1 = a PAR0 := by
  simp only [contBody, subBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The left-ordering gate body is zero EXACTLY when `diff_left = x − L − 1`. -/
theorem diffL_body_zero_iff (a : Assignment) :
    diffLBody.eval a = 0 ↔ a DIFF_L = a X - a LEAF_L - 1 := by
  simp only [diffLBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The right-ordering gate body is zero EXACTLY when `diff_right = R − x − 1`. -/
theorem diffR_body_zero_iff (a : Assignment) :
    diffRBody.eval a = 0 ↔ a DIFF_R = a LEAF_R - a X - 1 := by
  simp only [diffRBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The left range-wire binding is zero EXACTLY when `RL = HALF_P_MINUS_1 − diff_left` — so the
30-bit range lookup on `RL` is the strict half-field bound on `diff_left`. -/
theorem rangeLBind_body_zero_iff (a : Assignment) :
    rangeLBindBody.eval a = 0 ↔ a RL = HALF_P_MINUS_1 - a DIFF_L := by
  simp only [rangeLBindBody, HALF_P_MINUS_1, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The adjacency gate body is zero EXACTLY when the neighbor positions are consecutive. -/
theorem adj_body_zero_iff (a : Assignment) :
    adjBody.eval a = 0 ↔ a RPOS = a LPOS + 1 := by
  simp only [adjBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

-- Non-vacuity witnesses: each gate ACCEPTS its intended assignment and REJECTS a violating one.
#guard decide (contBody.eval (fun i => if i = CUR1 ∨ i = PAR0 then 5 else 0) = 0)
#guard decide (¬ (contBody.eval (fun i => if i = CUR1 then 5 else 0) = 0))
#guard decide (adjBody.eval (fun i => if i = RPOS then 8 else if i = LPOS then 7 else 0) = 0)
#guard decide (¬ (adjBody.eval (fun i => if i = RPOS then 9 else if i = LPOS then 7 else 0) = 0))
-- diff_left = x − L − 1 with x = 200, L = 100 ⇒ diff_left = 99: gate zero; a wrong diff_left rejects.
#guard decide (diffLBody.eval
  (fun i => if i = X then 200 else if i = LEAF_L then 100 else if i = DIFF_L then 99 else 0) = 0)
#guard decide (¬ (diffLBody.eval
  (fun i => if i = X then 200 else if i = LEAF_L then 100 else if i = DIFF_L then 98 else 0) = 0))

-- Shape pins.
#guard nonRevocationDesc.traceWidth == NONREV_WIDTH
#guard nonRevocationDesc.piCount == 2
#guard nonRevocationDesc.constraints.length == 14
#guard nonRevocationDesc.tables.length == 1
#guard (chipLookupTuple [.var LEAF_L, .var LEAF_R] PAR0 LEVEL0_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES

#assert_axioms cont_body_zero_iff
#assert_axioms diffL_body_zero_iff
#assert_axioms diffR_body_zero_iff
#assert_axioms rangeLBind_body_zero_iff
#assert_axioms adj_body_zero_iff

end Dregg2.Circuit.Emit.NonRevocationEmit
