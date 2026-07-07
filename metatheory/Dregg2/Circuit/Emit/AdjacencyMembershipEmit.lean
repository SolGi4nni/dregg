/-
# Dregg2.Circuit.Emit.AdjacencyMembershipEmit — the sorted-set NEIGHBOR-ADJACENCY family,
emitted from Lean (the Golden-Vision non-membership lift, faithful IR-v2 twin of
`circuit/src/membership_adjacency_air.rs`).

## What this file IS

The `EffectVmDescriptor2` for the neighbor-adjacency STARK: given a binary Poseidon2 Merkle
tree of sorted leaves, it proves that `leaf_lower` (at reconstructed index `idx_lower`) and
`leaf_upper` (at `idx_upper`) are **consecutive** leaves under a shared public `root`. That
consecutiveness is what turns `lower < candidate < upper` into a SOUND non-membership witness
(no set member can sit strictly between two adjacent leaves), closing the wide-bracket forge
`membership_adjacency_air.rs` documents (`AIR-SOUNDNESS-AUDIT.md` finding #2).

The trace is MULTI-ROW: one binary-tree level per row, two parallel authentication paths
(lower ‖ upper) plus a shared power-of-two accumulator. The hand AIR's `ConstraintExpr` forms
map onto IR-v2 as:

* `Binary`/`Polynomial` (dir binary, child ordering, index step, pow doubling) → `Base .gate`
  (per-row, on the transition domain — exactly the hand AIR's row-local convention).
* `Hash2to1 (par = hash_2_to_1(left,right))` → a `Poseidon2Chip` arity-2 lookup, out0 = parent,
  lanes 1..7 witnessed. This is the FAITHFUL reconstruction the census flagged: the deployed
  hand AIR carries each Poseidon2 output as a lossy 1-felt digest enforced only by the FRI
  evaluator; the chip lookup binds the FULL permutation, so a forged parent has no serving chip
  row → UNSAT.
* `Transition (next.cur = local.par ; next.idx_in = local.idx_out ; next.pow = local.pow2)`
  → `windowGate` (`onTransition = true`, `nxt`/`loc` over the row window). The hand AIR's
  `ConstraintExpr::Transition` is a pure cross-row copy — the base `VmConstraint.transition`
  form is EffectVM-state-layout indexed, so the faithful twin of a bare `next[a]==local[b]`
  copy is a `windowGate`, NOT `.base .transition`.
* `BoundaryDef::PiBinding First/Last` → `Base .piBinding`; `BoundaryDef::Fixed` (row-0 `pow=1`,
  `idx_in=0`) → `Base .boundary .first`.

## THE CATCH TOOTH (preserved — the census flagged it as SILENTLY DROPPABLE)

`verify_adjacency` (`membership_adjacency_air.rs:627`) enforces `idx_upper - idx_lower == 1`
in the RUST VERIFIER WRAPPER — it is NOT in `adjacency_descriptor()`'s constraint list, so an
emit author who mirrors only the descriptor would drop the forge-closing teeth. We INTERNALIZE
it as a `Base .boundary .last` gate `u_idx_out - l_idx_out - 1 == 0` on the Last row (where the
two `idx_out` columns are already `piBinding`-pinned to the `idx_lower`/`idx_upper` PIs). This
is STRICTLY STRONGER than the wrapper's PI subtraction (it binds the in-circuit reconstructed
indices directly), and it lives IN the descriptor so it can never be dropped. (The wrapper's
own `idx_upper - idx_lower != 1` check at `:627` remains a named verifier-side belt-and-braces.)

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + two genuinely-proven,
non-vacuous semantic lemmas (`consecutive_body_zero_iff` — the catch tooth's teeth; and
`dir_binary_body_zero_iff`). `#assert_axioms` both ⊆ {}. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.AdjacencyMembershipEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowExpr WindowConstraint Lookup TableId chipLookupTuple
   CHIP_RATE CHIP_OUT_LANES emitVmJson2)

set_option autoImplicit false

/-! ## §1 — Trace column layout (18 semantic columns + two 7-lane chip blocks; width 32).

Mirrors `adj_col` in `membership_adjacency_air.rs` for cols 0..18, then appends the two
Poseidon2-chip lane blocks the faithful (non-lossy) digest carries. -/

-- Lower path.
def L_CUR : Nat := 0
def L_SIB : Nat := 1
def L_DIR : Nat := 2
def L_LEFT : Nat := 3
def L_RIGHT : Nat := 4
def L_PAR : Nat := 5
def L_IDX_IN : Nat := 6
def L_IDX_OUT : Nat := 7
-- Upper path (mirror, +8).
def U_CUR : Nat := 8
def U_SIB : Nat := 9
def U_DIR : Nat := 10
def U_LEFT : Nat := 11
def U_RIGHT : Nat := 12
def U_PAR : Nat := 13
def U_IDX_IN : Nat := 14
def U_IDX_OUT : Nat := 15
-- Shared power-of-two accumulator.
def POW : Nat := 16
def POW2 : Nat := 17

/-- Lanes 1..7 of the lower parent's chip permutation (out0 is `L_PAR`). -/
def L_PAR_LANES : List Nat := [18, 19, 20, 21, 22, 23, 24]
/-- Lanes 1..7 of the upper parent's chip permutation (out0 is `U_PAR`). -/
def U_PAR_LANES : List Nat := [25, 26, 27, 28, 29, 30, 31]

/-- Total main-trace width: 18 semantic + 7 + 7 chip lanes. -/
def ADJ_WIDTH : Nat := 32

/-! ## §2 — Public inputs (`adj_pi`). -/
def PI_ROOT : Nat := 0
def PI_LEAF_LOWER : Nat := 1
def PI_LEAF_UPPER : Nat := 2
def PI_IDX_LOWER : Nat := 3
def PI_IDX_UPPER : Nat := 4
def ADJ_PI_COUNT : Nat := 5

/-! ## §3 — Expression builders (the hand AIR's polynomial bodies). -/

/-- `-1 * e`. -/
def negE (e : EmittedExpr) : EmittedExpr := .mul (.const (-1)) e

/-- `dir*(dir-1) = dir*dir - dir` (the `ConstraintExpr::Binary` body). -/
def dirBinaryBody (dir : Nat) : EmittedExpr :=
  .add (.mul (.var dir) (.var dir)) (negE (.var dir))

/-- `left - cur - dir*sib + dir*cur` (child ordering, left). -/
def leftOrderBody (cur sib dir left : Nat) : EmittedExpr :=
  .add (.var left)
    (.add (negE (.var cur))
      (.add (negE (.mul (.var dir) (.var sib))) (.mul (.var dir) (.var cur))))

/-- `right - sib - dir*cur + dir*sib` (child ordering, right). -/
def rightOrderBody (cur sib dir right : Nat) : EmittedExpr :=
  .add (.var right)
    (.add (negE (.var sib))
      (.add (negE (.mul (.var dir) (.var cur))) (.mul (.var dir) (.var sib))))

/-- `idx_out - idx_in - dir*pow` (the same-row index accumulation step). -/
def idxStepBody (dir idxIn idxOut : Nat) : EmittedExpr :=
  .add (.var idxOut) (.add (negE (.var idxIn)) (negE (.mul (.var dir) (.var POW))))

/-- `pow2 - 2*pow` (the same-row doubling helper). -/
def pow2Body : EmittedExpr := .add (.var POW2) (.mul (.const (-2)) (.var POW))

/-- `pow - 1` (the row-0 `Fixed pow = 1` anchor). -/
def powAnchorBody : EmittedExpr := .add (.var POW) (.const (-1))

/-- `u_idx_out - l_idx_out - 1` — THE CATCH TOOTH internalized (consecutiveness on the Last row,
where `L_IDX_OUT`/`U_IDX_OUT` are `piBinding`-pinned to `idx_lower`/`idx_upper`). -/
def consecutiveBody : EmittedExpr :=
  .add (.var U_IDX_OUT) (.add (negE (.var L_IDX_OUT)) (.const (-1)))

/-- A cross-row copy `next[hi] = local[lo]` as a transition `windowGate` body `nxt hi - loc lo`. -/
def copyWindow (hi lo : Nat) : WindowConstraint :=
  { body := .add (.nxt hi) (.mul (.const (-1)) (.loc lo)), onTransition := true }

/-! ## §4 — Per-path constraint block (mirrors the hand AIR's `for (cur,..) in [lower, upper]`). -/

/-- The five per-row gates + two cross-row copies for one authentication path. `laneCols` are the
7 witnessed permutation lanes of `par = hash_2_to_1(left, right)`. -/
def pathBlock (cur sib dir left right par idxIn idxOut : Nat) (laneCols : List Nat) :
    List VmConstraint2 :=
  [ .base (.gate (dirBinaryBody dir))
  , .base (.gate (leftOrderBody cur sib dir left))
  , .base (.gate (rightOrderBody cur sib dir right))
  , .lookup ⟨TableId.poseidon2, chipLookupTuple [.var left, .var right] par laneCols⟩
  , .base (.gate (idxStepBody dir idxIn idxOut))
  , .windowGate (copyWindow cur par)      -- next.cur   = local.par (chain continuity)
  , .windowGate (copyWindow idxIn idxOut) -- next.idx_in = local.idx_out (index carry)
  ]

/-! ## §5 — The full constraint list + descriptor. -/

def adjacencyConstraints : List VmConstraint2 :=
  pathBlock L_CUR L_SIB L_DIR L_LEFT L_RIGHT L_PAR L_IDX_IN L_IDX_OUT L_PAR_LANES ++
  pathBlock U_CUR U_SIB U_DIR U_LEFT U_RIGHT U_PAR U_IDX_IN U_IDX_OUT U_PAR_LANES ++
  [ -- shared power accumulator
    .base (.gate pow2Body)
  , .windowGate (copyWindow POW POW2)            -- next.pow = local.pow2
    -- leaves at row 0
  , .base (.piBinding VmRow.first L_CUR PI_LEAF_LOWER)
  , .base (.piBinding VmRow.first U_CUR PI_LEAF_UPPER)
    -- root at the last row (both paths agree)
  , .base (.piBinding VmRow.last L_PAR PI_ROOT)
  , .base (.piBinding VmRow.last U_PAR PI_ROOT)
    -- reconstructed indices at the last row
  , .base (.piBinding VmRow.last L_IDX_OUT PI_IDX_LOWER)
  , .base (.piBinding VmRow.last U_IDX_OUT PI_IDX_UPPER)
    -- row-0 accumulator anchors (`Fixed`)
  , .base (.boundary VmRow.first powAnchorBody)
  , .base (.boundary VmRow.first (.var L_IDX_IN))
  , .base (.boundary VmRow.first (.var U_IDX_IN))
    -- THE CATCH TOOTH: consecutiveness, internalized on the Last row
  , .base (.boundary VmRow.last consecutiveBody) ]

/-- **`adjacencyDesc`** — the neighbor-adjacency descriptor. Two arity-2 child→parent chip
lookups per level (lower ‖ upper), the per-row ordering/binary/index gates, the cross-row
continuity/carry `windowGate`s, the leaf/root/index `piBinding`s, the row-0 `Fixed` anchors, and
the internalized consecutiveness catch tooth. The chip table (`TID_P2`) is Presence-detected. -/
def adjacencyDesc : EffectVmDescriptor2 :=
  { name        := "dregg-membership-adjacency::poseidon2-v1"
  , traceWidth  := ADJ_WIDTH
  , piCount     := ADJ_PI_COUNT
  , tables      := []
  , constraints := adjacencyConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §6 — The byte-pinned wire golden (the Rust decoder ingests THIS string).

THE EQUALITY-GATE ANCHOR: this exact string is embedded verbatim in
`circuit-prove/tests/adjacency_membership_emit_gate.rs` (`GOLDEN_JSON`), decoded there via
`parse_vm_descriptor2`, asserted equal to an independently hand-built descriptor, then
proven+verified. A drift on either side breaks THIS `#guard` (Lean) or the Rust `assert_eq!`. -/

#guard emitVmJson2 adjacencyDesc ==
  "{\"name\":\"dregg-membership-adjacency::poseidon2-v1\",\"ir\":2,\"trace_width\":32,\"public_input_count\":5,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":2}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":0}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":1}}}}}},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":4},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":24}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":6}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":16}}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":5}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":7}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":10}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":9}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":8}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":9}}}}}},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":25},{\"t\":\"var\",\"v\":26},{\"t\":\"var\",\"v\":27},{\"t\":\"var\",\"v\":28},{\"t\":\"var\",\"v\":29},{\"t\":\"var\",\"v\":30},{\"t\":\"var\",\"v\":31}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":16}}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":13}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":15}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":16}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":16},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":17}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":5,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":13,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":7,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":15,\"pi_index\":4},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":6}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":14}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":7}},\"r\":{\"t\":\"const\",\"v\":-1}}}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §7 — Genuinely-proven, non-vacuous semantic lemmas. -/

/-- THE CATCH TOOTH's teeth: the consecutiveness gate body is zero EXACTLY when the upper index
is one past the lower — TRUE for a genuine adjacent pair, FALSE otherwise. -/
theorem consecutive_body_zero_iff (a : Assignment) :
    consecutiveBody.eval a = 0 ↔ a U_IDX_OUT = a L_IDX_OUT + 1 := by
  simp only [consecutiveBody, negE, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The direction bit is genuinely binary: `dir*(dir-1) = 0 ↔ dir ∈ {0,1}`. -/
theorem dir_binary_body_zero_iff (a : Assignment) :
    (dirBinaryBody L_DIR).eval a = 0 ↔ a L_DIR = 0 ∨ a L_DIR = 1 := by
  have key : (dirBinaryBody L_DIR).eval a = a L_DIR * (a L_DIR - 1) := by
    simp only [dirBinaryBody, negE, EmittedExpr.eval]; ring
  rw [key]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rintro (h0 | h1)
    · rw [h0]; ring
    · rw [h1]; ring

-- Non-vacuity witnesses: consecutiveness ACCEPTS an adjacent pair, REJECTS a gap.
#guard decide (consecutiveBody.eval (fun i => if i = U_IDX_OUT then 6 else if i = L_IDX_OUT then 5 else 0) = 0)
#guard decide (¬ (consecutiveBody.eval (fun i => if i = U_IDX_OUT then 7 else if i = L_IDX_OUT then 5 else 0) = 0))
-- dir binary ACCEPTS 0 and 1, REJECTS 2.
#guard decide ((dirBinaryBody L_DIR).eval (fun _ => 1) = 0)
#guard decide (¬ ((dirBinaryBody L_DIR).eval (fun i => if i = L_DIR then 2 else 0) = 0))

/-! ## §8 — Shape pins. -/
#guard adjacencyDesc.traceWidth == ADJ_WIDTH
#guard adjacencyDesc.piCount == ADJ_PI_COUNT
#guard adjacencyDesc.constraints.length == 26
#guard (chipLookupTuple [.var L_LEFT, .var L_RIGHT] L_PAR L_PAR_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES
#guard L_PAR_LANES.length == CHIP_OUT_LANES - 1
#guard U_PAR_LANES.length == CHIP_OUT_LANES - 1

#assert_axioms consecutive_body_zero_iff
#assert_axioms dir_binary_body_zero_iff

end Dregg2.Circuit.Emit.AdjacencyMembershipEmit
