/-
# NonRevocationAdjacencyEmit — deployed-depth sorted-tree non-revocation, composed in Lean

The deployed revocation tree is binary and depth 4.  Its node function is the fact-domain
Poseidon2 compression `hash_fact(left, [right])`; its non-membership statement is the conjunction

* the two private neighbours are adjacent members of the public root, and
* the public queried item is strictly bracketed by those neighbours.

The first half is the depth-general, one-tree-level-per-row construction proved and emitted by
`AdjacencyMembershipEmit`.  This module reuses its direction, child-ordering, index reconstruction,
cross-row continuity, shared-power, root-agreement, and internalized-consecutiveness algebra.  The
only node-function specialization is the deployed revocation tree's fact-domain chip seed
`[left, right, 0, 0, 0, 0xFACF, 1]`, rather than adjacency's generic arity-2 node seed.  The second
half is the already-proved `NonRevocationEmit` ordering algebra, attached to the FIRST path row where
`L_CUR` and `U_CUR` are the two leaves.  Rust supplies one witness row per path level and interprets
this emitted descriptor; it authors no constraint.

Public inputs remain exactly `[revocation_root, queried_item]`.  The bracketing leaves and their
indices remain private; membership, common-root agreement, reconstructed-index consecutiveness, and
strict ordering are all internal to the descriptor.  Thus the existing deployed proof wire does not
gain verifier-wrapper obligations or prover-chosen public handles.
-/
import Dregg2.Circuit.Emit.AdjacencyMembershipEmit
import Dregg2.Circuit.Emit.NonRevocationEmit

namespace Dregg2.Circuit.Emit.NonRevocationAdjacencyEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTuple rangeTableDef
   CHIP_RATE CHIP_OUT_LANES emitVmJson2)
open Dregg2.Circuit.Emit.AdjacencyMembershipEmit

set_option autoImplicit false

/-! ## §1 — The five ordering columns appended to adjacency's 32-column path trace. -/

/-- Public queried item `x`. -/
def X : Nat := ADJ_WIDTH
/-- `x - lower - 1`, range-checked directly. -/
def DIFF_L : Nat := X + 1
/-- `upper - x - 1`, range-checked directly. -/
def DIFF_R : Nat := X + 2
/-- `HALF_P_MINUS_1 - DIFF_L`, range-checked to retain the canonical half-field bound. -/
def RL : Nat := X + 3
/-- `HALF_P_MINUS_1 - DIFF_R`, range-checked to retain the canonical half-field bound. -/
def RR : Nat := X + 4

def NONREV_ADJ_WIDTH : Nat := ADJ_WIDTH + 5
def PI_ROOT : Nat := 0
def PI_QUERIED_ITEM : Nat := 1
def NONREV_ADJ_PI_COUNT : Nat := 2

/-- `(p-1)/2 - 1` for BabyBear, shared with `NonRevocationEmit`. -/
def HALF_P_MINUS_1 : Int :=
  Dregg2.Circuit.Emit.NonRevocationEmit.HALF_P_MINUS_1

/-- The deployed strict-order range width, shared with `NonRevocationEmit`. -/
def ORDERING_BITS : Nat := Dregg2.Circuit.Emit.NonRevocationEmit.ORDERING_BITS

/-- `hash_fact`'s deployed fact-domain marker, `0xFACF`. -/
def FACT_MARK : Int := 64207

/-! ## §2 — Deployed fact-domain membership paths, one level per row. -/

/-- The deployed revocation node lookup: `parent = hash_fact(left, [right])`.  The arity-7 chip
seed is byte-identical to Rust's fact state `(left,right,0,0,0,0xFACF,1)`. -/
def factNodeLookup (left right parent : Nat) (laneCols : List Nat) : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var left, .var right, .const 0, .const 0, .const 0,
                     .const FACT_MARK, .const 1] parent laneCols⟩

/-- One depth-general authentication-path row.  All non-hash algebra is reused verbatim from the
proved adjacency emitter; only the node lookup is specialized to the deployed fact-domain root. -/
def factPathBlock (cur sib dir left right par idxIn idxOut : Nat) (laneCols : List Nat) :
    List VmConstraint2 :=
  [ .base (.gate (dirBinaryBody dir))
  , .base (.gate (leftOrderBody cur sib dir left))
  , .base (.gate (rightOrderBody cur sib dir right))
  , factNodeLookup left right par laneCols
  , .base (.gate (idxStepBody dir idxIn idxOut))
  , .windowGate (copyWindow cur par)
  , .windowGate (copyWindow idxIn idxOut) ]

/-- Membership + adjacency, with the leaves and indices PRIVATE.  The two paths start at their
private leaves, end at the same public root, reconstruct their indices from direction bits, and the
last-row catch tooth forces those reconstructed indices to differ by exactly one. -/
def membershipAdjacencyConstraints : List VmConstraint2 :=
  factPathBlock L_CUR L_SIB L_DIR L_LEFT L_RIGHT L_PAR
      L_IDX_IN L_IDX_OUT L_PAR_LANES ++
  factPathBlock U_CUR U_SIB U_DIR U_LEFT U_RIGHT U_PAR
      U_IDX_IN U_IDX_OUT U_PAR_LANES ++
  [ .base (.gate pow2Body)
  , .windowGate (copyWindow POW POW2)
  , .base (.piBinding VmRow.last L_PAR PI_ROOT)
  , .base (.piBinding VmRow.last U_PAR PI_ROOT)
  , .base (.boundary VmRow.first powAnchorBody)
  , .base (.boundary VmRow.first (.var L_IDX_IN))
  , .base (.boundary VmRow.first (.var U_IDX_IN))
  , .base (.boundary VmRow.last consecutiveBody) ] ++
  adjLastOrderFix ++ adjLastIdxFix

/-! ## §3 — Strict ordering on the first (leaf) row. -/

/-- `diff_left - x + lower + 1`; zero iff `diff_left = x - lower - 1`. -/
def diffLBody : EmittedExpr :=
  .add (.add (.add (.var DIFF_L) (.mul (.const (-1)) (.var X))) (.var L_CUR)) (.const 1)

/-- `diff_right - upper + x + 1`; zero iff `diff_right = upper - x - 1`. -/
def diffRBody : EmittedExpr :=
  .add (.add (.add (.var DIFF_R) (.mul (.const (-1)) (.var U_CUR))) (.var X)) (.const 1)

/-- Bind the lower canonical-half range wire. -/
def rangeLBindBody : EmittedExpr :=
  .add (.add (.var RL) (.var DIFF_L)) (.const (-HALF_P_MINUS_1))

/-- Bind the upper canonical-half range wire. -/
def rangeRBindBody : EmittedExpr :=
  .add (.add (.var RR) (.var DIFF_R)) (.const (-HALF_P_MINUS_1))

/-- The ordering constraints fire on the first row, where the running path values ARE the leaves.
All four range lookups are table constraints on every row; the witness repeats these five ordering
columns on every path row, so every lookup is served without weakening the first-row bindings. -/
def orderingConstraints : List VmConstraint2 :=
  [ .base (.boundary VmRow.first diffLBody)
  , .base (.boundary VmRow.first diffRBody)
  , .base (.boundary VmRow.first rangeLBindBody)
  , .base (.boundary VmRow.first rangeRBindBody)
  , .lookup ⟨TableId.range, [.var RL]⟩
  , .lookup ⟨TableId.range, [.var RR]⟩
  , .lookup ⟨TableId.range, [.var DIFF_L]⟩
  , .lookup ⟨TableId.range, [.var DIFF_R]⟩
  , .base (.piBinding VmRow.first X PI_QUERIED_ITEM) ]

/-- The composed, deployed-depth-capable non-revocation descriptor.  Trace height is path depth:
depth 4 therefore remains a 16-leaf tree, with four genuinely distinct authentication rows. -/
def nonRevocationAdjacencyDesc : EffectVmDescriptor2 :=
  { name        := "dregg-non-revocation-adjacency::poseidon2-fact-v1"
  , traceWidth  := NONREV_ADJ_WIDTH
  , piCount     := NONREV_ADJ_PI_COUNT
  , tables      := [rangeTableDef ORDERING_BITS]
  , constraints := membershipAdjacencyConstraints ++ orderingConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — Proof teeth: ordering and adjacency are forced, not verifier-wrapper assumptions. -/

theorem diffL_body_zero_iff (a : Assignment) :
    diffLBody.eval a = 0 ↔ a DIFF_L = a X - a L_CUR - 1 := by
  simp only [diffLBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

theorem diffR_body_zero_iff (a : Assignment) :
    diffRBody.eval a = 0 ↔ a DIFF_R = a U_CUR - a X - 1 := by
  simp only [diffRBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

theorem rangeLBind_body_zero_iff (a : Assignment) :
    rangeLBindBody.eval a = 0 ↔ a RL = HALF_P_MINUS_1 - a DIFF_L := by
  simp only [rangeLBindBody, HALF_P_MINUS_1,
    Dregg2.Circuit.Emit.NonRevocationEmit.HALF_P_MINUS_1, EmittedExpr.eval]
  constructor <;> intro h <;> omega

theorem rangeRBind_body_zero_iff (a : Assignment) :
    rangeRBindBody.eval a = 0 ↔ a RR = HALF_P_MINUS_1 - a DIFF_R := by
  simp only [rangeRBindBody, HALF_P_MINUS_1,
    Dregg2.Circuit.Emit.NonRevocationEmit.HALF_P_MINUS_1, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The ordering half has real teeth: its bound diff witnesses force `lower < x < upper`. -/
theorem ordering_forces_strict_bracket (a : Assignment)
    (hL : diffLBody.eval a = 0) (hR : diffRBody.eval a = 0)
    (hLnonneg : 0 ≤ a DIFF_L) (hRnonneg : 0 ≤ a DIFF_R) :
    a L_CUR < a X ∧ a X < a U_CUR := by
  rw [diffL_body_zero_iff] at hL
  rw [diffR_body_zero_iff] at hR
  omega

/-- A forged lower bracket (`x ≤ L`) contradicts the in-descriptor diff binding + direct range. -/
theorem forged_lower_bracket_refuted (a : Assignment)
    (hbind : diffLBody.eval a = 0) (hrange : 0 ≤ a DIFF_L) (hforge : a X ≤ a L_CUR) :
    False := by
  rw [diffL_body_zero_iff] at hbind
  omega

/-- A forged upper bracket (`x ≥ R`) contradicts the in-descriptor diff binding + direct range. -/
theorem forged_upper_bracket_refuted (a : Assignment)
    (hbind : diffRBody.eval a = 0) (hrange : 0 ≤ a DIFF_R) (hforge : a U_CUR ≤ a X) :
    False := by
  rw [diffR_body_zero_iff] at hbind
  omega

/-- The wide-bracket forge is algebraically impossible: if reconstructed indices are not adjacent,
the internal last-row consecutiveness body cannot vanish. -/
theorem nonadjacent_pair_refuted (a : Assignment)
    (hwide : a U_IDX_OUT ≠ a L_IDX_OUT + 1) :
    consecutiveBody.eval a ≠ 0 := by
  intro hzero
  exact hwide ((consecutive_body_zero_iff a).mp hzero)

/-! Non-vacuity witnesses: honest bracket/adjacency accept; each forged pole makes its body nonzero. -/
#guard decide (diffLBody.eval
  (fun i => if i = X then 200 else if i = L_CUR then 100 else if i = DIFF_L then 99 else 0) = 0)
#guard decide (¬ (diffLBody.eval
  (fun i => if i = X then 100 else if i = L_CUR then 100 else if i = DIFF_L then 0 else 0) = 0))
#guard decide (consecutiveBody.eval
  (fun i => if i = U_IDX_OUT then 6 else if i = L_IDX_OUT then 5 else 0) = 0)
#guard decide (¬ (consecutiveBody.eval
  (fun i => if i = U_IDX_OUT then 7 else if i = L_IDX_OUT then 5 else 0) = 0))

/-! ## §5 — Shape and authorship pins. -/
#guard nonRevocationAdjacencyDesc.traceWidth == 37
#guard nonRevocationAdjacencyDesc.piCount == 2
#guard nonRevocationAdjacencyDesc.constraints.length == 39
#guard nonRevocationAdjacencyDesc.tables.length == 1
#guard membershipAdjacencyConstraints.length == 30
#guard orderingConstraints.length == 9
#guard (chipLookupTuple [.var L_LEFT, .var L_RIGHT, .const 0, .const 0, .const 0,
                         .const FACT_MARK, .const 1] L_PAR L_PAR_LANES).length
       == CHIP_RATE + 1 + CHIP_OUT_LANES

#assert_axioms diffL_body_zero_iff
#assert_axioms diffR_body_zero_iff
#assert_axioms rangeLBind_body_zero_iff
#assert_axioms rangeRBind_body_zero_iff
#assert_axioms ordering_forces_strict_bracket
#assert_axioms forged_lower_bracket_refuted
#assert_axioms forged_upper_bracket_refuted
#assert_axioms nonadjacent_pair_refuted

end Dregg2.Circuit.Emit.NonRevocationAdjacencyEmit
