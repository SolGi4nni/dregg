/-
# Dregg2.Circuit.Emit.AccumulatorNonRevocationEmit — the alpha-batch NON-REVOCATION accumulator,
emitted from Lean.

## What this file IS

The emitted `EffectVmDescriptor2` twin of the hand-written DSL AIR
`circuit/src/dsl/accumulator.rs::accumulator_circuit_descriptor` — the RATIONAL-FUNCTION
non-membership batch AIR (NOT the sorted-Poseidon2 accumulator of `AccumulatorOpenEmit.lean` /
`AccumulatorInsertEmit.lean`; those model a categorically different object — a Merkle set-insert).

Each active row proves ONE ancestor's non-membership in a revocation set represented by the public
accumulator `Acc = P(alpha)` (`P(X) = ∏ (X − h_j)`): with `w = Q(alpha)`, `v = P(h)`,
polynomial division gives `Acc = w·(alpha − h) + v` with `v ≠ 0` iff `h ∉ set`. The AIR witnesses
this per row over `BabyBear^4 = BabyBear[X]/(X^4 − 11)`:

  * C1  `diff  = alpha − h`             (4 base-field equalities, degree 1)
  * C2  `prod  = w · diff`              (ext-field mul, 4 degree-2 gates)
  * C3  `sum   = prod + v`              (4 base-field equalities, degree 1)
  * C4  `check = v · v_inv`             (ext-field mul, 4 degree-2 gates — pins `check`)
  * `sum   == Acc`   on every active row (the accumulator binding)
  * `check == (1,0,0,0)` on every active row (forces `v ≠ 0`, i.e. genuine non-membership)

## Faithful mapping onto IR-v2 (`VmConstraint2`) — and the ONE soundness strengthening

The hand AIR references the public `alpha`/`Acc` through auxiliary columns `alpha_aux`/`acc_aux`
(a `.gate` cannot read a PI). It pins those columns to the PIs on the FIRST row (`PiBinding`), and
pins `sum == Acc` / `check == (1,0,0,0)` on EVERY row via `BoundaryRow::Index(k)` boundaries. IR-v2
has no `Index(k)` row tag (only `First`/`Last`), so the "hold on every row" is realized natively:

  * C1..C4, `sum==acc_aux`, `check==(1,0,0,0)` → `.base (.gate …)` (the transition domain `0..n−2`,
    the exact domain the hand AIR's `ConstraintExpr::Polynomial` fires on) PLUS a `.base
    (.boundary .last …)` twin for `sum==acc_aux` / `check` so the LAST active row is covered too
    (mirroring the hand AIR's `Index(n−1)` boundary; C1..C4 are transition-only in BOTH).
  * `alpha_aux`/`acc_aux` → `.base (.piBinding .first …)` (row 0) PLUS a `.windowGate` CONSTANCY
    gate `next[c] − loc[c] = 0` on the transition. The constancy is the IR-v2-native realization of
    "the aux equals its PI on EVERY row": row-0 pin + constancy ⇒ `alpha_aux`/`acc_aux` are the true
    public `alpha`/`Acc` on all rows. The DSL hand AIR OMITS the `alpha_aux` propagation (it pins
    `alpha_aux` only on row 0), which leaves C1 vacuous on rows `1..n−1` (a free `alpha_aux` solves
    `Acc = w·(alpha_aux−h)+v` for ANY `h`). This emit CLOSES that gap — a strict strengthening: every
    honest trace (constant `alpha_aux`, `acc_aux`) is still accepted; the malicious free-`alpha_aux`
    traces the hand AIR wrongly accepts are now REJECTED by the constancy `.windowGate`
    (`tampered_alpha_aux_drift_refuses` in the gate test bites EXACTLY this tooth).

No table is declared (`tables = []`): this AIR uses NO Poseidon2 chip and NO range lookup — pure
arithmetic + boundaries, exactly as the hand AIR (`lookup_tables: vec![]`).

## Axiom hygiene
Definitional descriptor + a byte-pinned `#guard` on `emitVmJson2`, plus genuinely-proven,
non-vacuous semantic lemmas: the constancy tooth (`alpha_constancy_zero_iff`), the accumulator
binding (`accum_row_binding`), and the non-membership `check` tooth (`check0_forces_one`). All
`#assert_axioms`-clean (pure `omega`). NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.AccumulatorNonRevocationEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowConstraint WindowExpr emitVmJson2)

set_option autoImplicit false

/-! ## §1 — The trace column layout (40 columns; mirrors `accumulator_types::col` + the 8 aux). -/

/-- Ancestor hash `h` embedded in `BabyBear^4`: cols 0..3. -/
def HASH : Nat := 0
/-- Quotient witness `w = Q(alpha)`: cols 4..7. -/
def QUOTIENT : Nat := 4
/-- Remainder witness `v = P(h)` (nonzero ⇔ non-member): cols 8..11. -/
def REMAINDER : Nat := 8
/-- Difference `alpha − h`: cols 12..15. -/
def DIFF : Nat := 12
/-- Product `w · (alpha − h)`: cols 16..19. -/
def PRODUCT : Nat := 16
/-- Sum `prod + v` (pinned to `Acc`): cols 20..23. -/
def SUM : Nat := 20
/-- Inverse of `v`: cols 24..27. -/
def V_INV : Nat := 24
/-- `v · v_inv` (pinned to `(1,0,0,0)`): cols 28..31. -/
def CHECK : Nat := 28
/-- Auxiliary `alpha` copy (pinned to `pi[ALPHA]` on row 0, constant across rows): cols 32..35. -/
def ALPHA_AUX : Nat := 32
/-- Auxiliary `Acc` copy (pinned to `pi[ACC]` on row 0, constant across rows): cols 36..39. -/
def ACC_AUX : Nat := 36
/-- Total main-trace width: 32 base + 8 aux. -/
def ACC_WIDTH : Nat := 40

/-- Public-input base for `Acc` (`pi[0..3]`). -/
def PI_ACC : Nat := 0
/-- Public-input base for `alpha` (`pi[4..7]`). -/
def PI_ALPHA : Nat := 4
/-- Public-input count: `Acc(4) + alpha(4) + num_ancestors(1)` (the last is API-only, unconstrained,
exactly as the hand AIR). -/
def PI_COUNT : Nat := 9

/-- The irreducible constant `W` for `BabyBear^4` (`X^4 − 11`). -/
def W : Int := 11

/-! ## §2 — Body builders (fully explicit `EmittedExpr` trees; the Rust twin mirrors these). -/

/-- `coeff · col`. -/
def coeffVar (k : Int) (c : Nat) : EmittedExpr := .mul (.const k) (.var c)
/-- `coeff · colA · colB` (the ext-field cross term). -/
def coeffMul (k : Int) (c d : Nat) : EmittedExpr := .mul (.const k) (.mul (.var c) (.var d))

/-- C1 lane `i`: `diff[i] − alpha_aux[i] + h[i]`. -/
def c1Body (i : Nat) : EmittedExpr :=
  .add (.add (coeffVar 1 (DIFF + i)) (coeffVar (-1) (ALPHA_AUX + i))) (coeffVar 1 (HASH + i))

/-- C3 lane `i`: `sum[i] − prod[i] − v[i]`. -/
def c3Body (i : Nat) : EmittedExpr :=
  .add (.add (coeffVar 1 (SUM + i)) (coeffVar (-1) (PRODUCT + i))) (coeffVar (-1) (REMAINDER + i))

/-- `sum[i] − acc_aux[i]` (the accumulator binding residual). -/
def sumAccBody (i : Nat) : EmittedExpr :=
  .add (coeffVar 1 (SUM + i)) (coeffVar (-1) (ACC_AUX + i))

/-- `check[i] − value_i` where `value = (1,0,0,0)`. -/
def checkOneBody (i : Nat) : EmittedExpr :=
  if i = 0 then .add (coeffVar 1 (CHECK + 0)) (.const (-1)) else coeffVar 1 (CHECK + i)

/-- Ext-field multiply residual `o[lane] − (a · b)[lane]` over `BabyBear[X]/(X^4−W)`, matching the
`accumulator.rs` term lists byte-for-byte (`a` = first factor base col, `b` = second, `o` = output
base col). -/
def extMulLane (o a b : Nat) : Nat → EmittedExpr
  | 0 =>
    .add (.add (.add (.add (coeffVar 1 (o + 0)) (coeffMul (-1) (a + 0) (b + 0)))
      (coeffMul (-W) (a + 1) (b + 3))) (coeffMul (-W) (a + 2) (b + 2))) (coeffMul (-W) (a + 3) (b + 1))
  | 1 =>
    .add (.add (.add (.add (coeffVar 1 (o + 1)) (coeffMul (-1) (a + 0) (b + 1)))
      (coeffMul (-1) (a + 1) (b + 0))) (coeffMul (-W) (a + 2) (b + 3))) (coeffMul (-W) (a + 3) (b + 2))
  | 2 =>
    .add (.add (.add (.add (coeffVar 1 (o + 2)) (coeffMul (-1) (a + 0) (b + 2)))
      (coeffMul (-1) (a + 1) (b + 1))) (coeffMul (-1) (a + 2) (b + 0))) (coeffMul (-W) (a + 3) (b + 3))
  | _ =>
    .add (.add (.add (.add (coeffVar 1 (o + 3)) (coeffMul (-1) (a + 0) (b + 3)))
      (coeffMul (-1) (a + 1) (b + 2))) (coeffMul (-1) (a + 2) (b + 1))) (coeffMul (-1) (a + 3) (b + 0))

/-- The constancy window body for column `c`: `next[c] − loc[c]`. -/
def constBody (c : Nat) : WindowExpr := .add (.nxt c) (.mul (.const (-1)) (.loc c))

/-! ## §3 — The constraint groups (order fixes the byte-pin). -/

def c1Gates : List VmConstraint2 := (List.range 4).map (fun i => .base (.gate (c1Body i)))
def c2Gates : List VmConstraint2 :=
  (List.range 4).map (fun i => .base (.gate (extMulLane PRODUCT QUOTIENT DIFF i)))
def c3Gates : List VmConstraint2 := (List.range 4).map (fun i => .base (.gate (c3Body i)))
def c4Gates : List VmConstraint2 :=
  (List.range 4).map (fun i => .base (.gate (extMulLane CHECK REMAINDER V_INV i)))
def sumAccGates : List VmConstraint2 := (List.range 4).map (fun i => .base (.gate (sumAccBody i)))
def sumAccLast : List VmConstraint2 :=
  (List.range 4).map (fun i => .base (.boundary VmRow.last (sumAccBody i)))
def checkOneGates : List VmConstraint2 := (List.range 4).map (fun i => .base (.gate (checkOneBody i)))
def checkOneLast : List VmConstraint2 :=
  (List.range 4).map (fun i => .base (.boundary VmRow.last (checkOneBody i)))
def alphaPins : List VmConstraint2 :=
  (List.range 4).map (fun i => .base (.piBinding VmRow.first (ALPHA_AUX + i) (PI_ALPHA + i)))
def accPins : List VmConstraint2 :=
  (List.range 4).map (fun i => .base (.piBinding VmRow.first (ACC_AUX + i) (PI_ACC + i)))
def alphaConst : List VmConstraint2 :=
  (List.range 4).map (fun i => .windowGate ⟨constBody (ALPHA_AUX + i), true⟩)
def accConst : List VmConstraint2 :=
  (List.range 4).map (fun i => .windowGate ⟨constBody (ACC_AUX + i), true⟩)

/-- **`accumulatorNonRevDesc`** — the emitted alpha-batch non-revocation descriptor. -/
def accumulatorNonRevDesc : EffectVmDescriptor2 :=
  { name        := "dregg-accumulator-nonrev-emit-v2"
  , traceWidth  := ACC_WIDTH
  , piCount     := PI_COUNT
  , tables      := []
  , constraints := c1Gates ++ c2Gates ++ c3Gates ++ c4Gates
                     ++ sumAccGates ++ sumAccLast ++ checkOneGates ++ checkOneLast
                     ++ alphaPins ++ accPins ++ alphaConst ++ accConst
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — The byte-pinned wire golden (the Rust decoder ingests THIS string). -/

#guard emitVmJson2 accumulatorNonRevDesc ==
  "{\"name\":\"dregg-accumulator-nonrev-emit-v2\",\"ir\":2,\"trace_width\":40,\"public_input_count\":9,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":12}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":13}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":34}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":35}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":3}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":12}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":15}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"var\",\"v\":14}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"var\",\"v\":13}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":13}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":12}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"var\",\"v\":15}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"var\",\"v\":14}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":14}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":13}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"var\",\"v\":12}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"var\",\"v\":15}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":15}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":14}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"var\",\"v\":13}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"var\",\"v\":12}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":21}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":17}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":18}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":23}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":19}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":28}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":24}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":27}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":26}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"var\",\"v\":25}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":29}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":25}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":24}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":27}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"var\",\"v\":26}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":30}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":26}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":25}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":24}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"var\",\"v\":27}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":31}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":27}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"var\",\"v\":26}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"var\",\"v\":25}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"var\",\"v\":24}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":36}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":21}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":37}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":38}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":23}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":39}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":36}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":21}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":37}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":38}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":23}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":39}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":28}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":29}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":30}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":31}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":28}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":29}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":30}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":31}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":32,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":33,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":34,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":35,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":36,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":37,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":38,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":39,\"pi_index\":3},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":32},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":32}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":33},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":33}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":34},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":34}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":35}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":36},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":36}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":37}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":38},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":38}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":39},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":39}}}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §5 — Genuinely-proven, non-vacuous semantic lemmas. -/

/-- **The constancy tooth (the soundness strengthening).** The window body is zero EXACTLY when the
aux column does not drift between rows — the Lean face of the `.windowGate` that forces `alpha_aux`
(and `acc_aux`) to carry the true PI on every row, closing the hand AIR's free-`alpha_aux` gap. -/
theorem alpha_constancy_zero_iff (env : VmRowEnv) (c : Nat) :
    (constBody c).eval env = 0 ↔ env.nxt c = env.loc c := by
  simp only [constBody, WindowExpr.eval]
  constructor <;> intro h <;> omega

/-- **The accumulator binding.** On a row where C3 (`sum = prod + v`) and the `sum==acc_aux` gate
both hold, `prod + v = acc_aux` (lane 0) — i.e. `w·(alpha−h) + v = Acc`, the accumulator equation. -/
theorem accum_row_binding (a : Assignment)
    (hc3 : (c3Body 0).eval a = 0) (hsum : (sumAccBody 0).eval a = 0) :
    a PRODUCT + a REMAINDER = a ACC_AUX := by
  simp only [c3Body, sumAccBody, coeffVar, EmittedExpr.eval, Nat.add_zero] at hc3 hsum
  omega

/-- **The non-membership `check` tooth.** The lane-0 `check` gate is zero EXACTLY when `check[0] = 1`
— combined with C4 (`check = v·v_inv`), this forces `v ≠ 0` (genuine non-membership). -/
theorem check0_forces_one (a : Assignment) :
    (checkOneBody 0).eval a = 0 ↔ a CHECK = 1 := by
  have h0 : checkOneBody 0 = .add (coeffVar 1 (CHECK + 0)) (.const (-1)) := rfl
  rw [h0]
  simp only [coeffVar, EmittedExpr.eval, Nat.add_zero]
  constructor <;> intro h <;> omega

-- Non-vacuity witnesses (TRUE and FALSE): the constancy gate ACCEPTS a non-drifting window and
-- REJECTS a drifting one; the check gate ACCEPTS `check[0]=1` and REJECTS `check[0]=0`.
#guard decide ((constBody ALPHA_AUX).eval
  { loc := fun _ => 3, nxt := fun _ => 3, pub := fun _ => 0 } = 0)
#guard decide (¬ ((constBody ALPHA_AUX).eval
  { loc := fun _ => 3, nxt := fun j => if j = ALPHA_AUX then 4 else 3, pub := fun _ => 0 } = 0))
#guard decide ((checkOneBody 0).eval (fun i => if i = CHECK then 1 else 0) = 0)
#guard decide (¬ ((checkOneBody 0).eval (fun _ => 0) = 0))

-- Shape pins.
#guard accumulatorNonRevDesc.traceWidth == ACC_WIDTH
#guard accumulatorNonRevDesc.piCount == PI_COUNT
#guard accumulatorNonRevDesc.constraints.length == 48
#guard accumulatorNonRevDesc.tables == []

#assert_axioms alpha_constancy_zero_iff
#assert_axioms accum_row_binding
#assert_axioms check0_forces_one

end Dregg2.Circuit.Emit.AccumulatorNonRevocationEmit
