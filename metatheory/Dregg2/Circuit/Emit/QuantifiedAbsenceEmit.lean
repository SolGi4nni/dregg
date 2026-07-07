/-
# Dregg2.Circuit.Emit.QuantifiedAbsenceEmit — the emit-from-Lean descriptor for the
`quantified_absence` family (Approach B: the certified-complement quotient accumulator).

## What this file IS

A faithful `EffectVmDescriptor2` that DECLARES, in the IR-v2 grammar, the per-element relation the
hand-written `QuotientAccumulatorAir` (`circuit/src/quantified_absence.rs:438`) enforces on each row
of its BabyBear⁴-extension trace. That AIR proves the "for-all-NOT" statement via the accumulator
quotient `Acc_all / Acc_satisfying`: for each element it checks the polynomial-division identity

    w · (α − elem) + v == Acc_all          (over BabyBear⁴, X⁴ − 11)

by materializing the three intermediate extension values `diff = α − elem`, `prod = w · diff`, and
`sum = prod + v`, then binding `sum == Acc_all`. Every enforced constraint is Base-arithmetic
(`VmConstraint.gate`) or a boundary `PiBinding`; the AIR does NO hashing (the element arrives
pre-hashed, embedded into the extension), so this descriptor declares NO chip/range table — the
`node8`/heap lookups the hash-carrying families need do not appear here.

The three hand-AIR constraints (`quantified_absence.rs:476-495`), per BabyBear⁴ limb:
  * C1  `diff  == α − elem`         → 4 linear `gate`s  (`diffGates`)
  * C2  `prod  == w · diff`         → 4 degree-2 `gate`s realizing `ExtElem::mul` mod (X⁴ − 11) (`prodGates`)
  * C3  `sum   == prod + v`         → 4 linear `gate`s  (`sumGates`)
and the boundary (`quantified_absence.rs:515-523`) `sum == Acc_all` on the active rows, emitted as
the first-row `PiBinding` of the SUM group to the `Acc_all` public inputs (`sumPins`).

`α` lives in the public inputs (`quantified_absence.rs:464`, `public_inputs[4..8]`); a `gate` body
cannot read a PI, so the descriptor materializes α into a dedicated ALPHA column group pinned to the
α public inputs by `PiBinding` (`alphaPins`), and C1's gate reads those columns — the emit realization
the dossier prescribes. The single-logical-row-repeated model (á la `MerkleMembershipEmit`) carries
one element's witness; the hand AIR's per-row uniformity of α / `Acc_all` over the N active rows is
represented by the repeated row, exactly as the Merkle template folds a depth-2 opening into one row.

## THE OFF-DESCRIPTOR CARRIER (honest scope — DECO-leaf posture)

Like the hand AIR, this descriptor proves ONLY the arithmetic quotient identity over witness-supplied
`(elem, w, v)` bound to the public `(Acc_all, α)`. It does NOT recompute the predicate, and it does
NOT verify that `Acc_all` is a genuine product `∏(α − hᵢ)` or that `v` is the honest cofactor — those
remain the executor-verified / witnessed carriers of the family (the hand AIR does not check them
either; this is the weak-but-faithful emit, not a soundness upgrade). Named explicitly so no reader
mistakes the descriptor for a full non-membership proof.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + genuinely-proven, non-vacuous
semantic lemmas: the C1 diff gate (linear, `omega`), the C2 ext-mult limb-0 gate (the degree-2
bilinear form with the X⁴−11 coupling, `ring`/`linarith`), and the C3 sum gate. `#assert_axioms`
kernel-clean. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.QuantifiedAbsenceEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmConstraint2 emitVmJson2)

set_option autoImplicit false

/-! ## §1 — The BabyBear⁴ trace column layout (six extension groups + the materialized α group).

Each group is four consecutive base columns (limb 0..3), matching `qacc_col` in
`quantified_absence.rs:384`; ALPHA (24..27) is the emit-only group holding the α challenge, pinned to
the α public inputs. -/

def E0 : Nat := 0    -- ELEMENT   (elem embedded in BabyBear⁴; cols 0..3)
def E1 : Nat := 1
def E2 : Nat := 2
def E3 : Nat := 3
def Q0 : Nat := 4    -- QUOTIENT  (w; cols 4..7)
def Q1 : Nat := 5
def Q2 : Nat := 6
def Q3 : Nat := 7
def V0 : Nat := 8    -- REMAINDER (v; cols 8..11)
def V1 : Nat := 9
def V2 : Nat := 10
def V3 : Nat := 11
def D0 : Nat := 12   -- DIFF      (α − elem; cols 12..15)
def D1 : Nat := 13
def D2 : Nat := 14
def D3 : Nat := 15
def P0 : Nat := 16   -- PRODUCT   (w · diff; cols 16..19)
def P1 : Nat := 17
def P2 : Nat := 18
def P3 : Nat := 19
def S0 : Nat := 20   -- SUM       (prod + v; cols 20..23)
def S1 : Nat := 21
def S2 : Nat := 22
def S3 : Nat := 23
def A0 : Nat := 24   -- ALPHA     (materialized α challenge; cols 24..27)
def A1 : Nat := 25
def A2 : Nat := 26
def A3 : Nat := 27

/-- Total main-trace width: seven BabyBear⁴ groups. -/
def QACC_WIDTH : Nat := 28

/-- Public inputs: `Acc_all` (0..3) then `α` (4..7). (`num_elements`, the hand AIR's PI 8, indexes
its multi-row boundary loop and has no role in the single-row emit — dropped, not referenced.) -/
def PI_ACC0 : Nat := 0
def PI_ALPHA0 : Nat := 4
def QACC_PI_COUNT : Nat := 8

/-! ## §2 — Constraint bodies. -/

/-- `(col a) − (col b)` as an `EmittedExpr` (the `MerkleMembershipEmit` subtraction idiom). -/
def subCols (a b : Nat) : EmittedExpr := .add (.var a) (.mul (.const (-1)) (.var b))

/-- Product of the two named columns. -/
def vv (a b : Nat) : EmittedExpr := .mul (.var a) (.var b)

/-- Multiply by the BabyBear⁴ irreducible constant W = 11 (the reduction of X⁴ ≡ 11). -/
def w11 (e : EmittedExpr) : EmittedExpr := .mul (.const 11) e

/-! ### C1 — `diff == α − elem`, per limb. Body `(Dᵢ − Aᵢ) + Eᵢ` vanishes iff `Dᵢ = Aᵢ − Eᵢ`. -/

def diffBody (d a e : Nat) : EmittedExpr := .add (subCols d a) (.var e)

def diffGates : List VmConstraint2 :=
  [ .base (.gate (diffBody D0 A0 E0))
  , .base (.gate (diffBody D1 A1 E1))
  , .base (.gate (diffBody D2 A2 E2))
  , .base (.gate (diffBody D3 A3 E3)) ]

/-! ### C2 — `prod == w · diff` over BabyBear⁴ (X⁴ − 11). The four output-limb polynomials are
`ExtElem::mul` (`accumulator_types.rs:93`) term-for-term. Body `Pᵢ − cᵢ` vanishes iff `Pᵢ = cᵢ`. -/

/-- `c0 = q0·d0 + 11·(q1·d3 + q2·d2 + q3·d1)`. -/
def prodC0 : EmittedExpr :=
  .add (vv Q0 D0) (w11 (.add (.add (vv Q1 D3) (vv Q2 D2)) (vv Q3 D1)))
/-- `c1 = q0·d1 + q1·d0 + 11·(q2·d3 + q3·d2)`. -/
def prodC1 : EmittedExpr :=
  .add (.add (vv Q0 D1) (vv Q1 D0)) (w11 (.add (vv Q2 D3) (vv Q3 D2)))
/-- `c2 = q0·d2 + q1·d1 + q2·d0 + 11·(q3·d3)`. -/
def prodC2 : EmittedExpr :=
  .add (.add (.add (vv Q0 D2) (vv Q1 D1)) (vv Q2 D0)) (w11 (vv Q3 D3))
/-- `c3 = q0·d3 + q1·d2 + q2·d1 + q3·d0` (no W term — the X⁴ head has no wraparound). -/
def prodC3 : EmittedExpr :=
  .add (.add (.add (vv Q0 D3) (vv Q1 D2)) (vv Q2 D1)) (vv Q3 D0)

def prodBody (p : Nat) (c : EmittedExpr) : EmittedExpr := .add (.var p) (.mul (.const (-1)) c)

def prodGates : List VmConstraint2 :=
  [ .base (.gate (prodBody P0 prodC0))
  , .base (.gate (prodBody P1 prodC1))
  , .base (.gate (prodBody P2 prodC2))
  , .base (.gate (prodBody P3 prodC3)) ]

/-! ### C3 — `sum == prod + v`, per limb. Body `(Sᵢ − Pᵢ) − Vᵢ` vanishes iff `Sᵢ = Pᵢ + Vᵢ`. -/

def sumBody (s p v : Nat) : EmittedExpr := .add (subCols s p) (.mul (.const (-1)) (.var v))

def sumGates : List VmConstraint2 :=
  [ .base (.gate (sumBody S0 P0 V0))
  , .base (.gate (sumBody S1 P1 V1))
  , .base (.gate (sumBody S2 P2 V2))
  , .base (.gate (sumBody S3 P3 V3)) ]

/-! ### The boundary — `sum == Acc_all`: first-row PiBinding of the SUM group to the `Acc_all` PIs. -/

def sumPins : List VmConstraint2 :=
  [ .base (.piBinding VmRow.first S0 (PI_ACC0 + 0))
  , .base (.piBinding VmRow.first S1 (PI_ACC0 + 1))
  , .base (.piBinding VmRow.first S2 (PI_ACC0 + 2))
  , .base (.piBinding VmRow.first S3 (PI_ACC0 + 3)) ]

/-! ### The α materialization — first-row PiBinding of the ALPHA group to the α PIs (so C1 reads α). -/

def alphaPins : List VmConstraint2 :=
  [ .base (.piBinding VmRow.first A0 (PI_ALPHA0 + 0))
  , .base (.piBinding VmRow.first A1 (PI_ALPHA0 + 1))
  , .base (.piBinding VmRow.first A2 (PI_ALPHA0 + 2))
  , .base (.piBinding VmRow.first A3 (PI_ALPHA0 + 3)) ]

/-- **`quantifiedAbsenceDesc`** — the certified-complement quotient-accumulator descriptor:
`diff = α − elem`, `prod = w · diff`, `sum = prod + v` (the three per-element relations), with `sum`
pinned to the public `Acc_all` and `α` materialized from its public inputs. -/
def quantifiedAbsenceDesc : EffectVmDescriptor2 :=
  { name        := "quantified-absence-quotient-accumulator::babybear4-v1"
  , traceWidth  := QACC_WIDTH
  , piCount     := QACC_PI_COUNT
  , tables      := []
  , constraints := diffGates ++ prodGates ++ sumGates ++ sumPins ++ alphaPins
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — The byte-pinned wire golden (the Rust decoder ingests THIS string).

THE EQUALITY-GATE ANCHOR: this exact string is embedded verbatim in
`circuit-prove/tests/quantified_absence_emit_gate.rs` (`GOLDEN_JSON`), decoded there via
`parse_vm_descriptor2`, asserted equal to an independent Rust builder, and proven. A drift on either
side breaks THIS `#guard` (Lean) or the Rust `assert_eq!(decoded, hand_built)`. -/

#guard emitVmJson2 quantifiedAbsenceDesc ==
  "{\"name\":\"quantified-absence-quotient-accumulator::babybear4-v1\",\"ir\":2,\"trace_width\":28,\"public_input_count\":8,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"var\",\"v\":0}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}},\"r\":{\"t\":\"var\",\"v\":1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}},\"r\":{\"t\":\"var\",\"v\":2}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}},\"r\":{\"t\":\"var\",\"v\":3}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":12}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"var\",\"v\":13}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":13}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"var\",\"v\":14}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"var\",\"v\":15}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"var\",\"v\":12}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":17}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":18}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":19}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":20,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":21,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":22,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":23,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":24,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":25,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":26,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":27,\"pi_index\":7}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — Genuinely-proven, non-vacuous semantic lemmas (the gate teeth).

Each `_zero_iff` says the emitted gate body vanishes EXACTLY on the intended relation — TRUE when it
holds, FALSE otherwise — the Lean face of the row-for-row `assert_zero` the Rust Ir2 main AIR runs
(`descriptor_ir2.rs:2210`). -/

/-- C1: the diff gate vanishes iff `diff = α − elem` (limb 0; the linear tooth). -/
theorem diffBody0_zero_iff (a : Assignment) :
    (diffBody D0 A0 E0).eval a = 0 ↔ a D0 = a A0 - a E0 := by
  simp only [diffBody, subCols, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- C3: the sum gate vanishes iff `sum = prod + v` (limb 0; the linear tooth). -/
theorem sumBody0_zero_iff (a : Assignment) :
    (sumBody S0 P0 V0).eval a = 0 ↔ a S0 = a P0 + a V0 := by
  simp only [sumBody, subCols, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- C2: the product gate vanishes iff `prod₀` equals the BabyBear⁴ (X⁴−11) mult limb-0 polynomial
`q0·d0 + 11·(q1·d3 + q2·d2 + q3·d1)` — the degree-2 bilinear tooth WITH the irreducible coupling. -/
theorem prodBody0_zero_iff (a : Assignment) :
    (prodBody P0 prodC0).eval a = 0 ↔
      a P0 = a Q0 * a D0 + 11 * (a Q1 * a D3 + a Q2 * a D2 + a Q3 * a D1) := by
  simp only [prodBody, prodC0, vv, w11, EmittedExpr.eval]
  constructor <;> intro h <;> linarith

-- Non-vacuity witnesses: each gate ACCEPTS a consistent assignment and REJECTS an inconsistent one.
-- (diff: D0 = A0 − E0 with A0=9, E0=2 ⇒ D0=7 accepts; D0=8 rejects.)
#guard decide ((diffBody D0 A0 E0).eval
  (fun i => if i = A0 then 9 else if i = E0 then 2 else if i = D0 then 7 else 0) = 0)
#guard decide (¬ ((diffBody D0 A0 E0).eval
  (fun i => if i = A0 then 9 else if i = E0 then 2 else if i = D0 then 8 else 0) = 0))
-- (prod limb 0: q=(1,2,3,4), d=(5,6,7,8) ⇒ c0 = 5 + 11·(16+21+24) = 676. P0=676 accepts; 677 rejects.)
#guard decide ((prodBody P0 prodC0).eval
  (fun i => if i = Q0 then 1 else if i = Q1 then 2 else if i = Q2 then 3 else if i = Q3 then 4
            else if i = D0 then 5 else if i = D1 then 6 else if i = D2 then 7 else if i = D3 then 8
            else if i = P0 then 676 else 0) = 0)
#guard decide (¬ ((prodBody P0 prodC0).eval
  (fun i => if i = Q0 then 1 else if i = Q1 then 2 else if i = Q2 then 3 else if i = Q3 then 4
            else if i = D0 then 5 else if i = D1 then 6 else if i = D2 then 7 else if i = D3 then 8
            else if i = P0 then 677 else 0) = 0))

-- Shape pins.
#guard quantifiedAbsenceDesc.traceWidth == QACC_WIDTH
#guard quantifiedAbsenceDesc.piCount == QACC_PI_COUNT
#guard quantifiedAbsenceDesc.constraints.length == 20
#guard quantifiedAbsenceDesc.tables.length == 0

#assert_axioms diffBody0_zero_iff
#assert_axioms sumBody0_zero_iff
#assert_axioms prodBody0_zero_iff

end Dregg2.Circuit.Emit.QuantifiedAbsenceEmit
