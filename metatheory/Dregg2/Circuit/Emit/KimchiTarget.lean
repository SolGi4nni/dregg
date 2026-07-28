/-
# Dregg2.Circuit.Emit.KimchiTarget — Kimchi's gate vocabulary as an EMISSION TARGET

`AirBuilder` models dregg's own AIR: a `Head` is `Σ coeff·∏cols + const` and `cgH` lowers it to a
`VmConstraint2` gate. This file models the OTHER end of a compiler — the row vocabulary a Kimchi
(Mina/Pickles) circuit is made of — so that a lowering pass can be written between them and its
semantics preservation can be a theorem rather than a differential test.

## Sourced from the real thing, not from memory

Every constant and every constraint body below is transcribed from `~/dev/proof-systems` at
`f6d958dc05` (workspace `0.7.0`), file and line named at each definition:

  * `GateType` — `kimchi/src/circuits/gate.rs:56-97`, **fourteen** variants, `#[repr(C)]` with
    `Zero` as `#[default]`, so the discriminant ORDER is load-bearing for serialization and
    `KGateType.ordinal` pins it.
  * `COLUMNS = 15`, `PERMUTS = 7` — `kimchi/src/circuits/wires.rs:7,10`. Fifteen witness columns,
    of which only the first seven participate in the permutation argument (`Wirable::wire` asserts
    `col < PERMUTS`, `wires.rs:60`); columns 7..14 are advice-only.
  * The **double**-generic gate — `kimchi/src/circuits/polynomials/generic.rs:55-70,84-117`.
    `GENERIC_REGISTERS = 3`, `GENERIC_COEFFS = 5`, `DOUBLE_GENERIC_COEFFS = 10`, and
    `CONSTRAINTS = 2`: ONE row carries TWO independent generic sub-gates.
  * `RangeCheck0` — `kimchi/src/circuits/polynomials/range_check/circuitgates.rs:76-92,149-232`,
    `CONSTRAINTS = 10`: eight 2-bit crumbs, one 88-bit recomposition, one compact-mode equation.

## What `holds` is, and why the unmodelled gates are `False`

A row's `holds` is the conjunction of the gate's own constraint bodies at that row, over an
arbitrary `CommRing`. Only the three gates this compiler actually emits — `zero`, `generic`,
`rangeCheck0` — have their bodies transcribed. **The rest are `False`, not `True`.**

That is deliberate and it is the fail-CLOSED choice. A `True` default would let the compiler emit a
`Poseidon` or `VarBaseMul` row and still discharge a soundness theorem about it, which is exactly
the "gate that cannot go red" shape. `False` makes such a circuit unsatisfiable instead — so a
soundness theorem over it goes VACUOUS rather than WRONG, and `KGateType.modelled` plus the
anti-vacuity obligation `lowered_all_modelled` (in `KimchiLower`) is what detects the vacuity.

## The generic gate's semantics is not invented here

`KimchiVerify.genericGateConstraint` already transcribes `generic.rs` on the VERIFIER side, and it
is reality-gated: `KimchiRealProofGate`/`KimchiPoseidonGate` drive it on real proofs that o1-labs'
own `kimchi::verifier::verify` accepts. `KimchiTargetWeld.generic_holds_iff_verifier_body` proves
this file's per-row `holds` is exactly that body being zero for every `alpha` — so the target's
semantics is the deployed verifier's, welded, not a second opinion.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`.
NEW file. Imports `AirBuilder` only (for `Assignment`), so it is cheap to depend on.
-/
import Dregg2.Circuit.Emit.AirBuilder

namespace Dregg2.Circuit.Emit.KimchiTarget

set_option autoImplicit false

/-! ## §1 — the row shape: 15 columns, 7 of them permutable. -/

/-- `wires.rs:7` — `pub const COLUMNS: usize = 15`. The number of witness columns in a row. -/
def K_COLUMNS : Nat := 15

/-- `wires.rs:10` — `pub const PERMUTS: usize = 7`. Only columns `0..6` can be wired by the
permutation argument; `7..14` are advice-only and unreachable from a copy constraint. -/
def K_PERMUTS : Nat := 7

/-- `generic.rs:56` — `GENERIC_REGISTERS = 3`. -/
def K_GENERIC_REGISTERS : Nat := 3

/-- `generic.rs:60` — `GENERIC_COEFFS = GENERIC_REGISTERS + 1 /- mul -/ + 1 /- cst -/`. -/
def K_GENERIC_COEFFS : Nat := K_GENERIC_REGISTERS + 1 + 1

/-- `generic.rs:65` — `DOUBLE_GENERIC_COEFFS = GENERIC_COEFFS * 2`. -/
def K_DOUBLE_GENERIC_COEFFS : Nat := K_GENERIC_COEFFS * 2

/-- `generic.rs:69` — `DOUBLE_GENERIC_REGISTERS = GENERIC_REGISTERS * 2`. -/
def K_DOUBLE_GENERIC_REGISTERS : Nat := K_GENERIC_REGISTERS * 2

example : K_GENERIC_COEFFS = 5 := rfl
example : K_DOUBLE_GENERIC_COEFFS = 10 := rfl
example : K_DOUBLE_GENERIC_REGISTERS = 6 := rfl

/-- **`GateType`** — `kimchi/src/circuits/gate.rs:76-97`, all fourteen variants in source order.
`Zero` is `#[default]` and the enum is `#[repr(C)]`, so the ordinals below are the wire encoding. -/
inductive KGateType where
  /-- Zero gate. -/
  | zero
  /-- Generic arithmetic gate (a DOUBLE generic — two sub-gates per row). -/
  | generic
  /-- Poseidon permutation gate (width-3 Pasta, 5 rounds/row). -/
  | poseidon
  /-- Complete EC addition in affine form. -/
  | completeAdd
  /-- EC variable-base scalar multiplication. -/
  | varBaseMul
  /-- EC variable-base scalar multiplication with the endomorphism optimisation. -/
  | endoMul
  /-- The scalar corresponding to an endoscaling. -/
  | endoMulScalar
  /-- Lookup. -/
  | lookup
  /-- Range check, part 0. -/
  | rangeCheck0
  /-- Range check, part 1. -/
  | rangeCheck1
  /-- Foreign-field addition. -/
  | foreignFieldAdd
  /-- Foreign-field multiplication. -/
  | foreignFieldMul
  /-- Keccak XOR-16. -/
  | xor16
  /-- Keccak ROT-64. -/
  | rot64
  deriving Repr, DecidableEq, Inhabited

/-- The `#[repr(C)]` discriminant of `GateType` (`gate.rs:76-97`). Serialization depends on it, so
it is pinned here rather than left to Lean's constructor order. -/
def KGateType.ordinal : KGateType → Nat
  | .zero            => 0
  | .generic         => 1
  | .poseidon        => 2
  | .completeAdd     => 3
  | .varBaseMul      => 4
  | .endoMul         => 5
  | .endoMulScalar   => 6
  | .lookup          => 7
  | .rangeCheck0     => 8
  | .rangeCheck1     => 9
  | .foreignFieldAdd => 10
  | .foreignFieldMul => 11
  | .xor16           => 12
  | .rot64           => 13

/-- Every `GateType` in `gate.rs`, in discriminant order. -/
def KGateType.all : List KGateType :=
  [.zero, .generic, .poseidon, .completeAdd, .varBaseMul, .endoMul, .endoMulScalar,
   .lookup, .rangeCheck0, .rangeCheck1, .foreignFieldAdd, .foreignFieldMul, .xor16, .rot64]

theorem KGateType.all_length : KGateType.all.length = 14 := rfl

theorem KGateType.all_complete (g : KGateType) : g ∈ KGateType.all := by
  cases g <;> decide

theorem KGateType.ordinal_all : KGateType.all.map KGateType.ordinal = List.range 14 := rfl

theorem KGateType.ordinal_injective : Function.Injective KGateType.ordinal := by
  intro a b h; cases a <;> cases b <;> simp_all [KGateType.ordinal]

/-- Whether the gate has an ALWAYS-ON selector commitment in the verifier index, as opposed to an
`Option` one that only exists when the feature flag is set (`kimchi/src/verifier_index.rs:83-132`).
`zero` and `lookup` have no selector polynomial at all. -/
def KGateType.selectorKind : KGateType → String
  | .zero | .lookup => "none"
  | .generic | .poseidon | .completeAdd | .varBaseMul | .endoMul | .endoMulScalar => "always"
  | _ => "optional"

/-- **A Kimchi circuit row.** `CircuitGate<F>` (`gate.rs:128-138`) is `{ typ, wires, coeffs }`.

Two deliberate departures, both named:

  * `wires` here holds VARIABLE indices, not `Wire { row, col }` cells. Cell placement plus the
    permutation argument that identifies copied cells is a SEPARATE pass (`KimchiPartition`'s named
    remainder), and — the reason this is the right differential object — **placement adds no rows**.
    The row COUNT, which is what `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` measures, is fixed here.
  * `coeffs` is `List ℤ` rather than `Vec<F>`: every coefficient this compiler emits is an integer
    (a round constant, a modulus, a power of two, `±1`), and casting into the target ring at
    evaluation keeps the row shape ring-generic. -/
structure KRow where
  gate : KGateType
  wires : List Nat
  coeffs : List ℤ
  deriving Repr, DecidableEq, Inhabited

/-- A row is WELL-FORMED when it carries exactly the 15 witness columns and 15 coefficient columns
a real `CircuitGate` is materialised into. The smart constructors below pad to this. -/
def KRow.wf (r : KRow) : Prop := r.wires.length = K_COLUMNS ∧ r.coeffs.length = K_COLUMNS

instance (r : KRow) : Decidable (KRow.wf r) := by unfold KRow.wf; infer_instance

/-- Pad a list to length `n` with `d`. -/
def padTo {α : Type} (d : α) (n : Nat) (l : List α) : List α :=
  l.take n ++ List.replicate (n - l.length) d

theorem padTo_length {α : Type} (d : α) (n : Nat) (l : List α) (h : l.length ≤ n) :
    (padTo d n l).length = n := by
  simp [padTo, List.length_append, List.length_take, List.length_replicate,
    Nat.min_eq_left h]
  omega

/-- Normalise a row to well-formed shape: 15 wires (padding with column 0) and 15 coefficients
(padding with 0). -/
def KRow.pad (r : KRow) : KRow :=
  { gate := r.gate
  , wires := padTo 0 K_COLUMNS r.wires
  , coeffs := padTo (0 : ℤ) K_COLUMNS r.coeffs }

theorem KRow.pad_wf (r : KRow) (hw : r.wires.length ≤ K_COLUMNS)
    (hc : r.coeffs.length ≤ K_COLUMNS) : (KRow.pad r).wf :=
  ⟨padTo_length _ _ _ hw, padTo_length _ _ _ hc⟩

theorem KRow.pad_gate (r : KRow) : (KRow.pad r).gate = r.gate := rfl

/-! ## §2 — row semantics, over an arbitrary `CommRing`.

Kimchi lives over a Pasta field, but every constraint body is a polynomial identity, so the bodies
are stated `CommRing`-generically exactly as `KimchiVerify` states them. Instantiate at `ZMod pN`
for the deployed statement; instantiate at `ℤ` when a bound argument keeps every intermediate
canonical, which is what the BabyBear reduction in `KimchiPoseidon2` does. -/

section Semantics

variable {R : Type} [CommRing R]

/-- The row's witness values under an assignment. -/
def KRow.wv (a : Nat → R) (r : KRow) : List R := r.wires.map a

/-- The row's coefficients in the target ring. -/
def KRow.cv (r : KRow) : List R := r.coeffs.map (fun z => (z : R))

/-- `w i` — the `i`-th witness column of the row, `0` past the end. -/
def KRow.w (a : Nat → R) (r : KRow) (i : Nat) : R := (r.wv a).getD i 0

/-- `c i` — the `i`-th coefficient of the row, `0` past the end. -/
def KRow.c (r : KRow) (i : Nat) : R := (r.cv (R := R)).getD i 0

/-- **The FIRST generic sub-gate** (`generic.rs:84-100`):
`c₀·w₀ + c₁·w₁ + c₂·w₂ + c₃·(w₀·w₁) + c₄`.
Coefficient roles, `generic.rs:29-31`: `c₀` left, `c₁` right, `c₂` out, `c₃` mul, `c₄` const. -/
def genericBody1 (a : Nat → R) (r : KRow) : R :=
  r.c 0 * r.w a 0 + r.c 1 * r.w a 1 + r.c 2 * r.w a 2
    + r.c 3 * (r.w a 0 * r.w a 1) + r.c 4

/-- **The SECOND generic sub-gate** (`generic.rs:102-117`), on witness columns `3,4,5` and
coefficients `5..9`. One Kimchi row carries BOTH — `CONSTRAINTS = 2` (`generic.rs:55`). -/
def genericBody2 (a : Nat → R) (r : KRow) : R :=
  r.c 5 * r.w a 3 + r.c 6 * r.w a 4 + r.c 7 * r.w a 5
    + r.c 8 * (r.w a 3 * r.w a 4) + r.c 9

/-- The 2-bit "crumb" constraint `x·(x−1)·(x−2)·(x−3)` (`range_check/circuitgates.rs`, the eight
`crumb()` constraints on columns 7..14). Degree 4. -/
def crumbBody (x : R) : R := x * (x - 1) * (x - 2) * (x - 3)

/-- The eight crumb columns of a `RangeCheck0` row: `7..14`
(`range_check/circuitgates.rs:76-92,149-166`). -/
def rc0CrumbCols : List Nat := [7, 8, 9, 10, 11, 12, 13, 14]

/-- The four 12-bit PLOOKUP columns of a `RangeCheck0` row: `3..6`. These are range-constrained by
the lookup argument against `RANGE_CHECK_TABLE_ID = 1` (`lookup/lookups.rs:447-524`,
`LookupPattern::RangeCheck` = four singleton lookups on `w[3..6]`), NOT by a gate body — so a
forcing lemma about them takes the lookup as a HYPOTHESIS, the way `rangeNonneg_forces` takes its
boolean pins. -/
def rc0PlookupCols : List Nat := [3, 4, 5, 6]

/-- The two 12-bit COPY columns of a `RangeCheck0` row: `1,2`. Their lookups are DEFERRED to the
companion `Zero` row (`range_check/gadget.rs:100-111` wires `(0,1)↔(3,3)` etc.). -/
def rc0CopyCols : List Nat := [1, 2]

/-- The place values of a `RangeCheck0` row's twelve limbs/crumbs in the 88-bit recomposition
(`range_check/circuitgates.rs:149-166`): the value `w₀` is
`2⁷⁶·w₁ + 2⁶⁴·w₂ + 2⁵²·w₃ + 2⁴⁰·w₄ + 2²⁸·w₅ + 2¹⁶·w₆ + 2¹⁴·w₇ + … + 2⁰·w₁₄`,
i.e. six 12-bit limbs then eight 2-bit crumbs, MSB first. -/
def rc0Places : List (Nat × Nat) :=
  [(1, 76), (2, 64), (3, 52), (4, 40), (5, 28), (6, 16),
   (7, 14), (8, 12), (9, 10), (10, 8), (11, 6), (12, 4), (13, 2), (14, 0)]

/-- The 88-bit recomposition body: `(Σ 2^place · w_col) − w₀`. -/
def rc0RecompBody (a : Nat → R) (r : KRow) : R :=
  (rc0Places.map (fun p => (2 : R) ^ p.2 * r.w a p.1)).sum - r.w a 0

/-- **`RangeCheck0`'s constraint list** — `CONSTRAINTS = 10` (`circuitgates.rs:177`): eight crumbs
on columns 7..14, the 88-bit recomposition, and the compact-mode equation
`coeff(0)·(next(1) − (curr(0) + 2⁸⁸·next(0)))` (`circuitgates.rs:226-232`).

The compact equation reads the NEXT row, which this per-row semantics does not carry; the compiler
emits `RangeCheck0` only in the standalone mode `create_range_check` (`gadget.rs:63-69`) where
`coeffs = vec![F::zero()]`, so the compact constraint is identically zero. `rc0Standalone` below is
the predicate that pins that, and it is an emission obligation, not an assumption. -/
def rc0Bodies (a : Nat → R) (r : KRow) : List R :=
  rc0CrumbCols.map (fun col => crumbBody (r.w a col)) ++ [rc0RecompBody a r]

/-- A `RangeCheck0` row is in STANDALONE mode when its compact-mode coefficient is zero
(`gadget.rs:63-69`: `create_range_check` passes `vec![F::zero()]`). -/
def rc0Standalone (r : KRow) : Prop := r.coeffs.getD 0 0 = 0

instance (r : KRow) : Decidable (rc0Standalone r) := by unfold rc0Standalone; infer_instance

/-- **The gates whose constraint bodies this target has transcribed.** Emission is restricted to
these; see the header on why the others are `False` rather than `True`. -/
def KGateType.modelled : KGateType → Bool
  | .zero | .generic | .rangeCheck0 => true
  | _ => false

/-- **A row HOLDS** when every constraint body of its gate vanishes at that row.

`zero` constrains nothing (`gate.rs:151`, `CircuitGate::zero` carries no coefficients and no
argument implementation). `generic` is the two double-generic bodies. `rangeCheck0` is its ten
bodies with the compact equation dropped by the standalone obligation.

Everything else is **`False`** — fail-closed. A compiler that emits one produces an unsatisfiable
circuit, which `KimchiLower.lowered_all_modelled` refuses rather than silently discharges. -/
def KRow.holds (a : Nat → R) (r : KRow) : Prop :=
  match r.gate with
  | .zero => True
  | .generic => genericBody1 a r = 0 ∧ genericBody2 a r = 0
  | .rangeCheck0 => (∀ b ∈ rc0Bodies a r, b = 0) ∧ rc0Standalone r
  | _ => False

/-- A list of rows is SATISFIED by an assignment when every row holds. -/
def rowsHold (a : Nat → R) (rs : List KRow) : Prop := ∀ r ∈ rs, r.holds a

theorem rowsHold_nil (a : Nat → R) : rowsHold a [] := by intro r hr; cases hr

theorem rowsHold_append {a : Nat → R} {rs ss : List KRow}
    (h : rowsHold a (rs ++ ss)) : rowsHold a rs ∧ rowsHold a ss := by
  constructor <;> intro r hr <;> exact h r (by simp [hr])

theorem rowsHold_of_append {a : Nat → R} {rs ss : List KRow}
    (h1 : rowsHold a rs) (h2 : rowsHold a ss) : rowsHold a (rs ++ ss) := by
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · exact h1 r h
  · exact h2 r h

theorem rowsHold_cons {a : Nat → R} {r : KRow} {rs : List KRow}
    (h : rowsHold a (r :: rs)) : r.holds a ∧ rowsHold a rs :=
  ⟨h r (by simp), fun x hx => h x (by simp [hx])⟩

/-- **An unmodelled gate is UNSATISFIABLE**, not free. This is the tooth on the fail-closed
default: it is what makes an accidental `Poseidon`/`VarBaseMul` emission show up as vacuity in a
soundness proof rather than as a silently-discharged obligation. -/
theorem unmodelled_row_never_holds (a : Nat → R) (r : KRow) (h : r.gate.modelled = false) :
    ¬ r.holds a := by
  unfold KRow.holds
  cases hg : r.gate <;> simp_all [KGateType.modelled]

/-- Conversely, the three modelled gates are exactly the ones with a transcribed body. -/
theorem modelled_iff (g : KGateType) :
    g.modelled = true ↔ (g = .zero ∨ g = .generic ∨ g = .rangeCheck0) := by
  cases g <;> simp [KGateType.modelled]

end Semantics

/-! ## §3 — smart constructors.

Every row a lowering emits goes through one of these, so `wf` and `modelled` hold by construction
and the compiler cannot spell an unmodelled gate by accident. -/

/-- A `Zero` row (`gate.rs:151`). Emitted as the companion row of a gadget that needs one. -/
def mkZero : KRow := KRow.pad { gate := .zero, wires := [], coeffs := [] }

/-- **The double-generic row** (`generic.rs:153`, `create_generic(wires, c : [F; 10])`).
`l₁ r₁ o₁` are the first sub-gate's three witness columns and `cl₁ cr₁ co₁ cm₁ cc₁` its five
coefficients; likewise the second. Emitting both halves in one row is what the packing pass
`KimchiLower.packGenerics` exists to arrange. -/
def mkGeneric2
    (l1 r1 o1 : Nat) (cl1 cr1 co1 cm1 cc1 : ℤ)
    (l2 r2 o2 : Nat) (cl2 cr2 co2 cm2 cc2 : ℤ) : KRow :=
  KRow.pad
    { gate := .generic
    , wires := [l1, r1, o1, l2, r2, o2]
    , coeffs := [cl1, cr1, co1, cm1, cc1, cl2, cr2, co2, cm2, cc2] }

/-- A generic row using only its FIRST sub-gate; the second half is all-zero coefficients, which
makes `genericBody2` identically `0`. This is what an unpacked lowering emits and what
`packGenerics` later fuses in pairs. -/
def mkGeneric1 (l r o : Nat) (cl cr co cm cc : ℤ) : KRow :=
  mkGeneric2 l r o cl cr co cm cc 0 0 0 0 0 0 0 0

/-- A standalone 64-bit `RangeCheck0` row (`range_check/gadget.rs:63-69`, `create_range_check`:
one row, `coeffs = vec![F::zero()]`). `v` is the checked column and `limbs` are the twelve
limb/crumb columns in `rc0Places` order. -/
def mkRangeCheck0 (v : Nat) (c1 c2 : Nat) (p3 p4 p5 p6 : Nat)
    (k7 k8 k9 k10 k11 k12 k13 k14 : Nat) : KRow :=
  KRow.pad
    { gate := .rangeCheck0
    , wires := [v, c1, c2, p3, p4, p5, p6, k7, k8, k9, k10, k11, k12, k13, k14]
    , coeffs := [0] }

theorem mkZero_gate : mkZero.gate = .zero := rfl
theorem mkGeneric2_gate (l1 r1 o1 : Nat) (cl1 cr1 co1 cm1 cc1 : ℤ)
    (l2 r2 o2 : Nat) (cl2 cr2 co2 cm2 cc2 : ℤ) :
    (mkGeneric2 l1 r1 o1 cl1 cr1 co1 cm1 cc1 l2 r2 o2 cl2 cr2 co2 cm2 cc2).gate = .generic := rfl
theorem mkGeneric1_gate (l r o : Nat) (cl cr co cm cc : ℤ) :
    (mkGeneric1 l r o cl cr co cm cc).gate = .generic := rfl
theorem mkRangeCheck0_gate (v c1 c2 p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14 : Nat) :
    (mkRangeCheck0 v c1 c2 p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14).gate = .rangeCheck0 := rfl

theorem mkGeneric2_wf (l1 r1 o1 : Nat) (cl1 cr1 co1 cm1 cc1 : ℤ)
    (l2 r2 o2 : Nat) (cl2 cr2 co2 cm2 cc2 : ℤ) :
    (mkGeneric2 l1 r1 o1 cl1 cr1 co1 cm1 cc1 l2 r2 o2 cl2 cr2 co2 cm2 cc2).wf := by
  refine ⟨?_, ?_⟩ <;> rfl

theorem mkZero_wf : mkZero.wf := ⟨rfl, rfl⟩

/-! ### §3a — what the smart constructors' rows MEAN.

These unfold the two generic bodies at a `mkGeneric1`/`mkGeneric2` row, which is the rewrite every
forcing lemma downstream needs. -/

section CtorSemantics

variable {R : Type} [CommRing R]

@[simp] theorem mkGeneric2_body1 (a : Nat → R)
    (l1 r1 o1 : Nat) (cl1 cr1 co1 cm1 cc1 : ℤ)
    (l2 r2 o2 : Nat) (cl2 cr2 co2 cm2 cc2 : ℤ) :
    genericBody1 a (mkGeneric2 l1 r1 o1 cl1 cr1 co1 cm1 cc1 l2 r2 o2 cl2 cr2 co2 cm2 cc2)
      = (cl1 : R) * a l1 + (cr1 : R) * a r1 + (co1 : R) * a o1
        + (cm1 : R) * (a l1 * a r1) + (cc1 : R) := by
  rfl

@[simp] theorem mkGeneric2_body2 (a : Nat → R)
    (l1 r1 o1 : Nat) (cl1 cr1 co1 cm1 cc1 : ℤ)
    (l2 r2 o2 : Nat) (cl2 cr2 co2 cm2 cc2 : ℤ) :
    genericBody2 a (mkGeneric2 l1 r1 o1 cl1 cr1 co1 cm1 cc1 l2 r2 o2 cl2 cr2 co2 cm2 cc2)
      = (cl2 : R) * a l2 + (cr2 : R) * a r2 + (co2 : R) * a o2
        + (cm2 : R) * (a l2 * a r2) + (cc2 : R) := by
  rfl

/-- A `mkGeneric1` row's SECOND body is identically zero — the half-row is genuinely free, which is
why the packing pass can fuse two of them without changing what the circuit says. -/
@[simp] theorem mkGeneric1_body2 (a : Nat → R) (l r o : Nat) (cl cr co cm cc : ℤ) :
    genericBody2 a (mkGeneric1 l r o cl cr co cm cc) = 0 := by
  simp [mkGeneric1]

@[simp] theorem mkGeneric1_body1 (a : Nat → R) (l r o : Nat) (cl cr co cm cc : ℤ) :
    genericBody1 a (mkGeneric1 l r o cl cr co cm cc)
      = (cl : R) * a l + (cr : R) * a r + (co : R) * a o + (cm : R) * (a l * a r) + (cc : R) := by
  simp [mkGeneric1]

/-- The row-level `holds` for a single generic, as one equation. -/
theorem mkGeneric1_holds_iff (a : Nat → R) (l r o : Nat) (cl cr co cm cc : ℤ) :
    (mkGeneric1 l r o cl cr co cm cc).holds a
      ↔ (cl : R) * a l + (cr : R) * a r + (co : R) * a o
          + (cm : R) * (a l * a r) + (cc : R) = 0 := by
  unfold KRow.holds
  simp [mkGeneric1_gate]

theorem mkZero_holds (a : Nat → R) : mkZero.holds a := by
  unfold KRow.holds; simp [mkZero]

end CtorSemantics

/-! ## §4 — the cost model: rows are the currency.

`docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` prices this whole route in ROWS, ratcheted at 2% by
`scripts/check-mina-attestation.sh`. So the compiler's cost function has to be a `def` that can be
evaluated and compared, not a comment. -/

/-- The gate histogram of an emitted circuit, in `GateType` discriminant order — the same shape the
o1js measurement reports (`Generic 1,623 · RangeCheck0 701 · Lookup 278` for one Poseidon2-w16
permutation, `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §3.8). -/
def gateHistogram (rs : List KRow) : List (KGateType × Nat) :=
  KGateType.all.map (fun g => (g, (rs.filter (fun r => r.gate == g)).length))

/-- Total rows. This is the number the differential compares. -/
def rowCount (rs : List KRow) : Nat := rs.length

theorem histogram_sums_to_rowCount (rs : List KRow) :
    ((gateHistogram rs).map Prod.snd).sum = rowCount rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hmem : r.gate ∈ KGateType.all := KGateType.all_complete r.gate
    simp only [gateHistogram, rowCount, List.map_map, Function.comp_def] at ih ⊢
    -- Each gate bucket either grows by one (the row's own gate) or is unchanged.
    cases r.gate <;>
      simp_all [KGateType.all, List.filter_cons, rowCount, gateHistogram] <;> omega

/-- **The Pickles domain ceiling.** `2^16 = 65,536` rows
(`mina/src/lib/crypto/kimchi_backend/pasta/basic/kimchi_pasta_basic.ml:16-17`), and Pickles
HARD-REJECTS chunking (`mina/src/lib/pickles/verify.ml:61-76` raises `Is_chunked`), so this is a
wall, not a target that a bigger domain can absorb. -/
def PICKLES_MAX_ROWS : Nat := 65536

example : PICKLES_MAX_ROWS = 2 ^ 16 := rfl

/-- `zk_rows = 3` (`KimchiVerify.zkRows`; `constraints.rs`), subtracted from every domain. -/
def K_ZK_ROWS : Nat := 3

#assert_axioms KGateType.ordinal_injective
#assert_axioms KGateType.all_complete
#assert_axioms unmodelled_row_never_holds
#assert_axioms mkGeneric1_holds_iff
#assert_axioms histogram_sums_to_rowCount
#assert_axioms padTo_length

end Dregg2.Circuit.Emit.KimchiTarget
