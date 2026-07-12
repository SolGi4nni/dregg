/-
# Dregg2.Deos.VaultSatDescriptor — the WELDED vault-deposit (tag 19) satisfaction descriptor, made
REAL at the v12 geometry (the G5 emit-prep sibling of `DischargeSatDescriptor`).

The tag-19 in-AIR gate polynomials (`circuit/src/effect_vm/vault_weld.rs` — the overflow-safe
multi-limb product comparison: 15-bit operand decomposition, schoolbook products with witnessed
carries, lexicographic borrow comparison, is-nonzero strict positivity) were built and toothed at the
constraint level, but NO staged descriptor was emitted and NO producer aux-fill exported. This module
is the tag-19 emit keystone: the genuine `EffectVmDescriptor2` over the deployed R=24 rotated cohort
carrying the vault NO-DILUTION gates, plus the refinement rung — a satisfying trace with the capacity
selector on FORCES the `VaultDepositFieldGate` discipline (`Dregg2.Deos.CapacitySatisfaction` §9)
over the rotated state-block FIELD columns the ~124-bit wide commit absorbs:

 * `d = Δassets ≠ 0` and `m = Δshares ≠ 0` (the is-nonzero witnesses — the ERC-4626 inflation and
   the no-deposit teeth), with `d, m ∈ [0, 2^30)` from the limb range checks;
 * `before[assets] · m ≤ before[shares] · d` — NO DILUTION, through the 2×2→4-limb schoolbook
   products (`P = Ta·m`, `Q = Sa·d`) and the borrow subtraction `Q − P` with no final borrow.

## v12 offsets, derived — never literals

Field columns via the escrow `beforeFieldCol`/`afterFieldCol` (canonical `B_SPAN`); the product/
compare aux block based at `GRAD_ROT_WIDTH + 16` where `GRAD_ROT_WIDTH` is the COMPUTED graduated
cohort width (`DischargeSatDescriptor.GRAD_ROT_WIDTH`, the Lean twin of the Rust
`trace_rotated::GRAD_ROT_WIDTH`). The defs track the geometry-grow through the canonical constants —
REGEN-READY.

## STAGED — the registry row rides the BIG-BANG regen

NOT yet in `rotation-v3-staged-registry.tsv`, NO FP pin, NO live routing: those land in the ONE
shared big-bang descriptor regen (G5 17/18/19 + flat-mem). The floor decode / selector-force /
uniformity gates are the separate `vault_weld::vault_floor_gates` block a prove exercise welds on
top (the gentian pattern).

## The ℤ-model note (house pattern)

`Satisfied2` is the exact-ℤ abstraction: the is-nonzero inverse witnesses (`d·d_inv = 1`) admit only
unit deltas over ℤ (the general field witness lives in the Rust STARK exercise), exactly like the
house is-zero gadgets (`CarrierBoundFloorGadget`'s `inv` witnesses). All theorems here are of the
FORCING/refutation form (satisfied ⟹ discipline), which the abstraction carries soundly; the
`#guard` witnesses use unit deltas — where the DILUTION tooth is still non-trivially expressible
(`Ta = 5, Sa = 3, d = m = 1`: `5 > 3` dilutes, the final-borrow gate bites in isolation).

## Axiom hygiene

`#assert_all_clean` at the close. No axiom, no `sorry`, no core edit.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Deos.SettleEscrowSatDescriptor
import Dregg2.Deos.DischargeSatDescriptor

namespace Dregg2.Deos.VaultSatDescriptor

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (rotateV3)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Deos.SettleEscrowSatDescriptor
  (settleEscrowV1Base beforeFieldCol afterFieldCol)
open Dregg2.Deos.DischargeSatDescriptor (GRAD_ROT_WIDTH bitSum bitSum_nonneg_lt)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt gate_modEq_iff)

set_option autoImplicit false

/-! ## §0 — the mod-`p` → ℤ bounded-lift primitives.

`VmConstraint.holdsVm` on a gate asserts the body `≡ 0 [ZMOD p]` (`p = 2013265921`, the deployed
BabyBear field constraint), NOT `= 0` over ℤ. Two primitives upgrade the congruence to the exact-ℤ
facts the conservation invariant states. Both are the DEPLOYED range-check canonicality made
load-bearing — they DERIVE the exactness from the `[0, 2^15)` limb/carry bounds, they do not assume
it. -/

/-- Field-faithful lift: two CANONICAL (`0 ≤ · < p`) integers congruent mod `p` are EQUAL (the
escrow/discharge `canonEq`). -/
private theorem canonEq {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha0 : 0 ≤ a) (hap : a < 2013265921) (hb0 : 0 ≤ b) (hbp : b < 2013265921) : a = b := by
  unfold Int.ModEq at h
  rwa [Int.emod_eq_of_lt ha0 hap, Int.emod_eq_of_lt hb0 hbp] at h

/-- **THE BOUNDED-LIFT LEMMA.** A residual `R` congruent to `0 mod p` that the 15-bit limb/carry
range checks confine to the open interval `(−p, p)` is EXACTLY `0` over ℤ. This is the soundness
payoff of `CARRY_BITS = 15`: at 15-bit operands every honest gate residual `R = xᵢ·yⱼ + cin − t −
2^15·cout` has `|R| ≤ 2^30 − 1 < p`, so `p ∣ R` collapses to `R = 0`. (At 16-bit carries `|R|` could
reach `2^31 − 1 > p` and the lift was UNSOUND.) -/
private theorem modEqZeroBounded {R : ℤ} (h : R ≡ 0 [ZMOD 2013265921])
    (hlo : -2013265921 < R) (hhi : R < 2013265921) : R = 0 := by
  rw [Int.modEq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  omega

/-- A 15-bit × 15-bit limb product lands in `[0, 2^30)` — the deterministic partial-product bound
that keeps every schoolbook gate residual inside `(−p, p)`. -/
private theorem limbMul_lt {a b : ℤ} (ha : 0 ≤ a ∧ a < 32768) (hb : 0 ≤ b ∧ b < 32768) :
    0 ≤ a * b ∧ a * b < 1073741824 := by
  refine ⟨mul_nonneg ha.1 hb.1, ?_⟩
  calc a * b ≤ 32767 * b := by
        apply mul_le_mul_of_nonneg_right (by omega) hb.1
    _ ≤ 32767 * 32767 := by apply mul_le_mul_of_nonneg_left (by omega) (by omega)
    _ < 1073741824 := by norm_num

/-! ### Clean-context schoolbook/borrow gate lifts.

Each welded gate residual is a fixed linear combination of a 15-bit×15-bit partial product (`[0,
2^30)`), a handful of 15-bit limbs/carries (`[0, 2^15)`), and boolean borrow bits. Feeding the exact
bounds as EXPLICIT arguments keeps the `omega` that discharges the `(−p, p)` confinement in a tiny
context (no ambient mod-`p` congruences to churn on), so the lift stays fast. `hR` re-associates the
`EmittedExpr.eval` shape (`+ (−1)·`) to the readable normal form by `ring`. -/

private theorem liftProdA {R xy z ca : ℤ} (h : R ≡ 0 [ZMOD 2013265921])
    (hR : R = xy - z - 32768 * ca)
    (hxy : 0 ≤ xy ∧ xy < 1073741824) (hz : 0 ≤ z ∧ z < 32768) (hc : 0 ≤ ca ∧ ca < 32768) :
    R = 0 := by refine modEqZeroBounded h ?_ ?_ <;> · subst hR; omega

private theorem liftProdB {R xy ca t cb : ℤ} (h : R ≡ 0 [ZMOD 2013265921])
    (hR : R = xy + ca - t - 32768 * cb)
    (hxy : 0 ≤ xy ∧ xy < 1073741824) (hca : 0 ≤ ca ∧ ca < 32768)
    (ht : 0 ≤ t ∧ t < 32768) (hcb : 0 ≤ cb ∧ cb < 32768) :
    R = 0 := by refine modEqZeroBounded h ?_ ?_ <;> · subst hR; omega

private theorem liftProdC {R xy t z cc : ℤ} (h : R ≡ 0 [ZMOD 2013265921])
    (hR : R = xy + t - z - 32768 * cc)
    (hxy : 0 ≤ xy ∧ xy < 1073741824) (ht : 0 ≤ t ∧ t < 32768)
    (hz : 0 ≤ z ∧ z < 32768) (hc : 0 ≤ cc ∧ cc < 32768) :
    R = 0 := by refine modEqZeroBounded h ?_ ?_ <;> · subst hR; omega

private theorem liftProdD {R xy cb cc z z3 : ℤ} (h : R ≡ 0 [ZMOD 2013265921])
    (hR : R = xy + cb + cc - z - 32768 * z3)
    (hxy : 0 ≤ xy ∧ xy < 1073741824) (hcb : 0 ≤ cb ∧ cb < 32768) (hcc : 0 ≤ cc ∧ cc < 32768)
    (hz : 0 ≤ z ∧ z < 32768) (hz3 : 0 ≤ z3 ∧ z3 < 32768) :
    R = 0 := by refine modEqZeroBounded h ?_ ?_ <;> · subst hR; omega

private theorem liftBorrow0 {R q p bb w : ℤ} (h : R ≡ 0 [ZMOD 2013265921])
    (hR : R = q - p + 32768 * bb - w)
    (hq : 0 ≤ q ∧ q < 32768) (hp : 0 ≤ p ∧ p < 32768)
    (hbb : 0 ≤ bb ∧ bb ≤ 1) (hw : 0 ≤ w ∧ w < 32768) :
    R = 0 := by refine modEqZeroBounded h ?_ ?_ <;> · subst hR; omega

private theorem liftBorrowN {R q p bbp bb w : ℤ} (h : R ≡ 0 [ZMOD 2013265921])
    (hR : R = q - p - bbp + 32768 * bb - w)
    (hq : 0 ≤ q ∧ q < 32768) (hp : 0 ≤ p ∧ p < 32768) (hbbp : 0 ≤ bbp ∧ bbp ≤ 1)
    (hbb : 0 ≤ bb ∧ bb ≤ 1) (hw : 0 ≤ w ∧ w < 32768) :
    R = 0 := by refine modEqZeroBounded h ?_ ?_ <;> · subst hR; omega

private theorem liftBit {R b : ℤ} (h : R ≡ 0 [ZMOD 2013265921]) (hR : R = b)
    (hb : 0 ≤ b ∧ b ≤ 1) : R = 0 := by refine modEqZeroBounded h ?_ ?_ <;> · subst hR; omega

/-- **THE SIGN-GATE CARRY LIFT (low limb).** The delta-addition carry residual `a + b − s − 2^15·c`
(operand limb + delta limb − sum limb − 2^15·carry-bit) is a sum of `[0, 2^15)` limbs and a boolean
carry, so `|R| < 2^16 < p` and the mod-`p` gate lifts to the exact-ℤ limb identity. -/
private theorem liftCarry0 {R a b s c : ℤ} (h : R ≡ 0 [ZMOD 2013265921])
    (hR : R = a + b - s - 32768 * c)
    (ha : 0 ≤ a ∧ a < 32768) (hb : 0 ≤ b ∧ b < 32768) (hs : 0 ≤ s ∧ s < 32768)
    (hc : 0 ≤ c ∧ c ≤ 1) : R = 0 := by refine modEqZeroBounded h ?_ ?_ <;> · subst hR; omega

/-- **THE SIGN-GATE CARRY LIFT (high limb).** As `liftCarry0` with the incoming carry `cin` folded in
(`a + b + cin − s − 2^15·c`), still `|R| < 2^16 < p`. -/
private theorem liftCarry1 {R a b cin s c : ℤ} (h : R ≡ 0 [ZMOD 2013265921])
    (hR : R = a + b + cin - s - 32768 * c)
    (ha : 0 ≤ a ∧ a < 32768) (hb : 0 ≤ b ∧ b < 32768) (hcin : 0 ≤ cin ∧ cin ≤ 1)
    (hs : 0 ≤ s ∧ s < 32768) (hc : 0 ≤ c ∧ c ≤ 1) : R = 0 := by
  refine modEqZeroBounded h ?_ ?_ <;> · subst hR; omega

/-- Operand-assembly lift: a CANONICAL field value congruent to a two-limb `[0, 2^30)` sum equals it
over ℤ. -/
private theorem liftCanonAssembly {v a b : ℤ} (h : v ≡ a + 32768 * b [ZMOD 2013265921])
    (hv : 0 ≤ v ∧ v < 2013265921) (ha : 0 ≤ a ∧ a < 32768) (hbnd : 0 ≤ b ∧ b < 32768) :
    v = a + 32768 * b := by refine canonEq h hv.1 hv.2 ?_ ?_ <;> omega

/-- Delta-assembly lift: a raw ℤ delta that the deposit direction keeps in `[0, p)` and that is
congruent to a two-limb `[0, 2^30)` sum equals it over ℤ (the range check then bounds it `< 2^30`). -/
private theorem liftDelta {v a b : ℤ} (h : v ≡ a + 32768 * b [ZMOD 2013265921])
    (hv0 : 0 ≤ v) (hvp : v < 2013265921) (ha : 0 ≤ a ∧ a < 32768) (hbnd : 0 ≤ b ∧ b < 32768) :
    v = a + 32768 * b := by refine canonEq h hv0 hvp ?_ ?_ <;> omega

/-! ## §1 — the welded columns (the Rust `vault_weld` twin, canonical-constant-derived). -/

/-- The capacity selector column (`prmCol 2` — a SEPARATE descriptor, slot reused). Rust
`vault_weld::VAULT_SEL_COL`. -/
def VAULT_SEL_COL : Nat := prmCol 2
/-- The selector PI slot (the appended 47th). Rust `VAULT_SEL_PI`. -/
def VAULT_SEL_PI : Nat := 46

/-- Limb width (15 bits keeps every partial product `< 2^30 < p`). Rust `LIMB_BITS`. -/
def LIMB_BITS : Nat := 15
/-- Cross-term carry width (one bit past the limb width). Rust `CARRY_BITS`. -/
def CARRY_BITS : Nat := 15
/-- `2^15` as the numeral the gates carry (the Rust `TWO15`). -/
def TWO15 : Int := 32768

/-- The product/compare aux block base (past the 16-column floor-decode headroom). Rust `V`. -/
def V : Nat := GRAD_ROT_WIDTH + 16

def TA0 : Nat := V
def TA1 : Nat := V + 1
def SA0 : Nat := V + 2
def SA1 : Nat := V + 3
def M0 : Nat := V + 4
def M1 : Nat := V + 5
def D0 : Nat := V + 6
def D1 : Nat := V + 7
def P0 : Nat := V + 8
def P1 : Nat := V + 9
def P2 : Nat := V + 10
def P3 : Nat := V + 11
def PCA : Nat := V + 12
def PCB : Nat := V + 13
def PCC : Nat := V + 14
def PT1 : Nat := V + 15
def Q0 : Nat := V + 16
def Q1 : Nat := V + 17
def Q2 : Nat := V + 18
def Q3 : Nat := V + 19
def QCA : Nat := V + 20
def QCB : Nat := V + 21
def QCC : Nat := V + 22
def QT1 : Nat := V + 23
def W0 : Nat := V + 24
def W1 : Nat := V + 25
def W2 : Nat := V + 26
def W3 : Nat := V + 27
def BB0 : Nat := V + 28
def BB1 : Nat := V + 29
def BB2 : Nat := V + 30
def BB3 : Nat := V + 31
def D_INV : Nat := V + 32
def M_INV : Nat := V + 33
/-- `after[assets]` limbs (lo, hi) — the SIGN-GATE decomposition. Rust `AA0`/`AA1`. -/
def AA0 : Nat := V + 34
def AA1 : Nat := V + 35
/-- `after[shares]` limbs (lo, hi) — the SIGN-GATE decomposition. Rust `AS0`/`AS1`. -/
def AS0 : Nat := V + 36
def AS1 : Nat := V + 37
/-- The asset delta-addition carry bits (`before + Δassets = after`, no final carry). Rust
`DCAR0`/`DCAR1`. -/
def DCAR0 : Nat := V + 38
def DCAR1 : Nat := V + 39
/-- The share delta-addition carry bits (`before + Δshares = after`, no final carry). Rust
`MCAR0`/`MCAR1`. -/
def MCAR0 : Nat := V + 40
def MCAR1 : Nat := V + 41
/-- First bit-decomposition column. Rust `BIT_BASE`. -/
def BIT_BASE : Nat := V + 42

/-- The ordered range-checked columns and their bit widths — the Rust `range_specs` list, in
lockstep with the producer fill (bit blocks assigned in list order from `BIT_BASE`). -/
def rangeSpecs : List (Nat × Nat) :=
  [(TA0, LIMB_BITS), (TA1, LIMB_BITS), (SA0, LIMB_BITS), (SA1, LIMB_BITS),
   (M0, LIMB_BITS), (M1, LIMB_BITS), (D0, LIMB_BITS), (D1, LIMB_BITS),
   (P0, LIMB_BITS), (P1, LIMB_BITS), (P2, LIMB_BITS), (P3, LIMB_BITS),
   (PCA, LIMB_BITS), (PCB, CARRY_BITS), (PCC, CARRY_BITS), (PT1, LIMB_BITS),
   (Q0, LIMB_BITS), (Q1, LIMB_BITS), (Q2, LIMB_BITS), (Q3, LIMB_BITS),
   (QCA, LIMB_BITS), (QCB, CARRY_BITS), (QCC, CARRY_BITS), (QT1, LIMB_BITS),
   (W0, LIMB_BITS), (W1, LIMB_BITS), (W2, LIMB_BITS), (W3, LIMB_BITS),
   (AA0, LIMB_BITS), (AA1, LIMB_BITS), (AS0, LIMB_BITS), (AS1, LIMB_BITS)]

/-! ## §2 — the gate bodies (byte-for-byte the Rust builders' expression trees). -/

/-- `(-1) · e` (the Rust `neg`). -/
def neg (e : EmittedExpr) : EmittedExpr := .mul (.const (-1)) e
/-- `a − b` as the Rust `sub`: `a + (−1)·b`. -/
def sub (a b : EmittedExpr) : EmittedExpr := .add a (neg b)

/-- A selector-gated gate `sel · body`. Rust `sel_gate`. -/
def selGate (body : EmittedExpr) : VmConstraint2 :=
  .base (.gate (.mul (.var VAULT_SEL_COL) body))

/-- A selector-gated booleanity gate `sel · (b · (b − 1))`. -/
def selBoolGate (b : Nat) : VmConstraint2 :=
  selGate (.mul (.var b) (.add (.var b) (.const (-1))))

/-- `Δshares` as the gates read it. -/
def mExpr (share : Nat) : EmittedExpr :=
  sub (.var (afterFieldCol share)) (.var (beforeFieldCol share))
/-- `Δassets` as the gates read it. -/
def dExpr (asset : Nat) : EmittedExpr :=
  sub (.var (afterFieldCol asset)) (.var (beforeFieldCol asset))

/-- **THE OVERFLOW-SAFE 2×2 → 4-LIMB SCHOOLBOOK PRODUCT GATES** (Rust `product_gates`):
`A: x0·y0 = z0 + cA·2^15` · `B: x1·y0 + cA = t1 + cB·2^15` · `C: x0·y1 + t1 = z1 + cC·2^15` ·
`D: x1·y1 + cB + cC = z2 + z3·2^15`. -/
def productGates (x0 x1 y0 y1 z0 z1 z2 z3 ca cb cc t1 : Nat) : List VmConstraint2 :=
  [ selGate (sub (sub (.mul (.var x0) (.var y0)) (.var z0)) (.mul (.const TWO15) (.var ca)))
  , selGate (sub (sub (.add (.mul (.var x1) (.var y0)) (.var ca)) (.var t1))
      (.mul (.const TWO15) (.var cb)))
  , selGate (sub (sub (.add (.mul (.var x0) (.var y1)) (.var t1)) (.var z1))
      (.mul (.const TWO15) (.var cc)))
  , selGate (sub (sub (.add (.add (.mul (.var x1) (.var y1)) (.var cb)) (.var cc)) (.var z2))
      (.mul (.const TWO15) (.var z3))) ]

/-- **THE 4-LIMB BORROW COMPARISON GATES** (Rust `borrow_compare_gates`): per limb
`Q_i − P_i − bb_{i−1} + bb_i·2^15 − w_i = 0` (`bb_{−1} = 0`), each `bb_i` boolean, and the final
`bb3 = 0` no-borrow gate (`bb3 = 0 ⟺ P ≤ Q ⟺` no dilution). -/
def borrowCompareGates : List VmConstraint2 :=
  [ selGate (sub (.add (sub (.var Q0) (.var P0)) (.mul (.const TWO15) (.var BB0))) (.var W0))
  , selBoolGate BB0
  , selGate (sub (.add (sub (sub (.var Q1) (.var P1)) (.var BB0))
      (.mul (.const TWO15) (.var BB1))) (.var W1))
  , selBoolGate BB1
  , selGate (sub (.add (sub (sub (.var Q2) (.var P2)) (.var BB1))
      (.mul (.const TWO15) (.var BB2))) (.var W2))
  , selBoolGate BB2
  , selGate (sub (.add (sub (sub (.var Q3) (.var P3)) (.var BB2))
      (.mul (.const TWO15) (.var BB3))) (.var W3))
  , selBoolGate BB3
  , selGate (.var BB3) ]

/-- **THE SIGN (NO-BORROW) GATES** — the deposit-direction weld (Rust `sign_gates`). For each of
assets and shares, decompose `after` into two 15-bit limbs and pin `before + Δ = after` through a
15-bit ADD carry chain with NO final carry:

  * `after = A0 + 2^15·A1`                       (after-assembly, `after` canonical)
  * `Blo + Δlo = A0 + 2^15·car0`                 (low-limb add, `car0` boolean)
  * `Bhi + Δhi + car0 = A1 + 2^15·car1`          (high-limb add, `car1` boolean)
  * `car1 = 0`                                    (NO FINAL CARRY ⟹ `before + Δ < 2^30`)

Since `Δ = Δlo + 2^15·Δhi ∈ [0, 2^30)` (its limbs are range-checked) and the chain is exact over ℤ,
`after = before + Δ ≥ before` — the DEPOSIT direction is DERIVED, killing the withdrawal-as-deposit
wrap band (a large negative `after − before` whose mod-`p` residue re-enters `[0, 2^30)`). -/
def signGates (asset share : Nat) : List VmConstraint2 :=
  -- assets: after = before + Δassets, no final carry.
  [ selGate (sub (.var (afterFieldCol asset)) (.add (.var AA0) (.mul (.const TWO15) (.var AA1))))
  , selGate (sub (sub (.add (.var TA0) (.var D0)) (.var AA0)) (.mul (.const TWO15) (.var DCAR0)))
  , selGate (sub (sub (.add (.add (.var TA1) (.var D1)) (.var DCAR0)) (.var AA1))
      (.mul (.const TWO15) (.var DCAR1)))
  , selGate (.var DCAR1)
  , selBoolGate DCAR0
  , selBoolGate DCAR1
  -- shares: after = before + Δshares, no final carry.
  , selGate (sub (.var (afterFieldCol share)) (.add (.var AS0) (.mul (.const TWO15) (.var AS1))))
  , selGate (sub (sub (.add (.var SA0) (.var M0)) (.var AS0)) (.mul (.const TWO15) (.var MCAR0)))
  , selGate (sub (sub (.add (.add (.var SA1) (.var M1)) (.var MCAR0)) (.var AS1))
      (.mul (.const TWO15) (.var MCAR1)))
  , selGate (.var MCAR1)
  , selBoolGate MCAR0
  , selBoolGate MCAR1 ]

/-- The per-spec range-check gates: `n` booleanity gates then the assembly
`sel · (col − Σ 2^i bit_i)`, bit blocks assigned in list order from `base` (the Rust `range_gates`
fold). -/
def rangeGatesAux : List (Nat × Nat) → Nat → List VmConstraint2
  | [], _ => []
  | (col, n) :: rest, base =>
      ((List.range n).map (fun i => selBoolGate (base + i)))
        ++ [selGate (.add (.var col) (neg (bitSum (fun i => base + i) n)))]
        ++ rangeGatesAux rest (base + n)

def rangeGates : List VmConstraint2 := rangeGatesAux rangeSpecs BIT_BASE

/-- **THE VAULT SATISFACTION GATES** — the exact list (order and all) the Rust
`vault_weld::vault_satisfaction_gates` builds: the four operand assemblies, the two is-nonzero
strict-positivity gates, the two products (`P = Ta·m`, `Q = Sa·d`), the borrow comparison, then all
limb/carry range checks. -/
def vaultSatGates (asset share : Nat) : List VmConstraint2 :=
  [ selGate (sub (.var (beforeFieldCol asset)) (.add (.var TA0) (.mul (.const TWO15) (.var TA1))))
  , selGate (sub (.var (beforeFieldCol share)) (.add (.var SA0) (.mul (.const TWO15) (.var SA1))))
  , selGate (sub (mExpr share) (.add (.var M0) (.mul (.const TWO15) (.var M1))))
  , selGate (sub (dExpr asset) (.add (.var D0) (.mul (.const TWO15) (.var D1))))
  , selGate (sub (.mul (dExpr asset) (.var D_INV)) (.const 1))
  , selGate (sub (.mul (mExpr share) (.var M_INV)) (.const 1)) ]
    ++ signGates asset share
    ++ productGates TA0 TA1 M0 M1 P0 P1 P2 P3 PCA PCB PCC PT1
    ++ productGates SA0 SA1 D0 D1 Q0 Q1 Q2 Q3 QCA QCB QCC QT1
    ++ borrowCompareGates
    ++ rangeGates

/-! ## §3 — THE WELDED DESCRIPTOR (the tag-19 emit keystone). -/

/-- The total range-check bit-column count (the Rust `total_bits`). -/
def TOTAL_RANGE_BITS : Nat := rangeSpecs.foldl (fun a s => a + s.2) 0

/-- The descriptor trace width: past the last range-check bit column. -/
def VAULT_WIDTH : Nat := BIT_BASE + TOTAL_RANGE_BITS

/-- **`vaultSatVmDescriptor2R24`** — the welded vault-deposit satisfaction descriptor over the R=24
rotated cohort. `graduateV1 (rotateV3 settle-base)` (the `asset`/`share` freezes dropped) PLUS the
vault satisfaction gates PLUS the selector PI pin; the trace WIDENED to carry the product/compare
aux block (tables re-declared at the widened arity). `piCount = 47`. STAGED: the registry row + FP
pin ride the big-bang regen. -/
def vaultSatVmDescriptor2R24 (asset share : Nat) : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3
    { settleEscrowV1Base asset share with name := "dregg-effectvm-vault-deposit-sat-v1" })
  { base with
    name        := "dregg-effectvm-vault-deposit-sat-v1-rot24-v3-staged"
    traceWidth  := VAULT_WIDTH
    tables      := v2Tables VAULT_WIDTH
    piCount     := base.piCount + 1
    constraints := base.constraints ++ vaultSatGates asset share
                     ++ [.base (.piBinding .first VAULT_SEL_COL VAULT_SEL_PI)] }

/-- Each welded gate is a member of the descriptor's constraint list. -/
theorem vaultGate_mem (asset share : Nat) (g : VmConstraint2)
    (hg : g ∈ vaultSatGates asset share) :
    g ∈ (vaultSatVmDescriptor2R24 asset share).constraints := by
  unfold vaultSatVmDescriptor2R24
  simp only [List.mem_append]
  exact Or.inl (Or.inr hg)

/-! ## §4 — THE REFINEMENT RUNG. -/

/-- A welded gate's body vanishes mod `p` on a satisfying NON-LAST row (the STABLE `holdsVm`
interface — now the DEPLOYED field congruence). -/
theorem vault_gate_holds (hash : List ℤ → ℤ) (asset share : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (vaultSatVmDescriptor2R24 asset share) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (g : VmConstraint2) (hg : g ∈ vaultSatGates asset share)
    (body : EmittedExpr) (hbody : g = .base (.gate body)) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi g (vaultGate_mem asset share g hg)
  rw [hbody] at hrow
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, hnl] using hrow

/-- A selector-gated body vanishes mod `p` on a selector-on satisfying NON-LAST row. -/
theorem sel_body_vanishes (hash : List ℤ → ℤ) (asset share : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (vaultSatVmDescriptor2R24 asset share) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc VAULT_SEL_COL = 1)
    (body : EmittedExpr) (hmem : selGate body ∈ vaultSatGates asset share) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have h := vault_gate_holds hash asset share hsat i hi hnl (selGate body) hmem
    (.mul (.var VAULT_SEL_COL) body) rfl
  simp only [EmittedExpr.eval, hsel, one_mul] at h
  exact h

/-- The range-check induction: every spec'd column is forced into `[0, 2^n)` (one induction over the
spec list gives ALL the range facts uniformly). Each spec width is `≤ 15`, so the assembled bit sum
lives in `[0, 2^15) ⊂ [0, p)`; with the column CANONICAL the mod-`p` assembly congruence lifts to the
exact-ℤ pin, and the mod-`p` booleanity gate + `p`'s primality forces each canonical bit to `{0,1}`. -/
theorem rangeAux_forces (loc : Nat → Int)
    (hcanon : ∀ c, 0 ≤ loc c ∧ loc c < 2013265921)
    (specs : List (Nat × Nat)) (base : Nat)
    (hwidth : ∀ col n, (col, n) ∈ specs → (2 : ℤ) ^ n < 2013265921)
    (hvan : ∀ body : EmittedExpr, selGate body ∈ rangeGatesAux specs base →
      body.eval loc ≡ 0 [ZMOD 2013265921]) :
    ∀ col n : Nat, (col, n) ∈ specs → 0 ≤ loc col ∧ loc col < 2 ^ n := by
  induction specs generalizing base with
  | nil => intro col n h; cases h
  | cons hd rest ih =>
    obtain ⟨c0, n0⟩ := hd
    intro col n hmem
    rcases List.mem_cons.mp hmem with heq | htail
    · injection heq with h1 h2
      subst h1; subst h2
      -- the bit columns are boolean (mod-`p` booleanity + canonicality + `p` prime).
      have hbits : ∀ j, j < n → loc (base + j) = 0 ∨ loc (base + j) = 1 := by
        intro j hj
        have hb := hvan (.mul (.var (base + j)) (.add (.var (base + j)) (.const (-1))))
          (by
            simp only [rangeGatesAux]
            apply List.mem_append_left
            apply List.mem_append_left
            exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
        simp only [EmittedExpr.eval] at hb
        rw [Int.modEq_zero_iff_dvd] at hb
        obtain ⟨hb0, hbp⟩ := hcanon (base + j)
        rcases (pPrimeInt.dvd_mul.mp hb) with hd | hd
        · left;  obtain ⟨k, hk⟩ := hd; omega
        · right; obtain ⟨k, hk⟩ := hd; omega
      -- the assembly pins the column to the bit sum (mod-`p` → exact by canonicality + `2^n < p`).
      have hasm := hvan (.add (.var col) (neg (bitSum (fun i => base + i) n)))
        (by
          simp only [rangeGatesAux]
          apply List.mem_append_left
          apply List.mem_append_right
          exact List.mem_singleton.mpr rfl)
      simp only [neg, EmittedExpr.eval] at hasm
      have hb := bitSum_nonneg_lt loc (fun i => base + i) n hbits
      have hnp : (2 : ℤ) ^ n < 2013265921 := hwidth col n (List.mem_cons.mpr (Or.inl rfl))
      have hsumLt : (bitSum (fun i => base + i) n).eval loc < 2013265921 := by omega
      have hpin : loc col = (bitSum (fun i => base + i) n).eval loc :=
        canonEq ((gate_modEq_iff (by ring)).mp hasm) (hcanon col).1 (hcanon col).2 hb.1 hsumLt
      constructor <;> omega
    · exact ih (base + n0)
        (fun col' n' hmem' => hwidth col' n' (List.mem_cons_of_mem _ hmem'))
        (fun body hb => hvan body (by
          simp only [rangeGatesAux]
          exact List.mem_append_right _ hb))
        col n htail

/-- **THE REFINEMENT KEYSTONE.** On a satisfying trace, a NON-LAST row whose vault selector is `1`
FORCES the `VaultDepositFieldGate` discipline over the rotated field columns the wide commit
absorbs: a genuine deposit (`Δassets ≠ 0`), a genuine mint (`Δshares ≠ 0` — the ERC-4626 inflation
tooth), both deltas in the `[0, 2^30)` operand window, and NO DILUTION
(`before[assets]·Δshares ≤ before[shares]·Δassets`) through the overflow-safe limb products and the
borrow comparison. -/
theorem vaultSatV3_forces (hash : List ℤ → ℤ) (asset share : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (vaultSatVmDescriptor2R24 asset share) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc VAULT_SEL_COL = 1)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921) :
    (envAt t i).loc (afterFieldCol asset) - (envAt t i).loc (beforeFieldCol asset) ≠ 0
    ∧ (envAt t i).loc (afterFieldCol share) - (envAt t i).loc (beforeFieldCol share) ≠ 0
    ∧ 0 ≤ (envAt t i).loc (afterFieldCol asset) - (envAt t i).loc (beforeFieldCol asset)
    ∧ (envAt t i).loc (afterFieldCol asset) - (envAt t i).loc (beforeFieldCol asset) < 1073741824
    ∧ 0 ≤ (envAt t i).loc (afterFieldCol share) - (envAt t i).loc (beforeFieldCol share)
    ∧ (envAt t i).loc (afterFieldCol share) - (envAt t i).loc (beforeFieldCol share) < 1073741824
    ∧ (envAt t i).loc (beforeFieldCol asset)
        * ((envAt t i).loc (afterFieldCol share) - (envAt t i).loc (beforeFieldCol share))
      ≤ (envAt t i).loc (beforeFieldCol share)
        * ((envAt t i).loc (afterFieldCol asset) - (envAt t i).loc (beforeFieldCol asset)) := by
  have van := sel_body_vanishes hash asset share hsat i hi hnl hsel
  -- specific canonicality facts for the four field columns (the deposit deltas).
  have hcAaf := hcanon (afterFieldCol asset)
  have hcBaf := hcanon (beforeFieldCol asset)
  have hcAsf := hcanon (afterFieldCol share)
  have hcBsf := hcanon (beforeFieldCol share)
  -- ALL the range facts in one induction (`rangeGates ⊆ vaultSatGates`), lifted mod-`p` → ℤ by the
  -- deployed canonicality invariant (each spec is 15-bit, so `2^15 = 32768 < p`).
  have hranges := rangeAux_forces (envAt t i).loc hcanon rangeSpecs BIT_BASE
    (by intro col n h
        simp only [rangeSpecs] at h
        fin_cases h <;> norm_num [LIMB_BITS, CARRY_BITS])
    (fun body hb => van body (by
      unfold vaultSatGates
      exact List.mem_append_right _ hb))
  have hTA0 := hranges TA0 LIMB_BITS (by simp [rangeSpecs])
  have hTA1 := hranges TA1 LIMB_BITS (by simp [rangeSpecs])
  have hSA0 := hranges SA0 LIMB_BITS (by simp [rangeSpecs])
  have hSA1 := hranges SA1 LIMB_BITS (by simp [rangeSpecs])
  have hM0 := hranges M0 LIMB_BITS (by simp [rangeSpecs])
  have hM1 := hranges M1 LIMB_BITS (by simp [rangeSpecs])
  have hD0 := hranges D0 LIMB_BITS (by simp [rangeSpecs])
  have hD1 := hranges D1 LIMB_BITS (by simp [rangeSpecs])
  have hP0 := hranges P0 LIMB_BITS (by simp [rangeSpecs])
  have hP1 := hranges P1 LIMB_BITS (by simp [rangeSpecs])
  have hP2 := hranges P2 LIMB_BITS (by simp [rangeSpecs])
  have hP3 := hranges P3 LIMB_BITS (by simp [rangeSpecs])
  have hPCA := hranges PCA LIMB_BITS (by simp [rangeSpecs])
  have hPCB := hranges PCB CARRY_BITS (by simp [rangeSpecs])
  have hPCC := hranges PCC CARRY_BITS (by simp [rangeSpecs])
  have hPT1 := hranges PT1 LIMB_BITS (by simp [rangeSpecs])
  have hQ0 := hranges Q0 LIMB_BITS (by simp [rangeSpecs])
  have hQ1 := hranges Q1 LIMB_BITS (by simp [rangeSpecs])
  have hQ2 := hranges Q2 LIMB_BITS (by simp [rangeSpecs])
  have hQ3 := hranges Q3 LIMB_BITS (by simp [rangeSpecs])
  have hQCA := hranges QCA LIMB_BITS (by simp [rangeSpecs])
  have hQCB := hranges QCB CARRY_BITS (by simp [rangeSpecs])
  have hQCC := hranges QCC CARRY_BITS (by simp [rangeSpecs])
  have hQT1 := hranges QT1 LIMB_BITS (by simp [rangeSpecs])
  have hW0 := hranges W0 LIMB_BITS (by simp [rangeSpecs])
  have hW1 := hranges W1 LIMB_BITS (by simp [rangeSpecs])
  have hW2 := hranges W2 LIMB_BITS (by simp [rangeSpecs])
  have hW3 := hranges W3 LIMB_BITS (by simp [rangeSpecs])
  have hAA0 := hranges AA0 LIMB_BITS (by simp [rangeSpecs])
  have hAA1 := hranges AA1 LIMB_BITS (by simp [rangeSpecs])
  have hAS0 := hranges AS0 LIMB_BITS (by simp [rangeSpecs])
  have hAS1 := hranges AS1 LIMB_BITS (by simp [rangeSpecs])
  rw [show (2 : Int) ^ LIMB_BITS = 32768 by norm_num [LIMB_BITS]]
    at hTA0 hTA1 hSA0 hSA1 hM0 hM1 hD0 hD1 hP0 hP1 hP2 hP3 hPCA hPT1
       hQ0 hQ1 hQ2 hQ3 hQCA hQT1 hW0 hW1 hW2 hW3 hAA0 hAA1 hAS0 hAS1
  rw [show (2 : Int) ^ CARRY_BITS = 32768 by norm_num [CARRY_BITS]] at hPCB hPCC hQCB hQCC
  -- the borrow bits are genuinely boolean (mod-`p` booleanity + canonicality + `p` prime).
  have bbBool : ∀ b : Nat, selBoolGate b ∈ vaultSatGates asset share →
      0 ≤ (envAt t i).loc b ∧ (envAt t i).loc b ≤ 1 := by
    intro b hmem
    have h := van (.mul (.var b) (.add (.var b) (.const (-1)))) hmem
    simp only [EmittedExpr.eval] at h
    rw [Int.modEq_zero_iff_dvd] at h
    obtain ⟨hb0, hbp⟩ := hcanon b
    rcases pPrimeInt.dvd_mul.mp h with hd | hd
    · obtain ⟨k, hk⟩ := hd; constructor <;> omega
    · obtain ⟨k, hk⟩ := hd; constructor <;> omega
  have hBB0 := bbBool BB0 (by simp [vaultSatGates, borrowCompareGates])
  have hBB1 := bbBool BB1 (by simp [vaultSatGates, borrowCompareGates])
  have hBB2 := bbBool BB2 (by simp [vaultSatGates, borrowCompareGates])
  have hBB3 := bbBool BB3 (by simp [vaultSatGates, borrowCompareGates])
  -- the sign-gate carry bits are boolean (same booleanity gadget as the borrow bits).
  have hDCAR0 := bbBool DCAR0 (by simp [vaultSatGates, signGates])
  have hDCAR1 := bbBool DCAR1 (by simp [vaultSatGates, signGates])
  have hMCAR0 := bbBool MCAR0 (by simp [vaultSatGates, signGates])
  have hMCAR1 := bbBool MCAR1 (by simp [vaultSatGates, signGates])
  -- the four operand assemblies.
  have hTa := van (sub (.var (beforeFieldCol asset))
    (.add (.var TA0) (.mul (.const TWO15) (.var TA1)))) (by simp [vaultSatGates])
  have hSa := van (sub (.var (beforeFieldCol share))
    (.add (.var SA0) (.mul (.const TWO15) (.var SA1)))) (by simp [vaultSatGates])
  have hm := van (sub (mExpr share) (.add (.var M0) (.mul (.const TWO15) (.var M1))))
    (by simp [vaultSatGates])
  have hd := van (sub (dExpr asset) (.add (.var D0) (.mul (.const TWO15) (.var D1))))
    (by simp [vaultSatGates])
  -- the two is-nonzero witnesses.
  have hdnz := van (sub (.mul (dExpr asset) (.var D_INV)) (.const 1)) (by simp [vaultSatGates])
  have hmnz := van (sub (.mul (mExpr share) (.var M_INV)) (.const 1)) (by simp [vaultSatGates])
  -- the product P = Ta·m, gate by gate.
  have hPA := van (sub (sub (.mul (.var TA0) (.var M0)) (.var P0))
    (.mul (.const TWO15) (.var PCA))) (by simp [vaultSatGates, productGates])
  have hPB := van (sub (sub (.add (.mul (.var TA1) (.var M0)) (.var PCA)) (.var PT1))
    (.mul (.const TWO15) (.var PCB))) (by simp [vaultSatGates, productGates])
  have hPC := van (sub (sub (.add (.mul (.var TA0) (.var M1)) (.var PT1)) (.var P1))
    (.mul (.const TWO15) (.var PCC))) (by simp [vaultSatGates, productGates])
  have hPD := van (sub (sub (.add (.add (.mul (.var TA1) (.var M1)) (.var PCB)) (.var PCC))
    (.var P2)) (.mul (.const TWO15) (.var P3))) (by simp [vaultSatGates, productGates])
  -- the product Q = Sa·d, gate by gate.
  have hQA := van (sub (sub (.mul (.var SA0) (.var D0)) (.var Q0))
    (.mul (.const TWO15) (.var QCA))) (by simp [vaultSatGates, productGates])
  have hQB := van (sub (sub (.add (.mul (.var SA1) (.var D0)) (.var QCA)) (.var QT1))
    (.mul (.const TWO15) (.var QCB))) (by simp [vaultSatGates, productGates])
  have hQC := van (sub (sub (.add (.mul (.var SA0) (.var D1)) (.var QT1)) (.var Q1))
    (.mul (.const TWO15) (.var QCC))) (by simp [vaultSatGates, productGates])
  have hQD := van (sub (sub (.add (.add (.mul (.var SA1) (.var D1)) (.var QCB)) (.var QCC))
    (.var Q2)) (.mul (.const TWO15) (.var Q3))) (by simp [vaultSatGates, productGates])
  -- the borrow comparison, limb by limb, and the final no-borrow gate.
  have hb0 := van (sub (.add (sub (.var Q0) (.var P0)) (.mul (.const TWO15) (.var BB0)))
    (.var W0)) (by simp [vaultSatGates, borrowCompareGates])
  have hb1 := van (sub (.add (sub (sub (.var Q1) (.var P1)) (.var BB0))
    (.mul (.const TWO15) (.var BB1))) (.var W1)) (by simp [vaultSatGates, borrowCompareGates])
  have hb2 := van (sub (.add (sub (sub (.var Q2) (.var P2)) (.var BB1))
    (.mul (.const TWO15) (.var BB2))) (.var W2)) (by simp [vaultSatGates, borrowCompareGates])
  have hb3 := van (sub (.add (sub (sub (.var Q3) (.var P3)) (.var BB2))
    (.mul (.const TWO15) (.var BB3))) (.var W3)) (by simp [vaultSatGates, borrowCompareGates])
  have hbb3 := van (.var BB3) (by simp [vaultSatGates, borrowCompareGates])
  -- reduce every extracted gate body to its arithmetic form (still a mod-`p` congruence).
  simp only [sub, neg, mExpr, dExpr, TWO15, EmittedExpr.eval] at hTa hSa hm hd hdnz hmnz
  simp only [sub, neg, TWO15, EmittedExpr.eval] at hPA hPB hPC hPD hQA hQB hQC hQD
  simp only [sub, neg, TWO15, EmittedExpr.eval] at hb0 hb1 hb2 hb3 hbb3
  -- OPERAND WELDS: the before-field values are canonical, the limb reconstruction `< 2^30 < p`, so
  -- the mod-`p` assembly congruence lifts to the exact-ℤ equality (clean-context helpers).
  have eTa : (envAt t i).loc (beforeFieldCol asset)
      = (envAt t i).loc TA0 + 32768 * (envAt t i).loc TA1 :=
    liftCanonAssembly ((gate_modEq_iff (by ring)).mp hTa) hcBaf hTA0 hTA1
  have eSa : (envAt t i).loc (beforeFieldCol share)
      = (envAt t i).loc SA0 + 32768 * (envAt t i).loc SA1 :=
    liftCanonAssembly ((gate_modEq_iff (by ring)).mp hSa) hcBsf hSA0 hSA1
  -- SIGN WELDS: the no-borrow ADD chain `before + Δ = after` (no final carry) DERIVES the deposit
  -- direction `before ≤ after` — no `hAssetDep`/`hShareDep` assumption. This kills the
  -- withdrawal-as-deposit wrap band: a large negative `after − before` whose mod-`p` residue would
  -- re-enter `[0, 2^30)` cannot satisfy the chain (its `after` reconstruction would carry out).
  have hAAasm := van (sub (.var (afterFieldCol asset))
    (.add (.var AA0) (.mul (.const TWO15) (.var AA1)))) (by simp [vaultSatGates, signGates])
  have hAc0 := van (sub (sub (.add (.var TA0) (.var D0)) (.var AA0))
    (.mul (.const TWO15) (.var DCAR0))) (by simp [vaultSatGates, signGates])
  have hAc1 := van (sub (sub (.add (.add (.var TA1) (.var D1)) (.var DCAR0)) (.var AA1))
    (.mul (.const TWO15) (.var DCAR1))) (by simp [vaultSatGates, signGates])
  have hAnc := van (.var DCAR1) (by simp [vaultSatGates, signGates])
  have hSAasm := van (sub (.var (afterFieldCol share))
    (.add (.var AS0) (.mul (.const TWO15) (.var AS1)))) (by simp [vaultSatGates, signGates])
  have hMc0 := van (sub (sub (.add (.var SA0) (.var M0)) (.var AS0))
    (.mul (.const TWO15) (.var MCAR0))) (by simp [vaultSatGates, signGates])
  have hMc1 := van (sub (sub (.add (.add (.var SA1) (.var M1)) (.var MCAR0)) (.var AS1))
    (.mul (.const TWO15) (.var MCAR1))) (by simp [vaultSatGates, signGates])
  have hMnc := van (.var MCAR1) (by simp [vaultSatGates, signGates])
  simp only [sub, neg, TWO15, EmittedExpr.eval] at hAAasm hAc0 hAc1 hAnc hSAasm hMc0 hMc1 hMnc
  have eAA : (envAt t i).loc (afterFieldCol asset)
      = (envAt t i).loc AA0 + 32768 * (envAt t i).loc AA1 :=
    liftCanonAssembly ((gate_modEq_iff (by ring)).mp hAAasm) hcAaf hAA0 hAA1
  have eASf : (envAt t i).loc (afterFieldCol share)
      = (envAt t i).loc AS0 + 32768 * (envAt t i).loc AS1 :=
    liftCanonAssembly ((gate_modEq_iff (by ring)).mp hSAasm) hcAsf hAS0 hAS1
  have ec0A := liftCarry0 hAc0 (by ring) hTA0 hD0 hAA0 hDCAR0
  have ec1A := liftCarry1 hAc1 (by ring) hTA1 hD1 hDCAR0 hAA1 hDCAR1
  have ec0M := liftCarry0 hMc0 (by ring) hSA0 hM0 hAS0 hMCAR0
  have ec1M := liftCarry1 hMc1 (by ring) hSA1 hM1 hMCAR0 hAS1 hMCAR1
  have encA : (envAt t i).loc DCAR1 = 0 := liftBit hAnc (by ring) hDCAR1
  have encM : (envAt t i).loc MCAR1 = 0 := liftBit hMnc (by ring) hMCAR1
  -- deposit direction DERIVED (linear over the exact carry chain + limb ranges).
  have hAssetDep : (envAt t i).loc (beforeFieldCol asset)
      ≤ (envAt t i).loc (afterFieldCol asset) := by omega
  have hShareDep : (envAt t i).loc (beforeFieldCol share)
      ≤ (envAt t i).loc (afterFieldCol share) := by omega
  clear hAAasm hAc0 hAc1 hAnc hSAasm hMc0 hMc1 hMnc
  -- DELTA WELDS: the deposit direction (`before ≤ after`) makes the raw ℤ delta canonical `[0, p)`,
  -- and the limb reconstruction is `< 2^30 < p`, so the mod-`p` congruence lifts to the exact delta.
  have em : (envAt t i).loc (afterFieldCol share) - (envAt t i).loc (beforeFieldCol share)
      = (envAt t i).loc M0 + 32768 * (envAt t i).loc M1 :=
    liftDelta ((gate_modEq_iff (by ring)).mp hm) (sub_nonneg.mpr hShareDep)
      (lt_of_le_of_lt (sub_le_self _ hcBsf.1) hcAsf.2) hM0 hM1
  have ed : (envAt t i).loc (afterFieldCol asset) - (envAt t i).loc (beforeFieldCol asset)
      = (envAt t i).loc D0 + 32768 * (envAt t i).loc D1 :=
    liftDelta ((gate_modEq_iff (by ring)).mp hd) (sub_nonneg.mpr hAssetDep)
      (lt_of_le_of_lt (sub_le_self _ hcBaf.1) hcAaf.2) hD0 hD1
  -- PRODUCT / BORROW LIFTS: each schoolbook/borrow residual is confined to `(−p, p)` by the 15-bit
  -- limb+carry range checks (the `CARRY_BITS = 15` soundness payoff), so the mod-`p` gate becomes the
  -- exact-ℤ equality the schoolbook reconstruction consumes (clean-context helpers).
  replace hPA := liftProdA hPA (by ring) (limbMul_lt hTA0 hM0) hP0 hPCA
  replace hPB := liftProdB hPB (by ring) (limbMul_lt hTA1 hM0) hPCA hPT1 hPCB
  replace hPC := liftProdC hPC (by ring) (limbMul_lt hTA0 hM1) hPT1 hP1 hPCC
  replace hPD := liftProdD hPD (by ring) (limbMul_lt hTA1 hM1) hPCB hPCC hP2 hP3
  replace hQA := liftProdA hQA (by ring) (limbMul_lt hSA0 hD0) hQ0 hQCA
  replace hQB := liftProdB hQB (by ring) (limbMul_lt hSA1 hD0) hQCA hQT1 hQCB
  replace hQC := liftProdC hQC (by ring) (limbMul_lt hSA0 hD1) hQT1 hQ1 hQCC
  replace hQD := liftProdD hQD (by ring) (limbMul_lt hSA1 hD1) hQCB hQCC hQ2 hQ3
  replace hb0 := liftBorrow0 hb0 (by ring) hQ0 hP0 hBB0 hW0
  replace hb1 := liftBorrowN hb1 (by ring) hQ1 hP1 hBB0 hBB1 hW1
  replace hb2 := liftBorrowN hb2 (by ring) hQ2 hP2 hBB1 hBB2 hW2
  replace hb3 := liftBorrowN hb3 (by ring) hQ3 hP3 hBB2 hBB3 hW3
  replace hbb3 := liftBit hbb3 (by ring) hBB3
  -- the strict-positivity witnesses (kept at the mod-`p` level — the inverse witness `d_inv` is NOT
  -- range-checked, so `d·d_inv` need not be canonical; the `≠ 0` teeth need only the congruence).
  have hdinv : ((envAt t i).loc (afterFieldCol asset) - (envAt t i).loc (beforeFieldCol asset))
      * (envAt t i).loc D_INV ≡ 1 [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hdnz
  have hminv : ((envAt t i).loc (afterFieldCol share) - (envAt t i).loc (beforeFieldCol share))
      * (envAt t i).loc M_INV ≡ 1 [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hmnz
  -- every mod-`p` congruence has now been consumed; drop them so the remaining `omega`/
  -- `linear_combination` steps run in a purely-linear (congruence-free) context.
  clear hTa hSa hm hd hdnz hmnz van hsat
  -- the schoolbook reconstruction: P = Ta·m over the limbs (pure algebra).
  have ePlimb : ((envAt t i).loc TA0 + 32768 * (envAt t i).loc TA1)
      * ((envAt t i).loc M0 + 32768 * (envAt t i).loc M1)
      = (envAt t i).loc P0 + 32768 * (envAt t i).loc P1
        + 1073741824 * (envAt t i).loc P2 + 35184372088832 * (envAt t i).loc P3 := by
    linear_combination hPA + 32768 * hPB + 32768 * hPC + 1073741824 * hPD
  have eQlimb : ((envAt t i).loc SA0 + 32768 * (envAt t i).loc SA1)
      * ((envAt t i).loc D0 + 32768 * (envAt t i).loc D1)
      = (envAt t i).loc Q0 + 32768 * (envAt t i).loc Q1
        + 1073741824 * (envAt t i).loc Q2 + 35184372088832 * (envAt t i).loc Q3 := by
    linear_combination hQA + 32768 * hQB + 32768 * hQC + 1073741824 * hQD
  have eP : (envAt t i).loc (beforeFieldCol asset)
      * ((envAt t i).loc (afterFieldCol share) - (envAt t i).loc (beforeFieldCol share))
      = (envAt t i).loc P0 + 32768 * (envAt t i).loc P1
        + 1073741824 * (envAt t i).loc P2 + 35184372088832 * (envAt t i).loc P3 := by
    rw [eTa, em]; exact ePlimb
  have eQ : (envAt t i).loc (beforeFieldCol share)
      * ((envAt t i).loc (afterFieldCol asset) - (envAt t i).loc (beforeFieldCol asset))
      = (envAt t i).loc Q0 + 32768 * (envAt t i).loc Q1
        + 1073741824 * (envAt t i).loc Q2 + 35184372088832 * (envAt t i).loc Q3 := by
    rw [eSa, ed]; exact eQlimb
  -- the borrow telescope: Q − P = W ≥ 0 (no final borrow).
  have hPleQ : (envAt t i).loc P0 + 32768 * (envAt t i).loc P1
        + 1073741824 * (envAt t i).loc P2 + 35184372088832 * (envAt t i).loc P3
      ≤ (envAt t i).loc Q0 + 32768 * (envAt t i).loc Q1
        + 1073741824 * (envAt t i).loc Q2 + 35184372088832 * (envAt t i).loc Q3 := by
    omega
  refine ⟨?_, ?_, by omega, by omega, by omega, by omega, ?_⟩
  · intro h0
    rw [h0, zero_mul] at hdinv
    rw [Int.modEq_iff_dvd] at hdinv
    omega
  · intro h0
    rw [h0, zero_mul] at hminv
    rw [Int.modEq_iff_dvd] at hminv
    omega
  · rw [eP, eQ]; exact hPleQ

/-! ## §5 — THE TEETH (in-AIR): the three forgeries are UNSAT. -/

/-- **THE INFLATION (ZERO-MINT) TOOTH.** The ERC-4626 first-depositor attack — a deposit minting
ZERO shares — CANNOT satisfy the welded descriptor on a selector-on NON-LAST row. -/
theorem vault_zero_mint_unsat (hash : List ℤ → ℤ) (asset share : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (vaultSatVmDescriptor2R24 asset share) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc VAULT_SEL_COL = 1)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hzero : (envAt t i).loc (afterFieldCol share) = (envAt t i).loc (beforeFieldCol share)) :
    False := by
  have h := (vaultSatV3_forces hash asset share hsat i hi hnl hsel hcanon).2.1
  omega

/-- **THE NO-DEPOSIT TOOTH.** A "deposit" that does not advance total assets CANNOT satisfy the
welded descriptor on a selector-on NON-LAST row. -/
theorem vault_no_deposit_unsat (hash : List ℤ → ℤ) (asset share : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (vaultSatVmDescriptor2R24 asset share) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc VAULT_SEL_COL = 1)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hnodep : (envAt t i).loc (afterFieldCol asset) = (envAt t i).loc (beforeFieldCol asset)) :
    False := by
  have h := (vaultSatV3_forces hash asset share hsat i hi hnl hsel hcanon).1
  omega

/-- **THE DILUTION (OVER-MINT) TOOTH.** A deposit minting shares past the fair ratio
(`Ta·m > Sa·d`) CANNOT satisfy the welded descriptor on a selector-on NON-LAST row. -/
theorem vault_dilution_unsat (hash : List ℤ → ℤ) (asset share : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (vaultSatVmDescriptor2R24 asset share) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc VAULT_SEL_COL = 1)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdilute : (envAt t i).loc (beforeFieldCol share)
        * ((envAt t i).loc (afterFieldCol asset) - (envAt t i).loc (beforeFieldCol asset))
      < (envAt t i).loc (beforeFieldCol asset)
        * ((envAt t i).loc (afterFieldCol share) - (envAt t i).loc (beforeFieldCol share))) :
    False := by
  have h :=
    (vaultSatV3_forces hash asset share hsat i hi hnl hsel hcanon).2.2.2.2.2.2
  omega

/-- **THE WITHDRAWAL-AS-DEPOSIT TOOTH (the re-audit residual, CLOSED).** A vault-draining WITHDRAWAL
masquerading as a deposit — `before[assets] = 10^9`, `after[assets] = 0`, so the true `Δassets = −10^9`
whose mod-`p` residue `1013265921 < 2^30` had a valid limb decomposition under the old delta gate —
CANNOT satisfy the welded descriptor. The sign-gate ADD chain DERIVES `before ≤ after`, so the forged
positive-delta band is UNSAT; no `hAssetDep` assumption is available to launder it. -/
theorem vault_withdrawal_forgery_unsat (hash : List ℤ → ℤ) (asset share : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (vaultSatVmDescriptor2R24 asset share) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc VAULT_SEL_COL = 1)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hbefore : (envAt t i).loc (beforeFieldCol asset) = 1000000000)
    (hafter : (envAt t i).loc (afterFieldCol asset) = 0) :
    False := by
  have h := (vaultSatV3_forces hash asset share hsat i hi hnl hsel hcanon).2.2.1
  rw [hbefore, hafter] at h
  omega

/-! ## §6 — NON-VACUITY TEETH (`#guard`): the gate bodies BITE on concrete rows.

Unit-delta witnesses (the ℤ-model admits only unit inverse witnesses — the general field witness is
the Rust STARK exercise). The DILUTION tooth is still non-trivial at unit deltas: `Ta = 5 > Sa = 3`
with `d = m = 1` dilutes, and ONLY the final-borrow gate bites. -/

section Witnesses

/-- A row assignment from an association list (unlisted columns read 0). -/
private def mkLoc (assigns : List (Nat × Int)) : Nat → Int := fun c =>
  ((assigns.find? (fun p => p.1 == c)).map Prod.snd).getD 0

/-- Evaluate a welded gate's body on a row assignment. -/
private def gateVal (g : VmConstraint2) (loc : Nat → Int) : Int :=
  match g with
  | .base (.gate body) => body.eval loc
  | _ => 999  -- never matched: the welded gates are all `.gate`

/-- The core (non-bit) witness columns for a single-limb vault row: operands, products, borrow
chain (general in the sign of `Q − P`), inverse witnesses. Deltas are expected in `[0, 2^15)` so
every product fits one limb. -/
private def coreAssigns (sel ba aa bs asv dInv mInv : Int) : List (Nat × Int) :=
  let d := aa - ba
  let m := asv - bs
  let p := ba * m
  let q := bs * d
  let bb : Int := if q < p then 1 else 0
  [(VAULT_SEL_COL, sel),
   (beforeFieldCol 0, ba), (afterFieldCol 0, aa),
   (beforeFieldCol 1, bs), (afterFieldCol 1, asv),
   (TA0, ba), (SA0, bs), (M0, m), (D0, d),
   (P0, p), (Q0, q),
   (W0, q - p + bb * 32768), (W1, 32767 * bb), (W2, 32767 * bb), (W3, 32767 * bb),
   (BB0, bb), (BB1, bb), (BB2, bb), (BB3, bb),
   -- SIGN-GATE witnesses: after-limbs (single-limb, so hi = 0) + zero carries (before + Δ = after
   -- fits one limb for these unit-delta rows).
   (AA0, aa), (AS0, asv),
   (D_INV, dInv), (M_INV, mInv)]

/-- The range-check bit blocks for the core assignment (list order from `BIT_BASE`, exactly the
producer's fill discipline). -/
private def rangeBitsFor (core : List (Nat × Int)) : List (Nat × Int) :=
  go rangeSpecs BIT_BASE
where
  go : List (Nat × Nat) → Nat → List (Nat × Int)
    | [], _ => []
    | (col, n) :: rest, base =>
        (List.range n).map
            (fun i => (base + i, (((((mkLoc core col).toNat >>> i) &&& 1 : Nat) : Int))))
          ++ go rest (base + n)

/-- The full witness row. -/
private def vaultLoc (sel ba aa bs asv dInv mInv : Int) : Nat → Int :=
  let core := coreAssigns sel ba aa bs asv dInv mInv
  mkLoc (core ++ rangeBitsFor core)

-- HONEST unit-delta fair mint: Ta=2, Sa=4, d=m=1 → 2·1 ≤ 4·1 — every welded gate body is 0.
#guard (vaultSatGates 0 1).all (fun g => gateVal g (vaultLoc 1 2 3 4 5 1 1) == 0)
-- ZERO-MINT inflation: a positive deposit minting zero shares — some gate body is NON-zero.
#guard !(vaultSatGates 0 1).all (fun g => gateVal g (vaultLoc 1 2 3 4 4 1 0) == 0)
-- NO-DEPOSIT: total assets not advanced — some gate body is NON-zero.
#guard !(vaultSatGates 0 1).all (fun g => gateVal g (vaultLoc 1 2 2 4 5 0 1) == 0)
-- DILUTION: Ta=5 > Sa=3 at unit deltas (5·1 > 3·1) — the final-borrow gate bites.
#guard !(vaultSatGates 0 1).all (fun g => gateVal g (vaultLoc 1 5 6 3 4 1 1) == 0)
-- SELECTOR OFF: the gates are inert even on the diluting row.
#guard (vaultSatGates 0 1).all (fun g => gateVal g (vaultLoc 0 5 6 3 4 1 1) == 0)
-- The descriptor publishes 47 PIs (the rotated 46 + the appended selector slot).
#guard (vaultSatVmDescriptor2R24 0 1).piCount == 47
-- Gate count: 6 core + 12 sign (no-borrow) + 8 product + 9 borrow + one bool-per-bit + one
-- assembly-per-spec.
#guard (vaultSatGates 0 1).length == 6 + 12 + 8 + 9 + TOTAL_RANGE_BITS + rangeSpecs.length
-- The bit budget: 28 15-bit limbs (24 product/compare + 4 sign after-limbs) + 4 15-bit carries.
#guard TOTAL_RANGE_BITS == 28 * LIMB_BITS + 4 * CARRY_BITS
-- The width derivation through the canonical constants (34 aux + 8 sign-gate aux = 42).
#guard (vaultSatVmDescriptor2R24 0 1).traceWidth == GRAD_ROT_WIDTH + 16 + 42 + TOTAL_RANGE_BITS
#guard V == GRAD_ROT_WIDTH + 16

end Witnesses

/-! ## §7 — Axiom hygiene. -/

#assert_all_clean [
  vaultGate_mem,
  vault_gate_holds,
  sel_body_vanishes,
  rangeAux_forces,
  vaultSatV3_forces,
  vault_zero_mint_unsat,
  vault_no_deposit_unsat,
  vault_dilution_unsat,
  vault_withdrawal_forgery_unsat
]

end Dregg2.Deos.VaultSatDescriptor
