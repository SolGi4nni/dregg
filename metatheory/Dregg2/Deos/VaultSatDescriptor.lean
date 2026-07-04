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

set_option autoImplicit false

/-! ## §1 — the welded columns (the Rust `vault_weld` twin, canonical-constant-derived). -/

/-- The capacity selector column (`prmCol 2` — a SEPARATE descriptor, slot reused). Rust
`vault_weld::VAULT_SEL_COL`. -/
def VAULT_SEL_COL : Nat := prmCol 2
/-- The selector PI slot (the appended 47th). Rust `VAULT_SEL_PI`. -/
def VAULT_SEL_PI : Nat := 46

/-- Limb width (15 bits keeps every partial product `< 2^30 < p`). Rust `LIMB_BITS`. -/
def LIMB_BITS : Nat := 15
/-- Cross-term carry width (one bit past the limb width). Rust `CARRY_BITS`. -/
def CARRY_BITS : Nat := 16
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
/-- First bit-decomposition column. Rust `BIT_BASE`. -/
def BIT_BASE : Nat := V + 34

/-- The ordered range-checked columns and their bit widths — the Rust `range_specs` list, in
lockstep with the producer fill (bit blocks assigned in list order from `BIT_BASE`). -/
def rangeSpecs : List (Nat × Nat) :=
  [(TA0, LIMB_BITS), (TA1, LIMB_BITS), (SA0, LIMB_BITS), (SA1, LIMB_BITS),
   (M0, LIMB_BITS), (M1, LIMB_BITS), (D0, LIMB_BITS), (D1, LIMB_BITS),
   (P0, LIMB_BITS), (P1, LIMB_BITS), (P2, LIMB_BITS), (P3, LIMB_BITS),
   (PCA, LIMB_BITS), (PCB, CARRY_BITS), (PCC, CARRY_BITS), (PT1, LIMB_BITS),
   (Q0, LIMB_BITS), (Q1, LIMB_BITS), (Q2, LIMB_BITS), (Q3, LIMB_BITS),
   (QCA, LIMB_BITS), (QCB, CARRY_BITS), (QCC, CARRY_BITS), (QT1, LIMB_BITS),
   (W0, LIMB_BITS), (W1, LIMB_BITS), (W2, LIMB_BITS), (W3, LIMB_BITS)]

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

/-- A welded gate's body vanishes on a satisfying NON-LAST row. -/
theorem vault_gate_holds (hash : List ℤ → ℤ) (asset share : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (vaultSatVmDescriptor2R24 asset share) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (g : VmConstraint2) (hg : g ∈ vaultSatGates asset share)
    (body : EmittedExpr) (hbody : g = .base (.gate body)) :
    body.eval (envAt t i).loc = 0 := by
  have hrow := hsat.rowConstraints i hi g (vaultGate_mem asset share g hg)
  rw [hbody] at hrow
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, hnl] using hrow

/-- A selector-gated body vanishes outright on a selector-on satisfying NON-LAST row. -/
theorem sel_body_vanishes (hash : List ℤ → ℤ) (asset share : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (vaultSatVmDescriptor2R24 asset share) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc VAULT_SEL_COL = 1)
    (body : EmittedExpr) (hmem : selGate body ∈ vaultSatGates asset share) :
    body.eval (envAt t i).loc = 0 := by
  have h := vault_gate_holds hash asset share hsat i hi hnl (selGate body) hmem
    (.mul (.var VAULT_SEL_COL) body) rfl
  simp only [EmittedExpr.eval, hsel, one_mul] at h
  exact h

/-- The range-check induction: every spec'd column is forced into `[0, 2^n)` (one induction over the
spec list gives ALL the range facts uniformly). -/
theorem rangeAux_forces (loc : Nat → Int)
    (specs : List (Nat × Nat)) (base : Nat)
    (hvan : ∀ body : EmittedExpr, selGate body ∈ rangeGatesAux specs base → body.eval loc = 0) :
    ∀ col n : Nat, (col, n) ∈ specs → 0 ≤ loc col ∧ loc col < 2 ^ n := by
  induction specs generalizing base with
  | nil => intro col n h; cases h
  | cons hd rest ih =>
    obtain ⟨c0, n0⟩ := hd
    intro col n hmem
    rcases List.mem_cons.mp hmem with heq | htail
    · injection heq with h1 h2
      subst h1; subst h2
      -- the bit columns are boolean.
      have hbits : ∀ j, j < n → loc (base + j) = 0 ∨ loc (base + j) = 1 := by
        intro j hj
        have hb := hvan (.mul (.var (base + j)) (.add (.var (base + j)) (.const (-1))))
          (by
            simp only [rangeGatesAux]
            apply List.mem_append_left
            apply List.mem_append_left
            exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
        simp only [EmittedExpr.eval] at hb
        rcases mul_eq_zero.mp hb with hb | hb
        · exact Or.inl hb
        · right; omega
      -- the assembly pins the column to the bit sum.
      have hasm := hvan (.add (.var col) (neg (bitSum (fun i => base + i) n)))
        (by
          simp only [rangeGatesAux]
          apply List.mem_append_left
          apply List.mem_append_right
          exact List.mem_singleton.mpr rfl)
      simp only [neg, EmittedExpr.eval] at hasm
      have hb := bitSum_nonneg_lt loc (fun i => base + i) n hbits
      constructor <;> omega
    · exact ih (base + n0)
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
    (hsel : (envAt t i).loc VAULT_SEL_COL = 1) :
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
  -- ALL the range facts in one induction (`rangeGates ⊆ vaultSatGates`).
  have hranges := rangeAux_forces (envAt t i).loc rangeSpecs BIT_BASE
    (fun body hb => van body (by
      unfold vaultSatGates
      exact List.mem_append_right _ hb))
  have hM0 := hranges M0 LIMB_BITS (by simp [rangeSpecs])
  have hM1 := hranges M1 LIMB_BITS (by simp [rangeSpecs])
  have hD0 := hranges D0 LIMB_BITS (by simp [rangeSpecs])
  have hD1 := hranges D1 LIMB_BITS (by simp [rangeSpecs])
  have hW0 := hranges W0 LIMB_BITS (by simp [rangeSpecs])
  have hW1 := hranges W1 LIMB_BITS (by simp [rangeSpecs])
  have hW2 := hranges W2 LIMB_BITS (by simp [rangeSpecs])
  have hW3 := hranges W3 LIMB_BITS (by simp [rangeSpecs])
  rw [show (2 : Int) ^ LIMB_BITS = 32768 by norm_num [LIMB_BITS]]
    at hM0 hM1 hD0 hD1 hW0 hW1 hW2 hW3
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
  -- reduce every extracted gate body to its arithmetic form.
  simp only [sub, neg, mExpr, dExpr, TWO15, EmittedExpr.eval] at hTa hSa hm hd hdnz hmnz
  simp only [sub, neg, TWO15, EmittedExpr.eval] at hPA hPB hPC hPD hQA hQB hQC hQD
  simp only [sub, neg, TWO15, EmittedExpr.eval] at hb0 hb1 hb2 hb3 hbb3
  -- linear consequences (operand welds).
  have eTa : (envAt t i).loc (beforeFieldCol asset)
      = (envAt t i).loc TA0 + 32768 * (envAt t i).loc TA1 := by omega
  have eSa : (envAt t i).loc (beforeFieldCol share)
      = (envAt t i).loc SA0 + 32768 * (envAt t i).loc SA1 := by omega
  have em : (envAt t i).loc (afterFieldCol share) - (envAt t i).loc (beforeFieldCol share)
      = (envAt t i).loc M0 + 32768 * (envAt t i).loc M1 := by omega
  have ed : (envAt t i).loc (afterFieldCol asset) - (envAt t i).loc (beforeFieldCol asset)
      = (envAt t i).loc D0 + 32768 * (envAt t i).loc D1 := by omega
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
  -- the strict-positivity witnesses.
  have hdinv : ((envAt t i).loc (afterFieldCol asset) - (envAt t i).loc (beforeFieldCol asset))
      * (envAt t i).loc D_INV = 1 := by linear_combination hdnz
  have hminv : ((envAt t i).loc (afterFieldCol share) - (envAt t i).loc (beforeFieldCol share))
      * (envAt t i).loc M_INV = 1 := by linear_combination hmnz
  refine ⟨?_, ?_, by omega, by omega, by omega, by omega, ?_⟩
  · intro h0
    rw [h0, zero_mul] at hdinv
    omega
  · intro h0
    rw [h0, zero_mul] at hminv
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
    (hzero : (envAt t i).loc (afterFieldCol share) = (envAt t i).loc (beforeFieldCol share)) :
    False := by
  have h := (vaultSatV3_forces hash asset share hsat i hi hnl hsel).2.1
  omega

/-- **THE NO-DEPOSIT TOOTH.** A "deposit" that does not advance total assets CANNOT satisfy the
welded descriptor on a selector-on NON-LAST row. -/
theorem vault_no_deposit_unsat (hash : List ℤ → ℤ) (asset share : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (vaultSatVmDescriptor2R24 asset share) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc VAULT_SEL_COL = 1)
    (hnodep : (envAt t i).loc (afterFieldCol asset) = (envAt t i).loc (beforeFieldCol asset)) :
    False := by
  have h := (vaultSatV3_forces hash asset share hsat i hi hnl hsel).1
  omega

/-- **THE DILUTION (OVER-MINT) TOOTH.** A deposit minting shares past the fair ratio
(`Ta·m > Sa·d`) CANNOT satisfy the welded descriptor on a selector-on NON-LAST row. -/
theorem vault_dilution_unsat (hash : List ℤ → ℤ) (asset share : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (vaultSatVmDescriptor2R24 asset share) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc VAULT_SEL_COL = 1)
    (hdilute : (envAt t i).loc (beforeFieldCol share)
        * ((envAt t i).loc (afterFieldCol asset) - (envAt t i).loc (beforeFieldCol asset))
      < (envAt t i).loc (beforeFieldCol asset)
        * ((envAt t i).loc (afterFieldCol share) - (envAt t i).loc (beforeFieldCol share))) :
    False := by
  have h := (vaultSatV3_forces hash asset share hsat i hi hnl hsel).2.2.2.2.2.2
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
-- Gate count: 6 core + 8 product + 9 borrow + one bool-per-bit + one assembly-per-spec.
#guard (vaultSatGates 0 1).length == 6 + 8 + 9 + TOTAL_RANGE_BITS + rangeSpecs.length
-- The bit budget: 24 15-bit limbs + 4 16-bit carries.
#guard TOTAL_RANGE_BITS == 24 * LIMB_BITS + 4 * CARRY_BITS
-- The width derivation through the canonical constants.
#guard (vaultSatVmDescriptor2R24 0 1).traceWidth == GRAD_ROT_WIDTH + 16 + 34 + TOTAL_RANGE_BITS
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
  vault_dilution_unsat
]

end Dregg2.Deos.VaultSatDescriptor
