/-
# Dregg2.Deos.DischargeSatDescriptor — the WELDED discharge-obligation (tag 18) satisfaction
descriptor, made REAL at the v12 geometry (the G5 emit-prep: 18/19 catch up to escrow-17's doneness).

The sealed-escrow satisfaction weld shipped end-to-end (`SettleEscrowSatDescriptor` — emitted
descriptor + producer + `gentian_carrier_floor_prove` real STARKs). Tags 18/19 had the in-AIR gate
POLYNOMIALS (`circuit/src/effect_vm/discharge_weld.rs`, sound-as-shaped: row-locality fixed,
selector-forcing strengthened, the due-ness range gadget with constraint-level teeth) but NO staged
descriptor emitted and NO exported producer aux-fill. This module is the tag-18 emit keystone: the
genuine `EffectVmDescriptor2` over the deployed R=24 rotated cohort carrying the DISCHARGE
satisfaction gates, plus the refinement rung — a satisfying trace with the capacity selector on
FORCES the discharge discipline (`DischargeFieldGate`, `Dregg2.Deos.CapacitySatisfaction` §8) over
the rotated state-block FIELD columns the ~124-bit wide commit absorbs.

## The construction (the escrow shape, plus the due-ness range gadget)

`dischargeSatVmDescriptor2R24 cur tot due` is `graduateV1 (rotateV3 base)` of a settle-shaped v1
base (the escrow base re-used: the transfer descriptor with the `cur`/`tot` field-freezes dropped —
a discharge CHANGES those two fields; `due` and the other five stay frozen), PLUS the selector-gated
satisfaction gates, PLUS the selector PI pin — the additive fifth-pin shape every deployed variant
uses. The gates (the Rust `discharge_weld::discharge_satisfaction_gates` twin, byte-for-byte):

 1. cursor advance `sel · (after[cur] − before[cur] − period) == 0`
 2. total advance  `sel · (after[tot] − before[tot] − amount) == 0`
 3. due-ness link  `sel · (clock − before[due] − DUE_DIFF) == 0`
 4. `DUE_DIFF` booleanity + assembly over `DUE_BITS = 28` bit columns (forces `DUE_DIFF ∈ [0, 2^28)`)
 5. `before[due]` booleanity + assembly (the wrap-to-small dodge closed)

## v12 offsets, derived — never literals

The rotated BEFORE/AFTER field columns are the escrow module's `beforeFieldCol`/`afterFieldCol`
(`EFFECT_VM_WIDTH + 4 + k` / `EFFECT_VM_WIDTH + B_SPAN + 4 + k`, `B_SPAN` the CANONICAL
`EffectVmEmitRotationV3.B_SPAN` — 227 at v13); the range-check aux block is based at
`GRAD_ROT_WIDTH + 16` where `GRAD_ROT_WIDTH` is COMPUTED as the graduated rotated cohort width
(`(graduateV1 (rotateV3 base)).traceWidth`), the Lean twin of the Rust
`trace_rotated::GRAD_ROT_WIDTH`. Nothing here freezes a v11 (or v12) literal: the defs track the
geometry-grow through the canonical constants, so the descriptor is REGEN-READY.

## STAGED — the registry row rides the BIG-BANG regen

This descriptor is NOT yet in `rotation-v3-staged-registry.tsv` and has NO FP pin and NO live
routing: the registry row + the drift-gate pin + the caveat-manifest coverage tie land in the ONE
shared big-bang descriptor regen (with G5 17/18/19 + the flat-mem weld). The floor decode /
selector-force / caveat-uniformity gates are the SEPARATE `discharge_weld::discharge_floor_gates`
block a prove exercise welds on top (the gentian pattern); the emitted descriptor here carries the
SATISFACTION discipline + the pinned selector it hangs on.

## Axiom hygiene

`#assert_all_clean` at the close. No axiom, no `sorry`, no core edit. The refinement reduces through
the STABLE `holdsVm_gate_false` interface, exactly like the escrow rung.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Deos.SettleEscrowSatDescriptor

namespace Dregg2.Deos.DischargeSatDescriptor

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (rotateV3)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Deos.SettleEscrowSatDescriptor
  (settleEscrowV1Base beforeFieldCol afterFieldCol)

set_option autoImplicit false

/-! ## §1 — the welded columns (the Rust `discharge_weld` twin, canonical-constant-derived). -/

/-- The capacity selector column — the free PARAM slot `prmCol 2` (a SEPARATE descriptor, so the
escrow slot is reused). Rust `discharge_weld::DISCHARGE_SEL_COL`. -/
def DISCHARGE_SEL_COL : Nat := prmCol 2

/-- The selector PI slot (the appended 47th, `pi_base + 4 = 46`). Rust `DISCHARGE_SEL_PI`. -/
def DISCHARGE_SEL_PI : Nat := 46

/-- The carrier-bound `period` scalar column (`prmCol 5`). Rust `PERIOD_COL`. -/
def PERIOD_COL : Nat := prmCol 5
/-- The carrier-bound `amount` scalar column (`prmCol 6`). Rust `AMOUNT_COL`. -/
def AMOUNT_COL : Nat := prmCol 6
/-- The batch-height `clock` scalar column (`prmCol 7`). Rust `CLOCK_COL`. -/
def CLOCK_COL : Nat := prmCol 7

/-- **THE GRADUATED ROTATED COHORT WIDTH** — computed from the canonical emit (the graduated
rotation of the settle-shaped base), NOT a literal; the Lean twin of the Rust
`trace_rotated::GRAD_ROT_WIDTH`. All the discharge aux columns are based past it. -/
def GRAD_ROT_WIDTH : Nat := (graduateV1 (rotateV3 (settleEscrowV1Base 0 1))).traceWidth

/-- The bit-width of the due-ness range check (Rust `discharge_weld::DUE_BITS`; ≤ 29 is the sound
BabyBear window, 28 taken). -/
def DUE_BITS : Nat := 28

/-- The range-check aux block base (past the 16-column floor-decode aux headroom). Rust `RC_BASE`. -/
def RC_BASE : Nat := GRAD_ROT_WIDTH + 16

/-- The due-ness difference column `DUE_DIFF = clock − before[due]`. Rust `DUE_DIFF_COL`. -/
def DUE_DIFF_COL : Nat := RC_BASE
/-- Bit `i` of the `DUE_DIFF` decomposition. Rust `diff_bit_col`. -/
def diffBitCol (i : Nat) : Nat := RC_BASE + 1 + i
/-- Bit `i` of the committed-`due_block` decomposition. Rust `due_bit_col`. -/
def dueBitCol (i : Nat) : Nat := RC_BASE + 1 + DUE_BITS + i

/-! ## §2 — the gate bodies (byte-for-byte the Rust builders' expression trees). -/

/-- Negation as the Rust `discharge_weld::neg`: `(-1) · e`. -/
def neg (e : EmittedExpr) : EmittedExpr := .mul (.const (-1)) e

/-- A selector-gated gate `sel · body` (inert when `sel = 0`). Rust `sel_gate`. -/
def selGate (body : EmittedExpr) : VmConstraint2 :=
  .base (.gate (.mul (.var DISCHARGE_SEL_COL) body))

/-- A selector-gated booleanity gate `sel · (b · (b − 1))`. Rust `sel_bool_gate`. -/
def selBoolGate (b : Nat) : VmConstraint2 :=
  selGate (.mul (.var b) (.add (.var b) (.const (-1))))

/-- `Σ_{i<n} 2^i · bit(i)` as the Rust `bit_sum` fold (seeded at `const 0`, low bit first). -/
def bitSum (bit : Nat → Nat) : Nat → EmittedExpr
  | 0 => .const 0
  | n + 1 => .add (bitSum bit n) (.mul (.const ((2 : Int) ^ n)) (.var (bit n)))

/-- A selector-gated range-assembly gate `sel · (value − Σ 2^i bit_i)`. Rust `sel_assembly_gate`. -/
def selAssemblyGate (value : EmittedExpr) (bit : Nat → Nat) (n : Nat) : VmConstraint2 :=
  selGate (.add value (neg (bitSum bit n)))

/-- (1) cursor advance `sel · (after[cur] − before[cur] − period)`. -/
def cursorGate (cur : Nat) : VmConstraint2 :=
  selGate (.add (.add (.var (afterFieldCol cur)) (neg (.var (beforeFieldCol cur))))
    (neg (.var PERIOD_COL)))

/-- (2) total advance `sel · (after[tot] − before[tot] − amount)`. -/
def totalGate (tot : Nat) : VmConstraint2 :=
  selGate (.add (.add (.var (afterFieldCol tot)) (neg (.var (beforeFieldCol tot))))
    (neg (.var AMOUNT_COL)))

/-- (3a) due-ness link `sel · (clock − before[due] − DUE_DIFF)`. -/
def dueLinkGate (due : Nat) : VmConstraint2 :=
  selGate (.add (.add (.var CLOCK_COL) (neg (.var (beforeFieldCol due))))
    (neg (.var DUE_DIFF_COL)))

/-- **THE DISCHARGE SATISFACTION GATES** — the exact list (order and all) the Rust
`discharge_weld::discharge_satisfaction_gates` builds: cursor, total, link, the `DUE_DIFF`
booleanity block + assembly, the `before[due]` booleanity block + assembly. -/
def dischargeSatGates (cur tot due : Nat) : List VmConstraint2 :=
  [cursorGate cur, totalGate tot, dueLinkGate due]
    ++ (List.range DUE_BITS).map (fun i => selBoolGate (diffBitCol i))
    ++ [selAssemblyGate (.var DUE_DIFF_COL) diffBitCol DUE_BITS]
    ++ (List.range DUE_BITS).map (fun i => selBoolGate (dueBitCol i))
    ++ [selAssemblyGate (.var (beforeFieldCol due)) dueBitCol DUE_BITS]

/-! ## §3 — THE WELDED DESCRIPTOR (the tag-18 emit keystone). -/

/-- The descriptor trace width: past the last due-bit column (covers the floor-decode aux headroom
`GRAD_ROT_WIDTH + 0..15` and the whole range-check block). -/
def DISCHARGE_WIDTH : Nat := dueBitCol (DUE_BITS - 1) + 1

/-- **`dischargeSatVmDescriptor2R24`** — the welded discharge-obligation satisfaction descriptor
over the R=24 rotated cohort. `graduateV1 (rotateV3 settle-base)` (the `cur`/`tot` freezes dropped)
PLUS the discharge satisfaction gates PLUS the selector PI pin; the trace WIDENED to carry the
range-check aux block (the tables re-declared at the widened arity). `piCount = 47`. STAGED: the
registry row + FP pin ride the big-bang regen. -/
def dischargeSatVmDescriptor2R24 (cur tot due : Nat) : EffectVmDescriptor2 :=
  let base := graduateV1 (rotateV3
    { settleEscrowV1Base cur tot with name := "dregg-effectvm-discharge-sat-v1" })
  { base with
    name        := "dregg-effectvm-discharge-sat-v1-rot24-v3-staged"
    traceWidth  := DISCHARGE_WIDTH
    tables      := v2Tables DISCHARGE_WIDTH
    piCount     := base.piCount + 1
    constraints := base.constraints ++ dischargeSatGates cur tot due
                     ++ [.base (.piBinding .first DISCHARGE_SEL_COL DISCHARGE_SEL_PI)] }

/-- Each welded gate is a member of the descriptor's constraint list. -/
theorem dischargeGate_mem (cur tot due : Nat) (g : VmConstraint2)
    (hg : g ∈ dischargeSatGates cur tot due) :
    g ∈ (dischargeSatVmDescriptor2R24 cur tot due).constraints := by
  unfold dischargeSatVmDescriptor2R24
  simp only [List.mem_append]
  exact Or.inl (Or.inr hg)

/-! ### Membership of the individual gates (the extraction plumbing). -/

theorem cursorGate_mem (cur tot due : Nat) :
    cursorGate cur ∈ dischargeSatGates cur tot due := by
  simp [dischargeSatGates]

theorem totalGate_mem (cur tot due : Nat) :
    totalGate tot ∈ dischargeSatGates cur tot due := by
  simp [dischargeSatGates]

theorem dueLinkGate_mem (cur tot due : Nat) :
    dueLinkGate due ∈ dischargeSatGates cur tot due := by
  simp [dischargeSatGates]

theorem diffBool_mem (cur tot due i : Nat) (hi : i < DUE_BITS) :
    selBoolGate (diffBitCol i) ∈ dischargeSatGates cur tot due := by
  unfold dischargeSatGates
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem dueBool_mem (cur tot due i : Nat) (hi : i < DUE_BITS) :
    selBoolGate (dueBitCol i) ∈ dischargeSatGates cur tot due := by
  unfold dischargeSatGates
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem diffAssembly_mem (cur tot due : Nat) :
    selAssemblyGate (.var DUE_DIFF_COL) diffBitCol DUE_BITS ∈ dischargeSatGates cur tot due := by
  unfold dischargeSatGates
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_singleton.mpr rfl

theorem dueAssembly_mem (cur tot due : Nat) :
    selAssemblyGate (.var (beforeFieldCol due)) dueBitCol DUE_BITS
      ∈ dischargeSatGates cur tot due := by
  unfold dischargeSatGates
  apply List.mem_append_right
  exact List.mem_singleton.mpr rfl

/-! ## §4 — THE REFINEMENT RUNG: a satisfying trace FORCES the discharge discipline. -/

/-- A welded gate's body vanishes on a satisfying NON-LAST row (the escrow `welded_gate_holds`
pattern, verbatim through the stable `holdsVm` interface). -/
theorem discharge_gate_holds (hash : List ℤ → ℤ) (cur tot due : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (dischargeSatVmDescriptor2R24 cur tot due) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (g : VmConstraint2) (hg : g ∈ dischargeSatGates cur tot due)
    (body : EmittedExpr) (hbody : g = .base (.gate body)) :
    body.eval (envAt t i).loc = 0 := by
  have hrow := hsat.rowConstraints i hi g (dischargeGate_mem cur tot due g hg)
  rw [hbody] at hrow
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, hnl] using hrow

/-- Any welded booleanity bit is genuinely boolean on a selector-on row. -/
theorem bit_boolean (hash : List ℤ → ℤ) (cur tot due : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (dischargeSatVmDescriptor2R24 cur tot due) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc DISCHARGE_SEL_COL = 1)
    (b : Nat) (hmem : selBoolGate b ∈ dischargeSatGates cur tot due) :
    (envAt t i).loc b = 0 ∨ (envAt t i).loc b = 1 := by
  have h := discharge_gate_holds hash cur tot due hsat i hi hnl (selBoolGate b) hmem
    (.mul (.var DISCHARGE_SEL_COL) (.mul (.var b) (.add (.var b) (.const (-1))))) rfl
  simp only [EmittedExpr.eval, hsel, one_mul] at h
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · right; omega

/-- A boolean-bit sum is in `[0, 2^n)` (the range-check payoff, by induction on the width). -/
theorem bitSum_nonneg_lt (loc : Nat → ℤ) (bit : Nat → Nat) :
    ∀ n, (∀ i, i < n → loc (bit i) = 0 ∨ loc (bit i) = 1) →
      0 ≤ (bitSum bit n).eval loc ∧ (bitSum bit n).eval loc < 2 ^ n := by
  intro n
  induction n with
  | zero => intro _; simp [bitSum, EmittedExpr.eval]
  | succ n ih =>
    intro hb
    obtain ⟨h0, h1⟩ := ih (fun i hi => hb i (Nat.lt_succ_of_lt hi))
    have hpow : (2 : ℤ) ^ (n + 1) = 2 ^ n + 2 ^ n := by
      rw [pow_succ]; ring
    have hp : (0 : ℤ) < 2 ^ n := by positivity
    simp only [bitSum, EmittedExpr.eval]
    rcases hb n (Nat.lt_succ_self n) with h | h <;> rw [h] <;> constructor <;> omega
  termination_by n => n

/-- An assembly gate on a selector-on row pins its value to the bit sum. -/
theorem assembly_pins (hash : List ℤ → ℤ) (cur tot due : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (dischargeSatVmDescriptor2R24 cur tot due) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc DISCHARGE_SEL_COL = 1)
    (vcol : Nat) (bit : Nat → Nat)
    (hmem : selAssemblyGate (.var vcol) bit DUE_BITS ∈ dischargeSatGates cur tot due) :
    (envAt t i).loc vcol = (bitSum bit DUE_BITS).eval (envAt t i).loc := by
  have h := discharge_gate_holds hash cur tot due hsat i hi hnl _ hmem
    (.mul (.var DISCHARGE_SEL_COL)
      (.add (.var vcol) (.mul (.const (-1)) (bitSum bit DUE_BITS)))) rfl
  simp only [EmittedExpr.eval, hsel, one_mul] at h
  omega

/-- **THE REFINEMENT KEYSTONE.** On a satisfying trace, a NON-LAST row whose discharge selector is
`1` FORCES the discharge discipline over the rotated field columns the wide commit absorbs (the
`DischargeFieldGate` conjuncts): the cursor advanced by exactly `period`, the discharged total by
exactly `amount`, and the committed due block is DUE (`before[due] ≤ clock`, via the range-checked
difference) — with `before[due]` itself range-bounded (the wrap-to-small dodge closed in the model
by the same bound). -/
theorem dischargeSatV3_forces (hash : List ℤ → ℤ) (cur tot due : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (dischargeSatVmDescriptor2R24 cur tot due) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc DISCHARGE_SEL_COL = 1) :
    (envAt t i).loc (afterFieldCol cur)
        = (envAt t i).loc (beforeFieldCol cur) + (envAt t i).loc PERIOD_COL
    ∧ (envAt t i).loc (afterFieldCol tot)
        = (envAt t i).loc (beforeFieldCol tot) + (envAt t i).loc AMOUNT_COL
    ∧ (envAt t i).loc (beforeFieldCol due) ≤ (envAt t i).loc CLOCK_COL
    ∧ 0 ≤ (envAt t i).loc (beforeFieldCol due)
    ∧ (envAt t i).loc (beforeFieldCol due) < 2 ^ DUE_BITS := by
  -- (1) cursor advance.
  have hcur := discharge_gate_holds hash cur tot due hsat i hi hnl _ (cursorGate_mem cur tot due)
    (.mul (.var DISCHARGE_SEL_COL)
      (.add (.add (.var (afterFieldCol cur)) (.mul (.const (-1)) (.var (beforeFieldCol cur))))
        (.mul (.const (-1)) (.var PERIOD_COL)))) rfl
  simp only [EmittedExpr.eval, hsel, one_mul] at hcur
  -- (2) total advance.
  have htot := discharge_gate_holds hash cur tot due hsat i hi hnl _ (totalGate_mem cur tot due)
    (.mul (.var DISCHARGE_SEL_COL)
      (.add (.add (.var (afterFieldCol tot)) (.mul (.const (-1)) (.var (beforeFieldCol tot))))
        (.mul (.const (-1)) (.var AMOUNT_COL)))) rfl
  simp only [EmittedExpr.eval, hsel, one_mul] at htot
  -- (3a) the due-ness link.
  have hlink := discharge_gate_holds hash cur tot due hsat i hi hnl _ (dueLinkGate_mem cur tot due)
    (.mul (.var DISCHARGE_SEL_COL)
      (.add (.add (.var CLOCK_COL) (.mul (.const (-1)) (.var (beforeFieldCol due))))
        (.mul (.const (-1)) (.var DUE_DIFF_COL)))) rfl
  simp only [EmittedExpr.eval, hsel, one_mul] at hlink
  -- (3b) DUE_DIFF ∈ [0, 2^28).
  have hdiffBits : ∀ j, j < DUE_BITS →
      (envAt t i).loc (diffBitCol j) = 0 ∨ (envAt t i).loc (diffBitCol j) = 1 :=
    fun j hj => bit_boolean hash cur tot due hsat i hi hnl hsel _ (diffBool_mem cur tot due j hj)
  have hdiffPin := assembly_pins hash cur tot due hsat i hi hnl hsel DUE_DIFF_COL diffBitCol
    (diffAssembly_mem cur tot due)
  have hdiffRange := bitSum_nonneg_lt (envAt t i).loc diffBitCol DUE_BITS hdiffBits
  -- (3c) before[due] ∈ [0, 2^28).
  have hdueBits : ∀ j, j < DUE_BITS →
      (envAt t i).loc (dueBitCol j) = 0 ∨ (envAt t i).loc (dueBitCol j) = 1 :=
    fun j hj => bit_boolean hash cur tot due hsat i hi hnl hsel _ (dueBool_mem cur tot due j hj)
  have hduePin := assembly_pins hash cur tot due hsat i hi hnl hsel (beforeFieldCol due) dueBitCol
    (dueAssembly_mem cur tot due)
  have hdueRange := bitSum_nonneg_lt (envAt t i).loc dueBitCol DUE_BITS hdueBits
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-! ## §5 — THE TEETH (in-AIR): the three forgeries are UNSAT. -/

/-- **THE NO-EARLY TOOTH.** A discharge with `clock < before[due]` (paying BEFORE the schedule is
due) on a selector-on NON-LAST row CANNOT satisfy the welded descriptor: the range-checked
difference forces `before[due] ≤ clock`. -/
theorem early_discharge_unsat (hash : List ℤ → ℤ) (cur tot due : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (dischargeSatVmDescriptor2R24 cur tot due) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc DISCHARGE_SEL_COL = 1)
    (hearly : (envAt t i).loc CLOCK_COL < (envAt t i).loc (beforeFieldCol due)) :
    False := by
  have h := (dischargeSatV3_forces hash cur tot due hsat i hi hnl hsel).2.2.1
  omega

/-- **THE NO-REPLAY TOOTH.** A discharge leaving the one-shot cursor where it was (no `+period`
advance, `period ≠ 0`) on a selector-on NON-LAST row CANNOT satisfy the welded descriptor. -/
theorem cursor_not_advanced_unsat (hash : List ℤ → ℤ) (cur tot due : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (dischargeSatVmDescriptor2R24 cur tot due) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc DISCHARGE_SEL_COL = 1)
    (hstuck : (envAt t i).loc (afterFieldCol cur) = (envAt t i).loc (beforeFieldCol cur))
    (hperiod : (envAt t i).loc PERIOD_COL ≠ 0) :
    False := by
  have h := (dischargeSatV3_forces hash cur tot due hsat i hi hnl hsel).1
  omega

/-- **THE NO-WRONG-AMOUNT TOOTH.** A discharge advancing the total by anything other than the
schedule amount on a selector-on NON-LAST row CANNOT satisfy the welded descriptor. -/
theorem wrong_amount_unsat (hash : List ℤ → ℤ) (cur tot due : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash (dischargeSatVmDescriptor2R24 cur tot due) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hsel : (envAt t i).loc DISCHARGE_SEL_COL = 1)
    (hwrong : (envAt t i).loc (afterFieldCol tot)
        ≠ (envAt t i).loc (beforeFieldCol tot) + (envAt t i).loc AMOUNT_COL) :
    False := by
  have h := (dischargeSatV3_forces hash cur tot due hsat i hi hnl hsel).2.1
  omega

/-! ## §6 — NON-VACUITY TEETH (`#guard`): the gate bodies BITE on concrete rows. -/

section Witnesses

/-- A row assignment from an association list (unlisted columns read 0). -/
private def mkLoc (assigns : List (Nat × Int)) : Nat → Int := fun c =>
  ((assigns.find? (fun p => p.1 == c)).map Prod.snd).getD 0

/-- Evaluate a welded gate's body on a row assignment. -/
private def gateVal (g : VmConstraint2) (loc : Nat → Int) : Int :=
  match g with
  | .base (.gate body) => body.eval loc
  | _ => 999  -- never matched: the welded gates are all `.gate`

/-- The bit columns of `v`, low bit first, as assignments. -/
private def bitsAssign (bit : Nat → Nat) (v : Nat) : List (Nat × Int) :=
  (List.range DUE_BITS).map (fun i => (bit i, ((v >>> i) &&& 1 : Nat)))

/-- The honest §10 discharge row: cursor 1000→1100 (+period 100), total 0→50 (+amount 50), due
1000 ≤ clock 1000 (`DUE_DIFF = 0`), selector on. Slots: cur 0, tot 1, due 2. -/
private def honestLoc (clock diff afterCur afterTot : Int) : Nat → Int :=
  mkLoc ([(DISCHARGE_SEL_COL, 1),
          (beforeFieldCol 0, 1000), (afterFieldCol 0, afterCur),
          (beforeFieldCol 1, 0),    (afterFieldCol 1, afterTot),
          (beforeFieldCol 2, 1000),
          (PERIOD_COL, 100), (AMOUNT_COL, 50), (CLOCK_COL, clock),
          (DUE_DIFF_COL, diff)]
    ++ bitsAssign dueBitCol 1000)

-- HONEST: every welded gate body is 0.
#guard (dischargeSatGates 0 1 2).all
  (fun g => gateVal g (honestLoc 1000 0 1100 50) == 0)
-- EARLY: clock 999 below due 1000 — some gate body is NON-zero (the link/assembly bite).
#guard !(dischargeSatGates 0 1 2).all
  (fun g => gateVal g (honestLoc 999 (-1) 1100 50) == 0)
-- NOT-ADVANCED: the cursor left at 1000 — the cursor gate bites.
#guard !(dischargeSatGates 0 1 2).all
  (fun g => gateVal g (honestLoc 1000 0 1000 50) == 0)
-- WRONG AMOUNT: total advanced to 9999 ≠ 50 — the total gate bites.
#guard !(dischargeSatGates 0 1 2).all
  (fun g => gateVal g (honestLoc 1000 0 1100 9999) == 0)
-- SELECTOR OFF: the gates are inert even with arbitrary garbage values.
#guard (dischargeSatGates 0 1 2).all
  (fun g => gateVal g (mkLoc [(beforeFieldCol 0, 7), (afterFieldCol 0, 9), (CLOCK_COL, 3)]) == 0)
-- The descriptor publishes 47 PIs (the rotated 46 + the appended selector slot).
#guard (dischargeSatVmDescriptor2R24 0 1 2).piCount == 47
-- The gate count: 3 relation gates + two 28-bit booleanity blocks + two assemblies.
#guard (dischargeSatGates 0 1 2).length == 3 + 2 * DUE_BITS + 2
-- The width covers exactly through the last due-bit column (the aux block derivation).
#guard (dischargeSatVmDescriptor2R24 0 1 2).traceWidth == GRAD_ROT_WIDTH + 16 + 1 + 2 * DUE_BITS
-- The aux block sits just past the 16-column floor-decode headroom (the Rust `RC_BASE` twin).
#guard DUE_DIFF_COL == GRAD_ROT_WIDTH + 16

end Witnesses

/-! ## §7 — Axiom hygiene. -/

#assert_all_clean [
  dischargeGate_mem,
  discharge_gate_holds,
  bit_boolean,
  bitSum_nonneg_lt,
  assembly_pins,
  dischargeSatV3_forces,
  early_discharge_unsat,
  cursor_not_advanced_unsat,
  wrong_amount_unsat
]

end Dregg2.Deos.DischargeSatDescriptor
