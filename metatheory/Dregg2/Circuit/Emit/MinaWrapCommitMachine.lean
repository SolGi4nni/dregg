/-
# `Dregg2.Circuit.Emit.MinaWrapCommitMachine` — the machine the COMMITMENT-COMBINATION stages of
Kimchi's `verify` need, and the three things `MinaWrapVerifierProgram`'s machine could not say.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every column index, every gate expression, every window leg, the ROM
manifest and the emitted descriptor are authored here and go through `EffectLower.lowerAir` of an
`EffectAirIR.EffectAir`; `mainRailOk = true` holds by `rfl`. There is no hand-written
`VmConstraint2` anywhere in this file. Rust PROVES the artifact and authors no constraint.
House Law #1.

## WHY A SECOND MACHINE AND NOT AN EDIT

`MinaWrapVerifierProgram`'s machine is the Fq sponge's machine and a sibling lane is building the
Poseidon round on it. This file takes the separate module the coordination requires, and the three
changes below are each forced by a DEPLOYED CAP or by an operation the commitment stages need —
none is taste.

  1. ⚑ **THE ROM ENCODES OPERAND INDICES, NOT ONE-HOT VECTORS.** The program machine spends
     `3 · NREG` manifest cells on one-hot operand selectors, so its instruction word is
     `1 + 4 + 3·NREG + 32` and the deployed `MAX_EXACT_PUBLIC_ARITY = 64`
     (`circuit/src/descriptor_ir2.rs`) caps it at `NREG = 9`. A chord-and-tangent addition needs
     twelve live values (§5), so the one-hot word is not merely wasteful, it is **REFUSED**:
     `one_hot_word_is_refused_at_this_register_count` is that as a `decide`. The index word is
     `1 + 3 + 3 + 1 + 32 = 40` cells and is **independent of `NREG`**, which is what makes the
     register file a free parameter rather than the thing the arity cap decides.
     The one-hot columns stay in the TRACE; three gates (`booleanity`, `Σ sel = 1`,
     `Σ r·sel_r = idx`) tie them to the ROM's index, and `oneHot_is_forced_by_the_index` proves the
     vector is determined — so nothing is weakened, only re-encoded.
  2. ⚑ **AN ASSERT-ZERO BIT.** `ZCHK · z_i = 0` on every limb. This is the primitive the program
     machine had no form of: a way for the DESCRIPTOR to demand that a computed value be a
     particular one. Without it a witnessed slope can be introduced but never CHECKED, and a
     witnessed slope that is never checked is the "MSM over free scalars" this campaign has already
     shipped once.
  3. ⚑ **A FREE OPERAND CODE.** `xr = NREG` and `yr = NREG+1` turn the corresponding routing gate
     off, so the operand is an unrouted (but still limb-range-checked) trace block — a WITNESS.
     Division is not an ALU operation and never will be; `s = (y₁−y₂)/(x₁−x₂)` enters as a witness
     and is pinned by (2). ⚠ The free code is ROM-pinned like every other field of the instruction,
     so it is the DESCRIPTOR that says where a witness may enter, not the prover.

And one deletion, because a no-op kept for symmetry is worse than one that does something:
**`SEL_CHAIN` is pinned to `0` by a gate and the 32 chain window legs are gone.** The register file
superseded the single chain edge in `MinaWrapVerifierProgram` and the program machine carried the
legs anyway, satisfied vacuously on every row it ever emitted.

## WHAT ONE ROW OF THIS MACHINE IS

`MinaWrapVerifierAir`'s Pasta ALU row, columns `0..225`, **unmoved** — so `alu_mul_forces`,
`alu_add_forces` and `alu_sub_forces` are statements about THIS row (`commit_reuses_the_alu_layout`)
and the sound-arithmetic floor is inherited rather than re-derived. Everything else is appended.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. Facts are NAMED THEOREMS — this file adds zero `#guard`s.
-/
import Dregg2.Circuit.Emit.MinaWrapVerifierAir
import Dregg2.Circuit.GateExpr

namespace Dregg2.Circuit.Emit.MinaWrapCommitMachine

open Dregg2.Circuit (Assignment Expr Constraint ConstraintSystem)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 TableDef TableId mainTableDef VmConstraint2 WindowExpr RowSemantics)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg WindowLeg LookupLeg PiPinLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.EffectLower (lowerAir P)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaFieldSound
open Dregg2.Circuit.Emit.PastaAddSubSound
open Dregg2.Circuit.Emit.MinaWrapVerifierAir

set_option autoImplicit false
set_option maxRecDepth 400000

/-! ## §1 — THE ROW.

⚑ **COLUMNS `0..225` DO NOT MOVE.** -/

/-- The register count. **Twelve is the chord-and-tangent addition's peak liveness** (§5): the
running total `(Xᵀ, Yᵀ)`, the ladder accumulator `(X, Y)`, the constant zero, the digit bit, the
witnessed slope, the two result coordinates and three temporaries. Eleven deadlocks the select;
thirteen buys nothing this file needs. -/
def NREG : Nat := 12

/-- The register file: `NREG` blocks of `SK` limb columns. -/
def REG_BASE : Nat := ALU_WIDTH

/-- The base column of register `r`. -/
def regCol (r : Nat) : Nat := REG_BASE + r * SK

/-- `XSEL` — one-hot over `NREG + 1` positions; position `NREG` is **FREE** (an unrouted witness). -/
def XSEL_BASE : Nat := REG_BASE + NREG * SK
/-- `YSEL` — one-hot over `NREG + 2`; `NREG` is the IMMEDIATE, `NREG + 1` is **FREE**. -/
def YSEL_BASE : Nat := XSEL_BASE + (NREG + 1)
/-- `WSEL` — one-hot over `NREG + 1`; position `NREG` is "write nothing". -/
def WSEL_BASE : Nat := YSEL_BASE + (NREG + 2)
/-- The ROM's `x` operand index, decoded into `XSEL` by §3. -/
def XIDX_COL : Nat := WSEL_BASE + (NREG + 1)
def YIDX_COL : Nat := XIDX_COL + 1
def WIDX_COL : Nat := XIDX_COL + 2
/-- The program counter. -/
def PC_COL : Nat := XIDX_COL + 3
/-- ⚑ The ASSERT-ZERO bit. ROM-pinned, so it is the descriptor that demands the check. -/
def ZCHK_COL : Nat := XIDX_COL + 4
/-- The instruction's IMMEDIATE, `SK` limbs, ROM-pinned. -/
def IMM_BASE : Nat := XIDX_COL + 5

/-- `226 + 12·32 + 13 + 14 + 13 + 5 + 32 = 687` declared main columns. -/
def CM_WIDTH : Nat := IMM_BASE + SK

theorem REG_BASE_eq : REG_BASE = 226 := rfl
theorem XSEL_BASE_eq : XSEL_BASE = 610 := rfl
theorem YSEL_BASE_eq : YSEL_BASE = 623 := rfl
theorem WSEL_BASE_eq : WSEL_BASE = 637 := rfl
theorem XIDX_COL_eq : XIDX_COL = 650 := rfl
theorem PC_COL_eq : PC_COL = 653 := rfl
theorem ZCHK_COL_eq : ZCHK_COL = 654 := rfl
theorem IMM_BASE_eq : IMM_BASE = 655 := rfl
theorem CM_WIDTH_eq : CM_WIDTH = 687 := rfl

/-- ⚑ **THE ARITHMETIC BLOCK IS UNMOVED**, so `MinaWrapVerifierAir`'s three forcing theorems are
statements about this row. An edit that shifted any operand base would break this `rfl` rather than
silently make the inherited soundness a claim about different columns. -/
theorem commit_reuses_the_alu_layout :
    (X_BASE, Y_BASE, Z_BASE, ALU_Q_BASE, ALU_C_BASE, SEL_MUL, SEL_ADD, SEL_SUB, SEL_CHAIN)
      = (0, 32, 64, 96, 128, 222, 223, 224, 225) := rfl

theorem register_file_starts_after_the_alu_row : REG_BASE = ALU_WIDTH := rfl

/-! ## §2 — EXPRESSION HELPERS. -/

def esub (a b : Expr) : Expr := .add a (.mul (.const (-1)) b)
def esum (l : List Expr) : Expr := l.foldl Expr.add (.const 0)

theorem esub_eval (a : Assignment) (u v : Expr) : (esub u v).eval a = u.eval a - v.eval a := by
  unfold esub; simp only [Expr.eval]; ring

/-! ## §3 — THE INSTRUCTION WORD, and why it is indices.

⚑ The deployed exact-public arity cap is the thing that decides this, so it is a `decide` and not a
sentence. -/

/-- The deployed cap (`circuit/src/descriptor_ir2.rs`, `MAX_EXACT_PUBLIC_ARITY`). -/
def MAX_ARITY : Nat := 64
/-- The deployed CELL cap on an exact-public manifest. -/
def MAX_ROM_CELLS : Nat := 2 ^ 25
/-- The deployed ROW cap. -/
def MAX_ROM_ROWS : Nat := 2 ^ 21

/-- The index-encoded instruction word: `pc+1` · 3 opcode selectors · `xr` · `yr` · `wr` · `zchk` ·
`SK` immediate limbs. -/
def ROM_ARITY : Nat := 1 + 3 + 3 + 1 + SK

theorem ROM_ARITY_eq : ROM_ARITY = 40 := rfl

/-- `MinaWrapVerifierProgram`'s one-hot word at this register count. -/
def ONEHOT_ARITY : Nat := 1 + 4 + 3 * NREG + SK

/-- ⚑ **THE ONE-HOT WORD IS REFUSED AT TWELVE REGISTERS, AND THE INDEX WORD FITS AT ANY.** `73 > 64`
against `40 ≤ 64`, and the largest register file a one-hot word admits is **nine** — two short of
the chord-and-tangent addition's twelve. This is why the encoding changed. -/
theorem one_hot_word_is_refused_at_this_register_count :
    ONEHOT_ARITY = 73 ∧ MAX_ARITY < ONEHOT_ARITY ∧ ROM_ARITY ≤ MAX_ARITY
      ∧ (1 + 4 + 3 * 9 + SK) = MAX_ARITY ∧ MAX_ARITY < (1 + 4 + 3 * 10 + SK) := by decide

/-- ⚑ **THE INDEX WORD'S ARITY DOES NOT DEPEND ON `NREG`, AND THE ONE-HOT WORD DOES** — stated as
a comparison of the two WORD FUNCTIONS at varying register counts, which is the property that
matters. ⚠ An earlier draft of this stated `(1+3+3+1+SK) = ROM_ARITY` with `nr` free: that is
`X = X` under a name it did not earn, and `#assert_axioms` cannot see the difference. -/
def oneHotWord (nr : Nat) : Nat := 1 + 4 + 3 * nr + SK
def indexWord (_nr : Nat) : Nat := 1 + 3 + 3 + 1 + SK

theorem index_word_is_register_count_independent :
    (∀ nr, indexWord nr = ROM_ARITY)
      ∧ oneHotWord 9 = MAX_ARITY ∧ MAX_ARITY < oneHotWord 10
      ∧ oneHotWord 12 ≠ oneHotWord 9 := by
  refine ⟨fun nr => rfl, by decide, by decide, by decide⟩

/-- ⚑ **THE LONGEST PROGRAM ONE INSTANCE CAN HOLD IS 838 860 INSTRUCTIONS** at this word, against
`MinaWrapVerifierProgram`'s 610 080 — the narrower word buys **1.37×**, and it is still the CELL cap
that binds, not the row cap. -/
theorem rom_capacity :
    MAX_ROM_CELLS / ROM_ARITY = 838860
      ∧ MAX_ROM_CELLS / ROM_ARITY < MAX_ROM_ROWS := by decide

/-! ## §4 — THE GATES. -/

/-- The `x`-routing gate at limb `i`: `Σ_{r<NREG} XSELᵣ · (x_i − REGᵣ_i)`. The FREE position
`XSEL_{NREG}` appears in NO term, so an instruction that selects it routes nothing. -/
def xRouteExpr (i : Nat) : Expr :=
  esum ((List.range NREG).map
    (fun r => Expr.mul (.var (XSEL_BASE + r)) (esub (.var (X_BASE + i)) (.var (regCol r + i)))))

/-- The `y`-routing gate at limb `i`: the register terms plus the IMMEDIATE term at position
`NREG`. The FREE position `NREG + 1` appears in no term. -/
def yRouteExpr (i : Nat) : Expr :=
  .add
    (esum ((List.range NREG).map
      (fun r => Expr.mul (.var (YSEL_BASE + r)) (esub (.var (Y_BASE + i)) (.var (regCol r + i))))))
    (.mul (.var (YSEL_BASE + NREG)) (esub (.var (Y_BASE + i)) (.var (IMM_BASE + i))))

def xRouteBody (a : Assignment) (i : Nat) : ℤ :=
  ((List.range NREG).map (fun r => a (XSEL_BASE + r) * (a (X_BASE + i) - a (regCol r + i)))).sum

def yRouteBody (a : Assignment) (i : Nat) : ℤ :=
  ((List.range NREG).map (fun r => a (YSEL_BASE + r) * (a (Y_BASE + i) - a (regCol r + i)))).sum
    + a (YSEL_BASE + NREG) * (a (Y_BASE + i) - a (IMM_BASE + i))

theorem range_NREG : List.range NREG = [0,1,2,3,4,5,6,7,8,9,10,11] := rfl

theorem xRouteExpr_eval (a : Assignment) (i : Nat) : (xRouteExpr i).eval a = xRouteBody a i := by
  unfold xRouteExpr xRouteBody esum
  simp [range_NREG, Expr.eval, esub]
  ring

theorem yRouteExpr_eval (a : Assignment) (i : Nat) : (yRouteExpr i).eval a = yRouteBody a i := by
  unfold yRouteExpr yRouteBody esum
  simp [range_NREG, Expr.eval, esub]
  ring

/-- `s · (s − 1)` — booleanity. -/
def cboolExpr (sel : Nat) : Expr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toSource
    (Dregg2.Circuit.GateExpr.gBool (.leaf sel))

theorem cboolExpr_eq (sel : Nat) :
    cboolExpr sel = .mul (.var sel) (.add (.var sel) (.const (-1))) := rfl

/-- `Σ_{k<n} sel_{base+k} − 1` — exactly one position on. -/
def selSumExpr (base n : Nat) : Expr :=
  .add (esum ((List.range n).map (fun k => Expr.var (base + k)))) (.const (-1))

/-- ⚑ **THE DECODE GATE**: `Σ_{k<n} k · sel_{base+k} − idx`. Degree **1**. With booleanity and the
sum gate this is what makes the ROM's INDEX and the trace's one-hot vector the same thing. -/
def decodeExpr (base n idxCol : Nat) : Expr :=
  .add (esum ((List.range n).map
          (fun k : Nat => Expr.mul (Expr.const (k : ℤ)) (Expr.var (base + k)))))
       (.mul (.const (-1)) (.var idxCol))

/-- ⚑ **THE ASSERT-ZERO GATE at limb `i`**: `ZCHK · z_i`. Degree **2**. -/
def zchkExpr (i : Nat) : Expr := .mul (.var ZCHK_COL) (.var (Z_BASE + i))

/-- The register-file window leg for register `r`, limb `i`. ONE leg, not a write leg and a hold
leg, so no assignment leaves the next row's register free.

⚑ **RE-EMIT**: was the expensive mux form (`WSEL·z + (1−WSEL)·reg`, 3 multiplications); this is
`nxt(reg) − gMux(WSEL, reg, z)` (`Dregg2.Circuit.GateExpr`'s form B, 2 multiplications) — the SAME
polynomial, one fewer multiplication. Also collapses the byte-identical cross-file duplicate in
`MinaWrapVerifierProgram.regWindowExpr` onto the same shared shape. -/
def regWindowExpr (r i : Nat) : WindowExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gEsub Dregg2.Circuit.GateExpr.idOps
      (.leaf (Dregg2.Circuit.GateExpr.WLeaf.nxt (regCol r + i)))
      (Dregg2.Circuit.GateExpr.gMux (.leaf (Dregg2.Circuit.GateExpr.WLeaf.loc (WSEL_BASE + r)))
        (.leaf (Dregg2.Circuit.GateExpr.WLeaf.loc (regCol r + i)))
        (.leaf (Dregg2.Circuit.GateExpr.WLeaf.loc (Z_BASE + i)))))

def regBody (cur nxt : Assignment) (r i : Nat) : ℤ :=
  nxt (regCol r + i) - (cur (WSEL_BASE + r) * cur (Z_BASE + i)
    + (1 - cur (WSEL_BASE + r)) * cur (regCol r + i))

def pcStartExpr : WindowExpr := .loc PC_COL
def pcThreadExpr : WindowExpr :=
  .add (.nxt PC_COL) (.mul (.const (-1)) (.add (.loc PC_COL) (.const 1)))
def pcBody (cur nxt : Assignment) : ℤ := nxt PC_COL - (cur PC_COL + 1)

/-! ## §5 — WHAT A ROW FORCES. -/

/-- ⚑ **A ROW'S `x` OPERAND IS THE REGISTER ITS INSTRUCTION NAMES.** -/
theorem xRoute_forces_operand (a : Assignment) (i r : Nat) (hr : r < NREG)
    (hsel : ∀ s, s < NREG → a (XSEL_BASE + s) = (if s = r then 1 else 0))
    (h : P ∣ xRouteBody a i) :
    a (X_BASE + i) ≡ a (regCol r + i) [ZMOD P] := by
  have hsum : xRouteBody a i = a (X_BASE + i) - a (regCol r + i) := by
    unfold xRouteBody
    rw [range_NREG]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hsel 0 (by decide), hsel 1 (by decide), hsel 2 (by decide), hsel 3 (by decide),
        hsel 4 (by decide), hsel 5 (by decide), hsel 6 (by decide), hsel 7 (by decide),
        hsel 8 (by decide), hsel 9 (by decide), hsel 10 (by decide), hsel 11 (by decide)]
    have hr12 : r < 12 := hr
    interval_cases r <;> norm_num
  rw [hsum] at h
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h))

/-- ⚑ **AN IMMEDIATE INSTRUCTION'S `y` IS THE ROM's CONSTANT.** -/
theorem yRoute_forces_immediate (a : Assignment) (i : Nat)
    (hreg : ∀ s, s < NREG → a (YSEL_BASE + s) = 0)
    (himm : a (YSEL_BASE + NREG) = 1)
    (h : P ∣ yRouteBody a i) :
    a (Y_BASE + i) ≡ a (IMM_BASE + i) [ZMOD P] := by
  have hsum : yRouteBody a i = a (Y_BASE + i) - a (IMM_BASE + i) := by
    unfold yRouteBody
    rw [range_NREG]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hreg 0 (by decide), hreg 1 (by decide), hreg 2 (by decide), hreg 3 (by decide),
        hreg 4 (by decide), hreg 5 (by decide), hreg 6 (by decide), hreg 7 (by decide),
        hreg 8 (by decide), hreg 9 (by decide), hreg 10 (by decide), hreg 11 (by decide), himm]
    ring
  rw [hsum] at h
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h))

/-- …and a REGISTER instruction's `y` is that register. -/
theorem yRoute_forces_register (a : Assignment) (i r : Nat) (hr : r < NREG)
    (hsel : ∀ s, s < NREG → a (YSEL_BASE + s) = (if s = r then 1 else 0))
    (himm : a (YSEL_BASE + NREG) = 0)
    (h : P ∣ yRouteBody a i) :
    a (Y_BASE + i) ≡ a (regCol r + i) [ZMOD P] := by
  have hsum : yRouteBody a i = a (Y_BASE + i) - a (regCol r + i) := by
    unfold yRouteBody
    rw [range_NREG]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hsel 0 (by decide), hsel 1 (by decide), hsel 2 (by decide), hsel 3 (by decide),
        hsel 4 (by decide), hsel 5 (by decide), hsel 6 (by decide), hsel 7 (by decide),
        hsel 8 (by decide), hsel 9 (by decide), hsel 10 (by decide), hsel 11 (by decide), himm]
    have hr12 : r < 12 := hr
    interval_cases r <;> norm_num
  rw [hsum] at h
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h))

/-- ⚑ **AND THE FREE CODE ROUTES NOTHING — as a theorem, because it is the hole this file
deliberately opens.** With every routed `YSEL` off (the FREE position on), the `y` gate body is
`0` on EVERY assignment: the operand block is an unrouted witness. It is still limb-range-checked,
so it is a value in `[0, 2^256)`; it is not related to any register, to the immediate, or to
anything else. ⚠ Read this next to `zchk_forces_congruence`: a witness introduced here and never
zchk-checked is UNCONSTRAINED, and every use of the free code in this cone is followed, in the
descriptor's own ROM, by the multiply and the assert that pin it. -/
theorem free_y_routes_nothing (a : Assignment) (i : Nat)
    (hreg : ∀ s, s < NREG → a (YSEL_BASE + s) = 0)
    (himm : a (YSEL_BASE + NREG) = 0) :
    yRouteBody a i = 0 := by
  unfold yRouteBody
  rw [range_NREG]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [hreg 0 (by decide), hreg 1 (by decide), hreg 2 (by decide), hreg 3 (by decide),
      hreg 4 (by decide), hreg 5 (by decide), hreg 6 (by decide), hreg 7 (by decide),
      hreg 8 (by decide), hreg 9 (by decide), hreg 10 (by decide), hreg 11 (by decide), himm]
  ring

/-- ⚑ **THE DECODE FORCES THE ONE-HOT VECTOR FROM THE ROM's INDEX.** Booleanity makes each selector
a bit, the sum gate makes exactly one of them set, and the weighted sum names WHICH. So the index
word says everything the one-hot word said — that is the content of the re-encoding, and it is a
theorem rather than an assurance. -/
theorem bits_sum_zero (sel : Nat → ℤ) : ∀ (l : List Nat),
    (∀ k ∈ l, sel k = 0 ∨ sel k = 1) → (l.map sel).sum = 0 → ∀ k ∈ l, sel k = 0 := by
  intro l
  induction l with
  | nil => intro _ _ k hk; cases hk
  | cons x xs ih =>
    intro hb hs
    simp only [List.map_cons, List.sum_cons] at hs
    have hrest : ∀ k ∈ xs, sel k = 0 ∨ sel k = 1 := fun k hk => hb k (List.mem_cons_of_mem _ hk)
    have hnn : 0 ≤ (xs.map sel).sum := by
      refine List.sum_nonneg ?_
      intro v hv
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
      rcases hrest k hk with h | h <;> rw [h] <;> norm_num
    have hx0 : sel x = 0 := by
      rcases hb x (List.mem_cons_self ..) with h | h
      · exact h
      · rw [h] at hs; linarith
    have hxs : (xs.map sel).sum = 0 := by rw [hx0] at hs; linarith
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk'
    · exact hx0
    · exact ih hrest hxs k hk'

/-- ⚑ **BOOLEANITY PLUS `Σ sel = 1` IS "EXACTLY ONE".** Over ℤ, and stated for a general list, so
the three decode gates below are three instances of one proved fact rather than three copies. -/
theorem bits_sum_one (sel : Nat → ℤ) : ∀ (l : List Nat), l.Nodup →
    (∀ k ∈ l, sel k = 0 ∨ sel k = 1) → (l.map sel).sum = 1 →
    ∃ k ∈ l, sel k = 1 ∧ ∀ j ∈ l, j ≠ k → sel j = 0 := by
  intro l
  induction l with
  | nil => intro _ _ hs; simp at hs
  | cons x xs ih =>
    intro hnd hb hs
    simp only [List.map_cons, List.sum_cons] at hs
    have hrest : ∀ k ∈ xs, sel k = 0 ∨ sel k = 1 := fun k hk => hb k (List.mem_cons_of_mem _ hk)
    have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
    have hxnm : x ∉ xs := (List.nodup_cons.mp hnd).1
    rcases hb x (List.mem_cons_self ..) with hx | hx
    · -- x is off; recurse into the tail
      have hxs : (xs.map sel).sum = 1 := by rw [hx] at hs; linarith
      obtain ⟨k, hk, hk1, hk0⟩ := ih hnd' hrest hxs
      refine ⟨k, List.mem_cons_of_mem _ hk, hk1, ?_⟩
      intro j hj hjk
      rcases List.mem_cons.mp hj with rfl | hj'
      · exact hx
      · exact hk0 j hj' hjk
    · -- x is on; the tail sums to zero, so every tail bit is off
      have hxs : (xs.map sel).sum = 0 := by rw [hx] at hs; linarith
      have hall := bits_sum_zero sel xs hrest hxs
      refine ⟨x, List.mem_cons_self .., hx, ?_⟩
      intro j hj hjx
      rcases List.mem_cons.mp hj with rfl | hj'
      · exact absurd rfl hjx
      · exact hall j hj'

/-- The sum of a one-hot-weighted list over a duplicate-free carrier is the weight. -/
theorem sum_map_ite (c : ℤ) (k0 : Nat) : ∀ (l : List Nat), l.Nodup → k0 ∈ l →
    (l.map (fun k : Nat => if k = k0 then c else 0)).sum = c := by
  intro l
  induction l with
  | nil => intro _ hm; cases hm
  | cons z zs ih =>
    intro hnd hm
    simp only [List.map_cons, List.sum_cons]
    have hzn : z ∉ zs := (List.nodup_cons.mp hnd).1
    rcases List.mem_cons.mp hm with rfl | hm'
    · have hz : ∀ w ∈ zs, (if w = k0 then c else 0) = 0 := by
        intro w hw'
        have : w ≠ k0 := ne_of_mem_of_not_mem hw' hzn
        simp [this]
      rw [if_pos rfl, List.map_congr_left hz]
      simp
    · have hzne : z ≠ k0 := by rintro rfl; exact hzn hm'
      rw [if_neg hzne, zero_add]
      exact ih (List.nodup_cons.mp hnd).2 hm'

/-- ⚑ **THE DECODE FORCES THE ONE-HOT VECTOR FROM THE ROM's INDEX.** Booleanity makes each selector
a bit, the sum gate makes exactly one of them set, and the weighted sum names WHICH. So the index
word says everything the one-hot word said — the content of the re-encoding, as a theorem rather
than an assurance. -/
theorem oneHot_is_forced_by_the_index (n idx : Nat) (sel : Nat → ℤ)
    (hbool : ∀ k, k < n → sel k = 0 ∨ sel k = 1)
    (hsum : ((List.range n).map sel).sum = 1)
    (hdec : ((List.range n).map (fun k : Nat => (k : ℤ) * sel k)).sum = (idx : ℤ))
    (hidx : idx < n) :
    ∀ k, k < n → sel k = (if k = idx then 1 else 0) := by
  have hb' : ∀ k ∈ List.range n, sel k = 0 ∨ sel k = 1 :=
    fun k hk => hbool k (List.mem_range.mp hk)
  obtain ⟨k0, hk0mem, hk0one, hk0rest⟩ :=
    bits_sum_one sel (List.range n) (List.nodup_range) hb' hsum
  have hk0n : k0 < n := List.mem_range.mp hk0mem
  have hw : ((List.range n).map (fun k : Nat => (k : ℤ) * sel k)).sum = (k0 : ℤ) := by
    have hcong : ∀ k ∈ List.range n,
        (k : ℤ) * sel k = (if k = k0 then (k0 : ℤ) else 0) := by
      intro k hk
      rcases eq_or_ne k k0 with rfl | hne
      · simp [hk0one]
      · simp [hne, hk0rest k hk hne]
    rw [List.map_congr_left hcong]
    exact sum_map_ite (k0 : ℤ) k0 (List.range n) List.nodup_range hk0mem
  have hk0 : k0 = idx := by
    have h := hw.symm.trans hdec
    exact_mod_cast h
  subst hk0
  intro k hk
  rcases eq_or_ne k k0 with rfl | hne
  · simp [hk0one]
  · simp [hne, hk0rest k (List.mem_range.mpr hk) hne]

/-- ⚑ **THE ASSERT-ZERO BIT MAKES A COMPUTED VALUE EQUAL A DEMANDED ONE.** With `ZCHK = 1` the
deployed reading `P ∣ ZCHK · z_i` forces every result limb `≡ 0`; both are 8-bit range-checked, so
they are `0` as integers, so the row's recomposed result is `0` and the row's own operation gate
then says `x ⊙ y ≡ 0 (mod pasta)`.

This is the primitive that turns *"the trace contains a value that happens to satisfy the slope
relation"* into *"the descriptor DEMANDS the slope relation"*. -/
theorem zchk_forces_zero_limbs (a : Assignment) (i : Nat) (hz : a ZCHK_COL = 1)
    (h : P ∣ (zchkExpr i).eval a)
    (hr : 0 ≤ a (Z_BASE + i) ∧ a (Z_BASE + i) < 2 ^ SB) :
    a (Z_BASE + i) = 0 := by
  have hb : (2 : ℤ) ^ SB ≤ P := by norm_num [SB, Dregg2.Circuit.Emit.EffectLower.P]
  have hbody : (zchkExpr i).eval a = a (Z_BASE + i) := by
    unfold zchkExpr; simp only [Expr.eval, hz]; ring
  rw [hbody] at h
  have h0 : a (Z_BASE + i) ≡ 0 [ZMOD P] := Int.modEq_zero_iff_dvd.mpr h
  exact Dregg2.Circuit.Emit.EffectLower.eq_of_modEq_canon hr.1 (lt_of_lt_of_le hr.2 hb)
    (by norm_num) (by norm_num [Dregg2.Circuit.Emit.EffectLower.P]) h0

/-- ⚑ **AND THE SUB ROW WITH THE BIT SET IS AN EQUALITY ASSERTION.** `SUB x, y → ∅` with
`ZCHK = 1` forces `x ≡ y (mod p)` over the Pasta prime, which is the shape every check in §6 takes.
The step from `alu_sub_forces` is one line, and it is the reason the bit is worth a column. -/
theorem zchk_sub_forces_equality (a : Assignment) (hsel : a SEL_SUB = 1) (hz : a ZCHK_COL = 1)
    (hx : ∀ i, i < SK → 0 ≤ a (X_BASE + i) ∧ a (X_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (Y_BASE + i) ∧ a (Y_BASE + i) < 2 ^ SB)
    (hzr : ∀ i, i < SK → 0 ≤ a (Z_BASE + i) ∧ a (Z_BASE + i) < 2 ^ SB)
    (hcb : 0 ≤ a ALU_AC_COL ∧ a ALU_AC_COL < 2)
    (hc : ∀ i, i < NA - 1 → 0 ≤ a (ALU_ACAR_BASE + i) ∧ a (ALU_ACAR_BASE + i) < 2 ^ ACB)
    (hgates : ∀ m, m < NA → P ∣ (aluAddSubExpr SEL_SUB pLimb (-1) 1 m).eval a)
    (hzchk : ∀ i, i < SK → P ∣ (zchkExpr i).eval a) :
    (pN : ℤ) ∣ (sVal a X_BASE - sVal a Y_BASE) := by
  have hsub := alu_sub_forces a hsel hx hy hzr hcb hc hgates
  have hzero : sVal a Z_BASE = 0 := by
    unfold sVal sumL
    have hc : ∀ i ∈ List.range SK, ((2 : ℤ) ^ SB) ^ i * a (Z_BASE + i) = 0 := by
      intro i hi
      rw [zchk_forces_zero_limbs a i hz (hzchk i (List.mem_range.mp hi))
        (hzr i (List.mem_range.mp hi))]
      ring
    rw [List.map_congr_left hc]
    simp
  rw [hzero, sub_zero] at hsub
  exact hsub

/-- ⚑ **THE WRITTEN REGISTER TAKES THIS ROW'S RESULT.** -/
theorem reg_write_forces_result (cur nxt : Assignment) (r i : Nat)
    (hw : cur (WSEL_BASE + r) = 1) (h : P ∣ regBody cur nxt r i) :
    nxt (regCol r + i) ≡ cur (Z_BASE + i) [ZMOD P] := by
  unfold regBody at h
  rw [hw] at h
  have h' : P ∣ nxt (regCol r + i) - cur (Z_BASE + i) := by
    have : nxt (regCol r + i) - (1 * cur (Z_BASE + i) + (1 - 1) * cur (regCol r + i))
        = nxt (regCol r + i) - cur (Z_BASE + i) := by ring
    rwa [this] at h
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h'))

/-- ⚑ **AND EVERY OTHER REGISTER IS PRESERVED.** -/
theorem reg_hold_forces_preservation (cur nxt : Assignment) (r i : Nat)
    (hw : cur (WSEL_BASE + r) = 0) (h : P ∣ regBody cur nxt r i) :
    nxt (regCol r + i) ≡ cur (regCol r + i) [ZMOD P] := by
  unfold regBody at h
  rw [hw] at h
  have h' : P ∣ nxt (regCol r + i) - cur (regCol r + i) := by
    have : nxt (regCol r + i) - (0 * cur (Z_BASE + i) + (1 - 0) * cur (regCol r + i))
        = nxt (regCol r + i) - cur (regCol r + i) := by ring
    rwa [this] at h
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h'))

/-- ⚑ **AND THE THIRD OPTION DOES NOT EXIST.** -/
theorem reg_window_leaves_nothing_free (cur nxt : Assignment) (r i : Nat)
    (h : P ∣ regBody cur nxt r i) :
    nxt (regCol r + i)
      ≡ cur (WSEL_BASE + r) * cur (Z_BASE + i)
        + (1 - cur (WSEL_BASE + r)) * cur (regCol r + i) [ZMOD P] := by
  unfold regBody at h
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h))

/-- ⚑ **THE COUNTER THREADS**, which is what makes the manifest key of row `j` predictable and so
unique — the pc thread fixes the ORDER of the instructions, the ROM permutation fixes WHICH. -/
theorem pc_thread_forces_successor (cur nxt : Assignment) (h : P ∣ pcBody cur nxt) :
    nxt PC_COL ≡ cur PC_COL + 1 [ZMOD P] := by
  unfold pcBody at h
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h))

/-! ## §6 — THE INSTRUCTION AND ITS MANIFEST. -/

/-- The ROM's table id. `.custom 100` ⇒ clear of `rangeTidW` (`.custom (64+bits)`, `bits ≤ 29`,
so at most `.custom 93`) and of `MinaWrapVerifierProgram`'s `.custom 96`. -/
def ROM_TID : TableId := .custom 100

/-- One instruction.

* `op` — `1` multiply · `2` add · `3` sub. There is NO nop: `selSumExpr` is inherited unchanged, so
  a padding row is a real ALU operation.
* `xr` — `< NREG` a register, `= NREG` the FREE witness block.
* `yr` — `< NREG` a register, `= NREG` the immediate, `= NREG+1` the FREE witness block.
* `wr` — `< NREG` a destination, `= NREG` write nothing.
* `zc` — `1` to demand the result be zero.
* `imm` — a canonical Pasta field element; ignored unless `yr = NREG`. -/
structure Instr where
  op  : Nat
  xr  : Nat
  yr  : Nat
  wr  : Nat
  zc  : Nat
  imm : Nat
  deriving Repr, DecidableEq

def limbNat (v i : Nat) : Nat := (v / 2 ^ (SB * i)) % 2 ^ SB

theorem manifest_limb_agrees_with_trace (v i : Nat) : (limbNat v i : ℤ) = limbAt v i := rfl

/-- The manifest row for instruction `I` at program counter `pc`. -/
def romRow (pc : Nat) (I : Instr) : List Nat :=
  (pc + 1)
    :: (if I.op = 1 then 1 else 0) :: (if I.op = 2 then 1 else 0) :: (if I.op = 3 then 1 else 0)
    :: I.xr :: I.yr :: I.wr :: I.zc
    :: (List.range SK).map (fun i => limbNat I.imm i)

def PAD : Instr := ⟨2, 0, NREG, NREG, 0, 0⟩

/-- The ROM: one manifest row per instruction, in program order. -/
def romRows (prog : List Instr) : List (List Nat) :=
  (List.range prog.length).map (fun j => romRow j (prog.getD j PAD))

theorem romRow_length (pc : Nat) (I : Instr) : (romRow pc I).length = ROM_ARITY := by
  unfold romRow ROM_ARITY
  simp [SK]

/-- ⚑ **THE MANIFEST KEY IS THE PROGRAM COUNTER, IT IS UNIQUE, AND IT IS NEVER ZERO.** A permutation
plus an injective key is a POINTWISE identification of trace row `j` with instruction `j`; without
key uniqueness the permutation would only say the MULTISET of instructions is right. -/
theorem romRow_head (pc : Nat) (I : Instr) : (romRow pc I).head? = some (pc + 1) := rfl

theorem romRow_key_injective (pc pc' : Nat) (I I' : Instr)
    (h : (romRow pc I).head? = (romRow pc' I').head?) : pc = pc' := by
  rw [romRow_head, romRow_head] at h
  simpa using h

theorem romRow_key_nonzero (pc : Nat) (I : Instr) : (romRow pc I).head? ≠ some 0 := by
  rw [romRow_head]; simp

/-- ⚑ **EVERY MANIFEST CELL IS A CANONICAL BabyBear FELT.** The deployed table walk refuses a
non-canonical representative and the Lean type is `Nat` — unbounded — so this obligation is the
emitter's. -/
theorem romRow_cells_canonical (pc : Nat) (I : Instr) (hpc : pc + 1 < 2013265921)
    (hx : I.xr ≤ NREG) (hy : I.yr ≤ NREG + 1) (hw : I.wr ≤ NREG) (hz : I.zc ≤ 1) :
    ∀ v ∈ romRow pc I, v < 2013265921 := by
  have hlimb : ∀ (v j : Nat), limbNat v j < 2013265921 := by
    intro v j
    have h1 : limbNat v j < 2 ^ SB := Nat.mod_lt _ (by positivity)
    have h2 : (2 : Nat) ^ SB = 256 := rfl
    omega
  have hnr : NREG = 12 := rfl
  intro v hv
  unfold romRow at hv
  simp only [List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h | h | h | h | h | h
  · omega
  · subst h; split <;> omega
  · subst h; split <;> omega
  · subst h; split <;> omega
  · subst h; omega
  · subst h; omega
  · subst h; omega
  · subst h; omega
  · obtain ⟨j, _, hj⟩ := h; subst hj; exact hlimb _ _

theorem romRow_canonicality_bound_is_P : (2013265921 : Nat) = P := rfl

/-- The queried tuple, read off the row's own cells. -/
def romTuple : List Expr :=
  (Expr.add (.var PC_COL) (.const 1))
    :: .var SEL_MUL :: .var SEL_ADD :: .var SEL_SUB
    :: .var XIDX_COL :: .var YIDX_COL :: .var WIDX_COL :: .var ZCHK_COL
    :: (List.range SK).map (fun i => Expr.var (IMM_BASE + i))

/-- ⚑ **THE EMITTED TUPLE HAS THE DECLARED ARITY.** The deployed parser refuses a mismatch and
NOTHING in `EffectAirIR`'s `mainRailOk` checks it — so the check lives here or it lives nowhere
until a Rust parse. -/
theorem romTuple_length : romTuple.length = ROM_ARITY := by decide

/-! ## §7 — THE AIR. -/

def regWindowLegs : List AirLeg :=
  ((List.range NREG).flatMap (fun r =>
    (List.range SK).map (fun i => AirLeg.window ⟨RowSel.transition, regWindowExpr r i⟩)))

def selBoolLegs : List AirLeg :=
  ((List.range (NREG + 1)).map (fun r => AirLeg.gate ⟨cboolExpr (XSEL_BASE + r), .const 0⟩))
  ++ ((List.range (NREG + 2)).map (fun r => AirLeg.gate ⟨cboolExpr (YSEL_BASE + r), .const 0⟩))
  ++ ((List.range (NREG + 1)).map (fun r => AirLeg.gate ⟨cboolExpr (WSEL_BASE + r), .const 0⟩))

/-- ⚑ **THE COMMITMENT MACHINE'S SOURCE AIR.** -/
def commitAir (pl : Nat → ℤ) (prog : List Instr) : EffectAir :=
  { tables := [ mainTableDef CM_WIDTH
              , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
              , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩
              , ⟨rangeTidW CBITS, "range_w1", 1, .rangeLimb CBITS⟩
              , ⟨ROM_TID, "pasta_commit_rom", ROM_ARITY, .exactPublicRows (romRows prog)⟩ ]
  , legs :=
      -- the ALU's own arithmetic, unmoved
      (List.range NG).map (fun m => AirLeg.gate ⟨aluMulExpr pl m, .const 0⟩)
      ++ (List.range NA).map
           (fun m => AirLeg.gate ⟨aluAddSubExpr SEL_ADD pl 1 (-1) m, .const 0⟩)
      ++ (List.range NA).map
           (fun m => AirLeg.gate ⟨aluAddSubExpr SEL_SUB pl (-1) 1 m, .const 0⟩)
      ++ [ AirLeg.gate ⟨cboolExpr SEL_MUL, .const 0⟩
         , AirLeg.gate ⟨cboolExpr SEL_ADD, .const 0⟩
         , AirLeg.gate ⟨cboolExpr SEL_SUB, .const 0⟩
         , AirLeg.gate ⟨selSumExpr SEL_MUL 3, .const 0⟩
         -- ⚑ the chain selector is DELETED, not carried: pinned to zero, its 32 window legs gone
         , AirLeg.gate ⟨.var SEL_CHAIN, .const 0⟩ ]
      -- the machine
      ++ (List.range SK).map (fun i => AirLeg.gate ⟨xRouteExpr i, .const 0⟩)
      ++ (List.range SK).map (fun i => AirLeg.gate ⟨yRouteExpr i, .const 0⟩)
      ++ selBoolLegs
      ++ [ AirLeg.gate ⟨selSumExpr XSEL_BASE (NREG + 1), .const 0⟩
         , AirLeg.gate ⟨selSumExpr YSEL_BASE (NREG + 2), .const 0⟩
         , AirLeg.gate ⟨selSumExpr WSEL_BASE (NREG + 1), .const 0⟩
         , AirLeg.gate ⟨decodeExpr XSEL_BASE (NREG + 1) XIDX_COL, .const 0⟩
         , AirLeg.gate ⟨decodeExpr YSEL_BASE (NREG + 2) YIDX_COL, .const 0⟩
         , AirLeg.gate ⟨decodeExpr WSEL_BASE (NREG + 1) WIDX_COL, .const 0⟩
         , AirLeg.gate ⟨cboolExpr ZCHK_COL, .const 0⟩ ]
      ++ (List.range SK).map (fun i => AirLeg.gate ⟨zchkExpr i, .const 0⟩)
      ++ regWindowLegs
      ++ [ AirLeg.window ⟨RowSel.first, pcStartExpr⟩
         , AirLeg.window ⟨RowSel.transition, pcThreadExpr⟩
         , AirLeg.lookup { table := ROM_TID, tuple := romTuple } ]
      -- the ranges, last
      ++ [ AirLeg.limbs ⟨limbCols X_BASE, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨limbCols Y_BASE, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨limbCols Z_BASE, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨limbCols ALU_Q_BASE, SB, rangeTidW SB⟩
         , AirLeg.limbs ⟨aluCarryCols, CB, rangeTidW CB⟩
         , AirLeg.limbs ⟨[ALU_AC_COL], CBITS, rangeTidW CBITS⟩
         , AirLeg.limbs ⟨aluAcarCols, ACB, rangeTidW SB⟩ ] }

/-- ⚑ **THE COMPILER ACCEPTS THE COMMITMENT MACHINE.** Every leg has a deployed main-rail image:
the 384 register windows and the `pc` thread because they are `.transition`; the `pc` start because
a `.first` window whose body reads `loc` only lowers to a `boundary`; the ROM lookup because its
multiplicity is `.const 1` and its side is `.query`; and the seven `limbs` legs because every
declared width is `0 < bits ≤ 29`. -/
theorem commitAir_mainRailOk (pl : Nat → ℤ) (prog : List Instr) :
    (commitAir pl prog).mainRailOk = true := by
  unfold commitAir EffectAir.mainRailOk
  simp only [List.all_append, List.all_map, List.all_flatMap, Bool.and_eq_true, List.all_eq_true,
    regWindowLegs, selBoolLegs]
  repeat' apply And.intro
  all_goals first
    | decide
    | (intro m _; rfl)

/-- The emitted descriptor at the Pallas-base / Vesta-scalar prime, for a given program. -/
def fpCommitDesc (name : String) (piCount : Nat) (extraLegs : List AirLeg)
    (prog : List Instr) : EffectVmDescriptor2 :=
  lowerAir name CM_WIDTH piCount []
    { commitAir pLimb prog with legs := (commitAir pLimb prog).legs ++ extraLegs }

/-! ## §8 — THE INTERPRETER.

Rust fills cells; it does not author them. The machine's interpreter runs here, over the same
`PastaField.Ref` reference arithmetic the sound atoms' own witnesses use. ⚑ Every value below is
COMPUTED from the instruction's actual inputs; nothing is asserted from what the program was
supposed to do. -/

abbrev RegFile := Nat → Nat

def opResult (op x y : Nat) : Nat :=
  if op = 1 then PastaField.Ref.fpMul x y
  else if op = 2 then PastaField.Ref.fpAdd x y
  else if op = 3 then PastaField.Ref.fpSub x y
  else 0

/-- The `x` operand an instruction reads: a register, or — at the FREE code — the witness the
program supplies for this program counter. -/
def xValue (st : RegFile) (wit : Nat) (I : Instr) : Nat :=
  if I.xr = NREG then wit else st I.xr

/-- The `y` operand: a register, the immediate, or the witness. -/
def yValue (st : RegFile) (wit : Nat) (I : Instr) : Nat :=
  if I.yr = NREG then I.imm else if I.yr = NREG + 1 then wit else st I.yr

def writeBack (v : Nat) (st : RegFile) (I : Instr) : RegFile := fun r =>
  if I.wr < NREG ∧ r = I.wr then v else st r

/-- ⚠ The written value is an ARGUMENT to `writeBack`, so it is computed ONCE per instruction. As
the body of the returned closure it was recomputed on every register read — and `materialize` reads
`NREG` of them per step, so the memoisation that was supposed to make the generator linear made it
twelve times slower instead. -/
def stepRegs (st : RegFile) (wit : Nat) (I : Instr) : RegFile :=
  writeBack (opResult I.op (xValue st wit I) (yValue st wit I)) st I

/-! ⚠ **THE GENERATOR IS QUADRATIC, AND IT IS NOT A `TODO` — it is a derived cost.** `RegFile` is
`Nat → Nat` and `stepRegs` is a CLOSURE; nothing memoises, so reading a register at instruction
depth `d` re-evaluates the write that produced it, whose operands re-evaluate THEIRS. A row emits
`NREG · SK = 384` register limbs, so a `d`-row program costs `Θ(d² · 384)` reads. Measured on this
cone: a 128-instruction fold takes ~29 s.

⚑ **AND THE OBVIOUS FIX MADE IT WORSE.** Collapsing each step to a strict `NREG`-element list
(`materialize`, with `materialize st = st` proved) forces `NREG` reads of the previous closure per
step, and those reads are exactly the expensive ones — an 8-instruction fold stopped finishing.
It was removed rather than kept as a no-op. The real fix is a `RegFile` that is DATA (an `Array`)
rather than a function, which changes every forcing theorem's statement and is the next rung. -/

/-- The arithmetic block of a row: the sound atom's own witness generator at the machine's column
bases. -/
def arithAsg (I : Instr) (xv yv : Nat) : Assignment :=
  let zv := opResult I.op xv yv
  if I.op = 1 then
    fun col => if col < MUL_WIDTH then mulAsg xv yv zv ((xv * yv - zv) / pN) pLimb col else 0
  else
    let sy : ℤ := if I.op = 2 then 1 else -1
    let sc : ℤ := if I.op = 2 then -1 else 1
    let cv : ℤ := if I.op = 2 then (if xv + yv ≥ pN then 1 else 0)
                  else (if xv < yv then 1 else 0)
    let w : Assignment := adAsg xv yv zv cv pLimb sy sc
    fun col =>
      if col < 3 * SK then w col
      else if col < ALU_AC_COL then 0
      else if col = ALU_AC_COL then w AC_COL
      else if col < SEL_MUL then w (ACAR_BASE + (col - ALU_ACAR_BASE))
      else 0

/-- One row of the machine. -/
def rowAsg (st : RegFile) (wit pc : Nat) (I : Instr) : Assignment := fun col =>
  let xv := xValue st wit I
  let yv := yValue st wit I
  if col < SEL_MUL then arithAsg I xv yv col
  else if col = SEL_MUL then (if I.op = 1 then 1 else 0)
  else if col = SEL_ADD then (if I.op = 2 then 1 else 0)
  else if col = SEL_SUB then (if I.op = 3 then 1 else 0)
  else if col = SEL_CHAIN then 0
  else if col < XSEL_BASE then limbAt (st ((col - REG_BASE) / SK)) ((col - REG_BASE) % SK)
  else if col < YSEL_BASE then (if col - XSEL_BASE = I.xr then 1 else 0)
  else if col < WSEL_BASE then (if col - YSEL_BASE = I.yr then 1 else 0)
  else if col < XIDX_COL then (if col - WSEL_BASE = I.wr then 1 else 0)
  else if col = XIDX_COL then (I.xr : ℤ)
  else if col = YIDX_COL then (I.yr : ℤ)
  else if col = WIDX_COL then (I.wr : ℤ)
  else if col = PC_COL then (pc : ℤ)
  else if col = ZCHK_COL then (I.zc : ℤ)
  else if col < CM_WIDTH then limbAt I.imm (col - IMM_BASE)
  else 0

/-- The machine's run: one row per instruction, threading the register file, the witness stream and
the counter. `wits` is the witness the program's free-code instructions read, indexed by `pc`. -/
def runRows (st : RegFile) (wits : Nat → Nat) (pc : Nat) : List Instr → List (List ℤ)
  | [] => []
  | I :: rest =>
      ((List.range CM_WIDTH).map (rowAsg st (wits pc) pc I))
        :: runRows (stepRegs st (wits pc) I) wits (pc + 1) rest

/-- The register file after a whole program. -/
def runRegs (st : RegFile) (wits : Nat → Nat) (pc : Nat) : List Instr → RegFile
  | [] => st
  | I :: rest => runRegs (stepRegs st (wits pc) I) wits (pc + 1) rest

/-- ⚑ **THE FREE-CODE INSTRUCTIONS ARE THE ONLY PLACE A WITNESS CAN ENTER, AND THE ROM NAMES THEM.**
An instruction whose `xr` and `yr` are both routed ignores the witness stream entirely — so the
census "how many free cells does this program have" is a property of the DESCRIPTOR's manifest, not
of the trace. -/
theorem routed_instruction_ignores_the_witness (st : RegFile) (w w' : Nat) (I : Instr)
    (hx : I.xr < NREG) (hy : I.yr ≤ NREG) :
    stepRegs st w I = stepRegs st w' I := by
  funext r
  unfold stepRegs xValue yValue
  have hx' : ¬ (I.xr = NREG) := by omega
  rcases Nat.lt_or_ge I.yr NREG with h | h
  · have h1 : ¬ (I.yr = NREG) := by omega
    have h2 : ¬ (I.yr = NREG + 1) := by omega
    simp [hx', h1, h2]
  · have h1 : I.yr = NREG := by omega
    simp [hx', h1]

/-- The count of instructions that may read a witness — the descriptor's own free-cell budget. -/
def freeCells (prog : List Instr) : Nat :=
  (prog.filter (fun I => decide (I.xr = NREG) || decide (I.yr = NREG + 1))).length

/-- The count of instructions the descriptor demands be zero. -/
def assertCount (prog : List Instr) : Nat :=
  (prog.filter (fun I => decide (I.zc = 1))).length

/-! ### §8b — ⚑ THE SAME GENERATOR AT THE OTHER PASTA PRIME.

A commitment's COORDINATES live in the base field `p`; the scalars that multiply it live in the
scalar field `q`. A machine that could only run at `p` would have to fake the scalar arithmetic,
which is the classic Pasta error. One generator, two fields, and the `p` one is this one at `pN`
**by `rfl`** — so there is no second copy to drift. -/

def refMul (N x y : Nat) : Nat := (x * y) % N
def refAdd (N x y : Nat) : Nat := (x + y) % N
def refSub (N x y : Nat) : Nat := (x + N - y) % N

theorem the_reference_ops_are_the_pasta_ones :
    refMul pN = PastaField.Ref.fpMul ∧ refAdd pN = PastaField.Ref.fpAdd
      ∧ refSub pN = PastaField.Ref.fpSub ∧ refMul qN = PastaField.Ref.fqMul
      ∧ refAdd qN = PastaField.Ref.fqAdd ∧ refSub qN = PastaField.Ref.fqSub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def opResultAt (N op x y : Nat) : Nat :=
  if op = 1 then refMul N x y
  else if op = 2 then refAdd N x y
  else if op = 3 then refSub N x y
  else 0

theorem opResultAt_is_the_base_field_one : opResultAt pN = opResult := rfl

def stepRegsAt (N : Nat) (st : RegFile) (wit : Nat) (I : Instr) : RegFile :=
  writeBack (opResultAt N I.op (xValue st wit I) (yValue st wit I)) st I

theorem stepRegsAt_is_the_base_field_one : stepRegsAt pN = stepRegs := rfl

def arithAsgAt (N : Nat) (pl : Nat → ℤ) (I : Instr) (xv yv : Nat) : Assignment :=
  let zv := opResultAt N I.op xv yv
  if I.op = 1 then
    fun col => if col < MUL_WIDTH then mulAsg xv yv zv ((xv * yv - zv) / N) pl col else 0
  else
    let sy : ℤ := if I.op = 2 then 1 else -1
    let sc : ℤ := if I.op = 2 then -1 else 1
    let cv : ℤ := if I.op = 2 then (if xv + yv ≥ N then 1 else 0)
                  else (if xv < yv then 1 else 0)
    let w : Assignment := adAsg xv yv zv cv pl sy sc
    fun col =>
      if col < 3 * SK then w col
      else if col < ALU_AC_COL then 0
      else if col = ALU_AC_COL then w AC_COL
      else if col < SEL_MUL then w (ACAR_BASE + (col - ALU_ACAR_BASE))
      else 0

theorem arithAsgAt_is_the_base_field_one : arithAsgAt pN pLimb = arithAsg := rfl

def rowAsgAt (N : Nat) (pl : Nat → ℤ) (st : RegFile) (wit pc : Nat) (I : Instr) : Assignment :=
  fun col =>
    let xv := xValue st wit I
    let yv := yValue st wit I
    if col < SEL_MUL then arithAsgAt N pl I xv yv col
    else if col = SEL_MUL then (if I.op = 1 then 1 else 0)
    else if col = SEL_ADD then (if I.op = 2 then 1 else 0)
    else if col = SEL_SUB then (if I.op = 3 then 1 else 0)
    else if col = SEL_CHAIN then 0
    else if col < XSEL_BASE then limbAt (st ((col - REG_BASE) / SK)) ((col - REG_BASE) % SK)
    else if col < YSEL_BASE then (if col - XSEL_BASE = I.xr then 1 else 0)
    else if col < WSEL_BASE then (if col - YSEL_BASE = I.yr then 1 else 0)
    else if col < XIDX_COL then (if col - WSEL_BASE = I.wr then 1 else 0)
    else if col = XIDX_COL then (I.xr : ℤ)
    else if col = YIDX_COL then (I.yr : ℤ)
    else if col = WIDX_COL then (I.wr : ℤ)
    else if col = PC_COL then (pc : ℤ)
    else if col = ZCHK_COL then (I.zc : ℤ)
    else if col < CM_WIDTH then limbAt I.imm (col - IMM_BASE)
    else 0

/-- ⚑ **THE Fq WITNESS GENERATOR IS THE Fp ONE.** -/
theorem rowAsgAt_is_the_base_field_one : rowAsgAt pN pLimb = rowAsg := rfl

def runRowsAt (N : Nat) (pl : Nat → ℤ) (st : RegFile) (wits : Nat → Nat) (pc : Nat) :
    List Instr → List (List ℤ)
  | [] => []
  | I :: rest =>
      ((List.range CM_WIDTH).map (rowAsgAt N pl st (wits pc) pc I))
        :: runRowsAt N pl (stepRegsAt N st (wits pc) I) wits (pc + 1) rest

theorem runRowsAt_is_the_base_field_one : runRowsAt pN pLimb = runRows := by
  funext st wits pc prog
  induction prog generalizing st pc with
  | nil => rfl
  | cons I rest ih =>
      simp only [runRowsAt, runRows, rowAsgAt_is_the_base_field_one,
        stepRegsAt_is_the_base_field_one, List.cons.injEq, true_and]
      exact ih _ _

/-! ### §8c — ⚑ THE REGISTER FILE AS DATA, welded to the closure it replaces.

The generator above is `Theta(d^2)`. This is the sponge lane's fix, copied rather than re-derived:
the register file is a strict `List Nat` of exactly `NREG` entries, and it is **NOT A SECOND
GENERATOR** — `regsOf_stepVecAt` proves the strict step IS `stepRegsAt` seen through `regsOf`, and
`runRowsVecAt_is_runRowsAt` lifts that to whole programs, so every denotation already proved reaches
the emitted artifact by REWRITING and not by re-establishment on a copy.

⚠ The shape that failed was a strict list wrapped around the closure (`materialize`): it kept the
closure as a fallback, so each step still forced `NREG` reads of it. Here the strict structure IS
the semantics — `readVec` bottoms out in `getD`, nothing re-reads a predecessor. -/

def readVec (rs : List Nat) (r : Nat) : Nat := rs.getD r 0
def regsOf (rs : List Nat) : RegFile := readVec rs

theorem readVec_map (f : Nat → Nat) (r : Nat) (h : r < NREG) :
    readVec ((List.range NREG).map f) r = f r := by
  unfold readVec
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem readVec_map_ge (f : Nat → Nat) (r : Nat) (h : ¬ r < NREG) :
    readVec ((List.range NREG).map f) r = 0 := by
  unfold readVec
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]
  rfl

def stepVecAt (N : Nat) (rs : List Nat) (wit : Nat) (I : Instr) : List Nat :=
  let z := opResultAt N I.op (xValue (regsOf rs) wit I) (yValue (regsOf rs) wit I)
  (List.range NREG).map (fun r => if I.wr < NREG ∧ r = I.wr then z else readVec rs r)

/-- ⚑ **THE STRICT STEP IS THE CLOSURE STEP.** -/
theorem regsOf_stepVecAt (N : Nat) (rs : List Nat) (wit : Nat) (I : Instr) (hlen : rs.length = NREG)
    : regsOf (stepVecAt N rs wit I) = stepRegsAt N (regsOf rs) wit I := by
  funext r
  unfold regsOf stepVecAt stepRegsAt writeBack
  by_cases h : r < NREG
  · rw [readVec_map _ r h]; split <;> rfl
  · rw [readVec_map_ge _ r h]
    have hw : ¬ (I.wr < NREG ∧ r = I.wr) := by
      rintro ⟨h1, rfl⟩; exact h h1
    rw [if_neg hw]
    unfold readVec
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem stepVecAt_length (N : Nat) (rs : List Nat) (wit : Nat) (I : Instr) :
    (stepVecAt N rs wit I).length = NREG := by
  unfold stepVecAt; simp

def runRowsVecAt (N : Nat) (pl : Nat → ℤ) (rs : List Nat) (wits : Nat → Nat) (pc : Nat) :
    List Instr → List (List ℤ)
  | [] => []
  | I :: rest =>
      ((List.range CM_WIDTH).map (rowAsgAt N pl (regsOf rs) (wits pc) pc I))
        :: runRowsVecAt N pl (stepVecAt N rs (wits pc) I) wits (pc + 1) rest

/-- ⚑ **AND THE STRICT GENERATOR EMITS THE SAME BYTES.** -/
theorem runRowsVecAt_is_runRowsAt (N : Nat) (pl : Nat → ℤ) (wits : Nat → Nat) :
    ∀ (prog : List Instr) (rs : List Nat) (pc : Nat), rs.length = NREG →
      runRowsVecAt N pl rs wits pc prog = runRowsAt N pl (regsOf rs) wits pc prog := by
  intro prog
  induction prog with
  | nil => intro _ _ _; rfl
  | cons I rest ih =>
      intro rs pc hlen
      show _ :: runRowsVecAt N pl (stepVecAt N rs (wits pc) I) wits (pc + 1) rest
        = _ :: runRowsAt N pl (stepRegsAt N (regsOf rs) (wits pc) I) wits (pc + 1) rest
      rw [← regsOf_stepVecAt N rs (wits pc) I hlen]
      exact congrArg _ (ih _ _ (stepVecAt_length _ _ _ _))

/-- The all-zero register file, and a single pinned input. -/
def zeroVec : List Nat := List.replicate NREG 0
def pinVec (r v : Nat) : List Nat := (List.range NREG).map (fun k => if k = r then v else 0)

theorem pinVec_length (r v : Nat) : (pinVec r v).length = NREG := by unfold pinVec; simp
theorem zeroVec_length : zeroVec.length = NREG := by unfold zeroVec; simp

#assert_axioms readVec_map
#assert_axioms readVec_map_ge
#assert_axioms regsOf_stepVecAt
#assert_axioms stepVecAt_length
#assert_axioms runRowsVecAt_is_runRowsAt
#assert_axioms pinVec_length
#assert_axioms zeroVec_length

#assert_axioms esub_eval
#assert_axioms xRouteExpr_eval
#assert_axioms yRouteExpr_eval
#assert_axioms xRoute_forces_operand
#assert_axioms yRoute_forces_immediate
#assert_axioms yRoute_forces_register
#assert_axioms free_y_routes_nothing
#assert_axioms oneHot_is_forced_by_the_index
#assert_axioms zchk_forces_zero_limbs
#assert_axioms zchk_sub_forces_equality
#assert_axioms reg_write_forces_result
#assert_axioms reg_hold_forces_preservation
#assert_axioms reg_window_leaves_nothing_free
#assert_axioms pc_thread_forces_successor
#assert_axioms one_hot_word_is_refused_at_this_register_count
#assert_axioms index_word_is_register_count_independent
#assert_axioms rom_capacity
#assert_axioms romTuple_length
#assert_axioms romRow_length
#assert_axioms romRow_head
#assert_axioms romRow_key_injective
#assert_axioms romRow_key_nonzero
#assert_axioms romRow_cells_canonical
#assert_axioms commit_reuses_the_alu_layout
#assert_axioms commitAir_mainRailOk
#assert_axioms routed_instruction_ignores_the_witness
#assert_axioms the_reference_ops_are_the_pasta_ones
#assert_axioms opResultAt_is_the_base_field_one
#assert_axioms stepRegsAt_is_the_base_field_one
#assert_axioms arithAsgAt_is_the_base_field_one
#assert_axioms rowAsgAt_is_the_base_field_one
#assert_axioms runRowsAt_is_the_base_field_one

end Dregg2.Circuit.Emit.MinaWrapCommitMachine
