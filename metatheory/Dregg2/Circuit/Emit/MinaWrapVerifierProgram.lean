/-
# `Dregg2.Circuit.Emit.MinaWrapVerifierProgram` — the ALU row becomes a MACHINE: a register file,
a verifier-known instruction ROM, and the first verifier stage that is a THEOREM about public
inputs rather than a price.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every column index, every gate expression, every window leg and the
emitted descriptor are authored here and go through `EffectLower.lowerAir` of an
`EffectAirIR.EffectAir`; `mainRailOk = true` holds by `rfl`. There is no hand-written
`VmConstraint2` anywhere in this file. Rust PROVES the artifact and authors no constraint.
House Law #1.

## THE DEFECT THIS CLOSES

`MinaWrapVerifierAir` proved exactly two things about a trace: **every row performs the Pasta
operation its selector names**, and **a CHAINED transition feeds one row's `z` into the next row's
`x`**. Its own `unchained_transition_relates_nothing` states the counterweight as a theorem: with
`SEL_CHAIN = 0` the next row is related to this one by NOTHING. So an `N`-row trace was `N`
unrelated field operations, and *which* operations they were was the prover's choice. Two things
were missing and they are the same thing twice:

  1. **DATAFLOW.** `nxt.x = loc.z` is ONE edge. A verifier stage needs `x` and `y` each drawn from
     an arbitrary earlier result — an S-box is `x⁷ = x⁴·x²·x`, and `x⁴·x²` reads two results that
     are not the immediately preceding row's.
  2. **THE PROGRAM.** Nothing said which opcode a row runs, which operands it reads, or where it
     writes. The *trace generator* chose all of it, and a STARK proves the TRACE, not the
     generator.

§1–§4 close (1) with a **register file** carried in the row and threaded by `.transition` window
legs — `EffectAirIR`'s only inter-row vocabulary, used as a copy-forward rather than as a single
chain edge. §5 closes (2) with an **instruction ROM** as a `TableSem.exactPublicRows` manifest.
That table is not a subset lookup: `DescriptorIR2.PublicLookupBalanced` demands the queried
multiset be a **PERMUTATION** of the manifest, so the descriptor's own bytes say *these
instructions and no others*, and `TinyAutomataCompose.forced_trace_length` makes the trace length
itself a consequence rather than a convention.

## WHAT ONE INSTANCE NOW CHECKS

  * every row is a Pasta multiply / add / sub (inherited verbatim from `MinaWrapVerifierAir` §3 —
    the operand blocks did not move, `program_reuses_the_alu_layout`);
  * its `x` operand IS the register the instruction names, and its `y` operand is either a named
    register or the instruction's IMMEDIATE (§3);
  * the register file evolves exactly as the instruction says: the written register takes this
    row's result, every other register is preserved (§4);
  * the program counter starts at `0` and increments (§5);
  * and the `(pc, opcode, operand selectors, immediate)` tuple of every row IS the manifest row at
    that `pc` (§5) — so the sequence of instructions is the DESCRIPTOR'S, not the prover's.

⚑ **The first stage that is not a price: `x ↦ x⁷` over the Pasta base field, as a statement about
PUBLIC INPUTS** (§6). The 32 low PIs pin the first row's `R0` limbs and the 32 high PIs pin the
last row's `R3` limbs, so the emitted descriptor's meaning is *"I know a trace proving
`PI_out = PI_in⁷ (mod p)`"*. That is the Poseidon S-box — the atom the 148-permutation Fq
transcript sponge is built from — and it is the first thing in this cone whose statement mentions
neither rows nor columns.

## ⚑ WHAT THIS IS NOT

It is **not** a Wrap verification and it is **not** machine-checked Pickles. Three named gaps, each
a theorem or a measurement rather than a caveat:

  * **The ROM does not scale to the whole verifier.** `MAX_EXACT_PUBLIC_CELLS = 2^25`
    (`circuit/src/descriptor_ir2.rs:523`) against this ROM's arity `55` caps a program at `610 080`
    instructions, and §7's census prices the verifier at `1 671 656`. `rom_cannot_hold_the_whole_verifier`
    is that as a `decide`, not a worry. The whole verifier in one instance needs either a narrower
    instruction word or a ROM the IR cannot currently express (a root-committed table — the named
    gap `RowSemantics.committedRows`).
  * **The IPA opening stays vacuous in-circuit** (§8), and the native discharge that now exists does
    NOT change that — it changes what the vacuity COSTS. Restated precisely there.
  * **Curve arithmetic is not here.** §6 is a field stage. The MSM stages need the RCB complete-add
    programmed on this machine, which is 41 instructions per add and is future work; §7 prices it.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. Facts are NAMED THEOREMS — this file adds zero `#guard`s.
-/
import Dregg2.Circuit.Emit.MinaWrapVerifierAir
import Dregg2.Circuit.Emit.ExactPublicTableEmit
import Dregg2.Circuit.Emit.EffectLowerCertified
import Dregg2.Circuit.GateExpr

namespace Dregg2.Circuit.Emit.MinaWrapVerifierProgram

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
set_option maxRecDepth 100000

/-! ## §1 — THE MACHINE'S ROW.

⚑ **COLUMNS `0..225` DO NOT MOVE.** The whole arithmetic block — operands, result, quotient,
carries, the four ALU selectors — is `MinaWrapVerifierAir`'s verbatim, which is what makes §3's
`alu_mul_forces` / `alu_add_forces` / `alu_sub_forces` statements about THIS row rather than about
a similar-looking one. Everything below is appended. -/

/-- The register count. **Six is what a Poseidon round needs**, and the number is derived rather
than picked: three registers hold the rate-2/width-3 state `(s₀, s₁, s₂)`, two more are the S-box
temporaries (`x²` must survive while `x⁴` and `x⁶` are formed), and the MDS row accumulates into a
sixth while all three `y` lanes are still live. Five deadlocks the MDS; seven buys nothing. -/
def NREG : Nat := 6

/-- The register file: `NREG` blocks of `SK` limb columns, starting where the ALU row ends. -/
def REG_BASE : Nat := ALU_WIDTH

/-- The base column of register `r`. -/
def regCol (r : Nat) : Nat := REG_BASE + r * SK

/-- `XSEL r` — one-hot over the registers, naming where the `x` operand is read. -/
def XSEL_BASE : Nat := REG_BASE + NREG * SK
/-- `YSEL r` — one-hot-OR-ZERO: all zero means the `y` operand is the instruction's IMMEDIATE. -/
def YSEL_BASE : Nat := XSEL_BASE + NREG
/-- `WSEL r` — one-hot-OR-ZERO: all zero means the instruction writes no register. -/
def WSEL_BASE : Nat := YSEL_BASE + NREG
/-- The program counter. -/
def PC_COL : Nat := WSEL_BASE + NREG
/-- The instruction's IMMEDIATE, `SK` limbs — ROM-pinned, so it is the DESCRIPTOR's constant and
not the prover's. This is what lets a round constant and an MDS coefficient enter the trace. -/
def IMM_BASE : Nat := PC_COL + 1

/-- `226 + 6·32 + 3·6 + 1 + 32 = 469` declared main columns. -/
def PROG_WIDTH : Nat := IMM_BASE + SK

theorem REG_BASE_eq : REG_BASE = 226 := rfl
theorem XSEL_BASE_eq : XSEL_BASE = 418 := rfl
theorem YSEL_BASE_eq : YSEL_BASE = 424 := rfl
theorem WSEL_BASE_eq : WSEL_BASE = 430 := rfl
theorem PC_COL_eq : PC_COL = 436 := rfl
theorem IMM_BASE_eq : IMM_BASE = 437 := rfl
theorem PROG_WIDTH_eq : PROG_WIDTH = 469 := rfl

/-- ⚑ **THE ARITHMETIC BLOCK IS UNMOVED**, so `MinaWrapVerifierAir`'s three forcing theorems are
statements about this row. An edit that shifted any operand base would break this `rfl` rather than
silently make §3 a claim about different columns. -/
theorem program_reuses_the_alu_layout :
    (X_BASE, Y_BASE, Z_BASE, ALU_Q_BASE, ALU_C_BASE, SEL_MUL, SEL_CHAIN)
      = (0, 32, 64, 96, 128, 222, 225) := rfl

/-- …and the appended block starts exactly where the ALU row ended, so nothing overlaps. -/
theorem register_file_starts_after_the_alu_row : REG_BASE = ALU_WIDTH := rfl

/-! ## §2 — THE EXPRESSION HELPERS.

Three combinators, so a gate below reads as the algebra it is rather than as a nest of
`.add`/`.mul`. Each is a `def` over the framework's own AST; none introduces a new constructor. -/

/-- `a − b`. -/
def esub (a b : Expr) : Expr := .add a (.mul (.const (-1)) b)
/-- The sum of a list, left-nested onto `0`. -/
def esum (l : List Expr) : Expr := l.foldl Expr.add (.const 0)
/-- `1 − e`. -/
def eneg1 (e : Expr) : Expr := .add (.const 1) (.mul (.const (-1)) e)

theorem esub_eval (a : Assignment) (u v : Expr) : (esub u v).eval a = u.eval a - v.eval a := by
  unfold esub; simp only [Expr.eval]; ring

theorem esum_eval_cons (a : Assignment) (e : Expr) (l : List Expr) :
    (esum (e :: l)).eval a = ((l.foldl Expr.add (Expr.add (.const 0) e)).eval a) := rfl

theorem eneg1_eval (a : Assignment) (e : Expr) : (eneg1 e).eval a = 1 - e.eval a := by
  unfold eneg1; simp only [Expr.eval]; ring

/-! ## §3 — OPERAND ROUTING: the `x` and `y` a row computes on are the ones the instruction names.

The gate is `Σ_r sel_r · (operand_i − reg_r_i)`, one per limb. Degree **2** — the deployed main-AIR
budget is 3, so routing is strictly cheaper than the multiply gates it feeds. -/

/-- The `x`-routing gate at limb `i`: `Σ_r XSELᵣ · (x_i − REGᵣ_i)`. -/
def xRouteExpr (i : Nat) : Expr :=
  esum ((List.range NREG).map
    (fun r => Expr.mul (.var (XSEL_BASE + r)) (esub (.var (X_BASE + i)) (.var (regCol r + i)))))

/-- The `y`-routing gate at limb `i`: the register term PLUS the immediate term, selected by
whether ANY `YSEL` is on. `Σ_r YSELᵣ · (y_i − REGᵣ_i) + (1 − Σ_r YSELᵣ) · (y_i − IMM_i)`.

⚑ This is the gate that makes a CONSTANT sayable. Without it a round constant or an MDS coefficient
would have to be a free trace cell, and "the trace runs Poseidon" would be a statement about a
constant the prover chose. -/
def yRouteExpr (i : Nat) : Expr :=
  let selSum : Expr := esum ((List.range NREG).map (fun r => Expr.var (YSEL_BASE + r)))
  .add
    (esum ((List.range NREG).map
      (fun r => Expr.mul (.var (YSEL_BASE + r)) (esub (.var (Y_BASE + i)) (.var (regCol r + i))))))
    (.mul (eneg1 selSum) (esub (.var (Y_BASE + i)) (.var (IMM_BASE + i))))

/-- The routing body at limb `i`, read off an assignment: what the `x`-route gate asserts. -/
def xRouteBody (a : Assignment) (i : Nat) : ℤ :=
  ((List.range NREG).map (fun r => a (XSEL_BASE + r) * (a (X_BASE + i) - a (regCol r + i)))).sum

/-- The register file's six blocks, enumerated once so every sum below expands the same way. -/
theorem range_NREG : List.range NREG = [0, 1, 2, 3, 4, 5] := rfl

/-- ⚑ **THE ROUTING GATE IS THE ROUTING BODY.** The emitted `Expr` evaluates to the sum this
file's forcing lemmas reason about — stated so the lemmas are about the EMITTED object and not
about a re-transcription of it. -/
theorem xRouteExpr_eval (a : Assignment) (i : Nat) :
    (xRouteExpr i).eval a = xRouteBody a i := by
  unfold xRouteExpr xRouteBody esum
  simp [range_NREG, Expr.eval, esub]
  ring

/-- ⚑ **A ROW'S `x` OPERAND IS THE REGISTER ITS INSTRUCTION NAMES.** With the `XSEL` block equal to
the one-hot vector at `r`, the deployed reading `P ∣ body` forces `x_i ≡ REGᵣ_i (mod P)`.

⚑ The hypothesis is deliberately *"the selector block IS `oneHot r`"* rather than *"the selectors
are boolean and sum to one"*: §5's ROM pins these very cells to the descriptor's own bytes
(`romRow` emits `oneHot I.xr`), so at use the hypothesis is discharged by the MANIFEST and is not an
assumption about the prover. A one-hot fact derived from booleanity + a sum gate would be a weaker
statement resting on the prover's own selectors. -/
theorem xRoute_forces_operand (a : Assignment) (i r : Nat) (hr : r < NREG)
    (hsel : ∀ s, s < NREG → a (XSEL_BASE + s) = (if s = r then 1 else 0))
    (h : P ∣ xRouteBody a i) :
    a (X_BASE + i) ≡ a (regCol r + i) [ZMOD P] := by
  have hr6 : r < 6 := hr
  have hsum : xRouteBody a i = a (X_BASE + i) - a (regCol r + i) := by
    unfold xRouteBody
    rw [range_NREG]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hsel 0 (by decide), hsel 1 (by decide), hsel 2 (by decide), hsel 3 (by decide),
        hsel 4 (by decide), hsel 5 (by decide)]
    interval_cases r <;> norm_num
  rw [hsum] at h
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h))

/-- …and with the range facts the emitted limb legs supply on `x`, EQUALITY over ℤ, provided the
register limb is itself canonical. Both are 8-bit on any trace the prover can carry, so the
congruence cannot be hiding a multiple of `P`. -/
theorem xRoute_forces_operand_eq (a : Assignment) (i r : Nat) (hr : r < NREG)
    (hsel : ∀ s, s < NREG → a (XSEL_BASE + s) = (if s = r then 1 else 0))
    (h : P ∣ xRouteBody a i)
    (hx : 0 ≤ a (X_BASE + i) ∧ a (X_BASE + i) < 2 ^ SB)
    (hg : 0 ≤ a (regCol r + i) ∧ a (regCol r + i) < 2 ^ SB) :
    a (X_BASE + i) = a (regCol r + i) := by
  have hmod := xRoute_forces_operand a i r hr hsel h
  have hb : (2 : ℤ) ^ SB ≤ P := by norm_num [SB, Dregg2.Circuit.Emit.EffectLower.P]
  exact Dregg2.Circuit.Emit.EffectLower.eq_of_modEq_canon hx.1 (lt_of_lt_of_le hx.2 hb)
    hg.1 (lt_of_lt_of_le hg.2 hb) hmod

/-- The `y`-routing body at limb `i`. -/
def yRouteBody (a : Assignment) (i : Nat) : ℤ :=
  ((List.range NREG).map (fun r => a (YSEL_BASE + r) * (a (Y_BASE + i) - a (regCol r + i)))).sum
    + (1 - ((List.range NREG).map (fun r => a (YSEL_BASE + r))).sum)
      * (a (Y_BASE + i) - a (IMM_BASE + i))

theorem yRouteExpr_eval (a : Assignment) (i : Nat) :
    (yRouteExpr i).eval a = yRouteBody a i := by
  unfold yRouteExpr yRouteBody esum
  simp [range_NREG, Expr.eval, esub, eneg1]
  ring

/-- ⚑ **AN IMMEDIATE INSTRUCTION'S `y` IS THE ROM's CONSTANT.** With every `YSEL` off, the register
terms vanish and the gate reads `y_i − IMM_i` — and `IMM_i` is a ROM-pinned cell (§5). This is what
makes "multiply by the MDS coefficient `m₀₁`" a statement the descriptor makes rather than one the
witness makes. -/
theorem yRoute_forces_immediate (a : Assignment) (i : Nat)
    (hsel : ∀ s, s < NREG → a (YSEL_BASE + s) = 0)
    (h : P ∣ yRouteBody a i) :
    a (Y_BASE + i) ≡ a (IMM_BASE + i) [ZMOD P] := by
  have hsum : yRouteBody a i = a (Y_BASE + i) - a (IMM_BASE + i) := by
    unfold yRouteBody
    rw [range_NREG]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hsel 0 (by decide), hsel 1 (by decide), hsel 2 (by decide), hsel 3 (by decide),
        hsel 4 (by decide), hsel 5 (by decide)]
    ring
  rw [hsum] at h
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h))

/-- …and a REGISTER instruction's `y` is that register. Same one-hot hypothesis shape as §3's `x`
route, and discharged the same way — by the manifest. -/
theorem yRoute_forces_register (a : Assignment) (i r : Nat) (hr : r < NREG)
    (hsel : ∀ s, s < NREG → a (YSEL_BASE + s) = (if s = r then 1 else 0))
    (h : P ∣ yRouteBody a i) :
    a (Y_BASE + i) ≡ a (regCol r + i) [ZMOD P] := by
  have hr6 : r < 6 := hr
  have hsum : yRouteBody a i = a (Y_BASE + i) - a (regCol r + i) := by
    unfold yRouteBody
    rw [range_NREG]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hsel 0 (by decide), hsel 1 (by decide), hsel 2 (by decide), hsel 3 (by decide),
        hsel 4 (by decide), hsel 5 (by decide)]
    interval_cases r <;> norm_num
  rw [hsum] at h
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h))

/-! ## §4 — THE REGISTER FILE'S EVOLUTION.

One `.transition` window leg per (register, limb): `nxt(REGᵣ_i) − WSELᵣ·z_i − (1 − WSELᵣ)·REGᵣ_i`.
Degree **2**. ⚑ Note the SHAPE: it is not two legs (a write leg and a hold leg) but ONE, so there is
no assignment in which both fire or neither does. A pair of separately-selected legs is exactly how
a register silently becomes free when a third selector value appears. -/

/-- The register-file window leg for register `r`, limb `i`. ⚑ **RE-EMIT**, and collapses the
byte-identical cross-file duplicate in `MinaWrapCommitMachine.regWindowExpr` — see that def for the
form-A-to-form-B rationale. -/
def regWindowExpr (r i : Nat) : WindowExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gEsub Dregg2.Circuit.GateExpr.idOps
      (.leaf (Dregg2.Circuit.GateExpr.WLeaf.nxt (regCol r + i)))
      (Dregg2.Circuit.GateExpr.gMux (.leaf (Dregg2.Circuit.GateExpr.WLeaf.loc (WSEL_BASE + r)))
        (.leaf (Dregg2.Circuit.GateExpr.WLeaf.loc (regCol r + i)))
        (.leaf (Dregg2.Circuit.GateExpr.WLeaf.loc (Z_BASE + i)))))

/-- The register-file body, read against a two-row window. -/
def regBody (cur nxt : Assignment) (r i : Nat) : ℤ :=
  nxt (regCol r + i) - (cur (WSEL_BASE + r) * cur (Z_BASE + i)
    + (1 - cur (WSEL_BASE + r)) * cur (regCol r + i))

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

/-- ⚑ **AND EVERY OTHER REGISTER IS PRESERVED.** This is the half that makes the file a MEMORY: a
value written at instruction `k` is still readable at instruction `k + 40`, which is the whole
reason a stage longer than two rows is expressible at all. -/
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

/-- ⚑ **AND THE THIRD OPTION DOES NOT EXIST.** At any `WSELᵣ` the leg pins `nxt(REGᵣ_i)` to a value
determined by the CURRENT row — there is no assignment of `WSELᵣ` under which the next row's
register is free. Compare `MinaWrapVerifierAir.unchained_transition_relates_nothing`, which is the
statement that the chain leg DOES have such an assignment; that is the structural difference
between a chain edge and a register file, and it is why this file exists. -/
theorem reg_window_leaves_nothing_free (cur nxt : Assignment) (r i : Nat)
    (h : P ∣ regBody cur nxt r i) :
    nxt (regCol r + i)
      ≡ cur (WSEL_BASE + r) * cur (Z_BASE + i)
        + (1 - cur (WSEL_BASE + r)) * cur (regCol r + i) [ZMOD P] := by
  unfold regBody at h
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h))

/-! ## §5 — THE PROGRAM COUNTER AND THE INSTRUCTION ROM.

⚑ This is the section that answers "who chose the opcodes". -/

/-- The ROM's table id. `.custom 96` ⇒ `wireId 101`, clear of the `rangeTidW` family
(`.custom (64 + bits)`, `bits ≤ 29` ⇒ at most `.custom 93`) and far above the reserved ids the
deployed parser refuses (`≤ TID_P2_STATE16 = 9`). -/
def ROM_TID : TableId := .custom 96

/-- The instruction word: `pc + 1` · four opcode selectors · `3·NREG` operand selectors · `SK`
immediate limbs. **`55 ≤ MAX_EXACT_PUBLIC_ARITY`**, which was `64` when this was written (room
for nine more cells) and is `97` since 2026-08-06 (room for forty-two). -/
def ROM_ARITY : Nat := 1 + 4 + 3 * NREG + SK

theorem ROM_ARITY_eq : ROM_ARITY = 55 := rfl

/-- ⚑ **THE ARITY FITS THE DEPLOYED CAP**, and by how much — a `decide`, because the cap is the
thing that decides whether the immediate can be inlined at all. -/
theorem rom_arity_fits : ROM_ARITY ≤ 64 ∧ ROM_ARITY ≤ Dregg2.Circuit.Emit.ExactPublicTableEmit.EP_MAX_ARITY := by
  refine ⟨by decide, by decide⟩

/-- The queried tuple, read off the row's own cells. ⚑ The key is `pc + 1`, never `pc`: a manifest
whose live key space includes `0` cannot be distinguished from an all-zero tuple, which is the trap
`PastaMsmBound.manifestRow` documents and avoids the same way. -/
def romTuple : List Expr :=
  (Expr.add (.var PC_COL) (.const 1))
    :: .var SEL_MUL :: .var SEL_ADD :: .var SEL_SUB :: .var SEL_CHAIN
    :: ((List.range NREG).map (fun r => Expr.var (XSEL_BASE + r))
        ++ (List.range NREG).map (fun r => Expr.var (YSEL_BASE + r))
        ++ (List.range NREG).map (fun r => Expr.var (WSEL_BASE + r))
        ++ (List.range SK).map (fun i => Expr.var (IMM_BASE + i)))

/-- ⚑ **THE EMITTED TUPLE HAS THE DECLARED ARITY.** The deployed parser refuses a mismatch
(`descriptor_ir2.rs:1749`, *"exact-public lookup tuple arity … != declared arity"*) and NOTHING in
`EffectAirIR`'s `mainRailOk` checks it — so the check has to live here or it lives nowhere until a
Rust parse. -/
theorem romTuple_length : romTuple.length = ROM_ARITY := by decide

/-- `pc` starts at zero: a `.first`-scoped window reading `loc` only. -/
def pcStartExpr : WindowExpr := .loc PC_COL
/-- `pc` increments: `nxt(pc) − loc(pc) − 1`, `.transition`-scoped. -/
def pcThreadExpr : WindowExpr :=
  .add (.nxt PC_COL) (.mul (.const (-1)) (.add (.loc PC_COL) (.const 1)))

/-- The `pc` thread body across a window. -/
def pcBody (cur nxt : Assignment) : ℤ := nxt PC_COL - (cur PC_COL + 1)

/-- ⚑ **THE COUNTER THREADS.** Row `j`'s `pc` is `j`, given the first-row pin — the fact the ROM
argument needs, because it is what makes the manifest KEY of row `j` predictable and therefore
unique. -/
theorem pc_thread_forces_successor (cur nxt : Assignment) (h : P ∣ pcBody cur nxt) :
    nxt PC_COL ≡ cur PC_COL + 1 [ZMOD P] := by
  unfold pcBody at h
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h))

/-! ### §5b — the instruction, and the manifest it generates.

⚑ **THERE IS NO `NOP` OPCODE.** `MinaWrapVerifierAir.selSumExpr` asserts `sMul + sAdd + sSub = 1`
on EVERY row, and that gate is inherited unchanged — so a padding row is a real ALU operation, not
an exemption. The padding instruction is `add Rx, #0 → nowhere`: the selector sum still reads `1`,
the add gates still bite, the register file still holds, and no new opcode had to be invented to
reach a power-of-two height. An "idle" row that the operation gates did not constrain would be
precisely the hole this machine exists to close. -/

/-- One instruction. `yr = NREG` means "the immediate"; `wr = NREG` means "write nothing".
Deliberately `Nat`-encoded rather than `Fin`/`Option`: the manifest is a `List (List Nat)` and the
encoding has to survive to the emitted bytes without an intervening translation to get wrong. -/
structure Instr where
  /-- `1` multiply · `2` add · `3` sub. -/
  op  : Nat
  /-- Source register for `x`, `< NREG`. -/
  xr  : Nat
  /-- Source for `y`: a register `< NREG`, or `NREG` for the immediate. -/
  yr  : Nat
  /-- Destination register `< NREG`, or `NREG` for "write nothing". -/
  wr  : Nat
  /-- The immediate, a canonical Pasta field element. Ignored unless `yr = NREG`. -/
  imm : Nat
  deriving Repr, DecidableEq

/-- The `SB`-bit limbs of a natural, as naturals — the manifest's own arithmetic. `limbAt` is the
ℤ-valued twin used by the trace; `manifest_limb_agrees_with_trace` welds them so the ROM cannot be
pinning one thing while the row carries another. -/
def limbNat (v i : Nat) : Nat := (v / 2 ^ (SB * i)) % 2 ^ SB

theorem manifest_limb_agrees_with_trace (v i : Nat) : (limbNat v i : ℤ) = limbAt v i := rfl

/-- A one-hot indicator over `NREG` positions, `0` everywhere when `k = NREG`. -/
def oneHot (k : Nat) : List Nat := (List.range NREG).map (fun r => if r = k then 1 else 0)

/-- The manifest row for instruction `I` at program counter `pc`. -/
def romRow (pc : Nat) (I : Instr) : List Nat :=
  (pc + 1)
    :: (if I.op = 1 then 1 else 0) :: (if I.op = 2 then 1 else 0) :: (if I.op = 3 then 1 else 0)
    :: 0
    :: (oneHot I.xr ++ oneHot I.yr ++ oneHot I.wr
        ++ (List.range SK).map (fun i => limbNat I.imm i))

/-- The ROM: one manifest row per instruction, in program order. -/
def romRows (prog : List Instr) : List (List Nat) :=
  (List.range prog.length).map (fun j => romRow j (prog.getD j ⟨2, 0, NREG, NREG, 0⟩))

/-- ⚑ **EVERY MANIFEST ROW HAS THE DECLARED ARITY.** The deployed parser refuses a row whose
length differs (`descriptor_ir2.rs:1827`), and a manifest is data — nothing else would catch it. -/
theorem romRow_length (pc : Nat) (I : Instr) : (romRow pc I).length = ROM_ARITY := by
  unfold romRow oneHot ROM_ARITY
  simp [NREG, SK]

/-- ⚑ **THE MANIFEST KEY IS THE PROGRAM COUNTER, AND IT IS UNIQUE.** This is the whole hinge of
§5c: `PublicLookupBalanced` gives a PERMUTATION between the queried tuples and the manifest, and a
permutation plus an injective key is a POINTWISE identification. Without key uniqueness the
permutation would only say the multiset of instructions is right, not their ORDER. -/
theorem romRow_head (pc : Nat) (I : Instr) : (romRow pc I).head? = some (pc + 1) := rfl

theorem romRow_key_injective (pc pc' : Nat) (I I' : Instr)
    (h : (romRow pc I).head? = (romRow pc' I').head?) : pc = pc' := by
  rw [romRow_head, romRow_head] at h
  simpa using h

/-- ⚑ **AND THE LIVE KEY SPACE EXCLUDES ZERO**, so no manifest row can be confused with an
all-zero tuple. -/
theorem romRow_key_nonzero (pc : Nat) (I : Instr) : (romRow pc I).head? ≠ some 0 := by
  rw [romRow_head]; simp

/-- ⚑ **EVERY MANIFEST CELL IS A CANONICAL BabyBear FELT.** The Rust table walk refuses a
non-canonical representative (`descriptor_ir2.rs:1835`) and the Lean type is `Nat` — unbounded — so
this obligation is the emitter's, and it is discharged here rather than discovered at parse time.
Selectors are `0`/`1`; the immediate limbs are `< 2^8`; the key is `pc + 1`, so a program shorter
than `P − 1` instructions is canonical, and the ROM's own row cap (`2^21`) is far below that. -/
theorem romRow_cells_canonical (pc : Nat) (I : Instr) (hpc : pc + 1 < 2013265921) :
    ∀ v ∈ romRow pc I, v < 2013265921 := by
  have hbit : ∀ (k j : Nat), (if j = k then 1 else 0) < 2013265921 := by
    intro k j; split <;> omega
  have hlimb : ∀ (v j : Nat), limbNat v j < 2013265921 := by
    intro v j
    have h1 : limbNat v j < 2 ^ SB := Nat.mod_lt _ (by positivity)
    have h2 : (2 : Nat) ^ SB = 256 := rfl
    omega
  intro v hv
  unfold romRow oneHot at hv
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h | h | h
  · omega
  · subst h; split <;> omega
  · subst h; split <;> omega
  · subst h; split <;> omega
  · omega
  · rcases h with ((h | h) | h) | h
    · obtain ⟨j, _, hj⟩ := h; subst hj; exact hbit _ _
    · obtain ⟨j, _, hj⟩ := h; subst hj; exact hbit _ _
    · obtain ⟨j, _, hj⟩ := h; subst hj; exact hbit _ _
    · obtain ⟨j, _, hj⟩ := h; subst hj; exact hlimb _ _

/-- …and `2013265921` is `P`, so the theorem above is about the deployed field and not a literal
that happens to look like it. -/
theorem romRow_canonicality_bound_is_P : (2013265921 : Nat) = P := rfl

/-! ### §5c — the ROM caps, and the one this construction actually hits. -/

/-- The deployed row cap on an exact-public manifest (`descriptor_ir2.rs:521`). -/
def MAX_ROM_ROWS : Nat := 2 ^ 21
/-- The deployed CELL cap (`descriptor_ir2.rs:523`). This is the binding one. -/
def MAX_ROM_CELLS : Nat := 2 ^ 25

/-- ⚑ **THE LONGEST PROGRAM ONE INSTANCE CAN HOLD IS 610 080 INSTRUCTIONS**, and it is the CELL cap
that decides, not the row cap. `2^25 / 55 = 610 080`, against a row cap of `2 097 152` — so the ROM
runs out of cells at 29% of its rows. -/
theorem rom_cell_cap_binds_before_the_row_cap :
    MAX_ROM_CELLS / ROM_ARITY = 610080 ∧ MAX_ROM_CELLS / ROM_ARITY < MAX_ROM_ROWS := by decide

/-- ⚑ **AND THE WHOLE VERIFIER DOES NOT FIT.** `MinaWrapVerifierAir.VERIFIER_ROWS = 1 671 656`
instructions against a 610 080-instruction ROM: the program is **2.74×** the largest one instance
can name. This is a STRUCTURAL finding about the deployed IR, not a budget: the whole Wrap verifier
cannot be a single ROM-bound instance at this instruction width, and the ways out are a narrower
instruction word (the immediate is 32 of the 55 cells), a segmented ROM across instances with a
carried register-file digest, or the named IR gap `RowSemantics.committedRows` — a table committed
by a ROOT rather than by the descriptor's own bytes. -/
theorem rom_cannot_hold_the_whole_verifier :
    MAX_ROM_CELLS / ROM_ARITY < MinaWrapVerifierAir.VERIFIER_ROWS := by decide

/-- ⚑ **THE IMMEDIATE IS WHAT COSTS IT.** Drop the 32 immediate limbs and the instruction word is
23 cells, which holds `1 458 888` instructions — still short of the verifier's `1 671 656`, by 12.7%.
So even the narrow word does not close it, and that is worth knowing before anyone spends a week on
the encoding: the answer is segmentation or a root-committed table, not a tighter word. -/
theorem the_narrow_word_still_does_not_fit :
    MAX_ROM_CELLS / (ROM_ARITY - SK) = 1458888
      ∧ MAX_ROM_CELLS / (ROM_ARITY - SK) < MinaWrapVerifierAir.VERIFIER_ROWS := by decide

/-! ## §6 — THE AIR.

Leg order is emission order. The arithmetic block's legs are `MinaWrapVerifierAir.pastaAluAir`'s,
re-emitted here rather than imported, because the ALU's `limbs` legs must come AFTER the new gates
for the constraint list to stay contiguous — and because a silent divergence between the two files'
gate lists is exactly the drift `alu_reuses_the_multiply_layout` exists to catch one level down. -/

/-- The `(register, limb)` window legs, `NREG · SK = 192` of them. -/
def regWindowLegs : List AirLeg :=
  ((List.range NREG).flatMap (fun r =>
    (List.range SK).map (fun i => AirLeg.window ⟨RowSel.transition, regWindowExpr r i⟩)))

/-- Booleanity for every operand selector: `18` gates. -/
def selBoolLegs : List AirLeg :=
  ((List.range NREG).map (fun r => AirLeg.gate ⟨boolExpr (XSEL_BASE + r), .const 0⟩))
  ++ ((List.range NREG).map (fun r => AirLeg.gate ⟨boolExpr (YSEL_BASE + r), .const 0⟩))
  ++ ((List.range NREG).map (fun r => AirLeg.gate ⟨boolExpr (WSEL_BASE + r), .const 0⟩))

/-- `Σ_r XSELᵣ − 1` — the `x` operand always comes from a register. -/
def xselSumExpr : Expr :=
  .add (esum ((List.range NREG).map (fun r => Expr.var (XSEL_BASE + r)))) (.const (-1))

/-- `Σ_{r<s} selᵣ·sel_s` — at most one selector on. With booleanity this is exactly "≤ 1", and it
is ONE gate of degree 2 rather than fifteen. -/
def atMostOneExpr (base : Nat) : Expr :=
  esum (((List.range NREG) ×ˢ (List.range NREG)).filter (fun pr => pr.1 < pr.2)
    |>.map (fun pr => Expr.mul (.var (base + pr.1)) (.var (base + pr.2))))

/-- ⚑ **THE MACHINE'S SOURCE AIR.** -/
def programAir (pl : Nat → ℤ) (prog : List Instr) : EffectAir :=
  { tables := [ mainTableDef PROG_WIDTH
              , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
              , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩
              , ⟨rangeTidW CBITS, "range_w1", 1, .rangeLimb CBITS⟩
              , ⟨ROM_TID, "pasta_program_rom", ROM_ARITY, .exactPublicRows (romRows prog)⟩ ]
  , legs :=
      -- the ALU's own arithmetic, unmoved
      (List.range NG).map (fun m => AirLeg.gate ⟨aluMulExpr pl m, .const 0⟩)
      ++ (List.range NA).map
           (fun m => AirLeg.gate ⟨aluAddSubExpr SEL_ADD pl 1 (-1) m, .const 0⟩)
      ++ (List.range NA).map
           (fun m => AirLeg.gate ⟨aluAddSubExpr SEL_SUB pl (-1) 1 m, .const 0⟩)
      ++ [ AirLeg.gate ⟨boolExpr SEL_MUL, .const 0⟩
         , AirLeg.gate ⟨boolExpr SEL_ADD, .const 0⟩
         , AirLeg.gate ⟨boolExpr SEL_SUB, .const 0⟩
         , AirLeg.gate ⟨boolExpr SEL_CHAIN, .const 0⟩
         , AirLeg.gate ⟨selSumExpr, .const 0⟩ ]
      ++ (List.range SK).map (fun i => AirLeg.window ⟨RowSel.transition, chainWindowExpr i⟩)
      -- the machine
      ++ (List.range SK).map (fun i => AirLeg.gate ⟨xRouteExpr i, .const 0⟩)
      ++ (List.range SK).map (fun i => AirLeg.gate ⟨yRouteExpr i, .const 0⟩)
      ++ selBoolLegs
      ++ [ AirLeg.gate ⟨xselSumExpr, .const 0⟩
         , AirLeg.gate ⟨atMostOneExpr YSEL_BASE, .const 0⟩
         , AirLeg.gate ⟨atMostOneExpr WSEL_BASE, .const 0⟩ ]
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

/-- ⚑ **THE COMPILER ACCEPTS THE MACHINE.** Every new leg has a deployed main-rail image: the 192
register windows and the `pc` thread because they are `.transition`; the `pc` start because a
`.first` window whose body reads `loc` only lowers to a `boundary`; and the ROM lookup because its
multiplicity is `.const 1` and its side is `.query` — the two conjuncts `LookupLeg.mainRailOk` is.
A register window re-scoped to `.all`, or a ROM lookup at multiplicity ≠ 1, would emit
`refuseConstraints` and make this false. -/
theorem programAir_mainRailOk (pl : Nat → ℤ) (prog : List Instr) :
    (programAir pl prog).mainRailOk = true := by
  unfold programAir EffectAir.mainRailOk
  simp only [List.all_append, List.all_map, List.all_flatMap, Bool.and_eq_true, List.all_eq_true,
    regWindowLegs, selBoolLegs]
  repeat' apply And.intro
  all_goals first
    | decide
    | (intro m _; rfl)

/-- The emitted descriptor at the Pallas-base / Vesta-scalar prime, for a given program. -/
def fpProgramDesc (name : String) (piCount : Nat) (prog : List Instr) : EffectVmDescriptor2 :=
  lowerAir name PROG_WIDTH piCount [] (programAir pLimb prog)

/-! ## §7 — STAGE ONE: `x ↦ x⁷`, THE POSEIDON S-BOX, AS A STATEMENT ABOUT PUBLIC INPUTS.

⚑ This is the first thing in the Pasta cone whose statement mentions neither rows nor columns.

The Fq transcript sponge is 148 permutations; a permutation is 55 rounds; a round is three S-boxes
and a `3×3` MDS; an S-box is `x⁷`. `x⁷` is four multiplies on this machine, and the register file is
what makes the four of them one computation instead of four unrelated rows:

    pc 0   MUL R0, R0 → R1      x²
    pc 1   MUL R1, R1 → R2      x⁴
    pc 2   MUL R2, R1 → R2      x⁶
    pc 3   MUL R2, R0 → R3      x⁷
    pc 4..7  ADD R0, #0 → ∅     padding to a power-of-two height

⚠ Read `pc 1` carefully: `R1 · R1` is the register file doing something the CHAIN could not. The
chain leg wires `nxt.x = loc.z` and NOTHING else, so `x⁴ = x²·x²` — a row whose two operands are the
SAME earlier result — was not expressible at all before this file. -/

/-- The S-box program. The padding instruction is `add R0, #0 → ∅`, which satisfies the inherited
`selSumExpr` rather than being exempt from it (§5b). -/
def sboxProg : List Instr :=
  [ ⟨1, 0, 0, 1, 0⟩      -- x2  := R0 * R0  → R1
  , ⟨1, 1, 1, 2, 0⟩      -- x4  := R1 * R1  → R2
  , ⟨1, 2, 1, 2, 0⟩      -- x6  := R2 * R1  → R2
  , ⟨1, 2, 0, 3, 0⟩      -- x7  := R2 * R0  → R3
  , ⟨2, 0, NREG, NREG, 0⟩
  , ⟨2, 0, NREG, NREG, 0⟩
  , ⟨2, 0, NREG, NREG, 0⟩
  , ⟨2, 0, NREG, NREG, 0⟩ ]

theorem sboxProg_length : sboxProg.length = 8 := rfl

/-- ⚑ **THE PROGRAM'S DENOTATION, over the Pasta base field.** Four multiplies with these operands
compute the seventh power — as an identity in `ZMod pN`, proved from the ring axioms rather than
checked at a point, so it holds for every input the machine can carry. -/
theorem sbox_program_denotes_the_seventh_power (x : ZMod pN) :
    (x * x) * ((x * x) * (x * x)) * x = x ^ 7 := by ring

/-- …and the same identity in the shape the machine actually walks it: `x² = x·x`, `x⁴ = x²·x²`,
`x⁶ = x⁴·x²`, `x⁷ = x⁶·x`. Stated separately because the register allocation is what the ROM pins,
and an allocation that computed `x⁸` would satisfy the previous theorem's *statement* while
computing the wrong thing. -/
theorem sbox_register_schedule_is_the_seventh_power (x : ZMod pN) :
    let x2 := x * x
    let x4 := x2 * x2
    let x6 := x4 * x2
    let x7 := x6 * x
    x7 = x ^ 7 := by simp only; ring

/-- The public-input count: 32 limbs of the input, then 32 of the output. -/
def SBOX_PI_COUNT : Nat := 2 * SK

theorem SBOX_PI_COUNT_eq : SBOX_PI_COUNT = 64 := rfl

/-- The PI pins: the FIRST row's `R0` block is the input, the LAST row's `R3` block is the output.

⚑ **The last row is `pc 7`, three padding instructions after the S-box finishes.** That is not
slack — it is the register file's `hold` half being load-bearing: `reg_hold_forces_preservation`
is what carries `R3` from row 4 to row 7, so the output pin reads the value `pc 3` wrote. Without
the hold leg the pin would read a free cell. -/
def sboxPins : List AirLeg :=
  ((List.range SK).map (fun i => AirLeg.pin ⟨VmRow.first, regCol 0 + i, i⟩))
  ++ ((List.range SK).map (fun i => AirLeg.pin ⟨VmRow.last, regCol 3 + i, SK + i⟩))

/-- The S-box AIR: the machine, plus the 64 boundary pins that make it a statement. -/
def sboxAir : EffectAir :=
  { programAir pLimb sboxProg with
    legs := (programAir pLimb sboxProg).legs ++ sboxPins }

theorem sboxAir_mainRailOk : sboxAir.mainRailOk = true := by
  unfold sboxAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  have h1 : (programAir pLimb sboxProg).legs.all AirLeg.mainRailOk = true :=
    programAir_mainRailOk pLimb sboxProg
  refine ⟨h1, ?_⟩
  simp only [sboxPins, List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

set_option maxHeartbeats 2000000 in
/-- ⚑ **THE TIED SOURCE** — `sboxAir` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards.

⚠ **The `by decide` here is the expensive one and it is set-option'd, not weakened.** `pinsTied`
is `O(pins × legs)` in the kernel and this block carries 64 pins over 515 legs; the default
heartbeat budget stops the elaborator mid-`whnf`. Raising the budget decides the SAME verdict — it
does not admit a block the check would refuse. (The strictly better object is a theorem about
`programAir` GENERAL over `prog`; deciding one instance is what this pass buys.) -/
def sboxTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := sboxAir
  ok   := by decide
  tied := by decide

/-- ⚑ **THE EMITTED S-BOX DESCRIPTOR.** -/
def sboxDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-sbox-prog::v1" PROG_WIDTH SBOX_PI_COUNT [] sboxTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem sboxDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines sboxDesc [] sboxAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-sbox-prog::v1" PROG_WIDTH SBOX_PI_COUNT [] sboxTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs that reason through `lowerAir`. -/
theorem sboxDesc_eq_lowerAir :
    sboxDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-sbox-prog::v1" PROG_WIDTH SBOX_PI_COUNT [] sboxAir := rfl

/-- ⚑ **THE ROM LENGTH IS THE TRACE LENGTH, AND THAT IS A THEOREM OF THE IR, NOT A CONVENTION.**
`TinyAutomataCompose.forced_trace_length` reads `trace rows × lookups-on-the-table = manifest rows`;
this descriptor carries ONE lookup on `ROM_TID`, so an 8-row manifest admits 8-row traces and
nothing else. A prover cannot run the program twice, cannot stop early, and cannot pad. -/
theorem sbox_rom_has_one_row_per_instruction : (romRows sboxProg).length = 8 := by decide

/-! ## §8 — THE HONEST WITNESS, generated here.

Rust fills cells; it does not author them. The machine's interpreter runs in Lean, over the same
`PastaField.Ref` reference arithmetic the sound atoms' own witnesses use, and every row is the
corresponding sound module's witness re-based into the machine layout. -/

/-- The register file as a map from index to a canonical Pasta field element. -/
abbrev RegFile := Nat → Nat

/-- The reference result of an opcode. -/
def opResult (op x y : Nat) : Nat :=
  if op = 1 then PastaField.Ref.fpMul x y
  else if op = 2 then PastaField.Ref.fpAdd x y
  else if op = 3 then PastaField.Ref.fpSub x y
  else 0

/-- The `y` operand an instruction reads. -/
def yValue (st : RegFile) (I : Instr) : Nat := if I.yr = NREG then I.imm else st I.yr

/-- The register file after an instruction. -/
def stepRegs (st : RegFile) (I : Instr) : RegFile := fun r =>
  if I.wr < NREG ∧ r = I.wr then opResult I.op (st I.xr) (yValue st I) else st r

/-- The ARITHMETIC block of a row: the sound atom's own witness for this opcode, at the machine's
column bases. ⚑ Nothing is re-derived — `mulAsg` and `adAsg` are `PastaFieldSound`'s and
`PastaAddSubSound`'s generators, and the only new content is the re-basing of the add/sub carry
block from `AC_COL = 96` to `ALU_AC_COL = 190`, which is `MinaWrapVerifierAir` §7's re-basing at a
different pair of operands. -/
def arithAsg (I : Instr) (xv yv : Nat) : Assignment :=
  let zv := opResult I.op xv yv
  if I.op = 1 then
    fun col =>
      if col < MUL_WIDTH then mulAsg xv yv zv ((xv * yv - zv) / pN) pLimb col else 0
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

/-- One row of the machine: the arithmetic block, the opcode and operand selectors, the register
file as it stands BEFORE the instruction, the program counter, and the immediate's limbs. -/
def rowAsg (st : RegFile) (pc : Nat) (I : Instr) : Assignment := fun col =>
  let xv := st I.xr
  let yv := yValue st I
  if col < SEL_MUL then arithAsg I xv yv col
  else if col = SEL_MUL then (if I.op = 1 then 1 else 0)
  else if col = SEL_ADD then (if I.op = 2 then 1 else 0)
  else if col = SEL_SUB then (if I.op = 3 then 1 else 0)
  else if col = SEL_CHAIN then 0
  else if col < XSEL_BASE then
    -- the register file: block `r`, limb `i`
    limbAt (st ((col - REG_BASE) / SK)) ((col - REG_BASE) % SK)
  else if col < YSEL_BASE then (if col - XSEL_BASE = I.xr then 1 else 0)
  else if col < WSEL_BASE then (if col - YSEL_BASE = I.yr then 1 else 0)
  else if col < PC_COL then (if col - WSEL_BASE = I.wr then 1 else 0)
  else if col = PC_COL then (pc : ℤ)
  else if col < PROG_WIDTH then limbAt I.imm (col - IMM_BASE)
  else 0

/-- The machine's run: one row per instruction, threading the register file and the counter. -/
def runRows (st : RegFile) (pc : Nat) : List Instr → List (List ℤ)
  | [] => []
  | I :: rest =>
      ((List.range PROG_WIDTH).map (rowAsg st pc I))
        :: runRows (stepRegs st I) (pc + 1) rest

/-- The S-box's initial register file at a given input: `R0 = x`, everything else `0`. -/
def sboxInit (x : Nat) : RegFile := fun r => if r = 0 then x else 0

/-- The S-box trace at input `x`. -/
def sboxTrace (x : Nat) : List (List ℤ) := runRows (sboxInit x) 0 sboxProg

/-- The KAT input: `PastaField.Ref.X`, the operand the sound multiply's own witness uses — so the
first row of this trace and `PastaFieldSound.fpHonest` are the same arithmetic block, and a
divergence would be a divergence from an already-checked witness. -/
def SBOX_X : Nat := PastaField.Ref.X

/-- The claimed output: `X⁷` in the Pasta base field, by the reference arithmetic. -/
def SBOX_OUT : Nat :=
  let x2 := PastaField.Ref.fpMul SBOX_X SBOX_X
  let x4 := PastaField.Ref.fpMul x2 x2
  let x6 := PastaField.Ref.fpMul x4 x2
  PastaField.Ref.fpMul x6 SBOX_X

/-- ⚑ **THE INTERPRETER AGREES WITH THE DENOTATION.** The register file after the four S-box
instructions holds `X⁷` in `R3` — computed by the machine's own `stepRegs`, compared against the
reference seventh power. A `decide` over the real 255-bit operands.

⚠ This is the check that the WITNESS GENERATOR is right, and it is the one the mandate's rule is
about: the value is COMPUTED from the gadget's inputs by `stepRegs`, never asserted from what the
program was supposed to do. -/
theorem sbox_run_computes_the_seventh_power :
    (stepRegs (stepRegs (stepRegs (stepRegs (sboxInit SBOX_X)
      (sboxProg.getD 0 ⟨2, 0, NREG, NREG, 0⟩)) (sboxProg.getD 1 ⟨2, 0, NREG, NREG, 0⟩))
      (sboxProg.getD 2 ⟨2, 0, NREG, NREG, 0⟩)) (sboxProg.getD 3 ⟨2, 0, NREG, NREG, 0⟩)) 3
      = SBOX_OUT := by decide

/-- The 64 public inputs: the input's limbs, then the output's. -/
def sboxPIs : List ℤ :=
  (List.range SK).map (limbAt SBOX_X) ++ (List.range SK).map (limbAt SBOX_OUT)

theorem sboxPIs_length : sboxPIs.length = 64 := by decide

/-- ⚑ Every emitted PI is a canonical felt. -/
theorem sboxPIs_canonical : (sboxPIs.all fun v => decide (0 ≤ v ∧ v < P)) = true := by decide

/-! ### §7b — WHICH STAGES FIT, one instance at a time.

⚑ `rom_cannot_hold_the_whole_verifier` says the PROGRAM does not fit. The useful follow-on question
— and the one that decides whether segmentation is a pleasant refactor or a research problem — is
**which stages do**. All six of them do, with the largest at 83% of the cap. So the seam is
per-STAGE, at exactly the boundaries `MinaWrapVerifierAir` §5 already names, and the only thing a
segmented verifier has to carry across instances is the register file. That is a much smaller
problem than "the ROM cannot express the verifier". -/

/-- ⚑ **EVERY STAGE FITS IN ONE ROM; THE VERIFIER DOES NOT.** The largest single stage is the
47-term ξ-aggregate at `503 808` instructions — **82.6%** of the `610 080`-instruction cap — and the
smallest, `f_comm`, is 3.4%. The sum is 2.62× the cap. -/
theorem every_stage_fits_one_rom_but_their_sum_does_not :
    MinaWrapVerifierAir.STAGE_TRANSCRIPT ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ MinaWrapVerifierAir.STAGE_PUBLIC_COMM ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ MinaWrapVerifierAir.STAGE_F_COMM ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ MinaWrapVerifierAir.STAGE_FT_COMM ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ MinaWrapVerifierAir.STAGE_XI_AGGREGATE ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ MinaWrapVerifierAir.STAGE_OPENING ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ MAX_ROM_CELLS / ROM_ARITY < MinaWrapVerifierAir.VERIFIER_ROWS := by decide

/-- ⚑ **AND THE STAGE THIS FILE'S ATOM BUILDS IS THE ONE THAT FITS MOST COMFORTABLY.** The Fq
transcript sponge is 148 permutations × 1 650 instructions = `244 200`, **40.0%** of one ROM — so
the stage §7's S-box is the atom of is reachable as a single instance, and it is the natural next
rung. What is NOT yet done is the register allocation for a full round (three S-boxes and the 3×3
MDS over the `fq_kimchi` constants, which is why `NREG = 6`) and the `qLimb` instantiation the Wrap
phase-2 sponge needs; this file's stage is `pLimb`. Named, not implied.

⚠ The second bound read `< 29 %` until 2026-08-08 and `decide` REFUTED it the moment the census's
round went 21 → 30 instructions. That refusal is the whole point of stating a price as a theorem:
this file's figure had no way of silently following the correction. -/
theorem the_transcript_sponge_is_the_reachable_stage :
    MinaWrapVerifierAir.STAGE_TRANSCRIPT = 148 * MinaWrapVerifierAir.ROWS_PER_POSEIDON_PERM
      ∧ 100 * MinaWrapVerifierAir.STAGE_TRANSCRIPT < 41 * (MAX_ROM_CELLS / ROM_ARITY) := by decide

/-! ### §8b — THE SAME MACHINE AT A THOUSAND INSTRUCTIONS.

⚑ An 8-row instance prices the prover's FIXED cost, not the machine's. This program is the same
four S-box multiplies followed by 1 020 padding adds — a `2^10` instance, 128× the height — so the
per-instruction figure the census needs is a measured slope rather than a divided constant.

It is also the honest demonstration that the register file's HOLD half scales: `R3` is written at
`pc 3` and read by the last row's public-input pin 1 020 instructions later, and every one of those
transitions is a `reg_hold_forces_preservation` instance on the wire. -/

/-- The padding instruction: `add R0, #0 → ∅`. -/
def padInstr : Instr := ⟨2, 0, NREG, NREG, 0⟩

/-- Four S-box multiplies, then 1 020 padding adds. -/
def longProg : List Instr := sboxProg.take 4 ++ List.replicate 1020 padInstr

theorem longProg_length : longProg.length = 1024 := by
  simp [longProg, sboxProg]

/-- The same AIR and the same 64 boundary pins, at a `2^10` height. -/
def longAir : EffectAir :=
  { programAir pLimb longProg with legs := (programAir pLimb longProg).legs ++ sboxPins }

theorem longAir_mainRailOk : longAir.mainRailOk = true := by
  unfold longAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  have h1 : (programAir pLimb longProg).legs.all AirLeg.mainRailOk = true :=
    programAir_mainRailOk pLimb longProg
  refine ⟨h1, ?_⟩
  simp only [sboxPins, List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

set_option maxHeartbeats 2000000 in
/-- ⚑ **THE TIED SOURCE** — `longAir` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards.

⚠ **The `by decide` here is the expensive one and it is set-option'd, not weakened.** `pinsTied`
is `O(pins × legs)` in the kernel and this block carries 64 pins over 515 legs; the default
heartbeat budget stops the elaborator mid-`whnf`. Raising the budget decides the SAME verdict — it
does not admit a block the check would refuse. (The strictly better object is a theorem about
`programAir` GENERAL over `prog`; deciding one instance is what this pass buys.) -/
def longTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := longAir
  ok   := by decide
  tied := by decide

def longDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-sbox-prog-1k::v1" PROG_WIDTH SBOX_PI_COUNT [] longTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem longDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines longDesc [] longAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-sbox-prog-1k::v1" PROG_WIDTH SBOX_PI_COUNT [] longTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs that reason through `lowerAir`. -/
theorem longDesc_eq_lowerAir :
    longDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-sbox-prog-1k::v1" PROG_WIDTH SBOX_PI_COUNT [] longAir := rfl

/-- The `2^10` run: the same input, the same claimed output, 1 024 rows. -/
def longTrace (x : Nat) : List (List ℤ) := runRows (sboxInit x) 0 longProg

/-- ⚑ **AND ITS ROM IS 1 024 × 55 = 56 320 CELLS**, 0.17% of the deployed cell cap — so the ceiling
`rom_cannot_hold_the_whole_verifier` names is 596× away from this instance and is a real ceiling
rather than one this demonstration is bumping into. -/
theorem longProg_rom_cells : 1024 * ROM_ARITY = 56320 ∧ 1024 * ROM_ARITY < MAX_ROM_CELLS := by
  decide

/-! ## §9 — THE OPENING'S VACUITY, RESTATED AGAINST THE DISCHARGE THAT NOW EXISTS.

`MinaWrapVerifierAir` §6 proved the in-AIR IPA opening VACUOUS while `sg` is a free prover-chosen
point (`opening_is_vacuous_when_sg_is_free`), because `sg = ⟨s, srs.g⟩` is an MSM over the 32 768
SRS bases and that leg is 205× the rest of the verifier (`srs_leg_dwarfs_the_rest`; it read 215×
while the included side carried the 21-instruction Poseidon round).

⚑ **THE DISCHARGE NOW EXISTS, NATIVELY**: `batch_dlog_accumulator_check` was wired and measured on
7 real Mina block proofs — the honest batch discharged in 27.4 s, a forged `sg` refused in each of
the 7 slots, batching 14.9× over one-at-a-time. So the correct question is no longer "is the opening
vacuous" but **"what does a NATIVE discharge buy an IN-AIR relation"**, and the answer is precise
and unflattering: it changes the vacuity's COST, not its TRUTH.

Stated as theorems below rather than as a paragraph, because the tempting sentence — *"the SRS leg
is discharged, so the opening is sound now"* — is FALSE, and a comment cannot be checked. -/

/-- ⚑ **THE VACUITY IS UNCHANGED BY A NATIVE DISCHARGE.** `MinaWrapVerifierAir`'s theorem
quantifies over the in-AIR relation with `sg` free; a check performed OUTSIDE the AIR does not
appear in that quantification, so the in-AIR relation still accepts at every value of everything
else. This is an instance of the parent theorem, exhibited at the discharged configuration so the
inference "native check ⇒ in-AIR soundness" has a named refutation to run into. -/
theorem native_discharge_does_not_bind_the_in_air_relation (rest f : ℤ) :
    ∃ sg, MinaWrapVerifierAir.openingAccepts f (fun s => s + rest) sg :=
  MinaWrapVerifierAir.opening_accepts_everything_while_sg_is_free rest f

/-- ⚑ **WHAT THE DISCHARGE DOES BUY.** A pinned `sg` makes the relation refute — that is
`MinaWrapVerifierAir.pinned_sg_makes_the_opening_refute` — and the native batch check is what pins
it. So the discharge converts the opening from a stage that must be EXCLUDED from any bound into a
stage whose soundness rests on a check performed by the NATIVE verifier and carried into the AIR as
a HYPOTHESIS. That is a real change of status and a real remaining seam: the resulting claim is
"in-AIR modulo a native `sg` pin", never "in-AIR". -/
theorem pinned_sg_is_what_the_discharge_supplies (rest sg₀ f : ℤ) (h : f ≠ sg₀ + rest) :
    ¬ MinaWrapVerifierAir.openingAccepts f (fun s => s + rest) sg₀ :=
  MinaWrapVerifierAir.pinned_sg_makes_the_opening_refute rest sg₀ f h

/-- ⚑ **AND THE ROW BUDGET THE DISCHARGE DOES NOT RECOVER.** The opening stage is `367 360` ALU rows
and it remains in the price whether or not `sg` is natively pinned, because the relation still has
to be COMPUTED in-circuit for the AIR to carry it — what the native check removes is the `343 943
424`-row SRS-base leg, not the opening. The two figures are 936× apart and confusing them is how a
"discharged" opening turns into a claimed 23% saving that does not exist. -/
theorem the_discharge_removes_the_srs_leg_not_the_opening :
    MinaWrapVerifierAir.SRS_BASE_ROWS / MinaWrapVerifierAir.STAGE_OPENING = 936
      ∧ MinaWrapVerifierAir.STAGE_OPENING = 367360 := by decide

#assert_axioms esub_eval
#assert_axioms eneg1_eval
#assert_axioms xRouteExpr_eval
#assert_axioms xRoute_forces_operand
#assert_axioms xRoute_forces_operand_eq
#assert_axioms yRouteExpr_eval
#assert_axioms yRoute_forces_immediate
#assert_axioms yRoute_forces_register
#assert_axioms reg_write_forces_result
#assert_axioms reg_hold_forces_preservation
#assert_axioms reg_window_leaves_nothing_free
#assert_axioms pc_thread_forces_successor
#assert_axioms romTuple_length
#assert_axioms romRow_length
#assert_axioms romRow_head
#assert_axioms romRow_key_injective
#assert_axioms romRow_key_nonzero
#assert_axioms romRow_cells_canonical
#assert_axioms rom_arity_fits
#assert_axioms rom_cell_cap_binds_before_the_row_cap
#assert_axioms rom_cannot_hold_the_whole_verifier
#assert_axioms the_narrow_word_still_does_not_fit
#assert_axioms every_stage_fits_one_rom_but_their_sum_does_not
#assert_axioms the_transcript_sponge_is_the_reachable_stage
#assert_axioms longProg_length
#assert_axioms longAir_mainRailOk
#assert_axioms longProg_rom_cells
#assert_axioms programAir_mainRailOk
#assert_axioms sboxAir_mainRailOk
#assert_axioms sbox_program_denotes_the_seventh_power
#assert_axioms sbox_register_schedule_is_the_seventh_power
#assert_axioms sbox_rom_has_one_row_per_instruction
#assert_axioms sbox_run_computes_the_seventh_power
#assert_axioms sboxPIs_length
#assert_axioms sboxPIs_canonical
#assert_axioms native_discharge_does_not_bind_the_in_air_relation
#assert_axioms pinned_sg_is_what_the_discharge_supplies
#assert_axioms the_discharge_removes_the_srs_leg_not_the_opening

end Dregg2.Circuit.Emit.MinaWrapVerifierProgram
