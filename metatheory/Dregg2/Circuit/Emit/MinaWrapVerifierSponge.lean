/-
# `Dregg2.Circuit.Emit.MinaWrapVerifierSponge` — the Fq transcript sponge on the machine: a full
Kimchi round over the REAL `fq_kimchi` constants, the 55-round permutation, and a two-element
absorption whose PUBLIC INPUTS are a Mina-agreeing Poseidon digest.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every column index, every gate expression, every instruction and the
emitted descriptors are authored here (and in `MinaWrapVerifierProgram`, whose `programAir` is
reused verbatim) and go through `EffectLower.lowerAir` of an `EffectAirIR.EffectAir`;
`mainRailOk = true` holds by `rfl`. There is no hand-written `VmConstraint2` anywhere in this file.
Rust PROVES the artifacts and authors no constraint. House Law #1.

## THE RUNG

`MinaWrapVerifierProgram` proved `x ↦ x⁷` over the Pasta BASE field as a statement about 64 public
inputs — the Poseidon S-box, and it named what was left: *"the register allocation for a full round
(three S-boxes and the 3×3 MDS over the real `fq_kimchi` constants, which is why `NREG = 6`) and the
`qLimb` instantiation the Wrap phase-2 sponge needs."* Both are here.

  * **§2 THE `qLimb` INSTANTIATION.** `MinaWrapVerifierAir` had `alu_mul_forces_fq` and no add/sub
    twin — so an ADD row at the Vesta-base modulus forced nothing, and a sponge is half additions.
    `alu_add_forces_fq` / `alu_sub_forces_fq` close it, through the SAME
    `addsub_gates_force_congruence` at `qLimb`, with no re-derived bound.
  * **§4 THE ROUND ALLOCATION, and it needs no moves.** Kimchi's own S-box schedule
    (`poseidon.rs:29-42`) is `s←x²; x←x·s; s←s²; x←x·s`, which is in-place with **ONE** scratch
    register — not the two `MinaWrapVerifierProgram` §7's `x²·x⁴·x⁶·x⁷` walk needs. That frees the
    other two registers to receive the MDS, and `the_allocation_hands_off` is the theorem that the
    round's OUTPUT registers are the next round's STATE registers: the allocation
    `allocAt r i = (4r + i) % 6` **cycles with period three and spends zero move instructions.**
  * **§5 THE DENOTATION, AS A REFINEMENT OF THE EXISTING REFERENCE.** The spec is not written here.
    It is `PastaPoseidonFq.Core.round fqParams` — the parametric schedule whose Fp instantiation is
    proved equal to `PastaPoseidon.Ref` function-for-function and whose Fq KATs were produced by
    driving o1-labs' own `ArithmeticSponge`. `the_round_program_computes_the_kimchi_round` says the
    30-instruction program's output registers hold exactly that, **for every input register file** —
    a general theorem, not a `decide` at a point.
  * **§6 THE PERMUTATION**, by induction over rounds, and **§7 A TWO-ELEMENT ABSORPTION**:
    `the_absorb_program_computes_the_kimchi_hash` says the emitted trace's squeeze lane is
    `Core.hash fqParams [x₀, x₁]` — the value `ArithmeticSponge::new(fq_kimchi::static_params())`
    returns after `absorb(&[x₀,x₁]); squeeze()`.

## ⚑ ORDER vs SET — the distinction this rung owes, made where it differs from the last one

`MinaWrapVerifierProgram` corrected itself in flight: the ROM permutation fixes WHICH instructions
run, the `pc` thread fixes their ORDER. On a sponge the same two poles land on different lies, and a
third appears that neither covers:

  * **The ROUND-CONSTANT SCHEDULE is the ROM's.** The immediate is a tuple cell and the `pc` key is
    injective, so *round `r` uses `rcsQ[r]`* is pointwise ROM-forced: using round 7's constant at
    round 3 changes the queried MULTISET and the bus refuses. `the_rom_pins_the_round_constant_schedule`
    is the Lean side; §5a of the Rust harness is the wire.
  * **The ABSORBED VALUES are NOT.** They enter through PI-pinned register cells, never as
    immediates (`the_absorbed_value_is_not_a_rom_constant`). What the ROM fixes about them is only
    the LANE each is added into (`the_rom_pins_the_absorb_lane`). So on the absorb the poles INVERT:
    the ROM fixes the absorb ORDER, the public-input pins fix the absorb SET. Swap the two absorbed
    values in the trace and the ROM is silent — the boundary pin refuses.
  * **And neither fixes that the values came from a Kimchi transcript.** That is the generator gap,
    unchanged and named in §9.

## ⚑ WHAT THIS IS NOT

  * **Not a Wrap verification.** This is one of six stages, it is the field stage, and the five MSM
    stages need curve arithmetic that is not programmed. `MinaWrapVerifierAir` §5 prices them.
  * **Not 148 permutations.** One is emitted and proved. §8 WELDS `MinaWrapVerifierAir`'s stage
    census to this file's emitted instruction lists — `the_census_round_is_the_emitted_round`,
    `the_census_perm_is_the_emitted_permutation` — so the census's round IS the emitted round by
    proof rather than by agreement. ⚠ It was **42.9% lower** until 2026-08-08, counting 21
    multiplies per round and omitting the nine additions the MDS sums and the round constants need;
    §8's header says what that cost and why a theorem recording the gap was not a fix.
  * **Not the Wrap sponge's TAPE.** `PastaPoseidonFq.fqPhase1` derives β, γ, α′, ζ′ from a real
    proof; nothing here connects this machine's registers to that tape.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. Facts are NAMED THEOREMS — this file adds zero `#guard`s.
-/
import Dregg2.Circuit.Emit.MinaWrapVerifierProgram
import Dregg2.Circuit.Emit.PastaPoseidonFq

namespace Dregg2.Circuit.Emit.MinaWrapVerifierSponge

open Dregg2.Circuit (Assignment Expr Constraint ConstraintSystem)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 TableDef TableId mainTableDef VmConstraint2 WindowExpr RowSemantics)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg WindowLeg LookupLeg PiPinLeg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.EffectLower (lowerAir P)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaFieldSound
open Dregg2.Circuit.Emit.PastaAddSubSound
open Dregg2.Circuit.Emit.MinaWrapVerifierAir
open Dregg2.Circuit.Emit.MinaWrapVerifierProgram
open Dregg2.Circuit.Emit.PastaPoseidonFq (mdsQ rcsQ fqParams)

set_option autoImplicit false
set_option maxRecDepth 400000

/-! ## §1 — THE SPEC IS NOT WRITTEN HERE.

⚑ The single most valuable thing about this rung is that its specification already existed.
`PastaPoseidonFq` carries the `fq_kimchi` MDS and the 55×3 round constants dumped from
`mina_poseidon::pasta::fq_kimchi::static_params()`, a parametric round/permutation/absorb schedule
whose Fp instantiation is `PastaPoseidon.Ref` *by proof* (`core_is_Ref_at_Fp`, by induction), and
twelve Fq digests produced by driving o1-labs' own `ArithmeticSponge` state machine.

So this file writes NO constants and NO reference. It states what the emitted PROGRAM computes and
proves that it is that object. A second transcription of the round would have been the exact drift
`PastaPoseidonFq`'s own docblock exists to prevent. -/

/-- The MDS entry, from the existing dump. -/
def mQ (j i : Nat) : Nat := PastaPoseidonFq.Core.mc fqParams j i

/-- The round constants of round `r`, from the existing dump. -/
def rQ (r i : Nat) : Nat := (rcsQ.getD r []).getD i 0

/-- ⚑ **THE CONSTANTS ARE THE DUMPED ONES, NOT A COPY.** Both accessors are `rfl`-equal to the
`PastaPoseidonFq` data, so an edit that introduced a local table would break this rather than
silently give the machine a second set of constants. -/
theorem the_constants_are_PastaPoseidonFq_s :
    (mQ 0 0 = (mdsQ.getD 0 []).getD 0 0) ∧ (rQ 0 0 = (rcsQ.getD 0 []).getD 0 0)
      ∧ fqParams.modulus = qN := ⟨rfl, rfl, rfl⟩

/-! ## §2 — THE `qLimb` INSTANTIATION OF THE ALU'S ADD AND SUB POLARITIES.

⚑ **THE GAP THIS CLOSES.** `MinaWrapVerifierAir` §3 proved `alu_mul_forces` at `pLimb`,
`alu_mul_forces_fq` at `qLimb`, and `alu_add_forces` / `alu_sub_forces` at `pLimb` ONLY. A sponge
round is 21 multiplies and 9 additions; without the two theorems below an ADD row of the emitted Fq
machine forced no Fq congruence at all, and the round's denotation would have rested on a gate
nobody had read at this modulus.

Both go through `PastaAddSubSound.addsub_gates_force_congruence` at `qLimb` — the same theorem the
`pLimb` polarity uses, instantiated at a different limb vector. **No bound is re-derived**;
`qLimb_bounds` and `qLimb_recomposes` are the existing facts, and that is what makes this a
one-line instantiation rather than a second proof. -/

/-- ⚑ **THE ADD POLARITY AT THE VESTA-BASE / PALLAS-SCALAR MODULUS.** -/
theorem alu_add_forces_fq (a : Assignment) (hsel : a SEL_ADD = 1)
    (hx : ∀ i, i < SK → 0 ≤ a (X_BASE + i) ∧ a (X_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (Y_BASE + i) ∧ a (Y_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (Z_BASE + i) ∧ a (Z_BASE + i) < 2 ^ SB)
    (hcb : 0 ≤ a ALU_AC_COL ∧ a ALU_AC_COL < 2)
    (hc : ∀ i, i < NA - 1 → 0 ≤ a (ALU_ACAR_BASE + i) ∧ a (ALU_ACAR_BASE + i) < 2 ^ ACB)
    (hgates : ∀ m, m < NA → P ∣ (aluAddSubExpr SEL_ADD qLimb 1 (-1) m).eval a) :
    (qN : ℤ) ∣ (sVal a X_BASE + sVal a Y_BASE - sVal a Z_BASE) := by
  have h := addsub_gates_force_congruence a X_BASE Y_BASE Z_BASE ALU_AC_COL ALU_ACAR_BASE qLimb
    1 (-1) (qN : ℤ) (Or.inl rfl) (Or.inr rfl) hx hy hz qLimb_bounds qLimb_recomposes hcb hc
    (fun m hm => by
      have hg := hgates m hm
      rw [aluAddSubExpr_eval, hsel, one_mul] at hg
      exact hg)
  simpa using h

/-- ⚑ **AND THE SUB POLARITY**, at `(sy, sc) = (−1, 1)`. The round does not use it; it is emitted
because the machine's row can be a sub and a row whose gates nobody has read at this modulus is
exactly the shape a later stage would silently inherit. -/
theorem alu_sub_forces_fq (a : Assignment) (hsel : a SEL_SUB = 1)
    (hx : ∀ i, i < SK → 0 ≤ a (X_BASE + i) ∧ a (X_BASE + i) < 2 ^ SB)
    (hy : ∀ i, i < SK → 0 ≤ a (Y_BASE + i) ∧ a (Y_BASE + i) < 2 ^ SB)
    (hz : ∀ i, i < SK → 0 ≤ a (Z_BASE + i) ∧ a (Z_BASE + i) < 2 ^ SB)
    (hcb : 0 ≤ a ALU_AC_COL ∧ a ALU_AC_COL < 2)
    (hc : ∀ i, i < NA - 1 → 0 ≤ a (ALU_ACAR_BASE + i) ∧ a (ALU_ACAR_BASE + i) < 2 ^ ACB)
    (hgates : ∀ m, m < NA → P ∣ (aluAddSubExpr SEL_SUB qLimb (-1) 1 m).eval a) :
    (qN : ℤ) ∣ (sVal a X_BASE - sVal a Y_BASE - sVal a Z_BASE) := by
  have h := addsub_gates_force_congruence a X_BASE Y_BASE Z_BASE ALU_AC_COL ALU_ACAR_BASE qLimb
    (-1) 1 (qN : ℤ) (Or.inr rfl) (Or.inl rfl) hx hy hz qLimb_bounds qLimb_recomposes hcb hc
    (fun m hm => by
      have hg := hgates m hm
      rw [aluAddSubExpr_eval, hsel, one_mul] at hg
      exact hg)
  simpa [sub_eq_add_neg] using h

/-! ## §3 — THE MODULUS-GENERAL INTERPRETER, WELDED TO THE Fp ONE.

⚑ `MinaWrapVerifierProgram`'s interpreter hard-codes `pN`. A sponge over the OTHER Pasta field
needs the same machine at `qN`, and copying the interpreter is how the two silently diverge. So the
interpreter below is parametric in the modulus and the emitted limb vector, and **the Fp one is
proved to be its instance by `rfl`** — there is no twin, there is one function and two points. -/

/-- The reference arithmetic at an arbitrary modulus. -/
def refMul (N x y : Nat) : Nat := (x * y) % N
def refAdd (N x y : Nat) : Nat := (x + y) % N
def refSub (N x y : Nat) : Nat := (x + N - y) % N

/-- ⚑ **AND THEY ARE `PastaField.Ref`'s OWN OPERATIONS**, at the two Pasta moduli. -/
theorem ref_ops_are_the_pasta_ones :
    refMul pN = PastaField.Ref.fpMul ∧ refAdd pN = PastaField.Ref.fpAdd
      ∧ refSub pN = PastaField.Ref.fpSub ∧ refMul qN = PastaField.Ref.fqMul
      ∧ refAdd qN = PastaField.Ref.fqAdd ∧ refSub qN = PastaField.Ref.fqSub :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The opcode's reference result at modulus `N`. -/
def opResultAt (N op x y : Nat) : Nat :=
  if op = 1 then refMul N x y
  else if op = 2 then refAdd N x y
  else if op = 3 then refSub N x y
  else 0

/-- ⚑ **THE Fp INTERPRETER IS THIS ONE AT `pN`.** -/
theorem opResultAt_is_the_program_interpreter : opResultAt pN = opResult := rfl

/-- The register file after an instruction, at modulus `N`. -/
def stepRegsAt (N : Nat) (st : RegFile) (I : Instr) : RegFile := fun r =>
  if I.wr < NREG ∧ r = I.wr then opResultAt N I.op (st I.xr) (yValue st I) else st r

theorem stepRegsAt_is_the_program_step : stepRegsAt pN = stepRegs := rfl

/-- Run a whole instruction list. -/
def runProgAt (N : Nat) (st : RegFile) : List Instr → RegFile
  | [] => st
  | I :: rest => runProgAt N (stepRegsAt N st I) rest

/-- ⚑ **RUNNING AN APPENDED PROGRAM IS RUNNING ONE THEN THE OTHER.** The fact the permutation's
induction is built on: a 55-round program is 55 round programs and nothing is smuggled at the
seams. -/
theorem runProgAt_append (N : Nat) (l₁ l₂ : List Instr) : ∀ st : RegFile,
    runProgAt N st (l₁ ++ l₂) = runProgAt N (runProgAt N st l₁) l₂ := by
  induction l₁ with
  | nil => intro st; rfl
  | cons I rest ih => intro st; simpa [runProgAt] using ih (stepRegsAt N st I)

/-! ## §4 — THE ROUND, ITS REGISTER ALLOCATION, AND WHY IT COSTS NO MOVES.

A full Kimchi round (`poseidon/src/permutation.rs:55-70`) is: S-box every lane, apply the 3×3 MDS,
add the round's three constants. On six registers that is

    a b c   the state          d   the S-box scratch          e f   the MDS outputs

and the schedule below spends **30 instructions: 21 multiplies and 9 additions.**

⚑ **THE S-BOX SCHEDULE IS KIMCHI'S OWN, AND THAT IS WHAT MAKES THE ALLOCATION FIT.**
`MinaWrapVerifierProgram` §7 walks `x² → x⁴ → x⁶ → x⁷`, which needs TWO live temporaries.
`poseidon.rs:29-42` walks `s←x²; x←x·s; s←s²; x←x·s` — four multiplies, the same count, but only
ONE. That single register is the whole difference between a round that needs three move
instructions to put its outputs back where the next round expects them and a round that needs
none. -/

/-- The in-place S-box of lane `a` with scratch `d`, four multiplies. Kimchi's own walk. -/
def sboxInstrs (a d : Nat) : List Instr :=
  [ ⟨1, a, a, d, 0⟩      -- d := a·a          = a²
  , ⟨1, a, d, a, 0⟩      -- a := a·d          = a³
  , ⟨1, d, d, d, 0⟩      -- d := d·d          = a⁴
  , ⟨1, a, d, a, 0⟩ ]    -- a := a·d          = a⁷

/-- One MDS row into `out`: three constant multiplies, two sums, and the round constant.
⚑ Every coefficient is an IMMEDIATE, so it is a cell of the ROM tuple and therefore the
DESCRIPTOR's — `yRoute_forces_immediate` is the gate and §9's harness is the wire. -/
def mdsRowInstrs (a b c d out : Nat) (m0 m1 m2 rc : Nat) : List Instr :=
  [ ⟨1, a, NREG, out, m0⟩    -- out := a·m0
  , ⟨1, b, NREG, d,   m1⟩    -- d   := b·m1
  , ⟨2, out, d, out, 0⟩      -- out := out + d
  , ⟨1, c, NREG, d,   m2⟩    -- d   := c·m2
  , ⟨2, out, d, out, 0⟩      -- out := out + d
  , ⟨2, out, NREG, out, rc⟩ ]-- out := out + rc

/-- ⚑ **THE FULL ROUND at an explicit allocation.** The third MDS row writes back into `a`, whose
last read is that row's own first instruction — so the state's third lane needs no register of its
own and the round closes on `(e, f, a)`. -/
def roundInstrs (a b c d e f : Nat) (m : Nat → Nat → Nat) (rc : Nat → Nat) : List Instr :=
  sboxInstrs a d ++ sboxInstrs b d ++ sboxInstrs c d
    ++ mdsRowInstrs a b c d e (m 0 0) (m 0 1) (m 0 2) (rc 0)
    ++ mdsRowInstrs a b c d f (m 1 0) (m 1 1) (m 1 2) (rc 1)
    ++ mdsRowInstrs a b c d a (m 2 0) (m 2 1) (m 2 2) (rc 2)

/-- ⚑ **A ROUND IS 30 INSTRUCTIONS**, and the split is 21 multiplies / 9 additions. -/
theorem roundInstrs_length (a b c d e f : Nat) (m : Nat → Nat → Nat) (rc : Nat → Nat) :
    (roundInstrs a b c d e f m rc).length = 30 := by
  simp [roundInstrs, sboxInstrs, mdsRowInstrs]

theorem roundInstrs_opcode_split (a b c d e f : Nat) (m : Nat → Nat → Nat) (rc : Nat → Nat) :
    ((roundInstrs a b c d e f m rc).filter (fun I => I.op == 1)).length = 21
      ∧ ((roundInstrs a b c d e f m rc).filter (fun I => I.op == 2)).length = 9 := by
  constructor <;> simp [roundInstrs, sboxInstrs, mdsRowInstrs]

/-- ⚑ **THE ALLOCATION.** Round `r` holds its state in registers `4r, 4r+1, 4r+2 (mod 6)`, scratches
in `4r+3`, and lands its MDS outputs in `4r+4`, `4r+5` and `4r` — which is the next round's state
triple. -/
def allocAt (r i : Nat) : Nat := (4 * r + i) % NREG

/-- ⚑ **THE HAND-OFF, AS A THEOREM.** The round's output registers `(e, f, a)` ARE the next round's
state registers `(a', b', c')`. This is the statement that the allocation cycles rather than
needing move instructions, and it is why a 55-round permutation costs `55 × 30` and not
`55 × 33`. -/
theorem the_allocation_hands_off (r : Nat) :
    (allocAt r 4, allocAt r 5, allocAt r 0)
      = (allocAt (r + 1) 0, allocAt (r + 1) 1, allocAt (r + 1) 2) := by
  unfold allocAt NREG
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> omega

/-- ⚑ **AND IT CYCLES WITH PERIOD THREE**, so there are exactly three distinct allocations in the
whole permutation and the denotation below needs exactly three base cases. -/
theorem the_allocation_has_period_three (r i : Nat) : allocAt (r + 3) i = allocAt r i := by
  unfold allocAt NREG; omega

/-- ⚑ **THE SIX REGISTERS OF A ROUND ARE SIX DIFFERENT REGISTERS.** Without this the "scratch"
register could be a state lane and the round would silently compute something else. -/
theorem the_allocation_is_injective (r i j : Nat) (hi : i < NREG) (hj : j < NREG)
    (h : allocAt r i = allocAt r j) : i = j := by
  unfold allocAt NREG at *; omega

/-- The first of the three allocations, together with the registers the NEXT round reads — which is
the pair of facts the permutation's induction step needs at once. -/
theorem alloc_case_0 (r : Nat) (h : r % 3 = 0) :
    allocAt r 0 = 0 ∧ allocAt r 1 = 1 ∧ allocAt r 2 = 2 ∧ allocAt r 3 = 3 ∧ allocAt r 4 = 4
      ∧ allocAt r 5 = 5 ∧ allocAt (r + 1) 0 = 4 ∧ allocAt (r + 1) 1 = 5
      ∧ allocAt (r + 1) 2 = 0 := by
  unfold allocAt NREG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem alloc_case_1 (r : Nat) (h : r % 3 = 1) :
    allocAt r 0 = 4 ∧ allocAt r 1 = 5 ∧ allocAt r 2 = 0 ∧ allocAt r 3 = 1 ∧ allocAt r 4 = 2
      ∧ allocAt r 5 = 3 ∧ allocAt (r + 1) 0 = 2 ∧ allocAt (r + 1) 1 = 3
      ∧ allocAt (r + 1) 2 = 4 := by
  unfold allocAt NREG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem alloc_case_2 (r : Nat) (h : r % 3 = 2) :
    allocAt r 0 = 2 ∧ allocAt r 1 = 3 ∧ allocAt r 2 = 4 ∧ allocAt r 3 = 5 ∧ allocAt r 4 = 0
      ∧ allocAt r 5 = 1 ∧ allocAt (r + 1) 0 = 0 ∧ allocAt (r + 1) 1 = 1
      ∧ allocAt (r + 1) 2 = 2 := by
  unfold allocAt NREG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The round of the Fq sponge at round index `r`, at that round's allocation. -/
def roundAt (r : Nat) : List Instr :=
  roundInstrs (allocAt r 0) (allocAt r 1) (allocAt r 2) (allocAt r 3) (allocAt r 4) (allocAt r 5)
    mQ (rQ r)

/-! ## §5 — WHAT THE ROUND PROGRAM COMPUTES.

Two steps, deliberately separated. `roundSchedule` is the ARITHMETIC THE PROGRAM WALKS, read off
`runProgAt` by kernel reduction — it is not a specification, it is the program's own trace
semantics. `PastaPoseidonFq.Core.round` IS the specification, and it already existed. The theorem
that matters is the one between them. -/

/-- The S-box the program walks: `s←x²; x←x·s; s←s²; x←x·s`. -/
def sboxSchedule (N x : Nat) : Nat :=
  refMul N (refMul N x (refMul N x x)) (refMul N (refMul N x x) (refMul N x x))

/-- One MDS row as the program walks it: three constant multiplies summed left-to-right, then the
round constant. -/
def mdsRowSchedule (N : Nat) (m₀ m₁ m₂ rc s₀ s₁ s₂ : Nat) : Nat :=
  refAdd N (refAdd N (refAdd N (refMul N (sboxSchedule N s₀) m₀) (refMul N (sboxSchedule N s₁) m₁))
    (refMul N (sboxSchedule N s₂) m₂)) rc

/-- The round the program walks, in the association order the instructions produce. -/
def roundSchedule (N : Nat) (m : Nat → Nat → Nat) (rc : Nat → Nat) (s₀ s₁ s₂ : Nat) :
    Nat × Nat × Nat :=
  ( mdsRowSchedule N (m 0 0) (m 0 1) (m 0 2) (rc 0) s₀ s₁ s₂
  , mdsRowSchedule N (m 1 0) (m 1 1) (m 1 2) (rc 1) s₀ s₁ s₂
  , mdsRowSchedule N (m 2 0) (m 2 1) (m 2 2) (rc 2) s₀ s₁ s₂ )

/-- The state triple as the reference carries it — a three-element list. -/
def tripleList (t : Nat × Nat × Nat) : List Nat := [t.1, t.2.1, t.2.2]

/-- ⚑ **THE PROGRAM WALKS THE SCHEDULE, at the round-0 allocation.** Kernel reduction of thirty
`stepRegsAt` applications — every register index is a numeral, so the write/hold branch of each is
decided, and the result is an expression in `st 0`, `st 1`, `st 2` alone. -/
theorem schedule_at_alloc_0 (N : Nat) (m : Nat → Nat → Nat) (rc : Nat → Nat) (st : RegFile) :
    (fun o => (o 4, o 5, o 0)) (runProgAt N st (roundInstrs 0 1 2 3 4 5 m rc))
      = roundSchedule N m rc (st 0) (st 1) (st 2) := rfl

/-- …at the second allocation, `(4,5,0,1,2,3)`. -/
theorem schedule_at_alloc_4 (N : Nat) (m : Nat → Nat → Nat) (rc : Nat → Nat) (st : RegFile) :
    (fun o => (o 2, o 3, o 4)) (runProgAt N st (roundInstrs 4 5 0 1 2 3 m rc))
      = roundSchedule N m rc (st 4) (st 5) (st 0) := rfl

/-- …and at the third, `(2,3,4,5,0,1)`. Three allocations is the whole cycle. -/
theorem schedule_at_alloc_2 (N : Nat) (m : Nat → Nat → Nat) (rc : Nat → Nat) (st : RegFile) :
    (fun o => (o 0, o 1, o 2)) (runProgAt N st (roundInstrs 2 3 4 5 0 1 m rc))
      = roundSchedule N m rc (st 2) (st 3) (st 4) := rfl

/-! ### §5b — the bridge to `ZMod qN`, and then back to the reference's `Nat`. -/

theorem refMul_cast (N x y : Nat) : ((refMul N x y : Nat) : ZMod N) = (x : ZMod N) * (y : ZMod N) := by
  unfold refMul; rw [ZMod.natCast_mod]; push_cast; ring

theorem refAdd_cast (N x y : Nat) : ((refAdd N x y : Nat) : ZMod N) = (x : ZMod N) + (y : ZMod N) := by
  unfold refAdd; rw [ZMod.natCast_mod]; push_cast; ring

/-- ⚑ **THE PROGRAM'S S-BOX IS `x⁷`** — over `ZMod N`, for every `x`, by the ring axioms. Not a
`decide` at a point: the schedule computes `x³ · x⁴`, and that it is the seventh power is a fact
about the field, not about an input. -/
theorem sboxSchedule_cast (N x : Nat) : ((sboxSchedule N x : Nat) : ZMod N) = (x : ZMod N) ^ 7 := by
  unfold sboxSchedule; simp only [refMul_cast]; ring

/-- …and `PastaPoseidonFq`'s S-box is the same seventh power. -/
theorem coreSbox_cast (x : Nat) :
    ((PastaPoseidonFq.Core.sbox fqParams x : Nat) : ZMod qN) = (x : ZMod qN) ^ 7 := by
  unfold PastaPoseidonFq.Core.sbox
  rw [show fqParams.modulus = qN from rfl, ZMod.natCast_mod]
  push_cast
  rfl

/-- Both sides land in `[0, qN)`, so an equality in `ZMod qN` is an equality of naturals. -/
theorem nat_of_zmod_eq (a b : Nat) (ha : a < qN) (hb : b < qN)
    (h : (a : ZMod qN) = (b : ZMod qN)) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at this

theorem refAdd_lt (x y : Nat) : refAdd qN x y < qN := Nat.mod_lt _ (by decide)

/-- ⚑ **ONE MDS ROW OF THE PROGRAM IS ONE MDS ROW OF THE REFERENCE.** The program reduces modulo
`qN` after every operation and the reference reduces once at the end; they agree because both are
the same element of `ZMod qN` and both are canonical. Proved from the ring axioms, so it holds at
every state rather than at a checked point. -/
theorem mdsRowSchedule_agrees (m₀ m₁ m₂ rc s₀ s₁ s₂ : Nat) :
    mdsRowSchedule qN m₀ m₁ m₂ rc s₀ s₁ s₂
      = (m₀ * PastaPoseidonFq.Core.sbox fqParams s₀ + m₁ * PastaPoseidonFq.Core.sbox fqParams s₁
          + m₂ * PastaPoseidonFq.Core.sbox fqParams s₂ + rc) % qN := by
  refine nat_of_zmod_eq _ _ (refAdd_lt _ _) (Nat.mod_lt _ (by decide)) ?_
  rw [ZMod.natCast_mod]
  simp only [mdsRowSchedule, refAdd_cast, refMul_cast, sboxSchedule_cast]
  push_cast [coreSbox_cast]
  ring

/-- ⚑ **THE PROGRAM'S ROUND IS `PastaPoseidonFq.Core.round`.** The schedule the thirty instructions
walk and the reference round — the one whose Fp instantiation is `PastaPoseidon.Ref` by proof and
whose Fq KATs came from o1-labs' own `ArithmeticSponge` — agree on EVERY state, as naturals.

This is the theorem the rung is for. Everything above it is layout; everything below it is
emission. -/
theorem roundSchedule_is_the_kimchi_round (r s₀ s₁ s₂ : Nat) :
    tripleList (roundSchedule qN mQ (rQ r) s₀ s₁ s₂)
      = PastaPoseidonFq.Core.round fqParams (rcsQ.getD r []) [s₀, s₁, s₂] := by
  have hround : PastaPoseidonFq.Core.round fqParams (rcsQ.getD r []) [s₀, s₁, s₂]
      = [ (mQ 0 0 * PastaPoseidonFq.Core.sbox fqParams s₀
            + mQ 0 1 * PastaPoseidonFq.Core.sbox fqParams s₁
            + mQ 0 2 * PastaPoseidonFq.Core.sbox fqParams s₂ + rQ r 0) % qN
        , (mQ 1 0 * PastaPoseidonFq.Core.sbox fqParams s₀
            + mQ 1 1 * PastaPoseidonFq.Core.sbox fqParams s₁
            + mQ 1 2 * PastaPoseidonFq.Core.sbox fqParams s₂ + rQ r 1) % qN
        , (mQ 2 0 * PastaPoseidonFq.Core.sbox fqParams s₀
            + mQ 2 1 * PastaPoseidonFq.Core.sbox fqParams s₁
            + mQ 2 2 * PastaPoseidonFq.Core.sbox fqParams s₂ + rQ r 2) % qN ] := rfl
  rw [hround]
  simp only [tripleList, roundSchedule, mdsRowSchedule_agrees]

/-! ## §6 — THE 55-ROUND PERMUTATION. -/

/-- The permutation program: the rounds, in order, each at its own allocation. -/
def permInstrsUpTo (n : Nat) : List Instr := (List.range n).flatMap roundAt

/-- The full `poseidon_block_cipher` for `PlonkSpongeConstantsKimchi`: 55 full rounds, no initial
ARK. -/
def permInstrs : List Instr := permInstrsUpTo PastaPoseidon.rounds

theorem permInstrs_length : permInstrs.length = 1650 := by
  have h : ∀ r, (roundAt r).length = 30 := fun r => roundInstrs_length _ _ _ _ _ _ _ _
  simp [permInstrs, permInstrsUpTo, PastaPoseidon.rounds, List.length_flatMap, h]

/-- ⚑ **THE PERMUTATION PROGRAM COMPUTES THE KIMCHI PERMUTATION.** By induction over rounds: after
`n` rounds the registers `allocAt n {0,1,2}` hold `Core.permFrom fqParams 0 n` of the initial state.
The step is `runProgAt_append` plus the round theorem at whichever of the three allocations `n`
lands on, and `the_allocation_hands_off` is what makes the induction hypothesis's registers the
next round's inputs. -/
theorem the_permutation_program_computes_the_kimchi_permutation (st : RegFile) : ∀ n : Nat,
    [ runProgAt qN st (permInstrsUpTo n) (allocAt n 0)
    , runProgAt qN st (permInstrsUpTo n) (allocAt n 1)
    , runProgAt qN st (permInstrsUpTo n) (allocAt n 2) ]
      = PastaPoseidonFq.Core.permFrom fqParams 0 n [st 0, st 1, st 2] := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      have hsplit : permInstrsUpTo (k + 1) = permInstrsUpTo k ++ roundAt k := by
        simp [permInstrsUpTo, List.range_succ]
      have hstep : PastaPoseidonFq.Core.permFrom fqParams 0 (k + 1) [st 0, st 1, st 2]
          = PastaPoseidonFq.Core.round fqParams (rcsQ.getD k [])
              (PastaPoseidonFq.Core.permFrom fqParams 0 k [st 0, st 1, st 2]) := by
        simp [PastaPoseidonFq.Core.permFrom, List.range_succ, fqParams]
      rw [hsplit, runProgAt_append, hstep, ← ih]
      set mid := runProgAt qN st (permInstrsUpTo k) with hmid
      have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hk with h | h | h
      · obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2⟩ := alloc_case_0 k h
        simp only [roundAt, e0, e1, e2, e3, e4, e5, f0, f1, f2]
        rw [← roundSchedule_is_the_kimchi_round k (mid 0) (mid 1) (mid 2),
          ← schedule_at_alloc_0 qN mQ (rQ k) mid]
        rfl
      · obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2⟩ := alloc_case_1 k h
        simp only [roundAt, e0, e1, e2, e3, e4, e5, f0, f1, f2]
        rw [← roundSchedule_is_the_kimchi_round k (mid 4) (mid 5) (mid 0),
          ← schedule_at_alloc_4 qN mQ (rQ k) mid]
        rfl
      · obtain ⟨e0, e1, e2, e3, e4, e5, f0, f1, f2⟩ := alloc_case_2 k h
        simp only [roundAt, e0, e1, e2, e3, e4, e5, f0, f1, f2]
        rw [← roundSchedule_is_the_kimchi_round k (mid 2) (mid 3) (mid 4),
          ← schedule_at_alloc_2 qN mQ (rQ k) mid]
        rfl

/-! ## §7 — THE ABSORPTION.

⚑ A fresh Kimchi sponge is `[0,0,0]`; `absorb(&[x₀,x₁])` adds `x₀` into lane 0 and `x₁` into lane 1
(`poseidon.rs:107-126`, the lane-counter branch); `squeeze()` finds the sponge `Absorbed`, runs one
`poseidon_block_cipher`, and returns lane 0. That is exactly the program below. -/

/-- The two absorb instructions: lane 0 takes register 3, lane 1 takes register 4. ⚑ The absorbed
values are REGISTER operands — never immediates — which is what §9's order-vs-set distinction turns
on. -/
def absorbInstrs : List Instr := [ ⟨2, 0, 3, 0, 0⟩, ⟨2, 1, 4, 1, 0⟩ ]

/-- ⚑ **THE ABSORBED VALUE IS NOT A ROM CONSTANT.** Both absorb instructions read a REGISTER for
their `y` operand and carry a zero immediate, so the ROM tuple says nothing whatever about the
value absorbed. Contrast the round constants, which are immediates and therefore ARE the
descriptor's (`the_rom_pins_the_round_constant_schedule`). -/
theorem the_absorbed_value_is_not_a_rom_constant :
    absorbInstrs.all (fun I => decide (I.yr < NREG) && decide (I.imm = 0)) = true := by decide

/-- ⚑ **BUT THE LANE IS.** The ROM names, for each absorb instruction, which state lane the value is
added into and which register it comes from. So the ROM fixes the absorb ORDER and the public-input
pins fix the absorb SET — the inverse of the division of labour on the instruction stream, where
the ROM fixes the set and the `pc` thread fixes the order. -/
theorem the_rom_pins_the_absorb_lane :
    absorbInstrs.map (fun I => (I.xr, I.yr, I.wr)) = [(0, 3, 0), (1, 4, 1)] := by decide

/-- ⚑ **AND THE ROUND-CONSTANT SCHEDULE IS THE ROM'S, POINTWISE.** Round `r`'s three constants enter
as IMMEDIATES of three instructions whose `pc` keys are distinct, and `romRow_key_injective` makes
the permutation balance a pointwise identification — so "round 3 used round 7's constant" changes
the queried multiset and the bus refuses. Exhibited as the fact that two different rounds carry
different immediates. -/
theorem the_rom_pins_the_round_constant_schedule :
    rQ 3 0 ≠ rQ 7 0 ∧ rQ 3 1 ≠ rQ 7 1 ∧ rQ 3 2 ≠ rQ 7 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The whole absorb-and-squeeze program: two absorbs, then the 55-round permutation. -/
def absorbCore : List Instr := absorbInstrs ++ permInstrs

theorem absorbCore_length : absorbCore.length = 1652 := by
  simp [absorbCore, absorbInstrs, permInstrs_length]

/-- ⚑ **THE ABSORB PROGRAM COMPUTES THE KIMCHI HASH.** Register `allocAt 55 0 = 4` of the final
register file holds `Core.hash fqParams [x₀, x₁]` — the value o1-labs' own `ArithmeticSponge`
returns from `absorb(&[x₀,x₁]); squeeze()`, for EVERY pair of absorbed values.

The hypotheses are the two the sponge's own semantics need: the state starts fresh, and the
absorbed values are canonical Fq elements (a non-canonical one would be a different element). -/
theorem the_absorb_program_computes_the_kimchi_sponge (st : RegFile)
    (h0 : st 0 = 0) (h1 : st 1 = 0) (h2 : st 2 = 0) (hx₀ : st 3 < qN) (hx₁ : st 4 < qN) :
    [ runProgAt qN st absorbCore (allocAt PastaPoseidon.rounds 0)
    , runProgAt qN st absorbCore (allocAt PastaPoseidon.rounds 1)
    , runProgAt qN st absorbCore (allocAt PastaPoseidon.rounds 2) ]
      = PastaPoseidonFq.Core.absorbAll fqParams [0, 0, 0] [st 3, st 4] := by
  -- the two absorb instructions put `(x₀, x₁, 0)` in the round-0 state registers
  have habs0 : runProgAt qN st absorbInstrs 0 = st 3 := by
    simp [runProgAt, absorbInstrs, stepRegsAt, opResultAt, yValue, NREG, refAdd, h0,
      Nat.mod_eq_of_lt hx₀]
  have habs1 : runProgAt qN st absorbInstrs 1 = st 4 := by
    simp [runProgAt, absorbInstrs, stepRegsAt, opResultAt, yValue, NREG, refAdd, h1,
      Nat.mod_eq_of_lt hx₁]
  have habs2 : runProgAt qN st absorbInstrs 2 = 0 := by
    simp [runProgAt, absorbInstrs, stepRegsAt, NREG, h2]
  -- …and that is exactly the state the reference's absorb loop hands to its closing permutation
  have hspec : PastaPoseidonFq.Core.absorbAll fqParams [0, 0, 0] [st 3, st 4]
      = PastaPoseidonFq.Core.permFrom fqParams 0 PastaPoseidon.rounds
          [(0 + st 3) % qN, (0 + st 4) % qN, 0] := rfl
  rw [Nat.zero_add, Nat.zero_add, Nat.mod_eq_of_lt hx₀, Nat.mod_eq_of_lt hx₁] at hspec
  have hperm := the_permutation_program_computes_the_kimchi_permutation
    (runProgAt qN st absorbInstrs) PastaPoseidon.rounds
  rw [habs0, habs1, habs2] at hperm
  have hsplit : runProgAt qN st absorbCore
      = runProgAt qN (runProgAt qN st absorbInstrs) permInstrs := by
    rw [absorbCore, runProgAt_append]
  rw [hsplit, hspec, permInstrs]
  exact hperm

/-- ⚑ **AND ITS SQUEEZE IS `Core.hash`** — the number `ArithmeticSponge::new(fq_kimchi::
static_params())` returns from `absorb(&[x₀,x₁]); squeeze()`, which is where the twelve KATs in
`PastaPoseidonFq` §4 came from. The corollary is `getD 0` of the state above, because `squeeze` on
an `Absorbed` sponge is exactly *permute, take lane 0*. -/
theorem the_absorb_program_squeezes_the_kimchi_hash (st : RegFile)
    (h0 : st 0 = 0) (h1 : st 1 = 0) (h2 : st 2 = 0) (hx₀ : st 3 < qN) (hx₁ : st 4 < qN) :
    runProgAt qN st absorbCore (allocAt PastaPoseidon.rounds 0)
      = PastaPoseidonFq.Core.hash fqParams [st 3, st 4] := by
  have hlane : ∀ (P : PastaPoseidonFq.Params) (xs : List Nat),
      PastaPoseidonFq.Core.hash P xs
        = (PastaPoseidonFq.Core.absorbAll P [0, 0, 0] xs).getD 0 0 := fun _ _ => rfl
  rw [hlane, ← the_absorb_program_computes_the_kimchi_sponge st h0 h1 h2 hx₀ hx₁,
    List.getD_cons_zero]

/-! ## §8 — ⚑⚑ THE STAGE PRICE, WELDED TO THE EMITTED PROGRAM.

This section used to hold a theorem named `the_census_underprices_the_round`, which proved
`ROWS_PER_PERM_MEASURED = 1650 ∧ MinaWrapVerifierAir.ROWS_PER_POSEIDON_PERM = 1155` — **both
numbers, as a conjunction, with nothing forcing them together.** It was true, it was
`#assert_axioms`-clean, and for a day every downstream figure in `MinaWrapVerifierAir` went on
being computed from the `1 155` it refutes. A theorem that RECORDS a disagreement does not repair
it; it licenses it.

⚑ **SO THE SECOND `def` IS GONE AND WHAT IS LEFT IS A WELD.** `MinaWrapVerifierAir` now derives its
round from `MULS_PER_POSEIDON_ROUND + ADDS_PER_POSEIDON_ROUND = 21 + 9`, and the theorems below
prove that def EQUAL TO THIS FILE'S EMITTED INSTRUCTION LISTS — `(roundAt r).length` and
`permInstrs.length`, whose values come from `roundInstrs_length`/`permInstrs_length` and therefore
from the schedule the descriptor actually emits. There is one number now. If the emitted round ever
changes length, or if the census is edited away from it, **this file fails to compile.** -/

/-- ⚑ **THE CENSUS'S ROUND IS THIS FILE'S EMITTED ROUND** — at every round index, so the weld is not
about round zero. -/
theorem the_census_round_is_the_emitted_round (r : Nat) :
    MinaWrapVerifierAir.ROWS_PER_POSEIDON_ROUND = (roundAt r).length := by
  have h : (roundAt r).length = 30 := roundInstrs_length _ _ _ _ _ _ _ _
  rw [h]
  decide

/-- ⚑ **AND THE CENSUS'S OPCODE SPLIT IS THE EMITTED ROUND'S OPCODE SPLIT.** This is the clause that
would have caught the original defect: the census carried `21` as its whole round, and the emitted
list has 21 multiplies **and nine additions beside them**. -/
theorem the_census_opcode_split_is_the_emitted_one (r : Nat) :
    MinaWrapVerifierAir.MULS_PER_POSEIDON_ROUND
        = ((roundAt r).filter (fun I => I.op == 1)).length
      ∧ MinaWrapVerifierAir.ADDS_PER_POSEIDON_ROUND
        = ((roundAt r).filter (fun I => I.op == 2)).length := by
  obtain ⟨hm, ha⟩ := roundInstrs_opcode_split (allocAt r 0) (allocAt r 1) (allocAt r 2)
    (allocAt r 3) (allocAt r 4) (allocAt r 5) mQ (rQ r)
  exact ⟨hm.symm, ha.symm⟩

/-- ⚑ **AND THE CENSUS'S PERMUTATION IS THE EMITTED PERMUTATION** — `1 650`, not the `1 155` the
census carried until 2026-08-08. -/
theorem the_census_perm_is_the_emitted_permutation :
    MinaWrapVerifierAir.ROWS_PER_POSEIDON_PERM = permInstrs.length := by
  rw [permInstrs_length]
  decide

/-- ⚑ **AND THE TRANSCRIPT STAGE IS 148 OF THEM.** The stage figure that feeds `VERIFIER_ROWS`,
`WRAP_CELLS` and `WRAP_ROWS_SOUND` is now the emitted program's own length times a permutation
count, with no literal in between. -/
theorem the_transcript_stage_is_148_emitted_permutations :
    MinaWrapVerifierAir.STAGE_TRANSCRIPT = 148 * permInstrs.length := by
  rw [permInstrs_length]
  decide

/-- ⚑ **WHAT THE OLD CENSUS WOULD HAVE SAID, AS A FACT ABOUT THE EMITTED OBJECT** — a
multiply-only round count is `21 · 55 = 1 155` and the emitted permutation is `1.428…×` that, so
the figure was low by **42.9%**: not 43%, and not 42%. Stated against `permInstrs.length` rather
than against a stale `def`, so it stays a fact after the `def` is fixed. -/
theorem a_multiply_only_round_underprices_the_emitted_permutation :
    PastaPoseidon.rounds * MinaWrapVerifierAir.MULS_PER_POSEIDON_ROUND = 1155
      ∧ 1155 < permInstrs.length
      ∧ 1428 * 1155 < 1000 * permInstrs.length
      ∧ 1000 * permInstrs.length < 1429 * 1155 := by
  rw [permInstrs_length]
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- ⚑ **AND THE STAGE STILL FITS ONE ROM** — 40.0% of the 610 080-instruction cap, against the
28.0% the under-priced census implied. The re-count moved the number and not the conclusion, which
is the useful kind of correction to be able to state. -/
theorem the_transcript_stage_fits_one_rom :
    MinaWrapVerifierAir.STAGE_TRANSCRIPT ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ 100 * MinaWrapVerifierAir.STAGE_TRANSCRIPT < 41 * (MAX_ROM_CELLS / ROM_ARITY) := by decide

/-! ## §9 — THE EMITTED DESCRIPTORS.

Two instances of the SAME machine: one full round at `2^5`, and a two-element absorption — 55 rounds
— at `2^11`. Two points is what makes §11's price a SLOPE rather than a fixed cost divided by a row
count. -/

/-- One full round, padded to a power-of-two height. The padding is `add R0, #0 → ∅`, which
satisfies the inherited `selSumExpr` rather than being exempt from it — there is no `nop`. -/
def round0Instrs : List Instr := roundInstrs 0 1 2 3 4 5 mQ (rQ 0)

/-- ⚑ **AND IT IS THE ALLOCATION'S OWN ROUND ZERO** — `allocAt 0 i = i`, so naming the concrete
register tuple here is a restatement and not a second program. -/
theorem round0Instrs_is_roundAt_0 : round0Instrs = roundAt 0 := rfl

def roundProg : List Instr := round0Instrs ++ List.replicate 2 padInstr

theorem roundProg_length : roundProg.length = 32 := by
  simp [roundProg, round0Instrs, roundInstrs_length]

/-- The absorption: two absorbs, 55 rounds, padded to `2^11`. -/
def absorbProg : List Instr := absorbCore ++ List.replicate 396 padInstr

theorem absorbProg_length : absorbProg.length = 2048 := by
  simp [absorbProg, absorbCore_length]

/-- ⚑ **AND THE PADDING IS WHY THE OUTPUT PIN READS THE COMPUTED VALUE.** The last row of each trace
is a padding instruction, so the register file it carries is the one the final real instruction
wrote — `reg_hold_forces_preservation` on the wire, exactly as `MinaWrapVerifierProgram` §7's S-box
output pin depends on. A program with no trailing padding would pin a register one write too
early. -/
theorem the_last_instruction_writes_nothing :
    (roundProg.getD 31 padInstr).wr = NREG ∧ (absorbProg.getD 2047 padInstr).wr = NREG := by
  constructor <;> rfl

/-- 192 public inputs: three state lanes in, three out. -/
def SPONGE_PI_COUNT : Nat := 6 * SK

theorem SPONGE_PI_COUNT_eq : SPONGE_PI_COUNT = 192 := rfl

/-- Pin a register block on a row to a public-input window. -/
def pinBlock (row : VmRow) (r base : Nat) : List AirLeg :=
  (List.range SK).map (fun i => AirLeg.pin ⟨row, regCol r + i, base + i⟩)

/-- ⚑ **A PIN BLOCK PUBLISHES REGISTER COLUMNS AND NOTHING ELSE** — the boundary half of
`MinaWrapVerifierProgram` §6a's composition. Every emitted instance of this machine (both sponge
descriptors, both Fp ones, the 46-link chain) builds its boundary out of these, so this one lemma
is the whole tie obligation for all five. -/
theorem pinBlock_regPin (row : VmRow) (r base : Nat) (hr : r < NREG) :
    RegPinBoundary (pinBlock row r base) := by
  intro p hp
  obtain ⟨i, hi, heq⟩ := List.mem_map.mp hp
  refine ⟨r, i, hr, List.mem_range.mp hi, ?_⟩
  have heq' : (⟨row, regCol r + i, base + i⟩ : PiPinLeg) = p := by
    have : AirLeg.pin (⟨row, regCol r + i, base + i⟩ : PiPinLeg) = AirLeg.pin p := heq
    injection this
  rw [← heq']

/-- The round instance's pins: the first row's `(R0,R1,R2)` is the input state, the last row's
`(R4,R5,R0)` is the output state — and those are exactly `allocAt 0 {0,1,2}` and
`allocAt 1 {0,1,2}`, the hand-off `the_allocation_hands_off` names. -/
def roundPins : List AirLeg :=
  pinBlock VmRow.first 0 0 ++ pinBlock VmRow.first 1 SK ++ pinBlock VmRow.first 2 (2 * SK)
    ++ pinBlock VmRow.last 4 (3 * SK) ++ pinBlock VmRow.last 5 (4 * SK)
    ++ pinBlock VmRow.last 0 (5 * SK)

/-- The absorb instance's pins: the fresh sponge state, the two absorbed values, and the squeeze.
⚑ The absorbed values are pinned to PUBLIC INPUTS and appear in no ROM tuple — that is the whole of
§7's order-vs-set inversion, in the emitted legs. -/
def absorbPins : List AirLeg :=
  pinBlock VmRow.first 0 0 ++ pinBlock VmRow.first 1 SK ++ pinBlock VmRow.first 2 (2 * SK)
    ++ pinBlock VmRow.first 3 (3 * SK) ++ pinBlock VmRow.first 4 (4 * SK)
    ++ pinBlock VmRow.last 4 (5 * SK)

/-- ⚑ **THE ROUND'S AIR** — `MinaWrapVerifierProgram.programAir` at `qLimb`, unchanged, plus the
192 boundary pins that make it a statement. Not one gate is authored here that is not authored
there. -/
def roundAir : EffectAir :=
  { programAir qLimb roundProg with legs := (programAir qLimb roundProg).legs ++ roundPins }

def absorbAir : EffectAir :=
  { programAir qLimb absorbProg with legs := (programAir qLimb absorbProg).legs ++ absorbPins }

theorem roundAir_mainRailOk : roundAir.mainRailOk = true := by
  unfold roundAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨programAir_mainRailOk qLimb roundProg, ?_⟩
  simp only [roundPins, pinBlock, List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  repeat' apply And.intro
  all_goals (intro _ _; rfl)

theorem absorbAir_mainRailOk : absorbAir.mainRailOk = true := by
  unfold absorbAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨programAir_mainRailOk qLimb absorbProg, ?_⟩
  simp only [absorbPins, pinBlock, List.all_append, List.all_map, Bool.and_eq_true,
    List.all_eq_true]
  repeat' apply And.intro
  all_goals (intro _ _; rfl)

/-! ### ⚑⚑ THE TIE VERDICT, AND THE CERTIFICATE THESE TWO ROWS DID NOT HAVE.

Measured 2026-08-09: `roundDesc` and `absorbDesc` were lowered with `lowerAir`, so **no
`CertifiedRefines` existed for either** — the emitted constraints were not certified against the
`programAir` legs they claim to implement, while `MinaWrapVerifierProgram`'s own `sboxDesc` and
`longDesc` (the SAME machine, an eight- and a 1 024-instruction program) carried the certificate
from `lowerTiedAir`. The mechanism existed and was used one file down; these two were never
switched over.

⚑ **`lowerTiedAir … |>.val` is `lowerAir …` by `rfl`, so ZERO BYTES MOVE** — the `_eq_lowerAir`
theorems below are that as a proof rather than as a claim. No re-emit, no VK rotation, nothing
re-genesises. What changes is that the emit no longer ELABORATES for a block either verdict
refuses. -/

theorem roundPins_regPin : RegPinBoundary roundPins := by
  unfold roundPins
  repeat' apply RegPinBoundary.append
  all_goals exact pinBlock_regPin _ _ _ (by decide)

theorem absorbPins_regPin : RegPinBoundary absorbPins := by
  unfold absorbPins
  repeat' apply RegPinBoundary.append
  all_goals exact pinBlock_regPin _ _ _ (by decide)

/-- ⚑ **THE ROUND ROW TIES EVERY COLUMN IT PUBLISHES.** Not decided over the assembled block —
composed from `programAir_boundary_pinsTied`, so it costs nothing at 192 pins and would cost
nothing at 2 048. -/
theorem roundAir_pinsTied : roundAir.pinsTied = true :=
  programAir_boundary_pinsTied qLimb roundProg roundPins roundPins_regPin

theorem absorbAir_pinsTied : absorbAir.pinsTied = true :=
  programAir_boundary_pinsTied qLimb absorbProg absorbPins absorbPins_regPin

def roundTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := roundAir
  ok   := roundAir_mainRailOk
  tied := roundAir_pinsTied

def absorbTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := absorbAir
  ok   := absorbAir_mainRailOk
  tied := absorbAir_pinsTied

/-- ⚑ **THE EMITTED ROUND DESCRIPTOR.** -/
def roundDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-fq-round::v1" PROG_WIDTH SPONGE_PI_COUNT [] roundTiedAir).val

/-- ⚑ **THE ROUND'S CERTIFICATE, PRODUCED BY THE EMIT.** Every leg of `roundAir` is FORCED by the
emitted descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in
the SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. -/
theorem roundDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines roundDesc [] roundAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-fq-round::v1" PROG_WIDTH SPONGE_PI_COUNT [] roundTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl`. -/
theorem roundDesc_eq_lowerAir :
    roundDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir
      "dregg-pasta-fq-round::v1" PROG_WIDTH SPONGE_PI_COUNT [] roundAir := rfl

/-- ⚑ **THE EMITTED ABSORPTION DESCRIPTOR.** -/
def absorbDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-fq-absorb::v1" PROG_WIDTH SPONGE_PI_COUNT [] absorbTiedAir).val

/-- ⚑⚑ **THE ABSORPTION'S CERTIFICATE.** This is the descriptor `MinaWrapClosingAir` §b names as
the standing gap ("a `CertifiedRefines` for `programAir`") on the Fq side; its Fp twin is
`MinaWrapVerifierSpongeFp.fpAbsorbDesc_certified`. ⚠ Read what it does and does not close in that
file's §b note: this certifies that the 858 emitted constraints FORCE the source legs. It does not
join those legs to `Core.perm` — `the_absorb_program_permutes_gen` is about `runProgAt`, and the
bridge from forced legs to the interpreter's run is a SECOND obligation, still open. -/
theorem absorbDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines absorbDesc [] absorbAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-fq-absorb::v1" PROG_WIDTH SPONGE_PI_COUNT [] absorbTiedAir).property

theorem absorbDesc_eq_lowerAir :
    absorbDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir
      "dregg-pasta-fq-absorb::v1" PROG_WIDTH SPONGE_PI_COUNT [] absorbAir := rfl

/-- ⚑ **BOTH ROMs FIT THE DEPLOYED CELL CAP**, and by how much. The absorption's manifest is
`2 048 × 55 = 112 640` cells against `2^25` — 0.34%, so `rom_cannot_hold_the_whole_verifier` is
still a real ceiling 297× away and not one this rung is bumping into. -/
theorem the_sponge_roms_fit :
    32 * ROM_ARITY = 1760 ∧ 2048 * ROM_ARITY = 112640
      ∧ 2048 * ROM_ARITY < MAX_ROM_CELLS := by decide

/-! ## §10 — THE HONEST WITNESS, generated here.

Rust fills cells; it does not author them. ⚑ The machine's row generator is
`MinaWrapVerifierProgram.rowAsg` made modulus-parametric and **proved to be it at `pN` by `rfl`** —
one generator, two fields, no second copy to drift. -/

/-- The ARITHMETIC block of a row at modulus `N`. -/
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

theorem arithAsgAt_is_the_program_one : arithAsgAt pN pLimb = arithAsg := rfl

/-- One row of the machine at modulus `N`. -/
def rowAsgAt (N : Nat) (pl : Nat → ℤ) (st : RegFile) (pc : Nat) (I : Instr) : Assignment :=
  fun col =>
    let xv := st I.xr
    let yv := yValue st I
    if col < SEL_MUL then arithAsgAt N pl I xv yv col
    else if col = SEL_MUL then (if I.op = 1 then 1 else 0)
    else if col = SEL_ADD then (if I.op = 2 then 1 else 0)
    else if col = SEL_SUB then (if I.op = 3 then 1 else 0)
    else if col = SEL_CHAIN then 0
    else if col < XSEL_BASE then
      limbAt (st ((col - REG_BASE) / SK)) ((col - REG_BASE) % SK)
    else if col < YSEL_BASE then (if col - XSEL_BASE = I.xr then 1 else 0)
    else if col < WSEL_BASE then (if col - YSEL_BASE = I.yr then 1 else 0)
    else if col < PC_COL then (if col - WSEL_BASE = I.wr then 1 else 0)
    else if col = PC_COL then (pc : ℤ)
    else if col < PROG_WIDTH then limbAt I.imm (col - IMM_BASE)
    else 0

/-- ⚑ **THE Fq WITNESS GENERATOR IS THE Fp ONE.** -/
theorem rowAsgAt_is_the_program_one : rowAsgAt pN pLimb = rowAsg := rfl

def runRowsAt (N : Nat) (pl : Nat → ℤ) (st : RegFile) (pc : Nat) : List Instr → List (List ℤ)
  | [] => []
  | I :: rest =>
      ((List.range PROG_WIDTH).map (rowAsgAt N pl st pc I))
        :: runRowsAt N pl (stepRegsAt N st I) (pc + 1) rest

theorem runRowsAt_is_the_program_one : runRowsAt pN pLimb = runRows := by
  funext st pc prog
  induction prog generalizing st pc with
  | nil => rfl
  | cons I rest ih =>
      simp only [runRowsAt, runRows, rowAsgAt_is_the_program_one, stepRegsAt_is_the_program_step,
        List.cons.injEq, true_and]
      exact ih _ _

/-! ### §10c — ⚑ THE GENERATOR HAS TO TERMINATE, AND THE CLOSURE ONE DOES NOT.

⚑ **THE DEFECT, DERIVED FROM THE DEFINITIONS.** `RegFile` is `Nat → Nat` and `stepRegsAt N st I` is
a CLOSURE whose body re-reads `st` on every application. Nothing memoises. So the cost of the value
standing in a register at instruction depth `d` is not `d` — reading it re-evaluates the write that
produced it, whose two operands re-evaluate THEIR writes, and the dataflow DAG is unfolded as a
TREE. Kimchi's S-box alone is four chained multiplies, each reading its predecessor twice.

One round (30 instructions) unfolds fine — `roundTrace` emits in about four seconds. The 55-round
absorption does not: 1 652 instructions were still running after **412 CPU-minutes** and left a
zero-byte fixture. That is not a slow machine, it is the wrong asymptotics, and it is why this
rung's absorption had never been proved.

⚑ **AND IT IS A DEFECT OF THE WITNESS GENERATOR, NOT OF THE AIR.** Not one gate, one column, one
constraint or one descriptor byte changes below. The register file becomes a `List Nat` of `NREG`
entries, which Lean evaluates STRICTLY: each write costs one `opResultAt`, each read is an index,
and the whole run is linear.

⚑ **IT IS ALSO NOT A SECOND GENERATOR.** `regsOf_stepVecAt` proves the strict step IS `stepRegsAt`
seen through `regsOf`, and `runRowsVecAt_is_runRowsAt` lifts that to whole programs. So every
denotation §5–§7 established — up to `the_absorb_program_squeezes_the_kimchi_hash` — transfers to
the emitted artifact by REWRITING, not by being re-established on a copy. A generator that agreed
with the semantics only on the cases someone checked is exactly the shape this campaign keeps
finding; there is no case-check here. -/

/-- Read register `r` out of a concrete `NREG`-entry file. Out-of-range reads are `0`, which is what
makes `regsOf` total and the step lemma hypothesis-free. -/
def readVec (rs : List Nat) (r : Nat) : Nat := if r < NREG then rs.getD r 0 else 0

/-- A concrete register file, viewed as the `RegFile` every theorem above is stated over. -/
def regsOf (rs : List Nat) : RegFile := readVec rs

/-- ⚑ **THE STRICT STEP.** The written value is computed ONCE, in a `let`, and the six entries are
built eagerly. That single `let` is the whole difference from `stepRegsAt`. -/
def stepVecAt (N : Nat) (rs : List Nat) (I : Instr) : List Nat :=
  let z := opResultAt N I.op (readVec rs I.xr) (yValue (regsOf rs) I)
  let g : Nat → Nat := fun r => if I.wr < NREG ∧ r = I.wr then z else readVec rs r
  [g 0, g 1, g 2, g 3, g 4, g 5]

/-- ⚑ **AND THE STRICT STEP IS `stepRegsAt`**, at every register index — including the out-of-range
ones, where both sides are `0` because `I.wr < NREG` and `r ≥ NREG` cannot both name the same
register. -/
theorem regsOf_stepVecAt (N : Nat) (rs : List Nat) (I : Instr) :
    regsOf (stepVecAt N rs I) = stepRegsAt N (regsOf rs) I := by
  funext r
  match r with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | (n + 6) =>
      have h1 : ¬ (I.wr < NREG ∧ n + 6 = I.wr) := by unfold NREG; omega
      have h2 : ¬ (n + 6 < NREG) := by unfold NREG; omega
      simp [regsOf, readVec, stepRegsAt, h1, h2]

/-- Run a whole program on the strict file. -/
def runProgVecAt (N : Nat) (rs : List Nat) : List Instr → List Nat
  | [] => rs
  | I :: rest => runProgVecAt N (stepVecAt N rs I) rest

/-- ⚑ **AND RUNNING IT IS `runProgAt`.** -/
theorem regsOf_runProgVecAt (N : Nat) : ∀ (prog : List Instr) (rs : List Nat),
    regsOf (runProgVecAt N rs prog) = runProgAt N (regsOf rs) prog := by
  intro prog
  induction prog with
  | nil => intro rs; rfl
  | cons I rest ih =>
      intro rs
      show regsOf (runProgVecAt N (stepVecAt N rs I) rest)
        = runProgAt N (stepRegsAt N (regsOf rs) I) rest
      rw [← regsOf_stepVecAt]
      exact ih _

/-- The trace, generated over the strict file. The ROW generator is `rowAsgAt` — unchanged, the same
one `rowAsgAt_is_the_program_one` welds to the Fp machine's. -/
def runRowsVecAt (N : Nat) (pl : Nat → ℤ) (rs : List Nat) (pc : Nat) : List Instr → List (List ℤ)
  | [] => []
  | I :: rest =>
      ((List.range PROG_WIDTH).map (rowAsgAt N pl (regsOf rs) pc I))
        :: runRowsVecAt N pl (stepVecAt N rs I) (pc + 1) rest

/-- ⚑ **THE EMITTED TRACE IS THE ONE `runRowsAt` DEFINES**, row for row and cell for cell. This is
the theorem that lets §10a and §10b below emit from the strict generator while every statement about
what the trace MEANS continues to be a statement about `runRowsAt`. -/
theorem runRowsVecAt_is_runRowsAt (N : Nat) (pl : Nat → ℤ) :
    ∀ (prog : List Instr) (rs : List Nat) (pc : Nat),
      runRowsVecAt N pl rs pc prog = runRowsAt N pl (regsOf rs) pc prog := by
  intro prog
  induction prog with
  | nil => intro rs pc; rfl
  | cons I rest ih =>
      intro rs pc
      simp only [runRowsVecAt, runRowsAt, List.cons.injEq, true_and]
      rw [ih, regsOf_stepVecAt]

/-! ### §10a — the round instance's witness. -/

/-- Three full-width Fq state lanes, so every limb of every operand block is exercised on row 0. -/
def ROUND_S0 : Nat := PastaField.Ref.X
def ROUND_S1 : Nat := PastaField.Ref.Y
def ROUND_S2 : Nat := PastaField.Ref.fqAdd PastaField.Ref.X PastaField.Ref.Y

def roundInit : RegFile := fun r =>
  if r = 0 then ROUND_S0 else if r = 1 then ROUND_S1 else if r = 2 then ROUND_S2 else 0

/-- The same initial state as a concrete six-entry file. -/
def roundInitVec : List Nat := [ROUND_S0, ROUND_S1, ROUND_S2, 0, 0, 0]

theorem regsOf_roundInitVec : regsOf roundInitVec = roundInit := by
  funext r
  match r with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | (n + 6) =>
      have h : ¬ (n + 6 < NREG) := by unfold NREG; omega
      simp [regsOf, readVec, roundInit, h]

def roundTrace : List (List ℤ) := runRowsVecAt qN qLimb roundInitVec 0 roundProg

/-- ⚑ **AND THE EMITTED ROUND TRACE IS `runRowsAt`'s.** -/
theorem roundTrace_is_the_program_run :
    roundTrace = runRowsAt qN qLimb roundInit 0 roundProg := by
  rw [roundTrace, runRowsVecAt_is_runRowsAt, regsOf_roundInitVec]

/-- The register file the round program ends in, run strictly. -/
def roundOutVec : List Nat := runProgVecAt qN roundInitVec round0Instrs

/-- The output state the machine reaches, computed by the interpreter — never asserted. -/
def roundOut : List Nat :=
  [regsOf roundOutVec 4, regsOf roundOutVec 5, regsOf roundOutVec 0]

theorem roundOut_is_the_program_output :
    roundOut = tripleList ( runProgAt qN roundInit round0Instrs 4
                          , runProgAt qN roundInit round0Instrs 5
                          , runProgAt qN roundInit round0Instrs 0 ) := by
  have h : regsOf roundOutVec = runProgAt qN roundInit round0Instrs := by
    rw [roundOutVec, regsOf_runProgVecAt, regsOf_roundInitVec]
  simp only [roundOut, tripleList, h]

/-- ⚑ **THE EMITTED ROUND'S OUTPUT IS THE KIMCHI ROUND OF ITS INPUT.** Not a `decide` at a point:
this is `roundSchedule_is_the_kimchi_round` instantiated, so the emitted artifact inherits a
statement that holds at every state. -/
theorem the_emitted_round_output_is_the_kimchi_round :
    roundOut = PastaPoseidonFq.Core.round fqParams (rcsQ.getD 0 [])
      [roundInit 0, roundInit 1, roundInit 2] :=
  roundOut_is_the_program_output.trans
    ((congrArg tripleList (schedule_at_alloc_0 qN mQ (rQ 0) roundInit)).trans
      (roundSchedule_is_the_kimchi_round 0 (roundInit 0) (roundInit 1) (roundInit 2)))

/-- …and the pinned input state is the three full-width lanes the witness starts from. -/
theorem the_round_input_state :
    (roundInit 0, roundInit 1, roundInit 2) = (ROUND_S0, ROUND_S1, ROUND_S2) := rfl

def roundPIs : List ℤ :=
  (List.range SK).map (limbAt ROUND_S0) ++ (List.range SK).map (limbAt ROUND_S1)
    ++ (List.range SK).map (limbAt ROUND_S2)
    ++ (List.range SK).map (limbAt (roundOut.getD 0 0))
    ++ (List.range SK).map (limbAt (roundOut.getD 1 0))
    ++ (List.range SK).map (limbAt (roundOut.getD 2 0))

theorem roundPIs_length : roundPIs.length = 192 := by
  simp [roundPIs, SK]

/-! ### §10b — the absorption's witness, at the values the UPSTREAM sponge was measured on.

⚑ The absorbed pair is `[1, 2]` deliberately: `PastaPoseidonFq` §4 pins
`Core.hash fqParams [1,2] = 18721052396410244253982636774728806624181288577958764574163425862396352099420`,
and that number was produced by `ArithmeticSponge::<Fq, PlonkSpongeConstantsKimchi, 55>::new(
fq_kimchi::static_params())` itself. So the emitted descriptor's OUTPUT PUBLIC INPUT is a value
o1-labs' own implementation returns, and the Rust harness pins its bytes.

The two absorbed lanes are the only small cells in the trace: every round constant is a 254-bit
element, so from round 1 onward every limb of every block is full-width. -/

def ABSORB_X0 : Nat := 1
def ABSORB_X1 : Nat := 2

def absorbInit : RegFile := fun r =>
  if r = 3 then ABSORB_X0 else if r = 4 then ABSORB_X1 else 0

/-- The fresh sponge with the two values already in their source registers, concretely. -/
def absorbInitVec : List Nat := [0, 0, 0, ABSORB_X0, ABSORB_X1, 0]

theorem regsOf_absorbInitVec : regsOf absorbInitVec = absorbInit := by
  funext r
  match r with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | (n + 6) =>
      have h : ¬ (n + 6 < NREG) := by unfold NREG; omega
      simp [regsOf, readVec, absorbInit, h]

def absorbTrace : List (List ℤ) := runRowsVecAt qN qLimb absorbInitVec 0 absorbProg

/-- ⚑ **AND THE EMITTED 2 048-ROW ABSORPTION TRACE IS `runRowsAt`'s** — the trace §7's denotation
is a statement about. Without this theorem the strict generator would be a second, unproved
implementation and every soundness statement above would stop reaching the artifact. -/
theorem absorbTrace_is_the_program_run :
    absorbTrace = runRowsAt qN qLimb absorbInit 0 absorbProg := by
  rw [absorbTrace, runRowsVecAt_is_runRowsAt, regsOf_absorbInitVec]

/-- The register file the absorption ends in, run strictly. -/
def absorbOutVec : List Nat := runProgVecAt qN absorbInitVec absorbCore

/-- The squeezed lane, computed by the interpreter. -/
def absorbOut : Nat := regsOf absorbOutVec (allocAt PastaPoseidon.rounds 0)

theorem absorbOut_is_the_program_output :
    absorbOut = runProgAt qN absorbInit absorbCore (allocAt PastaPoseidon.rounds 0) := by
  rw [absorbOut, absorbOutVec, regsOf_runProgVecAt, regsOf_absorbInitVec]

/-- ⚑ **THE EMITTED ABSORPTION'S OUTPUT IS `Core.hash fqParams [1, 2]`** — the Kimchi Fq sponge's
own answer, for the pair `PastaPoseidonFq` pinned against the upstream state machine. Proved from
the general theorem, so nothing here is a re-checked constant. -/
theorem the_emitted_absorb_output_is_the_kimchi_hash :
    absorbOut = PastaPoseidonFq.Core.hash fqParams [ABSORB_X0, ABSORB_X1] :=
  absorbOut_is_the_program_output.trans
    (the_absorb_program_squeezes_the_kimchi_hash absorbInit rfl rfl rfl (by decide) (by decide))

def absorbPIs : List ℤ :=
  (List.range SK).map (fun _ => (0 : ℤ)) ++ (List.range SK).map (fun _ => (0 : ℤ))
    ++ (List.range SK).map (fun _ => (0 : ℤ))
    ++ (List.range SK).map (limbAt ABSORB_X0) ++ (List.range SK).map (limbAt ABSORB_X1)
    ++ (List.range SK).map (limbAt absorbOut)

theorem absorbPIs_length : absorbPIs.length = 192 := by
  simp [absorbPIs, SK]

/-- ⚑ **AND THE FRESH-SPONGE PINS ARE THE ZERO VECTOR.** The statement the absorption descriptor
makes is `Core.hash` only if the three initial state lanes are pinned to zero; a verifier that
supplied a different initial state would be checking a different (still true) sentence about a
sponge that was not fresh. Stated so that is a fact about the emitted public inputs and not a
convention. -/
theorem the_absorb_pins_a_fresh_sponge :
    (absorbPIs.take (3 * SK)).all (fun v => decide (v = 0)) = true := by decide

#assert_axioms alu_add_forces_fq
#assert_axioms alu_sub_forces_fq
#assert_axioms ref_ops_are_the_pasta_ones
#assert_axioms opResultAt_is_the_program_interpreter
#assert_axioms stepRegsAt_is_the_program_step
#assert_axioms runProgAt_append
#assert_axioms the_constants_are_PastaPoseidonFq_s
#assert_axioms roundInstrs_length
#assert_axioms roundInstrs_opcode_split
#assert_axioms the_allocation_hands_off
#assert_axioms the_allocation_has_period_three
#assert_axioms the_allocation_is_injective
#assert_axioms alloc_case_0
#assert_axioms alloc_case_1
#assert_axioms alloc_case_2
#assert_axioms schedule_at_alloc_0
#assert_axioms schedule_at_alloc_4
#assert_axioms schedule_at_alloc_2
#assert_axioms refMul_cast
#assert_axioms refAdd_cast
#assert_axioms sboxSchedule_cast
#assert_axioms coreSbox_cast
#assert_axioms nat_of_zmod_eq
#assert_axioms mdsRowSchedule_agrees
#assert_axioms roundSchedule_is_the_kimchi_round
#assert_axioms permInstrs_length
#assert_axioms the_permutation_program_computes_the_kimchi_permutation
#assert_axioms the_absorbed_value_is_not_a_rom_constant
#assert_axioms the_rom_pins_the_absorb_lane
#assert_axioms the_rom_pins_the_round_constant_schedule
#assert_axioms absorbCore_length
#assert_axioms the_absorb_program_computes_the_kimchi_sponge
#assert_axioms the_absorb_program_squeezes_the_kimchi_hash
#assert_axioms the_census_round_is_the_emitted_round
#assert_axioms the_census_opcode_split_is_the_emitted_one
#assert_axioms the_census_perm_is_the_emitted_permutation
#assert_axioms the_transcript_stage_is_148_emitted_permutations
#assert_axioms a_multiply_only_round_underprices_the_emitted_permutation
#assert_axioms the_transcript_stage_fits_one_rom
#assert_axioms roundProg_length
#assert_axioms absorbProg_length
#assert_axioms the_last_instruction_writes_nothing
#assert_axioms roundAir_mainRailOk
#assert_axioms absorbAir_mainRailOk
#assert_axioms the_sponge_roms_fit
#assert_axioms arithAsgAt_is_the_program_one
#assert_axioms rowAsgAt_is_the_program_one
#assert_axioms runRowsAt_is_the_program_one
#assert_axioms regsOf_stepVecAt
#assert_axioms regsOf_runProgVecAt
#assert_axioms runRowsVecAt_is_runRowsAt
#assert_axioms regsOf_roundInitVec
#assert_axioms roundTrace_is_the_program_run
#assert_axioms roundOut_is_the_program_output
#assert_axioms regsOf_absorbInitVec
#assert_axioms absorbTrace_is_the_program_run
#assert_axioms absorbOut_is_the_program_output
#assert_axioms the_emitted_round_output_is_the_kimchi_round
#assert_axioms round0Instrs_is_roundAt_0
#assert_axioms the_round_input_state
#assert_axioms roundPIs_length
#assert_axioms the_emitted_absorb_output_is_the_kimchi_hash
#assert_axioms absorbPIs_length
#assert_axioms the_absorb_pins_a_fresh_sponge
#assert_axioms pinBlock_regPin
#assert_axioms roundPins_regPin
#assert_axioms absorbPins_regPin
#assert_axioms roundAir_pinsTied
#assert_axioms absorbAir_pinsTied
#assert_axioms roundDesc_certified
#assert_axioms roundDesc_eq_lowerAir
#assert_axioms absorbDesc_certified
#assert_axioms absorbDesc_eq_lowerAir

end Dregg2.Circuit.Emit.MinaWrapVerifierSponge
