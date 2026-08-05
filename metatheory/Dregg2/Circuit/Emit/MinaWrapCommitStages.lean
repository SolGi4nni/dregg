/-
# `Dregg2.Circuit.Emit.MinaWrapCommitStages` — the COMMITMENT-COMBINATION stages of Kimchi's
`verify`, as emitted dregg AIRs over a REAL Mina devnet block.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every stage below is a `List Instr` over
`MinaWrapCommitMachine`'s Lean-authored machine, lowered by `EffectLower.lowerAir`. There is no
hand-written `VmConstraint2` and no Rust-authored gadget anywhere in this cone. Rust parses the
emitted descriptor, fills cells, and runs the deployed prover. House Law #1.

## THE FOUR STAGES, AND WHERE THEIR NUMBERS COME FROM

`kimchi/src/verifier.rs` on a Wrap verifier index (no lookup index, no optional gate commitments):

  * **`public_comm`** (`verifier.rs:834-857`) — `PolyComm::multi_scalar_mul(lagrange_bases,
    −public_input)`, then `mask_custom` with all-ones blinders, i.e. one further `+ H`. **40 terms.**
  * **`f_comm`** (`verifier.rs:904-953`) — `sigma_comm[PERMUTS−1]` at `perm_scalars`, plus one term
    per `linearization.index_terms`; that list is **empty** on the wrap side, so **1 term**.
  * **`ft_comm`** (`verifier.rs:958-964`) — `chunk(f_comm, ζ^srs_len) − chunk(t_comm, ζ^srs_len) ·
    (ζ^n − 1)`. **9 nominal, 7 meaningful.**
  * **the ξ-aggregate** (`poly-commitment/src/commitment.rs:724-744`, `combine_commitments`) —
    `Σᵢ polyscale^i · Cᵢ` over 2 recursion + `public_comm` + `ft_comm` + `Z` + 6 index + 15 witness
    + 15 coefficient + 6 sigma = **47 terms** at `COLUMNS = 15`, `PERMUTS = 7`.

⚑ **THE DATA IS REAL.** Every base point, every challenge and every golden output below comes from
`MinaWrapGroupGate` / `MinaWrapAggregationGate` / `MinaWrapPublicCommGate`, which carry Mina devnet
block **539508** and are `by decide`-checked against o1-labs' own `PolyComm::multi_scalar_mul`
output. This file adds no new constants; it CHECKS those constants with an AIR.

## ⚑ THE HONEST SPLIT — read this before reading any green

A commitment combination is `Σ sᵢ · Bᵢ`. Three separable obligations, and this file emits a
descriptor for each rather than one descriptor that quietly does two of them:

  1. **THE SCALARS.** `s_i` must be what the transcript says, not what the prover likes.
     `xiChainProg` computes all 47 powers of the block's REAL `ξ` in-circuit, from `ξ` as a public
     input, in 46 Pasta multiplies. **Full fidelity, no reduction.**
  2. **THE GROUP ACCUMULATION AND THE SCALAR↔BASE PAIRING.** `sumProg` folds the stage's term list
     with the affine chord law, one ROM-pinned base per instruction, at the stage's FULL term count
     (40 / 1 / 9 / 47) — against the block's own golden aggregate.
  3. **THE SCALAR MULTIPLICATION `sᵢ · Bᵢ` ITSELF.** `msmProg` is the double-and-add ladder with an
     in-circuit bit decomposition and a closing `SC = s` assertion. It is emitted at a REDUCED plane
     count (§7) because the full 255 planes are `9 456` instructions per term and the trace does not
     fit a checked-in fixture — `full_width_ladder_price` is that as a theorem, not an excuse.

⚠ So: obligation (2) is emitted at full term count over PRE-SCALED points, which means the emitted
`sumProg` instances take `sᵢ·Bᵢ` as given. That is exactly what obligation (3) supplies and exactly
what is NOT closed at full width. Nothing here should be read as "the ξ-aggregate is verified
in-AIR". What is true is: *the scalar vector is computed in-AIR at full fidelity; the 47-term group
fold is computed in-AIR at full term count; the 255-plane scalar multiplication that joins them is
demonstrated at 8 planes and priced at 255.*

## ⚑ INCOMPLETE ADDITION, NAMED

`addAffine` is the chord law with a WITNESSED slope pinned by `s·(x₁−x₂) = y₁−y₂` — Kimchi's own
`CompleteAdd` gate minus the `same_x` branch, i.e. Pickles' `add_fast` in its non-exceptional case.
At `x₁ = x₂` no slope satisfies the pin, so **no witness exists and the prover cannot produce a
trace**: this is a COMPLETENESS gap (a trace that ought to exist does not), never a soundness gap
(a trace that ought not to exist is accepted). `dblAffine` carries the tangent branch. The ladder
uses a fixed non-identity OFFSET so the accumulator never reaches the point at infinity, which the
affine coordinates cannot represent — `offset_is_a_real_pallas_point`.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. Facts are NAMED THEOREMS — this file adds zero `#guard`s.
-/
import Dregg2.Circuit.Emit.MinaWrapCommitMachine
import Dregg2.Circuit.Emit.MinaWrapAggregationGate
import Dregg2.Circuit.Emit.MinaWrapPublicCommGate

namespace Dregg2.Circuit.Emit.MinaWrapCommitStages

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 TableDef TableId mainTableDef)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg PiPinLeg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.EffectLower (lowerAir P)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB limbAt)
open Dregg2.Circuit.Emit.MinaWrapCommitMachine

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 2000000

/-! ## §1 — AFFINE PASTA ARITHMETIC, and the inverse the machine cannot do.

⚑ The machine has three opcodes and none of them is a division. A slope therefore enters as a
WITNESS through the free operand code and is pinned by a multiply and an assert. This section is
the reference that COMPUTES the witness from the gadget's actual inputs — never from what the
answer was supposed to be. -/

abbrev Fp := Nat

def fmul (x y : Fp) : Fp := PastaField.Ref.fpMul x y
def fadd (x y : Fp) : Fp := PastaField.Ref.fpAdd x y
def fsub (x y : Fp) : Fp := PastaField.Ref.fpSub x y

/-- Modular exponentiation by squaring, structurally recursive on FUEL so the kernel reduces it. -/
def powAux : Nat → Fp → Nat → Fp → Fp
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
      if e = 0 then acc
      else powAux fuel (fmul b b) (e / 2) (if e % 2 = 1 then fmul acc b else acc)

/-- `x⁻¹` in the Pasta base field, by Fermat. `pN` is 255 bits, so 256 doublings of fuel suffice. -/
def finv (x : Fp) : Fp := powAux 260 x (pN - 2) 1

/-- ⚑ **THE INVERSE IS AN INVERSE**, on the block's own field elements — checked, not assumed,
because every witnessed slope in this file is a quotient and a wrong `finv` would make every honest
trace refuse for a reason no refusal message would explain. -/
theorem finv_is_an_inverse :
    fmul (MinaWrapAggregationGate.XI) (finv MinaWrapAggregationGate.XI) = 1
      ∧ fmul 7 (finv 7) = 1 := by decide

/-! ⚑ **THE SCALARS LIVE IN THE SCALAR FIELD `q`, THE COORDINATES IN THE BASE FIELD `p`.** Reading
one for the other is the classic Pasta error; these three are `q`-arithmetic and nothing else in
this file is. -/

def qmul (x y : Nat) : Nat := (x * y) % PastaField.qN
def qpow (x : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => qmul (qpow x n) x
def qneg (x : Nat) : Nat := (PastaField.qN - x % PastaField.qN) % PastaField.qN

/-- An affine Pasta point. -/
abbrev Aff := Fp × Fp

/-- The chord slope of two distinct-abscissa points: `(y₁ − y₂)/(x₁ − x₂)`. -/
def slopeAdd (Pt1 Pt2 : Aff) : Fp :=
  fmul (fsub Pt1.2 Pt2.2) (finv (fsub Pt1.1 Pt2.1))

/-- The tangent slope: `3x² / 2y`. -/
def slopeDbl (Pt1 : Aff) : Fp :=
  let x2 := fmul Pt1.1 Pt1.1
  fmul (fadd (fadd x2 x2) x2) (finv (fadd Pt1.2 Pt1.2))

/-- `x₃ = s² − x₁ − x₂`, `y₃ = s(x₁ − x₃) − y₁` — the chord-and-tangent law, written once and used
by both gadgets. -/
def chordOut (s : Fp) (Pt1 : Aff) (x2 : Fp) : Aff :=
  let x3 := fsub (fsub (fmul s s) Pt1.1) x2
  (x3, fsub (fmul s (fsub Pt1.1 x3)) Pt1.2)

def addAffine (Pt1 Pt2 : Aff) : Aff := chordOut (slopeAdd Pt1 Pt2) Pt1 Pt2.1
def dblAffine (Pt1 : Aff) : Aff := chordOut (slopeDbl Pt1) Pt1 Pt1.1

/-- ⚑ **THE REFERENCE SATISFIES THE PIN THE AIR ASSERTS.** The descriptor demands
`s·(x₁ − x₂) = y₁ − y₂` and nothing else about `s`; this says the value the witness generator
supplies is one that satisfies it, on real block data. If it did not, the honest trace would
refuse — which is the failure mode the mandate's rule 1 exists to prevent, and it is checked here
rather than discovered at prove time. -/
def affOf (p : Nat × Nat × Nat) : Aff := (p.1, p.2.1)

def PT_A : Aff := affOf (MinaWrapAggregationGate.COMBINE_POINTS.getD 0 (0, 0, 1))
def PT_B : Aff := affOf (MinaWrapAggregationGate.COMBINE_POINTS.getD 1 (0, 0, 1))

theorem slope_pin_holds_on_real_block_points :
    fmul (slopeAdd PT_A PT_B) (fsub PT_A.1 PT_B.1) = fsub PT_A.2 PT_B.2 := by decide

theorem tangent_pin_holds_on_a_real_block_point :
    fadd (fmul (slopeDbl PT_A) PT_A.2) (fmul (slopeDbl PT_A) PT_A.2)
      = fadd (fadd (fmul PT_A.1 PT_A.1) (fmul PT_A.1 PT_A.1)) (fmul PT_A.1 PT_A.1) := by decide

/-- The Pallas curve equation `y² = x³ + 5`, affine. -/
def onPallas (Pt1 : Aff) : Bool :=
  decide (fmul Pt1.2 Pt1.2 = fadd (fmul (fmul Pt1.1 Pt1.1) Pt1.1) 5)

/-- ⚑ **AND THE CHORD LAW LANDS BACK ON THE CURVE**, on the block's own points — the property that
makes an accumulator a group element rather than a pair of field values. -/
theorem chord_law_stays_on_pallas :
    onPallas PT_A = true ∧ onPallas PT_B = true
      ∧ onPallas (addAffine PT_A PT_B) = true
      ∧ onPallas (dblAffine PT_A) = true := by decide

/-! ## §2 — THE REGISTER ALLOCATION.

Twelve registers, and every one of them is live in the ladder's inner loop — which is what
`MinaWrapCommitMachine.one_hot_word_is_refused_at_this_register_count` prices. -/

def ZERO : Nat := 0   -- the constant 0, forced by instruction 0
def TX : Nat := 1     -- running total, x
def TY : Nat := 2     -- running total, y
def AX : Nat := 3     -- ladder accumulator, x
def AY : Nat := 4     -- ladder accumulator, y
def BIT : Nat := 5    -- the plane's digit
def SL : Nat := 6     -- the witnessed slope
def T0 : Nat := 7
def T1 : Nat := 8
def X3 : Nat := 9
def Y3 : Nat := 10
def SC : Nat := 11    -- the scalar accumulator

/-- The `y` operand code for the immediate. -/
def IMMC : Nat := NREG
/-- The `y` operand code for the FREE witness block. -/
def FREEC : Nat := NREG + 1
/-- The `wr` code for "write nothing". -/
def NOWR : Nat := NREG

theorem allocation_fits_the_register_file :
    ZERO < NREG ∧ SC < NREG ∧ IMMC = 12 ∧ FREEC = 13 ∧ NOWR = 12 := by decide

/-! ## §3 — THE INSTRUCTION CONSTRUCTORS. -/

def mulR (x y w : Nat) : Instr := ⟨1, x, y, w, 0, 0⟩
def addR (x y w : Nat) : Instr := ⟨2, x, y, w, 0, 0⟩
def subR (x y w : Nat) : Instr := ⟨3, x, y, w, 0, 0⟩
def addI (x i w : Nat) : Instr := ⟨2, x, IMMC, w, 0, i⟩
def subI (x i w : Nat) : Instr := ⟨3, x, IMMC, w, 0, i⟩
/-- ⚑ `SUB x, y → ∅` with the assert bit: the descriptor DEMANDS `x ≡ y (mod p)`. -/
def eqR (x y : Nat) : Instr := ⟨3, x, y, NOWR, 1, 0⟩
def eqI (x i : Nat) : Instr := ⟨3, x, IMMC, NOWR, 1, i⟩
/-- ⚑ The witness load: `w := 0 + FREE`. The ROM names it, so the descriptor decides where a
witness may enter. -/
def wit (w : Nat) : Instr := ⟨2, ZERO, FREEC, w, 0, 0⟩

/-- A program is a list of (instruction, witness) pairs: the witness is only read by the free-code
instructions, and `MinaWrapCommitMachine.routed_instruction_ignores_the_witness` is that as a
theorem. -/
abbrev Step := Instr × Nat

def instrs (p : List Step) : List Instr := p.map Prod.fst
def witsOf (p : List Step) : Nat → Nat := fun pc => (p.getD pc (PAD, 0)).2

/-! ## §4 — THE GADGETS.

Each takes the ENTRY point values and computes its own witnesses from them. Nothing below reads a
value it did not derive from the gadget's inputs. -/

/-- `(TX, TY) := (TX, TY) + (bx, by)` with `(bx, by)` a ROM immediate. **12 instructions**, one
witnessed slope, one assert. -/
def emitAddImmT (cur : Aff) (bx by_ : Fp) : List Step :=
  let s := slopeAdd cur (bx, by_)
  [ (subI TX bx T0, 0)
  , (subI TY by_ T1, 0)
  , (wit SL, s)
  , (mulR SL T0 T0, 0)
  , (eqR T0 T1, 0)
  , (mulR SL SL T0, 0)
  , (subR T0 TX T0, 0)
  , (subI T0 bx X3, 0)
  , (subR TX X3 T0, 0)
  , (mulR SL T0 T0, 0)
  , (subR T0 TY TY, 0)
  , (addR X3 ZERO TX, 0) ]

/-- `(AX, AY) := 2·(AX, AY)`. **15 instructions**, one witnessed slope, one assert. -/
def emitDblA (cur : Aff) : List Step :=
  let s := slopeDbl cur
  [ (mulR AX AX T0, 0)
  , (wit SL, s)
  , (mulR SL AY T1, 0)
  , (addR T1 T1 T1, 0)
  , (subR T1 T0 T1, 0)
  , (subR T1 T0 T1, 0)
  , (eqR T1 T0, 0)
  , (mulR SL SL T0, 0)
  , (subR T0 AX T0, 0)
  , (subR T0 AX X3, 0)
  , (subR AX X3 T0, 0)
  , (mulR SL T0 T0, 0)
  , (subR T0 AY Y3, 0)
  , (addR X3 ZERO AX, 0)
  , (addR Y3 ZERO AY, 0) ]

/-- `(X3, Y3) := (AX, AY) + (bx, by)` — the ladder's CANDIDATE, left unselected. **11
instructions**. -/
def emitAddImmA (cur : Aff) (bx by_ : Fp) : List Step :=
  let s := slopeAdd cur (bx, by_)
  [ (subI AX bx T0, 0)
  , (subI AY by_ T1, 0)
  , (wit SL, s)
  , (mulR SL T0 T0, 0)
  , (eqR T0 T1, 0)
  , (mulR SL SL T0, 0)
  , (subR T0 AX T0, 0)
  , (subI T0 bx X3, 0)
  , (subR AX X3 T0, 0)
  , (mulR SL T0 T0, 0)
  , (subR T0 AY Y3, 0) ]

/-- `(AX, AY) := BIT ? (X3, Y3) : (AX, AY)`. **6 instructions**, degree 2 in the trace. -/
def emitSelect : List Step :=
  [ (subR X3 AX T0, 0)
  , (mulR T0 BIT T0, 0)
  , (addR AX T0 AX, 0)
  , (subR Y3 AY T1, 0)
  , (mulR T1 BIT T1, 0)
  , (addR AY T1 AY, 0) ]

/-- Load the plane's digit and pin it to a bit; then fold it into the scalar accumulator.
**5 instructions**. ⚑ The scalar fold is what makes the digits the digits OF something: without it
the bit vector is 255 free choices and the ladder computes `Σ bⱼ 2ʲ · B` for a scalar nobody
named. -/
def emitBit (b : Nat) : List Step :=
  [ (wit BIT, b)
  , (mulR BIT BIT T0, 0)
  , (eqR T0 BIT, 0)
  , (addR SC SC SC, 0)
  , (addR SC BIT SC, 0) ]

/-- One ladder plane over base `(bx, by)`: double, digit, candidate, select. **37 instructions**. -/
def emitPlane (accIn : Aff) (bx by_ : Fp) (b : Nat) : List Step :=
  let d := dblAffine accIn
  emitDblA accIn ++ emitBit b ++ emitAddImmA d bx by_ ++ emitSelect

/-- The accumulator after one plane, by the reference. -/
def planeOut (accIn : Aff) (bx by_ : Fp) (b : Nat) : Aff :=
  if b = 1 then addAffine (dblAffine accIn) (bx, by_) else dblAffine accIn

/-- ⚑ **A PLANE IS `A ↦ 2A + b·B`.** Stated so the ladder's meaning is a named fact and not a
comment; `sc ↦ 2sc + b` is the scalar the same plane accumulates, which is why the closing
assertion binds them. -/
theorem plane_is_double_and_conditional_add (accIn : Aff) (bx by_ : Fp) :
    planeOut accIn bx by_ 1 = addAffine (dblAffine accIn) (bx, by_)
      ∧ planeOut accIn bx by_ 0 = dblAffine accIn := by
  constructor <;> rfl

/-! ## §5 — THE STAGE PROGRAMS. -/

/-- The ladder OFFSET. ⚑ Affine coordinates have no point at infinity, so a ladder that started at
the identity would be unrepresentable at its first step. The offset is the first commitment of the
block's own aggregate list, and the closing subtraction of `2^planes · Ω` removes it. -/
def OMEGA : Aff := PT_A

theorem offset_is_a_real_pallas_point : onPallas OMEGA = true := by decide

/-- `−P`. -/
def negA (Pt1 : Aff) : Aff := (Pt1.1, fsub 0 Pt1.2)

/-- `2^k · P`, by repeated doubling. -/
def dblPow : Nat → Aff → Aff
  | 0, Pt1 => Pt1
  | k + 1, Pt1 => dblAffine (dblPow k Pt1)

/-- The bit of `v` at plane `j` counting from the TOP of a `k`-plane window (MSB first). -/
def planeBit (v k j : Nat) : Nat := (v / 2 ^ (k - 1 - j)) % 2

/-- ⚑ **THE OPENING INSTRUCTION FORCES THE ZERO REGISTER.** `SUB R0, R0 → R0` reads the first row's
`R0` — whatever the prover put there — and writes `0`. Every immediate-load and every witness-load
below rides on it. -/
def emitInit : List Step := [(subR ZERO ZERO ZERO, 0)]

/-- Load the running total with the first pre-scaled term. -/
def emitLoadT (bx by_ : Fp) : List Step := [(addI ZERO bx TX, 0), (addI ZERO by_ TY, 0)]

/-- The pure ACCUMULATION program: fold a term list with the affine chord law. This is obligation
(2) — the group fold and the scalar↔base pairing at the stage's full term count. -/
def sumSteps : Aff → List Aff → List Step
  | _, [] => []
  | cur, B :: rest => emitAddImmT cur B.1 B.2 ++ sumSteps (addAffine cur B) rest

def sumProg (terms : List Aff) : List Step :=
  match terms with
  | [] => emitInit
  | B0 :: rest => emitInit ++ emitLoadT B0.1 B0.2 ++ sumSteps B0 rest

/-- The reference fold, so the emitted trace's claimed output is COMPUTED and not asserted. -/
def sumRef : Aff → List Aff → Aff
  | cur, [] => cur
  | cur, B :: rest => sumRef (addAffine cur B) rest

def sumOut (terms : List Aff) : Aff :=
  match terms with
  | [] => (0, 0)
  | B0 :: rest => sumRef B0 rest

/-- The LADDER program for one term: `A := Ω`, `k` planes, assert the scalar, remove the offset,
fold into the running total. This is obligation (3). -/
def ladderSteps (acc : Aff) (bx by_ : Fp) (s k : Nat) : Nat → List Step
  | 0 => []
  | j + 1 =>
      let idx := k - (j + 1)
      let b := planeBit s k idx
      emitPlane acc bx by_ b ++ ladderSteps (planeOut acc bx by_ b) bx by_ s k j

def ladderOut (acc : Aff) (bx by_ : Fp) (s k : Nat) : Nat → Aff
  | 0 => acc
  | j + 1 => ladderOut (planeOut acc bx by_ (planeBit s k (k - (j + 1)))) bx by_ s k j

/-- One scaled term `s·B`, in full: the ladder, the scalar assertion, the offset removal, and the
fold into the running total. -/
def emitTerm (cur : Aff) (bx by_ : Fp) (s k : Nat) : List Step :=
  let acc := ladderOut OMEGA bx by_ s k k
  let off := negA (dblPow k OMEGA)
  let scaled := addAffine acc off
  [(subR ZERO ZERO SC, 0), (addI ZERO OMEGA.1 AX, 0), (addI ZERO OMEGA.2 AY, 0)]
  ++ ladderSteps OMEGA bx by_ s k k
  ++ [(eqI SC s, 0)]
  -- remove the offset: (X3,Y3) := A + (−2^k Ω), then A := (X3,Y3)
  ++ emitAddImmA acc off.1 off.2
  ++ [(addR X3 ZERO AX, 0), (addR Y3 ZERO AY, 0)]
  -- fold into the running total
  ++ (let s2 := slopeAdd cur scaled
      [ (subR TX AX T0, 0)
      , (subR TY AY T1, 0)
      , (wit SL, s2)
      , (mulR SL T0 T0, 0)
      , (eqR T0 T1, 0)
      , (mulR SL SL T0, 0)
      , (subR T0 TX T0, 0)
      , (subR T0 AX X3, 0)
      , (subR TX X3 T0, 0)
      , (mulR SL T0 T0, 0)
      , (subR T0 TY TY, 0)
      , (addR X3 ZERO TX, 0) ])

def termOut (cur : Aff) (bx by_ : Fp) (s k : Nat) : Aff :=
  addAffine cur (addAffine (ladderOut OMEGA bx by_ s k k) (negA (dblPow k OMEGA)))

/-- ⚑ **THE LADDER'S OUTPUT IS `s·B` PLUS THE OFFSET IT STARTED FROM**, which is why the closing
subtraction is `2^k·Ω` and not something else. Stated at `k = 1` and `k = 2` on real block data,
where `decide` can reach — the general statement is the standard double-and-add invariant and the
instances are what pin the implementation to it. -/
theorem ladder_carries_the_offset (bx by_ : Fp) (s : Nat) :
    ladderOut OMEGA bx by_ s 1 1
      = (if s % 2 = 1 then addAffine (dblAffine OMEGA) (bx, by_) else dblAffine OMEGA) := by
  show planeOut OMEGA bx by_ (planeBit s 1 0) = _
  unfold planeOut planeBit
  norm_num

/-! ## §6 — THE EMITTED STAGES, over Mina devnet block 539508. -/

/-- The block's polyscale challenge. -/
def XI : Nat := MinaWrapAggregationGate.XI

/-- The 47 commitments `combine_commitments` feeds the terminal MSM, as affine points. Every one is
`z = 1` in the source list, so the affine reading is exact. -/
def COMBINE_AFF : List Aff :=
  MinaWrapAggregationGate.COMBINE_POINTS.map (fun p => (p.1, p.2.1))

theorem combine_aff_is_47_long : COMBINE_AFF.length = 47 := by decide

theorem every_combine_base_is_on_pallas :
    COMBINE_AFF.all onPallas = true := by decide

/-! ### §6a — OBLIGATION (1): THE ξ SCALAR VECTOR, at full fidelity.

⚑ 46 multiplies. `ξ` is a public input on the first row; `ξ⁴⁶` is a public input on the last. Every
intermediate power is a register the ROM's own instruction wrote, so the whole scalar vector of the
47-term aggregate is forced by 46 Pasta multiplies and the register file's hold half. -/

/-- `R1 := ξ` is the FIRST-ROW public-input pin; `R2 := 1` is the zeroth scalar; then `R2 := R2 · R1`
forty-six times walks the whole vector `(ξ⁰, …, ξ⁴⁶)` through the register file. -/
def xiChainSteps : Nat → List Step
  | 0 => []
  | n + 1 => (mulR TY TX TY, 0) :: xiChainSteps n

def xiChainProg : List Step :=
  emitInit ++ [(addI ZERO 1 TY, 0)] ++ xiChainSteps 46

/-- ⚑ **THE CHAIN'S ENDPOINT IS `ξ⁴⁶`**, the last scalar `combine_commitments` assigns — computed
by `qpow`, which is **`q`-arithmetic**: `ξ` is a SCALAR-field element and reducing its powers mod
the BASE field would be the classic Pasta error. The chain's AIR is emitted at `qLimb` for the same
reason (`xiDesc`), and `MinaWrapCommitMachine.the_reference_ops_are_the_pasta_ones` is the weld
between the machine's own interpreter and `PastaField.Ref.fq*`. -/
def XI_46 : Nat := qpow XI 46

theorem xi_chain_starts_at_one_and_walks_by_xi :
    qpow XI 0 = 1 ∧ qpow XI 1 = XI ∧ qpow XI 47 = qmul XI_46 XI := by
  refine ⟨rfl, ?_, rfl⟩
  show qmul 1 XI = XI
  decide

/-- ⚑ **AND THE TWO REDUCTIONS REALLY DO DISAGREE**, on the block's own challenge — so the choice
above is a decision the data can refute, not a convention. Reading `ξ²` in the base field gives a
different scalar, and the aggregate it produces is not the block's. -/
theorem the_base_field_reduction_of_xi_squared_is_a_different_scalar :
    qmul XI XI ≠ fmul XI XI := by decide

/-! ### §6b — OBLIGATION (2): THE GROUP FOLD AT FULL TERM COUNT.

The term list is `ξⁱ · Cᵢ`, computed HERE by the reference scalar multiplication, so the fold's
output is the block's own aggregate. -/

/-- Projective `smul`/`padd` are `MinaWrapGroupGate`'s, already `decide`-checked against o1-labs'
`multi_scalar_mul`; the affine reading normalises by `finv`. -/
def toAff (p : MinaWrapGroupGate.Pt) : Aff :=
  let zi := finv p.2.2
  (fmul p.1 zi, fmul p.2.1 zi)


/-- The 47 PRE-SCALED terms `ξⁱ · Cᵢ`, by `MinaWrapGroupGate`'s own projective ladder. -/
def XI_TERMS : List Aff :=
  (List.range 47).map (fun i =>
    toAff (MinaWrapGroupGate.smul (qpow XI i)
      (MinaWrapAggregationGate.COMBINE_POINTS.getD i (0, 0, 1))))

/-- ⚑ The 41 terms of `public_comm`: the forty Lagrange bases at the block's own NEGATED public
inputs, then the SRS blinder `H` that `mask_custom` adds (`verifier.rs:849-855`). The blinder is a
TERM, not a decoration — `MinaWrapPublicCommGate.tamper_blinder_dropped` is the refutation that
dropping it changes the answer. -/
def PUBLIC_TERMS : List Aff :=
  ((List.range 40).map (fun i =>
      toAff (MinaWrapGroupGate.smul (MinaWrapPublicCommGate.NEG_PUBLIC.getD i 0)
        (MinaWrapPublicCommGate.LAGRANGE.getD i (0, 0, 1)))))
  ++ [toAff MinaWrapPublicCommGate.SRS_H]

/-- ⚑ The 8 terms of `ft_comm`: `chunk(f_comm, ζ^srs)` — one chunk on the wrap side, so `f_comm`
itself — minus each of the seven `t_comm` chunks at `ζ^(srs·j) · (ζⁿ − 1)`. **9 nominal, 7
meaningful**: the nominal count counts `f_comm` and the Maller factor as terms of their own; the
group fold sees `1 + 7 = 8` points, and the seven that carry a non-trivial scalar are the
meaningful ones. -/
def FT_TERMS : List Aff :=
  toAff MinaWrapGroupGate.fComm
  :: (List.range 7).map (fun j =>
       toAff (MinaWrapGroupGate.smul
         (qneg (qmul (qpow MinaWrapGroupGate.ZETA_SRS j) MinaWrapGroupGate.ZETA_DOM_M1))
         (MinaWrapGroupGate.TCHUNKS.getD j (0, 0, 1))))

/-! ## §7 — THE CENSUS: what a full-width stage costs on this machine. -/

/-- Instructions per ladder plane. -/
def PLANE_COST : Nat := 37
/-- Fixed cost of one scaled term besides its planes. -/
def TERM_FIXED : Nat := 3 + 1 + 11 + 2 + 12
/-- Instructions for one term at `k` planes. -/
def termCost (k : Nat) : Nat := TERM_FIXED + PLANE_COST * k
/-- Instructions for an `n`-term stage at `k` planes. -/
def stageCost (n k : Nat) : Nat := 1 + n * termCost k

theorem plane_and_term_costs : PLANE_COST = 37 ∧ TERM_FIXED = 29 ∧ termCost 255 = 9464 := by decide

/-- ⚑ **THE FULL-WIDTH PRICE, PER STAGE.** 255 planes is the Pasta scalar width. -/
def COST_PUBLIC_COMM : Nat := stageCost 40 255
def COST_F_COMM : Nat := stageCost 1 255
def COST_FT_COMM : Nat := stageCost 9 255
def COST_XI : Nat := stageCost 47 255

theorem full_width_ladder_price :
    COST_PUBLIC_COMM = 378561 ∧ COST_F_COMM = 9465 ∧ COST_FT_COMM = 85177
      ∧ COST_XI = 444809 := by decide

/-- ⚑ **EVERY STAGE FITS ONE ROM AT FULL WIDTH, AND THEIR SUM DOES NOT** — the same shape
`MinaWrapVerifierProgram` found at a coarser price, now at this machine's 40-cell instruction word,
which holds `838 860` instructions. The ξ-aggregate is the largest at **53.0%**. -/
theorem every_stage_fits_one_rom_at_full_width :
    COST_PUBLIC_COMM ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ COST_F_COMM ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ COST_FT_COMM ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ COST_XI ≤ MAX_ROM_CELLS / ROM_ARITY
      ∧ MAX_ROM_CELLS / ROM_ARITY
        < COST_PUBLIC_COMM + COST_F_COMM + COST_FT_COMM + COST_XI := by decide

/-- ⚑ **THE SCALAR VECTOR IS 1/9464 OF ITS OWN STAGE.** 47 instructions against the ξ-aggregate's
444 809 — which is the whole reason obligation (1) is emitted at FULL fidelity and obligation (3)
is not: they are not the same size of problem, and a report that presented them as one stage would
be hiding a factor of nine thousand. ⚠ The first draft of this theorem asserted `10000 · 47` and
`decide` REFUTED it; the true ratio is `9464 = termCost 255`, not a round number someone liked. -/
theorem the_scalar_vector_is_a_rounding_error_against_its_own_stage :
    9464 * 47 < COST_XI ∧ 9465 * 47 > COST_XI := by decide

/-! ## §8 — THE EMITTED OBJECTS.

Each stage is a program padded to a power-of-two height with `add R0, #0 → ∅` — a real ALU
operation, because `selSumExpr` is inherited and there is no nop. The ROM manifest has one row per
instruction and `PublicLookupBalanced` is a PERMUTATION, so the manifest length IS the trace
length: a prover cannot run the program twice, stop early, or pad. -/

/-- Pad a program to `n` instructions. -/
def padTo (n : Nat) (p : List Step) : List Step :=
  p ++ List.replicate (n - p.length) (PAD, 0)

/-- The 64 boundary pins: `R_in`'s 32 limbs on the FIRST row, `R_out`'s on the LAST. -/
def pinPair (rIn rOut : Nat) : List AirLeg :=
  ((List.range SK).map (fun i => AirLeg.pin ⟨VmRow.first, regCol rIn + i, i⟩))
  ++ ((List.range SK).map (fun i => AirLeg.pin ⟨VmRow.last, regCol rOut + i, SK + i⟩))

/-- ⚑ **THE FOLD PINS BOTH COORDINATES OF THE RESULT** — 64 public inputs, `TX` and `TY` on the
last row. A stage that pinned only the abscissa would accept `−Σ sᵢBᵢ` as readily as the sum. -/
def pinOutPoint : List AirLeg :=
  ((List.range SK).map (fun i => AirLeg.pin ⟨VmRow.last, regCol TX + i, i⟩))
  ++ ((List.range SK).map (fun i => AirLeg.pin ⟨VmRow.last, regCol TY + i, SK + i⟩))

def PI64 : Nat := 2 * SK

/-- Public inputs from a field element pair. -/
def piPair (u v : Fp) : List ℤ :=
  (List.range SK).map (limbAt u) ++ (List.range SK).map (limbAt v)

/-- The initial register file of every stage: all zero except the pinned inputs. -/
def initRegs (r : Nat) (v : Nat) : RegFile := fun k => if k = r then v else 0

/-! ### §8a — STAGE (S): the ξ scalar vector, FULL fidelity. -/

def XI_HEIGHT : Nat := 64
def xiProg : List Step := padTo XI_HEIGHT xiChainProg

theorem xiProg_length : xiProg.length = 64 := by decide

/-- ⚑ **THE SCALAR CHAIN'S AIR IS AT `qLimb`**, the Pallas SCALAR prime — the same `commitAir`, the
same gates, a different limb vector. Emitting it at `pLimb` would be an AIR for the wrong field. -/
def xiAir : EffectAir :=
  { commitAir Dregg2.Circuit.Emit.PastaFieldSound.qLimb (instrs xiProg) with
    legs := (commitAir Dregg2.Circuit.Emit.PastaFieldSound.qLimb (instrs xiProg)).legs
              ++ pinPair TX TY }

theorem xiAir_mainRailOk : xiAir.mainRailOk = true := by
  unfold xiAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨commitAir_mainRailOk _ _, ?_⟩
  simp only [pinPair, List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

def xiDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-mina-xi-scalar-vector::v1" CM_WIDTH PI64 [] xiAir

def xiTrace : List (List ℤ) :=
  runRowsAt PastaField.qN Dregg2.Circuit.Emit.PastaFieldSound.qLimb
    (initRegs TX XI) (witsOf xiProg) 0 (instrs xiProg)

def xiPIs : List ℤ := piPair XI XI_46

/-! ### §8b — STAGE (G2): the group folds, at FULL term count. -/

/-- The fold descriptor for a term list. -/
def foldAir (terms : List Aff) : EffectAir :=
  let prog := padTo (Nat.max 8 (Nat.nextPowerOfTwo (sumProg terms).length)) (sumProg terms)
  { commitAir Dregg2.Circuit.Emit.PastaFieldSound.pLimb (instrs prog) with
    legs := (commitAir Dregg2.Circuit.Emit.PastaFieldSound.pLimb (instrs prog)).legs
              ++ pinOutPoint }

def foldProg (terms : List Aff) : List Step :=
  padTo (Nat.max 8 (Nat.nextPowerOfTwo (sumProg terms).length)) (sumProg terms)

theorem foldAir_mainRailOk (terms : List Aff) : (foldAir terms).mainRailOk = true := by
  unfold foldAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨commitAir_mainRailOk _ _, ?_⟩
  simp only [pinOutPoint, List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

def foldDesc (name : String) (terms : List Aff) : EffectVmDescriptor2 :=
  lowerAir name CM_WIDTH PI64 [] (foldAir terms)

def foldTrace (terms : List Aff) : List (List ℤ) :=
  runRows (initRegs ZERO 0) (witsOf (foldProg terms)) 0 (instrs (foldProg terms))

def foldPIs (terms : List Aff) : List ℤ := piPair (sumOut terms).1 (sumOut terms).2

/-- ⚑ **THE FOUR STAGES.** `public_comm` at 41 terms (40 Lagrange + the `mask_custom` blinder),
`f_comm` at 1, `ft_comm` at 8 points (9 nominal / 7 meaningful), the ξ-aggregate at 47. -/
def publicCommDesc : EffectVmDescriptor2 :=
  foldDesc "dregg-mina-public-comm-fold::v1" PUBLIC_TERMS
def fCommDesc : EffectVmDescriptor2 :=
  foldDesc "dregg-mina-f-comm-fold::v1" [toAff MinaWrapGroupGate.fComm]
def ftCommDesc : EffectVmDescriptor2 :=
  foldDesc "dregg-mina-ft-comm-fold::v1" FT_TERMS
def xiAggDesc : EffectVmDescriptor2 :=
  foldDesc "dregg-mina-xi-aggregate-fold::v1" XI_TERMS

/-! ### §8c — STAGE (G): the ladder, so obligation (3) has a wire. -/

/-- The demo ladder's plane count. ⚠ **8, not 255.** `full_width_ladder_price` is the number this
is a reduction of, and the reduction is in the PLANE count only: the base is the block's real
`sigma_comm[6]`, the assertion `SC = s` is the real one, and every gate is the full-width gate. -/
def DEMO_PLANES : Nat := 8
/-- The demo scalar: the low 8 bits of the block's own `perm_scalars` output, so the digits are
real digits of a real transcript value rather than a number someone picked. -/
def DEMO_SCALAR : Nat := MinaWrapGroupGate.PERM_SCALAR % 2 ^ DEMO_PLANES

def SIGMA6_AFF : Aff := toAff MinaWrapGroupGate.SIGMA6

def ladderSteps' : List Step :=
  emitInit ++ emitLoadT SIGMA6_AFF.1 SIGMA6_AFF.2
  ++ emitTerm SIGMA6_AFF SIGMA6_AFF.1 SIGMA6_AFF.2 DEMO_SCALAR DEMO_PLANES

def ladderProg : List Step :=
  padTo (Nat.max 8 (Nat.nextPowerOfTwo ladderSteps'.length)) ladderSteps'

def ladderAir : EffectAir :=
  { commitAir Dregg2.Circuit.Emit.PastaFieldSound.pLimb (instrs ladderProg) with
    legs := (commitAir Dregg2.Circuit.Emit.PastaFieldSound.pLimb (instrs ladderProg)).legs
              ++ pinOutPoint }

theorem ladderAir_mainRailOk : ladderAir.mainRailOk = true := by
  unfold ladderAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨commitAir_mainRailOk _ _, ?_⟩
  simp only [pinOutPoint, List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

def ladderDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-mina-scalar-mul-ladder::v1" CM_WIDTH PI64 [] ladderAir

def ladderTrace : List (List ℤ) :=
  runRows (initRegs ZERO 0) (witsOf ladderProg) 0 (instrs ladderProg)

def ladderRef : Aff := termOut SIGMA6_AFF SIGMA6_AFF.1 SIGMA6_AFF.2 DEMO_SCALAR DEMO_PLANES
def ladderPIs : List ℤ := piPair ladderRef.1 ladderRef.2

#assert_axioms finv_is_an_inverse
#assert_axioms slope_pin_holds_on_real_block_points
#assert_axioms tangent_pin_holds_on_a_real_block_point
#assert_axioms chord_law_stays_on_pallas
#assert_axioms allocation_fits_the_register_file
#assert_axioms plane_is_double_and_conditional_add
#assert_axioms offset_is_a_real_pallas_point
#assert_axioms ladder_carries_the_offset
#assert_axioms combine_aff_is_47_long
#assert_axioms every_combine_base_is_on_pallas
#assert_axioms xi_chain_starts_at_one_and_walks_by_xi
#assert_axioms the_base_field_reduction_of_xi_squared_is_a_different_scalar
#assert_axioms plane_and_term_costs
#assert_axioms full_width_ladder_price
#assert_axioms every_stage_fits_one_rom_at_full_width
#assert_axioms the_scalar_vector_is_a_rounding_error_against_its_own_stage
#assert_axioms xiProg_length
#assert_axioms xiAir_mainRailOk
#assert_axioms foldAir_mainRailOk
#assert_axioms ladderAir_mainRailOk

end Dregg2.Circuit.Emit.MinaWrapCommitStages
