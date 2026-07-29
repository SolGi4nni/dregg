/-
# Dregg2.Circuit.Emit.PastaMsmWindowed — the **WINDOWED** opening-check AIR: ONE RCB complete
add per **ROW**, threaded across rows by `DescriptorIR2.WindowExpr`, with a forcing theorem whose
statement does not mention the row count.

## Substrate, said out loud

**Lean-authored AIR.** Every generator here is a `def` producing `List VmConstraint2`; every
theorem is about that ACTUALLY EMITTED list. Rust hand-writes no constraint, no builder gadget and
no `air_accepts` predicate — it parses the emitted descriptor and runs it.

## Why this file exists — the defect it repairs

`PastaMsmAir.openingCheck_forces` is a real, gate-count-independent theorem. But the
`AirBuilder.Head`/`cgH` vocabulary is **STRAIGHT-LINE**: every generator emits ONE flat
single-row list over absolute column indices that only grow. So `PastaMsmAir.minaOpeningCheckDesc`
declares `traceWidth := 442` while its constraints address columns near `10^7`, and
`circuit/src/descriptor_ir2.rs:1555` rejects `column >= trace_width`. **The deployed prover would
REFUSE it.** Every row figure in that arc — including "17,375 adds at 442 columns, one root
segment at 26% of its height" — was conditional on a re-layout **nothing emitted**.

This file emits it. The primitive is `DescriptorIR2.WindowExpr` (`loc`/`nxt`), which the IR has
carried since the aggregation AIR and which no `Pasta*` generator used.

## What changes, structurally

  * The straight-line emitter's constraint list GROWS with the computation (573,377 gates for
    statement (B)); this one is **45 constraints, a CONSTANT** — `windowedRowDesc.constraints` has
    the same length at every term count and every scalar width (`windowedRowDesc_constraints_length`
    is `rfl`). The computation moves into the TRACE, which is what an AIR is for.
  * `traceWidth = 525`, and `windowedRowDesc_columns_in_bounds` proves by `decide` that **every
    column any emitted constraint addresses is `< 525`** — i.e. the exact predicate
    `descriptor_ir2.rs`'s `chk` closure enforces, discharged in the kernel before the prover ever
    sees the descriptor.
  * The row-to-row accumulator carry is 3 `windowGate`s (not 27): the thread body is the 9-limb
    VALUE head read across the window, so it forces `fpVal` equality directly.

## The theorem, and what it is independent of

`windowedRows_forces` (§4): if every row window of a trace satisfies the emitted constraints, the
accumulator after `h` rows represents `windowedRef` — the flat fold of RCB complete adds the rows
perform. **`h` is universally quantified and appears in the proof only as an induction variable.**
The statement at `h = 8,925` is the same theorem as at `h = 1`.

`windowed_forces_hornerRef` (§5) is the weld: at the Horner schedule, that flat fold **IS**
`PastaMsmLayouts.hornerRefFrom` — so the windowed emission forces exactly the predicate the
straight-line `hornerGates_forces` forces, and the re-layout changes the trace shape and NOTHING
about the relation. Nothing here restates `pallasRcbStep_forces` or `condPoint_forces`; both are
composed.

⚠ `hornerRefFrom` is a fold of the RCB FORMULA (`rcbAddZmod`) over projective triples in `ZMod p`.
That this fold is the multi-scalar multiplication is NOT a rewrite by
`PastaIpaFold.msmHorner_eq_msmN` — that theorem is an identity in an ABSTRACT
`AddCommGroup`/`Module`, so reaching it needs the formula-to-group-law transport (RCB'15 Thm 1,
valid only at ON-CURVE points), which this tree inherits as a residual and does NOT prove, and
needs an on-curve gate the emitted constraints do NOT contain. See §6.3.

## The obstruction windowing MOVES rather than removes — named, per §6

In a straight-line emission the SHAPE (which add happens when, and that a doubling is a doubling)
is baked into the emitted gate LIST. Windowing replaces that list with one row template, so the
shape moves into the TRACE, as selector columns. §3's `dblPinHeads` recover the doubling
STRUCTURALLY — on a row with `DBL = 1` the addend is FORCED to be the accumulator itself, so a
doubling row genuinely doubles and no hypothesis is needed for it. What remains hypothesised is
the PATTERN of `DBL` down the column (one doubling per plane), and that is stated as an explicit
hypothesis of §5, not hidden. It is the same status `PastaMsmAir.openingCheck_forces` already
gives its digit columns (`hD`), and §6.1 says exactly what would discharge it.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard`s reduce in the kernel. Imports read-only. Import line:
`import Dregg2.Circuit.Emit.PastaMsmWindowed`
-/
import Dregg2.Circuit.Emit.PastaMsmLayouts

namespace Dregg2.Circuit.Emit.PastaMsmWindowed

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2 WindowExpr WindowConstraint)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Emit.Bls12381Tower (evalH_mul)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.PastaField (pN fpValue fpVal fpVal_eq gateBodyEvalZero acceptB numLimbs
  limbBits)
open Dregg2.Circuit.Emit.PastaCurveComplete (pallasCompleteAdd)
open Dregg2.Circuit.Emit.PastaScalarMul (PtP PointIsZ rcbAddZmod pallasRcbStep_forces
  acceptB_append acceptB_cons acceptB_prefix acceptB_suffix gateBodyEvalZero_cgH)
open Dregg2.Circuit.Emit.PastaMsmLayouts (condPointGates condRef bitAt condPoint_forces
  binGate_forces gateBodyEvalZero_cg hornerPlaneRef hornerRefFrom)

set_option autoImplicit false

/-! ## §1 — THE ROW LAYOUT.

One row is ONE RCB complete add. `pallasCompleteAdd X1 Y1 Z1 X2 Y2 Z2 fresh` writes its 442-column
working block at `fresh..fresh+441` and lands its output at `fresh+234 / fresh+261 / fresh+288`
(`PastaScalarMul.pallasRcbStep_forces`'s conclusion). Putting the block at `fresh = 0` makes those
offsets absolute, and the caller-supplied point groups sit above it.

Every group is 9 contiguous limb columns (`numLimbs = 9`, `limbBits = 30`), and the three groups of
a point are contiguous (`X, X+9, X+18`) so a point occupies 27 columns. -/

/-- The RCB working block's base: the row template puts it at column 0. -/
def BLK : Nat := 0
/-- The block-relative output offsets `pallasCompleteAdd` lands on. -/
def OUTX : Nat := 234
def OUTY : Nat := 261
def OUTZ : Nat := 288

/-- The THREADED accumulator coming INTO this row (27 columns). -/
def ACCX : Nat := 442
def ACCY : Nat := 451
def ACCZ : Nat := 460

/-- The row's ADDEND — the selector's output, the second operand of the add (27 columns). -/
def OPX : Nat := 469
def OPY : Nat := 478
def OPZ : Nat := 487

/-- The row's SOURCE point — what the conditional add would add if its bit is set (27 columns). -/
def SRCX : Nat := 496
def SRCY : Nat := 505
def SRCZ : Nat := 514

/-- The conditional-add bit. -/
def BIT : Nat := 523
/-- The doubling-row selector: `1` ⇒ this row's source IS the accumulator, so the row doubles. -/
def DBL : Nat := 524

/-- The row template's width. Under `MAX_TRACE_WIDTH = 1024` (advisory on the IR-v2 path) with 499
columns to spare. -/
def W : Nat := 525

/-! ## §2 — THE EMITTED ROW-LOCAL GATES.

Three families, all `Head`-authored, all reading ONE row:

  1. the conditional select (`condPointGates`, 4 gates) — forces `OP = condRef bit SRC`;
  2. the complete add (`pallasCompleteAdd`, 33 gates) — forces `OUT = ACC + OP`;
  3. the doubling pins (4 gates) — on `DBL = 1`, forces `SRC = ACC` and `BIT = 1`.

Family 3 is what makes a doubling row STRUCTURALLY a doubling rather than a scheduled one. -/

/-- `DBL · (value at `srcBase` − value at `dstBase`)`. Zero with `DBL = 1` pins the two
reconstructed field elements EQUAL — on the value heads, so 3 gates carry what 27 limb pins would,
and the conclusion is directly the `fpVal` equality `PointIsZ` is stated in. -/
def dblPinHead (srcBase dstBase : Nat) : Head :=
  (Head.lin 1 DBL).mul ((fpValue srcBase).append ((fpValue dstBase).scale (-1)))

/-- `DBL · (BIT − 1)`. Zero with `DBL = 1` pins the conditional bit ON, so the selector passes the
source through rather than replacing it with `O`. -/
def dblBitHead : Head :=
  (Head.lin 1 DBL).mul ((Head.lin 1 BIT).addConst (-1))

/-- **The doubling pins** — 4 gates. -/
def dblPinGates : List VmConstraint2 :=
  [ cgH (dblPinHead SRCX ACCX)
  , cgH (dblPinHead SRCY ACCY)
  , cgH (dblPinHead SRCZ ACCZ)
  , cgH dblBitHead ]

/-- **The row-local gates** — the whole per-row template: selector, add, doubling pins, and the
booleanity of the doubling selector. `4 + 33 + 4 + 1 = 42` gates, INDEPENDENT of any row count. -/
def rowGates : List VmConstraint2 :=
  condPointGates BIT SRCX SRCY SRCZ OPX OPY OPZ
    ++ ((pallasCompleteAdd ACCX ACCY ACCZ OPX OPY OPZ BLK).1
        ++ (dblPinGates ++ [binGate DBL]))

/-! ## §3 — THE THREAD: `WindowExpr`, the primitive the emitter family never used.

`WindowExpr.loc c` reads the current row, `.nxt c` the next. The thread says the NEXT row's
accumulator IS this row's output — on the 9-limb VALUE heads, so 3 window constraints carry it and
land directly on `fpVal`. `onTransition = true` is the Rust `builder.when_transition()` arm, so the
last row (whose `nxt` is the wrap row) is exempt. -/

/-- The 9-limb value head read through a window, with `rd` choosing the row (`.loc` or `.nxt`). -/
def wVal (rd : Nat → WindowExpr) (base : Nat) : WindowExpr :=
  (List.range numLimbs).foldl
    (fun e i => .add e (.mul (.const ((2 : ℤ) ^ (limbBits * i))) (rd (base + i)))) (.const 0)

/-- The thread body: `nextRowValue(accBase) − thisRowValue(outBase)`. -/
def threadBody (accBase outBase : Nat) : WindowExpr :=
  .add (wVal .nxt accBase) (.mul (.const (-1)) (wVal .loc outBase))

/-- A transition window constraint. -/
def cw (b : WindowExpr) : VmConstraint2 := .windowGate ⟨b, true⟩

/-- **The emitted thread** — 3 window constraints carrying the accumulator from row to row. -/
def threadGates : List VmConstraint2 :=
  [ cw (threadBody ACCX OUTX), cw (threadBody ACCY OUTY), cw (threadBody ACCZ OUTZ) ]

/-- ⚑ **The windowed descriptor.** `traceWidth` is a REAL column count; the constraint list is a
CONSTANT 45 entries whatever the computation's size. -/
def windowedRowDesc : EffectVmDescriptor2 :=
  { name        := "dregg-pasta-rcb-windowed::v1"
  , traceWidth  := W
  , piCount     := 0
  , tables      := []
  , constraints := rowGates ++ threadGates
  , hashSites   := []
  , ranges      := [] }

/-! ### §3b — the deployed checker's OWN predicate, discharged in the kernel.

`circuit/src/descriptor_ir2.rs:1552-1562` refuses a descriptor whose any constraint references a
column `>= trace_width`. That is the check `PastaMsmAir.minaOpeningCheckDesc` fails. Here it is as
a Lean `decide`, over the actually-emitted list, so the refusal cannot come back. -/

/-- The largest column index a `WindowExpr` addresses (Rust `WindowExpr::max_var`). -/
def wMaxVar : WindowExpr → Nat
  | .loc c   => c + 1
  | .nxt c   => c + 1
  | .const _ => 0
  | .add a b => max (wMaxVar a) (wMaxVar b)
  | .mul a b => max (wMaxVar a) (wMaxVar b)

/-- The largest column index an `EmittedExpr` addresses. -/
def eMaxVar : Dregg2.Exec.CircuitEmit.EmittedExpr → Nat
  | .var c   => c + 1
  | .const _ => 0
  | .add a b => max (eMaxVar a) (eMaxVar b)
  | .mul a b => max (eMaxVar a) (eMaxVar b)

/-- The largest column a constraint addresses (the arms the row template uses). -/
def cMaxVar : VmConstraint2 → Nat
  | .base (.gate e) => eMaxVar e
  | .windowGate w   => wMaxVar w.body
  | _               => 0

set_option maxRecDepth 40000 in
/-- ⚑ **`windowedRowDesc_columns_in_bounds`** — EVERY column EVERY emitted constraint addresses is
`< traceWidth`. This is `descriptor_ir2.rs`'s `chk` closure, decided in the kernel over the emitted
list. The straight-line `minaOpeningCheckDesc` fails exactly this. -/
theorem windowedRowDesc_columns_in_bounds :
    windowedRowDesc.constraints.all (fun c => decide (cMaxVar c ≤ windowedRowDesc.traceWidth))
      = true := by decide

/-- ⚑ **The constraint count is a CONSTANT.** This is the whole structural change: the
straight-line emitter's list grows with the computation, this one does not. -/
theorem windowedRowDesc_constraints_length : windowedRowDesc.constraints.length = 45 := rfl

#guard windowedRowDesc.traceWidth == 525
#guard windowedRowDesc.constraints.length == 45

/-! ## §4 — THE FORCING, ROW-COUNT-INDEPENDENT.

A windowed trace is a row-indexed family of assignments. The per-row forcing composes exactly two
already-proved lemmas — `condPoint_forces` for the selector and `pallasRcbStep_forces` for the add
— and the row induction hands the accumulator invariant to the tail. `h` appears nowhere but as
the induction variable. -/

/-- A windowed trace: row `i`'s assignment. -/
abbrev WTrace := Nat → Assignment

/-- The two-row window at row `i`. -/
def envOf (T : WTrace) (i : Nat) : VmRowEnv := { loc := T i, nxt := T (i + 1), pub := T 0 }

/-- The value head, as an explicit sum (`AirBuilder.evalH_foldl_addLinG` applied to `fpValue`). -/
theorem fpVal_as_sum (a : Assignment) (base : Nat) :
    fpVal a base
      = ((List.range numLimbs).map (fun i => (2 : ℤ) ^ (limbBits * i) * a (base + i))).sum := by
  have hz : evalH Head.zero a = 0 := by simp [evalH, Head.zero]
  rw [fpVal, fpValue, evalH_foldl_addLinG, hz, zero_add]

/-- The windowed value head evaluates to the same sum, with `rd` selecting the row. -/
theorem wVal_eval (env : VmRowEnv) (rd : Nat → WindowExpr) (rdv : Nat → ℤ)
    (hrd : ∀ c, (rd c).eval env = rdv c) (base : Nat) :
    (wVal rd base).eval env
      = ((List.range numLimbs).map (fun i => (2 : ℤ) ^ (limbBits * i) * rdv (base + i))).sum := by
  have gen : ∀ (xs : List Nat) (e0 : WindowExpr),
      (xs.foldl (fun e i => WindowExpr.add e
          (.mul (.const ((2 : ℤ) ^ (limbBits * i))) (rd (base + i)))) e0).eval env
        = e0.eval env + (xs.map (fun i => (2 : ℤ) ^ (limbBits * i) * rdv (base + i))).sum := by
    intro xs
    induction xs with
    | nil => intro e0; simp
    | cons x rest ih =>
      intro e0
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      simp only [WindowExpr.eval, hrd]
      ring
  simpa [wVal, WindowExpr.eval] using gen (List.range numLimbs) (WindowExpr.const 0)

/-- The thread body evaluates to `nextRowValue(accBase) − thisRowValue(outBase)`. -/
theorem threadBody_eval (T : WTrace) (i accBase outBase : Nat) :
    (threadBody accBase outBase).eval (envOf T i)
      = fpVal (T (i + 1)) accBase - fpVal (T i) outBase := by
  simp only [threadBody, WindowExpr.eval]
  rw [wVal_eval (envOf T i) .nxt (fun c => T (i + 1) c) (fun c => rfl) accBase,
      wVal_eval (envOf T i) .loc (fun c => T i c) (fun c => rfl) outBase,
      fpVal_as_sum, fpVal_as_sum]
  ring

/-- Every EMITTED thread constraint's body vanishes on the window at row `i` — the integer model
`acceptB` uses, applied to the two-row window. -/
def ThreadAccepted (T : WTrace) (i : Nat) : Prop :=
  ∀ w : WindowConstraint, VmConstraint2.windowGate w ∈ threadGates → w.body.eval (envOf T i) = 0

/-- The thread's CONTENT: the next row's accumulator value IS this row's output value. Stated on
the three `fpVal`s the window constraints pin. -/
def Threaded (T : WTrace) (i : Nat) : Prop :=
  fpVal (T (i + 1)) ACCX = fpVal (T i) OUTX
  ∧ fpVal (T (i + 1)) ACCY = fpVal (T i) OUTY
  ∧ fpVal (T (i + 1)) ACCZ = fpVal (T i) OUTZ

/-- ⚑ **The thread constraints FORCE the carry.** A window on which every emitted `threadGate` body
vanishes has the next row's accumulator equal to this row's output — the `Threaded` predicate the
induction consumes. Nothing else in the file assumes the carry; it is derived from the emitted
`windowGate`s. -/
theorem threadGates_force (T : WTrace) (i : Nat) (h : ThreadAccepted T i) : Threaded T i := by
  refine ⟨?_, ?_, ?_⟩
  · have := h ⟨threadBody ACCX OUTX, true⟩ (by simp [threadGates, cw])
    rw [threadBody_eval] at this; linarith
  · have := h ⟨threadBody ACCY OUTY, true⟩ (by simp [threadGates, cw])
    rw [threadBody_eval] at this; linarith
  · have := h ⟨threadBody ACCZ OUTZ, true⟩ (by simp [threadGates, cw])
    rw [threadBody_eval] at this; linarith

/-- The point a row's SOURCE columns represent, and the bit it carries, decide the row's addend.
This is the reference ONE row computes. -/
def rowRef (bit : Bool) (S acc : PtP) : PtP := rcbAddZmod acc (condRef bit S)

/-- ⚑ **`row_forces`** — the emitted row template FORCES one RCB complete add of the SELECTED
addend. Composes `condPoint_forces` (the selector) and `pallasRcbStep_forces` (the add); neither is
restated. -/
theorem row_forces (a : Assignment) {acc S : PtP}
    (hacc : PointIsZ a ACCX ACCY ACCZ acc)
    (hS : PointIsZ a SRCX SRCY SRCZ S)
    (hrow : acceptB rowGates a = true) :
    PointIsZ a OUTX OUTY OUTZ (rowRef (bitAt a BIT) S acc) := by
  have hsel : acceptB (condPointGates BIT SRCX SRCY SRCZ OPX OPY OPZ) a = true :=
    acceptB_prefix _ _ a hrow
  have hrest : acceptB ((pallasCompleteAdd ACCX ACCY ACCZ OPX OPY OPZ BLK).1
      ++ (dblPinGates ++ [binGate DBL])) a = true := acceptB_suffix _ _ a hrow
  have hadd : acceptB (pallasCompleteAdd ACCX ACCY ACCZ OPX OPY OPZ BLK).1 a = true :=
    acceptB_prefix _ _ a hrest
  have hop : PointIsZ a OPX OPY OPZ (condRef (bitAt a BIT) S) :=
    condPoint_forces a BIT SRCX SRCY SRCZ OPX OPY OPZ hS hsel
  exact pallasRcbStep_forces a ACCX ACCY ACCZ OPX OPY OPZ BLK hacc hop hadd

/-- ⚑ **`dblRow_forces`** — on a row whose `DBL` selector is ON, the SOURCE is FORCED to be the
accumulator and the bit is FORCED on, so the row is a genuine DOUBLING. This is what keeps the
doubling structural under windowing rather than scheduled. -/
theorem dblRow_forces (a : Assignment) {acc : PtP}
    (hacc : PointIsZ a ACCX ACCY ACCZ acc)
    (hrow : acceptB rowGates a = true)
    (hdbl : a DBL = 1) :
    PointIsZ a SRCX SRCY SRCZ acc ∧ bitAt a BIT = true := by
  have hrest : acceptB ((pallasCompleteAdd ACCX ACCY ACCZ OPX OPY OPZ BLK).1
      ++ (dblPinGates ++ [binGate DBL])) a = true := acceptB_suffix _ _ a hrow
  have hpins : acceptB (dblPinGates ++ [binGate DBL]) a = true :=
    acceptB_suffix _ _ a (acceptB_suffix _ _ a hrow)
  have hp : acceptB dblPinGates a = true := acceptB_prefix _ _ a hpins
  simp only [dblPinGates, acceptB, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, gateBodyEvalZero_cgH] at hp
  obtain ⟨gX, gY, gZ, gB⟩ := hp
  have eX : fpVal a SRCX = fpVal a ACCX := by
    have h := of_decide_eq_true gX
    simp only [dblPinHead, evalH_mul, evalH_lin, evalH_append, evalH_scale, fpVal_eq, hdbl] at h
    linarith
  have eY : fpVal a SRCY = fpVal a ACCY := by
    have h := of_decide_eq_true gY
    simp only [dblPinHead, evalH_mul, evalH_lin, evalH_append, evalH_scale, fpVal_eq, hdbl] at h
    linarith
  have eZ : fpVal a SRCZ = fpVal a ACCZ := by
    have h := of_decide_eq_true gZ
    simp only [dblPinHead, evalH_mul, evalH_lin, evalH_append, evalH_scale, fpVal_eq, hdbl] at h
    linarith
  have eB : a BIT = 1 := by
    have h := of_decide_eq_true gB
    simp only [dblBitHead, evalH_mul, evalH_lin, evalH_addConst, hdbl] at h
    linarith
  obtain ⟨hx, hy, hz⟩ := hacc
  exact ⟨⟨by rw [eX]; exact hx, by rw [eY]; exact hy, by rw [eZ]; exact hz⟩, by simp [bitAt, eB]⟩

/-! ### §4b — the row induction. -/

/-- The reference the windowed trace computes over `h` rows: the flat fold of the per-row adds,
where each row's addend is the point its own selector chose. -/
def windowedRef (Sv : Nat → PtP) (bits : Nat → Bool) : PtP → Nat → PtP
  | acc, 0     => acc
  | acc, n + 1 => rowRef (bits n) (Sv n) (windowedRef Sv bits acc n)

/-- ⚑⚑ **`windowedRows_forces`** — **the WINDOWED emission forces the flat fold of complete adds.**
Any trace whose every row window satisfies the emitted row template and the emitted thread has its
accumulator, after `h` rows, representing `windowedRef` in `ZMod p`.

`h` is universally quantified and occurs in the proof ONLY as the induction variable: the statement
at `h = 8,925` is the same theorem as the statement at `h = 1`. Nothing scales with the row count
because the CONSTRAINT LIST does not — it is 45 entries at every `h`. -/
theorem windowedRows_forces (T : WTrace) (Sv : Nat → PtP) (acc0 : PtP)
    (h0 : PointIsZ (T 0) ACCX ACCY ACCZ acc0) :
    ∀ (h : Nat),
      (∀ i < h, acceptB rowGates (T i) = true) →
      (∀ i < h, Threaded T i) →
      (∀ i < h, PointIsZ (T i) SRCX SRCY SRCZ (Sv i)) →
      PointIsZ (T h) ACCX ACCY ACCZ
        (windowedRef Sv (fun i => bitAt (T i) BIT) acc0 h) := by
  intro h
  induction h with
  | zero => intro _ _ _; exact h0
  | succ n ih =>
    intro hrows hthr hsrc
    have hacc : PointIsZ (T n) ACCX ACCY ACCZ (windowedRef Sv (fun i => bitAt (T i) BIT) acc0 n) :=
      ih (fun i hi => hrows i (by omega)) (fun i hi => hthr i (by omega))
        (fun i hi => hsrc i (by omega))
    have hout : PointIsZ (T n) OUTX OUTY OUTZ
        (rowRef (bitAt (T n) BIT) (Sv n) (windowedRef Sv (fun i => bitAt (T i) BIT) acc0 n)) :=
      row_forces (T n) hacc (hsrc n (by omega)) (hrows n (by omega))
    obtain ⟨tx, ty, tz⟩ := hthr n (by omega)
    obtain ⟨ox, oy, oz⟩ := hout
    exact ⟨by rw [tx]; exact ox, by rw [ty]; exact oy, by rw [tz]; exact oz⟩

#assert_axioms fpVal_as_sum
#assert_axioms wVal_eval
#assert_axioms threadBody_eval
#assert_axioms threadGates_force
#assert_axioms row_forces
#assert_axioms dblRow_forces
#assert_axioms windowedRows_forces

/-! ### §4c — ⚑ THE ROW TEMPLATE BITES: satisfiable at birth, refutable under tamper.

`AirBuilder.rangeNonneg` sat in this tree for months as a shape every consumer read as a check.
A forcing theorem whose hypothesis nothing satisfies is TRUE AND EMPTY, so the row template is
exhibited here ACCEPTING honest rows of all three kinds and REFUSING tampered ones — in the
kernel, over the actually-emitted `rowGates`.

The witness is `PastaCurveComplete.rcbAsg` (already KAT-tested there) re-addressed to this file's
row layout: its block sits at `54` and this row's at `0`, its inputs at `0..53` and this row's at
`442..495`. -/

/-- An honest row assignment: accumulator `(accX,accY,accZ)`, source point `(srcX,srcY,srcZ)`,
conditional bit `bit`, doubling selector `dbl`. The addend is the SELECTED point — `src` when the
bit is on, `O = (0,1,0)` when it is off — so the row is exactly what an honest prover writes. -/
def rowAsg (accX accY accZ srcX srcY srcZ bit dbl : Nat) : Assignment :=
  let opX := if bit = 1 then srcX else 0
  let opY := if bit = 1 then srcY else 1
  let opZ := if bit = 1 then srcZ else 0
  let g := Dregg2.Circuit.Emit.PastaCurveComplete.rcbAsg pN
             Dregg2.Circuit.Emit.PastaCurveComplete.curveB3 accX accY accZ opX opY opZ
  fun col =>
    if col < 442 then g (col + 54)
    else if col < 469 then g (col - 442)
    else if col < 496 then g (col - 469 + 27)
    else if col < 505 then Dregg2.Circuit.Emit.PastaField.Ref.limbOf srcX (col - 496)
    else if col < 514 then Dregg2.Circuit.Emit.PastaField.Ref.limbOf srcY (col - 505)
    else if col < 523 then Dregg2.Circuit.Emit.PastaField.Ref.limbOf srcZ (col - 514)
    else if col = 523 then (bit : ℤ)
    else if col = 524 then (dbl : ℤ)
    else 0

open Dregg2.Circuit.Emit.PastaCurve (Gp)
open Dregg2.Circuit.Emit.PastaField (bumpAt)

/-- The Pallas generator, projective. -/
def GpX : Nat := Gp.1
def GpY : Nat := Gp.2

-- SATISFIABLE — a DOUBLING row (`DBL = 1`, source pinned to the accumulator, bit pinned on).
#guard acceptB rowGates (rowAsg GpX GpY 1 GpX GpY 1 1 1) == true
-- SATISFIABLE — a CONDITIONAL-ADD row that ADDS (`DBL = 0`, bit on, source a real point).
#guard acceptB rowGates (rowAsg GpX GpY 1 GpX GpY 1 1 0) == true
-- SATISFIABLE — a CONDITIONAL-ADD row that SKIPS (`DBL = 0`, bit off ⇒ addend is `O`).
#guard acceptB rowGates (rowAsg GpX GpY 1 GpX GpY 1 0 0) == true

-- ⚑ REFUTABLE — the DOUBLING PIN BITES: `DBL = 1` while the source is NOT the accumulator is
-- REFUSED. This is the gate that keeps a doubling row structurally a doubling.
#guard acceptB rowGates (rowAsg GpX GpY 1 0 1 0 1 1) == false
-- ⚑ REFUTABLE — `DBL = 1` with the conditional bit OFF is REFUSED (the bit pin).
#guard acceptB rowGates (rowAsg GpX GpY 1 GpX GpY 1 0 1) == false
-- REFUTABLE — a bumped output limb (X3 at column 234, Y3 at 261, Z3 at 288).
#guard acceptB rowGates (bumpAt (rowAsg GpX GpY 1 GpX GpY 1 1 0) 234) == false
#guard acceptB rowGates (bumpAt (rowAsg GpX GpY 1 GpX GpY 1 1 0) 261) == false
#guard acceptB rowGates (bumpAt (rowAsg GpX GpY 1 GpX GpY 1 1 0) 288) == false
-- REFUTABLE — a bumped accumulator limb (the add no longer matches its inputs).
#guard acceptB rowGates (bumpAt (rowAsg GpX GpY 1 GpX GpY 1 1 0) 442) == false
-- REFUTABLE — the selector bit is not a bit.
#guard acceptB rowGates (bumpAt (rowAsg GpX GpY 1 GpX GpY 1 1 0) 523) == false
-- ⚑ REFUTABLE — the FREE-TERM FORGERY: bit off but the addend is the point anyway (a term added
-- without paying for it). `condPointGates` refuses it, here at the windowed layout.
#guard acceptB rowGates
    (fun c => if 469 <= c && c < 496 then rowAsg GpX GpY 1 GpX GpY 1 1 0 c
              else rowAsg GpX GpY 1 GpX GpY 1 0 0 c) == false

/-! ## §5 — THE WELD: the windowed fold IS the bit-plane scan.

`PastaMsmLayouts.hornerRefFrom` is the reference the straight-line bit-plane AIR forces. A windowed
trace laid out at the HORNER SCHEDULE — per plane, one doubling row followed by `n` conditional-add
rows — computes exactly it.

The schedule is stated as an explicit hypothesis on the trace's own selector columns (§6.1 names
what would discharge it), and the CONTENT — that the flat fold then equals the nested one — is
proved, not assumed. -/

/-- Row index of the `t`-th row of plane `plane`, in a schedule of `n` terms per plane: one
doubling row then `n` conditional adds. -/
def rowIndex (n plane t : Nat) : Nat := plane * (n + 1) + t

/-- The Horner schedule, as a predicate on what the trace's selector and source columns carry.
`ptVals i` is term `i`'s base point and `bits plane i` is its scalar's bit at that plane. -/
structure HornerSchedule (T : WTrace) (Sv : Nat → PtP) (ptVals : Nat → PtP)
    (bits : Nat → Nat → Bool) (n nbits : Nat) : Prop where
  /-- The first row of every plane is a DOUBLING row. -/
  dblRow  : ∀ plane < nbits, T (rowIndex n plane 0) DBL = 1
  /-- The `t`-th conditional-add row of a plane carries term `t`'s base point … -/
  srcRow  : ∀ plane < nbits, ∀ t < n, Sv (rowIndex n plane (t + 1)) = ptVals t
  /-- … and term `t`'s bit at that plane. -/
  bitRow  : ∀ plane < nbits, ∀ t < n, bitAt (T (rowIndex n plane (t + 1))) BIT = bits plane t

/-- The windowed fold over one plane's `n` conditional-add rows IS `hornerPlaneRef`'s inner fold. -/
theorem plane_inner (T : WTrace) (Sv : Nat → PtP) (ptVals : Nat → PtP) (bits : Nat → Nat → Bool)
    (n nbits plane : Nat) (acc0 : PtP) (base : PtP)
    (hs : HornerSchedule T Sv ptVals bits n nbits) (hp : plane < nbits)
    (hbase : windowedRef Sv (fun i => bitAt (T i) BIT) acc0 (rowIndex n plane 1) = base) :
    ∀ t ≤ n,
      windowedRef Sv (fun i => bitAt (T i) BIT) acc0 (rowIndex n plane (t + 1))
        = (List.range t).foldl (fun b i => rcbAddZmod b (condRef (bits plane i) (ptVals i))) base := by
  intro t
  induction t with
  | zero => intro _; simpa using hbase
  | succ m ih =>
    intro hm
    have hrec : windowedRef Sv (fun i => bitAt (T i) BIT) acc0 (rowIndex n plane (m + 2))
        = rowRef (bitAt (T (rowIndex n plane (m + 1))) BIT) (Sv (rowIndex n plane (m + 1)))
            (windowedRef Sv (fun i => bitAt (T i) BIT) acc0 (rowIndex n plane (m + 1))) := by
      have : rowIndex n plane (m + 2) = (rowIndex n plane (m + 1)) + 1 := by
        simp [rowIndex]; omega
      rw [this, windowedRef]
    rw [hrec, ih (by omega), hs.srcRow plane hp m (by omega), hs.bitRow plane hp m (by omega),
      List.range_succ, List.foldl_append]
    rfl

#assert_axioms plane_inner

/-- Two `PointIsZ` readings of the SAME columns are the same point — the reference is a function
of the assignment, so a trace cannot represent two different points at one place. -/
theorem PointIsZ_unique {a : Assignment} {bX bY bZ : Nat} {P Q : PtP}
    (hP : PointIsZ a bX bY bZ P) (hQ : PointIsZ a bX bY bZ Q) : P = Q := by
  obtain ⟨p1, p2, p3⟩ := hP
  obtain ⟨q1, q2, q3⟩ := hQ
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [← p1, ← q1]
  · rw [← p2, ← q2]
  · rw [← p3, ← q3]

/-- ⚑ **`plane_step`** — the windowed rows of ONE plane compute exactly `hornerPlaneRef`: the
doubling row genuinely doubles (`dblRow_forces`, no hypothesis needed), and the `n` conditional-add
rows fold in the selected digits (`plane_inner`). -/
theorem plane_step (T : WTrace) (Sv : Nat → PtP) (ptVals : Nat → PtP) (bits : Nat → Nat → Bool)
    (n nbits plane : Nat) (acc0 : PtP)
    (hs : HornerSchedule T Sv ptVals bits n nbits) (hp : plane < nbits)
    (hrows : ∀ i < nbits * (n + 1), acceptB rowGates (T i) = true)
    (hthr : ∀ i < nbits * (n + 1), Threaded T i)
    (hsrc : ∀ i < nbits * (n + 1), PointIsZ (T i) SRCX SRCY SRCZ (Sv i))
    (h0 : PointIsZ (T 0) ACCX ACCY ACCZ acc0) :
    windowedRef Sv (fun i => bitAt (T i) BIT) acc0 (rowIndex n (plane + 1) 0)
      = hornerPlaneRef ptVals bits n
          (windowedRef Sv (fun i => bitAt (T i) BIT) acc0 (rowIndex n plane 0)) plane := by
  have hlt : rowIndex n plane 0 < nbits * (n + 1) := by
    simp only [rowIndex]
    have := Nat.mul_lt_mul_of_lt_of_le hp (Nat.le_refl (n + 1)) (Nat.succ_pos n)
    omega
  set r0 := rowIndex n plane 0 with hr0
  set acc := windowedRef Sv (fun i => bitAt (T i) BIT) acc0 r0 with hacc0
  -- the accumulator at the plane boundary is what the rows before it forced
  have haccP : PointIsZ (T r0) ACCX ACCY ACCZ acc :=
    windowedRows_forces T Sv acc0 h0 r0
      (fun i hi => hrows i (by omega)) (fun i hi => hthr i (by omega))
      (fun i hi => hsrc i (by omega))
  -- the doubling row genuinely doubles: its source is FORCED to be the accumulator
  obtain ⟨hsrcAcc, hbit⟩ :=
    dblRow_forces (T r0) haccP (hrows r0 hlt) (hs.dblRow plane hp)
  have hSv : Sv r0 = acc := (PointIsZ_unique (hsrc r0 hlt) hsrcAcc)
  -- so the row after the doubling row holds `acc + acc`
  have hbase : windowedRef Sv (fun i => bitAt (T i) BIT) acc0 (rowIndex n plane 1)
      = rcbAddZmod acc acc := by
    have hstep : rowIndex n plane 1 = r0 + 1 := by simp [rowIndex, hr0]
    rw [hstep, windowedRef, hSv, hbit]
    simp only [rowRef, condRef, if_true, ← hacc0]
  -- and the plane's `n` conditional-add rows fold in the selected digits
  have hfold := plane_inner T Sv ptVals bits n nbits plane acc0 (rcbAddZmod acc acc) hs hp hbase
    n (Nat.le_refl n)
  have hidx : rowIndex n plane (n + 1) = rowIndex n (plane + 1) 0 := by
    simp only [rowIndex]; ring
  rw [← hidx, hfold, hornerPlaneRef]

/-- ⚑⚑ **`windowed_forces_hornerRef`** — **the WINDOWED emission forces the SAME predicate the
straight-line bit-plane AIR forces.** At the Horner schedule, the flat fold of complete adds the
rows perform IS `PastaMsmLayouts.hornerRefFrom`.

`nbits` and `n` are universally quantified. Nothing in the proof is a function of the row count;
the emitted constraint list is 45 entries at every `(n, nbits)`
(`windowedRowDesc_constraints_length`). This is the statement that makes the windowed AIR a
re-layout rather than a different circuit. -/
theorem windowed_forces_hornerRef (T : WTrace) (Sv : Nat → PtP) (ptVals : Nat → PtP)
    (bits : Nat → Nat → Bool) (n nbits : Nat) (acc0 : PtP)
    (hs : HornerSchedule T Sv ptVals bits n nbits)
    (hrows : ∀ i < nbits * (n + 1), acceptB rowGates (T i) = true)
    (hthr : ∀ i < nbits * (n + 1), Threaded T i)
    (hsrc : ∀ i < nbits * (n + 1), PointIsZ (T i) SRCX SRCY SRCZ (Sv i))
    (h0 : PointIsZ (T 0) ACCX ACCY ACCZ acc0) :
    ∀ plane ≤ nbits,
      windowedRef Sv (fun i => bitAt (T i) BIT) acc0 (rowIndex n plane 0)
        = hornerRefFrom ptVals bits n plane acc0 := by
  intro plane
  induction plane with
  | zero => intro _; simp [rowIndex, windowedRef, hornerRefFrom]
  | succ m ih =>
    intro hm
    rw [plane_step T Sv ptVals bits n nbits m acc0 hs (by omega) hrows hthr hsrc h0,
      ih (by omega)]
    simp [hornerRefFrom, List.range_succ]

/-- ⚑⚑ **`windowed_accumulator_is_hornerRef`** — the deliverable, assembled: a windowed trace at
the Horner schedule has its FINAL accumulator columns representing, in `ZMod p`, exactly the
bit-plane scan `hornerRefFrom` — the SAME reference object `PastaMsmLayouts.hornerGates_forces`
lands on for the straight-line emission.

⚠ Read the conclusion at its actual strength: `hornerRefFrom` is a fold of the RCB FORMULA over
projective triples, not yet "the MSM". The step from the formula fold to the group-law MSM is
RCB'15 Thm 1 at on-curve points — an INHERITED, undischarged transport (`PastaMsmAir` §6.4) — plus
an on-curve gate these constraints do not emit (§6.3). This theorem closes the LAYOUT gap; it does
not close that one. -/
theorem windowed_accumulator_is_hornerRef (T : WTrace) (Sv : Nat → PtP) (ptVals : Nat → PtP)
    (bits : Nat → Nat → Bool) (n nbits : Nat) (acc0 : PtP)
    (hs : HornerSchedule T Sv ptVals bits n nbits)
    (hrows : ∀ i < nbits * (n + 1), acceptB rowGates (T i) = true)
    (hthr : ∀ i < nbits * (n + 1), Threaded T i)
    (hsrc : ∀ i < nbits * (n + 1), PointIsZ (T i) SRCX SRCY SRCZ (Sv i))
    (h0 : PointIsZ (T 0) ACCX ACCY ACCZ acc0) :
    PointIsZ (T (nbits * (n + 1))) ACCX ACCY ACCZ (hornerRefFrom ptVals bits n nbits acc0) := by
  have hforced := windowedRows_forces T Sv acc0 h0 (nbits * (n + 1)) hrows hthr hsrc
  have heq := windowed_forces_hornerRef T Sv ptVals bits n nbits acc0 hs hrows hthr hsrc h0
    nbits (Nat.le_refl nbits)
  have hidx : rowIndex n nbits 0 = nbits * (n + 1) := by simp [rowIndex]
  rw [hidx] at heq
  rw [← heq]
  exact hforced

#assert_axioms PointIsZ_unique
#assert_axioms plane_step
#assert_axioms windowed_forces_hornerRef
#assert_axioms windowed_accumulator_is_hornerRef

/-! ## §5b — ⚑ THE PRICE OF THE WINDOWED LAYOUT, against the deployed geometry.

The straight-line pricing instrument (`PastaMsmAir` §5b) counted GATES, because in a straight-line
emission the gate count IS the trace. Here the two separate: the gate count is a CONSTANT (45) and
the ROW count is the computation. So the price is a row count, and the deployed root's geometry
(trace `2^16` rows, `|D⁰| = 2^22` at `log_blowup 6`) is what it is measured against.

`PastaMsmLayouts.hornerRcbAdds n nbits = nbits * (n + 1)` is the row count: one doubling row per
plane, one conditional-add row per (plane, term). -/

/-- The deployed root's trace height (`WRAP_LOG_CEIL = 16`). -/
def DREGG_ROOT_ROWS : Nat := 65536
/-- The two-adicity ceiling at the deployed `log_blowup = 6` (`BabyBear::TWO_ADICITY = 27`). -/
def DREGG_MAX_ROWS : Nat := 2097152

/-- The emitted row count of the windowed bit-plane layout at `n` terms and `nbits` planes. -/
def windowedRows (n nbits : Nat) : Nat := nbits * (n + 1)

/-- Trace cells: rows × the CONSTANT row width. -/
def windowedCells (n nbits : Nat) : Nat := windowedRows n nbits * W

-- ⚑ STATEMENT (B), the IPA opening relation: 34 terms × 255 bit-planes.
#guard windowedRows 34 255 == 8925
-- Against the straight-line term-by-term ladder `PastaMsmAir` priced (17,375 adds): 1.94× fewer
-- rows, because the bit-plane scan shares ONE doubling chain across all 34 terms.
#guard Dregg2.Circuit.Emit.PastaMsmAir.openingCheckRcbAdds 34 255 == 17375
#guard 2 * windowedRows 34 255 < 2 * Dregg2.Circuit.Emit.PastaMsmAir.openingCheckRcbAdds 34 255
-- ⚑ It fits INSIDE ONE deployed root segment: 8,925 of 65,536 rows.
#guard windowedRows 34 255 < DREGG_ROOT_ROWS
-- and inside the two-adicity ceiling with room to spare.
#guard windowedRows 34 255 < DREGG_MAX_ROWS
-- A STARK trace height is a power of two, so the honest figure is the PADDED one: 2^14 = 16,384
-- rows, a quarter of a root segment.
#guard 8192 < windowedRows 34 255 && windowedRows 34 255 <= 16384
#guard 4 * 16384 == DREGG_ROOT_ROWS
-- Cells at the raw row count, against the straight-line 17,375 × 442 = 7,679,750.
#guard windowedCells 34 255 == 4685625
#guard windowedCells 34 255 < 7679750

-- ⚑ The `⟨s, srs.g⟩` leg (statement (A)) is UNCHANGED by windowing and still does not fit:
-- 32,768 terms × 255 planes.
#guard windowedRows 32768 255 == 8356095
#guard windowedRows 32768 255 > DREGG_MAX_ROWS
-- 3.98× past the single-proof ceiling. Windowing fixes the LAYOUT, not the SIZE — the `sg` leg is
-- still the one Pickles itself defers into an accumulator, and `PastaMsmLayouts` §6's
-- recommendation (DEFER, do not optimise) is untouched by this file.
#guard windowedRows 32768 255 / DREGG_MAX_ROWS == 3

/-! ## §6 — WHAT THIS DOES NOT DO. At the CURRENT resolution.

1. **The `DBL` PATTERN is hypothesised, the doubling ITSELF is not.** `dblRow_forces` proves a row
   with `DBL = 1` genuinely doubles — that part is structural, in the emitted gates. What §5 assumes
   is WHERE the ones sit down the column. Discharging it needs a forced row-type schedule: a
   threaded plane counter `k` with `nxt k = loc k + 1` off the boundary and `DBL = 1 ⟺ k = 0`,
   which needs an is-zero/inverse gadget (`AirBuilder.condNonzero` is the shape). That is a
   BUILDABLE rung, named here and not built.

2. **The ℤ model is inherited, NOT repaired.** `acceptB` and every `*_forces` in the `Pasta*`
   family read a gate body as an INTEGER zero; the deployed prover reads it as zero in BabyBear
   (`p = 2^31 − 2^27 + 1`), and a 9×30-limb value head reconstructs to `2^270`, far outside it.
   So a real STARK proof of this descriptor establishes the mod-BabyBear reading, and the
   ℤ ↔ felt gap is exactly the shared K1 residual (`project-felt-width-repair-campaign`,
   `Dregg2/Bignum.lean`) — UNCHANGED by this file, and NOT closed by having a proof object.
   A windowed emission does not make that gap smaller or larger; it must not be read as closing it.

3. **On-curve-ness is still not gated, and the skip encoding makes that BITE.** `condRef false P`
   is `O = (0 : 1 : 0)`, and RCB Alg. 7 at `Q = O` returns `Y₁ · (X₁, Y₁, Z₁)` — a correct
   projective representative only while `Y₁ ≠ 0`. On Pallas (prime order) no affine point has
   `Y = 0`, but NOTHING in the emitted gates says the accumulator is on the curve, and at
   `Y₁ = 0` the formula collapses to `(0,0,0)`, which is ABSORBING and satisfies the terminal
   `X = 0 ∧ Z = 0` predicate. This is a concrete witness of why the inherited "RCB completeness
   transport" residual (`PastaMsmAir` §6.4) is load-bearing rather than bookkeeping — and it is
   PRE-EXISTING: `PastaMsmLayouts.hornerAddStep` already adds `O` on an unset bit, so
   `hornerGates_forces` carries it too. Not introduced here; surfaced here.

4. **P10 is untouched.** Relation holding ≠ prover knowing (`PastaMsmAir` §6.1).

5. **The terminal predicate and the `delta` add are `PastaMsmAir`'s, unchanged** — a windowed run
   ends by threading its final accumulator into `pallasCompleteAdd` with `delta` and the two
   `fpIsZeroCore` gates. Those are one extra row and two gates; they are not re-emitted here.
-/

end Dregg2.Circuit.Emit.PastaMsmWindowed
