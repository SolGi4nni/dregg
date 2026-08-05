/-
# Dregg2.Circuit.Emit.PastaMsmBucketed — the **BUCKETED** MSM as a dregg AIR, and the retraction
of `PastaMsmLayouts` §7.3.

## Substrate, said out loud (HOUSE LAW #1)

**Lean-authored AIR.** Every gate here is a `def` returning `VmConstraint2`; every theorem is
about the ACTUALLY EMITTED list. Rust hand-writes no constraint, no `Builder` gadget and no
`air_accepts` predicate — it parses the emitted descriptor, fills trace CELLS and runs the
deployed prover. The curve arithmetic is **not re-authored**: `bucketedRowDesc_extends_windowed`
proves `PastaMsmWindowed.windowedRowDesc`'s 45 constraints are still a PREFIX, so the RCB complete
add in every row is the same `PastaCurveComplete.pallasCompleteAdd` the whole cone already uses.

## §A — the refusal this file retracts, quoted, and why it was wrong

`PastaMsmLayouts` §7.3 priced Pippenger at ~`10^6` rows — *"the one algorithm that WOULD fit"* —
and refused it:

> *bucket accumulation is data-dependent ROUTING, and the descriptor IR reaches no general lookup.
> `VmConstraint2` has no permutation/sort constraint kind, and `TableSem` offers only
> `Range{bits}` and `ExactPublicRows` — verifier-known constants. … The one door is `MemOp` …
> That is a new prover arm plus a new emitter.*

**Both halves are false, and the second one is false against this cone's own sibling.**

1. **`ExactPublicRows` is not a subset lookup — it is a PERMUTATION.**
   `DescriptorIR2.PublicLookupBalanced` demands the trace's lookup log be `Perm` of the declared
   manifest (`DescriptorIR2.lean:668-670`), not `Sublist` of it. A permutation between a witnessed
   trace column and a verifier-known list **is** a routing constraint: it says *these rows and no
   others, each exactly once*. `PastaMsmBound` already uses it that way — its
   `bound_forces_doubling` derives the `DBL` PATTERN by COUNTING manifest rows. §7.3 was written
   as though the mechanism it needed were absent from an IR that its own sibling file was already
   using for exactly this.

2. **The routing a bucketed MSM needs is a permutation against a verifier-known list**, not a
   witness-addressed memory. §C shows why: the thing that must be routed is *which generator is
   consumed at which sweep level*, and the SET of (window, generator) pairs is
   `{0..W} × {0..n}` — a Cartesian product, known to the verifier without knowing a single
   scalar. Only the *order* is data-dependent, and order is exactly what a permutation quantifies
   over.

⚑ So **no new constraint kind is required and none is proposed.** `MemOp` is not needed, no new
prover arm is needed, and the `TableAirIR` `.send`/`.receive` permutation bus (which is real —
`descriptor_ir2.rs:3690-3694` lowers it to `PermutationCheckBus`) is not needed either. What
§7.3 called "a new prover arm plus a new emitter" is one emitter, reusing three deployed teeth.

⚠ The one place §7.3's family of objections **does** still bite is named honestly in §7.2 below,
and it is a different objection than the one it made: `MAX_EXACT_PUBLIC_CELLS`.

## §B — the size verdict, RE-DERIVED, and it moves twice

The circulating figure was `1,605,709` bucketed adds against the emitted scan's `16,713,720`
(`10.4×`), measured by `circuit/src/pasta_msm.rs::bucketed_add_count` — textbook Pippenger:
one bucket-add per term, then a `2·(2^c − 1)` running-sum collapse per window.

**That is not the cheapest layout, and the cheaper one is also the one that needs no bucket
storage.** §1 emits the FUSED running-sum: sweep the digit level `d` from `D = 2^c − 1` down to
`0`, add each term's generator to a `RUN` accumulator at the row where the sweep is at that
term's digit, and fold `RUN` into `TOT` once per level. Because

  `Σ_i d_i·P_i = Σ_{d=1}^{D} ( Σ_{i : d_i ≥ d} P_i )`,

the buckets never materialise: `RUN` *is* the partial sum the collapse would have rebuilt. The
collapse's `2·(2^c − 1)` adds per window become `2^c − 1`, and — this is the part that matters
for the IR question — **there is nothing to address.** No bucket is ever read back, so no
witness-addressed memory is ever needed. `fusedBeatsBucketed` and `fusedBeatsNaive` are the
named theorems.

Measured against the real object (`n = 65,536` Vesta generators, `nbits = 255`), best window:

  | layout                                   | group ops    | ÷ naive | ÷ `2^21` |
  |------------------------------------------|--------------|---------|----------|
  | emitted bit-plane Horner scan (`nbits·(n+1)`) | 16,711,935 | 1.00×   | 7.97×    |
  | textbook Pippenger, `c = 12`             | 1,622,227    | 10.30×  | 0.774×   |
  | **fused running-sum, `c = 13`**          | **1,474,800**| **11.33×**| **0.703×**|

⚑ **So the row count fits one instance with no cut at all**, at `70.3%` of the `2^21` two-adicity
ceiling — `log_blowup = 6` and BabyBear `TWO_ADICITY = 27`, unchanged. The four-way cut
`PastaMsmSliced` exists to avoid is not needed for the ROWS. §7.1 says what that does and does
not buy, because the row count is not the only axis and this file does not pretend it is.

## §C — what the emitted object FORCES, in one place

Three exact-public manifests, three lookups, and the arithmetic template:

  * **`T_SCHED`** — `(tidx+1, dbl, win+1)`, one row per trace row, UNGUARDED. The window index and
    the doubling rows are verifier-known functions of the row index (each window is `c` doublings
    then `n + D` sweep rows — a CONSTANT length, because a term whose digit is 0 still occupies a
    row). This is what stops a prover choosing its own window structure.
  * **`T_COVER`** — `(win+1, gidx+1, dgt)`, guarded by `ISTERM`. Its manifest is the `W·n` real
    triples `(w, i, digit_w(s_i))` plus one all-zero row per non-term row. Being a PERMUTATION,
    it forces **each (window, generator) pair to be consumed exactly once, at the sweep level
    equal to that term's declared digit.** This single lookup is the whole routing.
  * **`T_SRS`** — `(gidx+1, 27 limbs)`, guarded by `ISTERM`: the row's `GEN` columns carry the real
    `srs.g[gidx]`, the same device `PastaMsmBound` uses.

and per row a single RCB complete add whose operands are SELECTED by the row mode
(§2): `TERM ⇒ RUN += GEN`, `STEP ⇒ TOT += RUN`, `DBL ⇒ TOT += TOT` with `RUN` reset to `O`.

## §D — what it does NOT force. Read this before citing the file.

⚑ **The digits are DECLARED, not DERIVED here.** `T_COVER`'s manifest carries
`digit_w(s_i)` as a descriptor parameter, exactly as `PastaMsmBound.manifestRow` carries
`scalarDigit`. So this descriptor is scalar-specialised: it forces the trace to compute
`Σ_i s_i·g_i` for the `s` the DESCRIPTOR names, and says nothing about where that `s` came from.
Binding `s` to `b_poly_coefficients(u⃗)` of a block's IPA challenges is a DIFFERENT, ALREADY-BUILT
rung — `PastaMsmScalarDerive`, whose `deriveRowDesc` recomputes `s_i = ∏_j c_j^{bit_j(i)}` from the
challenge vector on the wire and is proved at `4 × 1024 × 2131`. §7.3 states the weld and what it
costs, and it is CHEAPER here than there by construction: the derivation is repeated once per
row, and this layout has `20` rows per term where the bit-plane scan has `256`.

⚑ **And the control the native oracle already fails, this circuit fails identically**: a claim
REBUILT around tampered challenges — new challenges, new `s`, new `C` — is accepted, because the
relation binds the PAIR. Nothing in an MSM AIR can fix that; the challenges must be committed
elsewhere. §7.4.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. Named theorems, not `#guard`s. Imports read-only. NEW file; NOT imported by the
`Dregg2` root, per house practice for gates. Import line:
`import Dregg2.Circuit.Emit.PastaMsmBucketed`
-/
import Dregg2.Circuit.Emit.PastaMsmBound

namespace Dregg2.Circuit.Emit.PastaMsmBucketed

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2 EffectVmDescriptor2 WindowExpr WindowConstraint
  TableId TableDef Lookup)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.Bls12381Tower (evalH_mul)
open Dregg2.Circuit.Emit.PastaField (numLimbs limbBits fpValue fpVal fpVal_eq)
open Dregg2.Circuit.Emit.PastaMsmWindowed (wVal cw threadBody
  ACCX ACCY ACCZ OPX OPY OPZ SRCX SRCY SRCZ BIT DBL OUTX OUTY OUTZ windowedRowDesc)
open Dregg2.Circuit.Emit.PastaMsmBound (limbNat coordLimb limbsOfPt PTLIMBS)

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §0 — THE COST MODEL, re-derived rather than quoted.

Three closed forms over `(n, nbits, c)`, and the theorems that order them. Everything here is
`Nat` arithmetic the kernel decides; nothing is measured, sampled or asserted. -/

/-- Number of `c`-bit windows a `nbits`-bit scalar needs. -/
def windowsOf (nbits c : Nat) : Nat := (nbits + c - 1) / c

/-- The number of nonzero digit values in a `c`-bit window: `2^c − 1`. -/
def levelsOf (c : Nat) : Nat := 2 ^ c - 1

/-- **The EMITTED bit-plane Horner scan** — `PastaMsmLayouts.hornerRcbAdds`, restated so the
comparison is computed here and not quoted from another file. -/
def naiveAdds (n nbits : Nat) : Nat := nbits * (n + 1)

/-- **Textbook Pippenger** — one bucket-add per term per window, a `2·(2^c − 1)` running-sum
collapse per window, and `nbits` inter-window doublings. The closed form
`circuit/src/pasta_msm.rs::bucketed_add_count` computes. -/
def bucketedAdds (n nbits c : Nat) : Nat :=
  windowsOf nbits c * (n + 2 * levelsOf c) + nbits

/-- ⚑ **The FUSED running-sum** — what this file emits. Per window: `c` doubling rows, `n` term
rows (a zero digit still occupies one, which is what keeps the window length CONSTANT and hence
the schedule verifier-known), and `2^c − 1` level-fold rows.

The buckets are gone: `RUN` holds `Σ_{i : d_i ≥ d} P_i` directly, so nothing is ever stored at a
witness-dependent address and nothing is ever read back. -/
def fusedAdds (n nbits c : Nat) : Nat :=
  windowsOf nbits c * (c + n + levelsOf c)

/-- The trace height the emitted descriptor needs — one row per group operation. -/
def bucketedRows (n nbits c : Nat) : Nat := fusedAdds n nbits c

/-- The number of TERM rows: one per generator per window. This is also the size of `T_COVER`'s
real (non-padding) manifest content. -/
def termRows (n nbits c : Nat) : Nat := windowsOf nbits c * n

/-! ### §0b — the numbers, as named theorems over the REAL object.

`n = 65,536` Vesta generators (`accumulator_check.rs`'s `urs: &SRS<Vesta>` at `2^16`), full-width
`nbits = 255` scalars. `DREGG_MAX_ROWS = 2^21` is BabyBear's two-adicity `27` minus the deployed
`IR2_FRI_LOG_BLOWUP = 6`, unchanged by anything here. -/

/-- The Step/Tick SRS width. -/
def STEP_SRS : Nat := 65536
/-- Full-width Pasta scalars. -/
def FULL_BITS : Nat := 255
/-- The window this file recommends at the real parameters (§0c proves it optimal over `1..20`). -/
def BEST_C : Nat := 13

/-- The deployed row ceiling: `BabyBear::TWO_ADICITY (27) − IR2_FRI_LOG_BLOWUP (6)`. -/
def DREGG_MAX_ROWS : Nat := 2097152

/-- The emitted scan's height at the real object. -/
theorem naive_at_step : naiveAdds STEP_SRS FULL_BITS = 16711935 := by decide

/-- Textbook Pippenger at its own best window. -/
theorem bucketed_at_step : bucketedAdds STEP_SRS FULL_BITS 12 = 1622227 := by decide

/-- ⚑ **The fused layout's height at the real object.** -/
theorem fused_at_step : fusedAdds STEP_SRS FULL_BITS BEST_C = 1474800 := by decide

/-- ⚑ **IT FITS ONE INSTANCE, WITH NO CUT.** The whole `2^16`-generator MSM is below the two-adicity
ceiling at the deployed `log_blowup = 6` — the four-way cut `PastaMsmSliced` exists to dodge is not
needed for the ROW count. (§7.1 says what else it was buying.) -/
theorem fused_fits_one_instance : fusedAdds STEP_SRS FULL_BITS BEST_C < DREGG_MAX_ROWS := by decide

/-- …and by how much: `70.3%` of the ceiling, i.e. `29.7%` of headroom. Stated as an integer
inequality so no float appears in a claim. -/
theorem fused_uses_under_seventy_one_percent :
    100 * fusedAdds STEP_SRS FULL_BITS BEST_C < 71 * DREGG_MAX_ROWS := by decide

/-- ⚑ **The emitted scan does NOT fit**, by a factor of nearly eight — which is why the cut exists. -/
theorem naive_does_not_fit : DREGG_MAX_ROWS * 7 < naiveAdds STEP_SRS FULL_BITS := by decide

/-- ⚑ **The fused layout beats textbook Pippenger**, at each one's own best window. The saving is
the whole second half of the running-sum collapse. -/
theorem fusedBeatsBucketed :
    fusedAdds STEP_SRS FULL_BITS BEST_C < bucketedAdds STEP_SRS FULL_BITS 12 := by decide

/-- ⚑ **…and beats the emitted scan by more than 11×**, against the `10.4×` that circulated for
textbook Pippenger. Both bounds are stated, so the claim is bracketed rather than rounded. -/
theorem fusedBeatsNaive :
    11 * fusedAdds STEP_SRS FULL_BITS BEST_C < naiveAdds STEP_SRS FULL_BITS
    ∧ naiveAdds STEP_SRS FULL_BITS < 12 * fusedAdds STEP_SRS FULL_BITS BEST_C := by
  constructor <;> decide

/-- A window has at least as many DIGIT LEVELS as it has BITS — `c ≤ 2^c − 1`. This is the whole
reason the fused layout dominates: it trades one collapse add per level for `c` doublings, and
there are never fewer levels than bits. -/
theorem c_le_levels (c : Nat) : c ≤ levelsOf c := by
  have h : c < 2 ^ c := Nat.lt_two_pow_self
  simp only [levelsOf]; omega

/-- ⚑ **The generality behind the two instances above**: the fused layout costs no more than
textbook Pippenger at EVERY `(n, nbits, c)`, with no side condition at all. It drops one of the two
collapse adds per level (`2·L → L` per window) and pays `c` doublings per window instead of `nbits`
overall, and `c ≤ L` is `c_le_levels`. -/
theorem fused_le_bucketed (n nbits c : Nat) :
    fusedAdds n nbits c ≤ bucketedAdds n nbits c := by
  have h := Nat.mul_le_mul_left (windowsOf nbits c) (c_le_levels c)
  simp only [fusedAdds, bucketedAdds, Nat.mul_add, Nat.two_mul]
  omega

/-! ### §0c — `c = 13` is OPTIMAL, decided rather than searched by hand.

A cost claim that names a parameter is only as good as the parameter search behind it. This one is
a kernel `decide` over every window width the deployed prover could take. -/

/-- Every window width from 1 to 20 costs at least what `c = 13` costs, at the real object. -/
theorem best_c_is_thirteen :
    ((List.range 20).map (fun i => i + 1)).all
      (fun c => decide (fusedAdds STEP_SRS FULL_BITS BEST_C ≤ fusedAdds STEP_SRS FULL_BITS c))
      = true := by decide

/-- …and it is STRICTLY better than its neighbours, so `13` is not a plateau reported as a peak. -/
theorem best_c_is_strict :
    fusedAdds STEP_SRS FULL_BITS BEST_C < fusedAdds STEP_SRS FULL_BITS 12
    ∧ fusedAdds STEP_SRS FULL_BITS BEST_C < fusedAdds STEP_SRS FULL_BITS 14 := by
  constructor <;> decide

/-! ## §1 — THE ROW LAYOUT.

`PastaMsmWindowed` ends at width 525: the RCB working block at `0..441`, the threaded accumulator
`ACC` at `442..468`, the addend `OP` at `469..495`, the source point `SRC` at `496..522`, the
conditional bit `BIT` at `523` and the doubling selector `DBL` at `524`.

This file adds two THREADED POINT accumulators (the fused running sum and the total), one
manifest-bound generator group, two mode selectors and four small index columns. `ACC` and `SRC`
stop being free: §2 SELECTS them from the two accumulators and the generator, which is what makes
one row template serve three different group operations. -/

/-- The FUSED RUNNING SUM `Σ_{i : d_i ≥ dgt} g_i` — 27 columns, threaded. -/
def RUNX : Nat := 525
def RUNY : Nat := 534
def RUNZ : Nat := 543

/-- The window TOTAL `Σ_i d_i·g_i` so far — 27 columns, threaded. -/
def TOTX : Nat := 552
def TOTY : Nat := 561
def TOTZ : Nat := 570

/-- The manifest-bound GENERATOR this row consumes (meaningful iff `ISTERM = 1`) — 27 columns. -/
def GENX : Nat := 579
def GENY : Nat := 588
def GENZ : Nat := 597

/-- Mode: this row folds a generator into `RUN`. -/
def ISTERM : Nat := 606
/-- Mode: this row folds `RUN` into `TOT` (one sweep level closes). -/
def ISSTEP : Nat := 607

/-! The THIRD mode needs no new column: `PastaMsmWindowed.DBL` is reused verbatim
(`TOT += TOT`, `RUN := O`), which is why its booleanity and its `dblPinGates` come for free
from the inherited row template. -/

/-- The THREADED ROW INDEX — pinned to `0` on the first row, `+1` every row. It is what ties a
trace row to a `T_SCHED` manifest row; without it the multiset would say WHICH schedule rows occur
but not WHERE. Same device as `PastaMsmBound.TIDX`. -/
def TIDX : Nat := 608
/-- The WINDOW index this row belongs to, forced from `TIDX` by `T_SCHED`. -/
def WIN : Nat := 609
/-- The ABSOLUTE generator index this row consumes (meaningful iff `ISTERM = 1`). -/
def GIDX : Nat := 610
/-- The SWEEP LEVEL: the digit value currently being folded. Starts at `2^c − 1` in each window and
decrements by exactly one at each `ISSTEP` row. -/
def DGT : Nat := 611

/-- The bucketed row template's width. -/
def WK : Nat := 612

/-! ## §2 — THE EMITTED GATES.

Everything below is a `def` producing `VmConstraint2`. `Head.mul` (from `Bls12381Tower`, the
single source the whole cone uses) multiplies a selector column into a 9-limb VALUE head, so a
point select is 3 gates rather than 27 limb pins — and the conclusion lands directly on `fpVal`,
which is the predicate `PointIsZ` and every forcing lemma in this cone is stated in. -/

/-- `sel · (value at `base`)`. -/
def selTerm (sel base : Nat) : Head := (Head.lin 1 sel).mul (fpValue base)

/-- `(1 − sel) · (value at `base`)`. -/
def coselTerm (sel base : Nat) : Head := ((Head.lin (-1) sel).addConst 1).mul (fpValue base)

/-- `selTerm` evaluates to the product of the selector cell and the reconstructed field element. -/
theorem selTerm_eval (a : Assignment) (sel base : Nat) :
    evalH (selTerm sel base) a = a sel * fpVal a base := by
  simp only [selTerm, evalH_mul, evalH_lin, fpVal_eq]; ring

theorem coselTerm_eval (a : Assignment) (sel base : Nat) :
    evalH (coselTerm sel base) a = (1 - a sel) * fpVal a base := by
  simp only [coselTerm, evalH_mul, evalH_addConst, evalH_lin, fpVal_eq]; ring

/-! ### §2a — the mode pins.

`ISTERM`, `ISSTEP` and `DBL` are booleans summing to one, so exactly one of the three group
operations happens per row. `BIT` is pinned ON because every row of this layout really does add
its selected source — the conditional-add bit is what `PastaMsmWindowed` used to skip a zero digit,
and this layout skips nothing (that is the price of a CONSTANT window length, and it is why
`fusedAdds` counts `n` and not the number of nonzero digits). -/

/-- `ISTERM + ISSTEP + DBL − 1`. -/
def modeSumHead : Head :=
  (((Head.lin 1 ISTERM).addLin 1 ISSTEP).addLin 1 DBL).addConst (-1)

/-- `BIT − 1`: the selector always passes its source through. -/
def bitOnHead : Head := (Head.lin 1 BIT).addConst (-1)

/-- The four mode pins. `DBL`'s own booleanity comes from `PastaMsmWindowed.rowGates`. -/
def modeGates : List VmConstraint2 :=
  [ binGate ISTERM, binGate ISSTEP, cgH modeSumHead, cgH bitOnHead ]

/-! ### §2b — the OPERAND SELECTS: one row template, three group operations.

`ACC = ISTERM·RUN + (1 − ISTERM)·TOT` and `SRC = ISTERM·GEN + ISSTEP·RUN + DBL·TOT`. Feeding those
through `PastaMsmWindowed`'s already-proved template gives, per mode:

  * `ISTERM` ⇒ `OUT = RUN + GEN`;
  * `ISSTEP` ⇒ `OUT = TOT + RUN`;
  * `DBL`    ⇒ `OUT = TOT + TOT`, and `dblPinGates` independently forces `SRC = ACC`, so the
    doubling row is STRUCTURALLY a doubling exactly as it already was.

Degree 2 throughout, against `MAX_CONSTRAINT_DEGREE = 8`. -/

/-- `ISTERM·RUN + (1 − ISTERM)·TOT − ACC`, per coordinate. -/
def accSelHead (runB totB accB : Nat) : Head :=
  ((selTerm ISTERM runB).append (coselTerm ISTERM totB)).append ((fpValue accB).scale (-1))

/-- `ISTERM·GEN + ISSTEP·RUN + DBL·TOT − SRC`, per coordinate. -/
def srcSelHead (genB runB totB srcB : Nat) : Head :=
  (((selTerm ISTERM genB).append (selTerm ISSTEP runB)).append (selTerm DBL totB)).append
    ((fpValue srcB).scale (-1))

theorem accSelHead_eval (a : Assignment) (runB totB accB : Nat) :
    evalH (accSelHead runB totB accB) a
      = a ISTERM * fpVal a runB + (1 - a ISTERM) * fpVal a totB - fpVal a accB := by
  simp only [accSelHead, evalH_append, evalH_scale, selTerm_eval, coselTerm_eval, fpVal_eq]; ring

theorem srcSelHead_eval (a : Assignment) (genB runB totB srcB : Nat) :
    evalH (srcSelHead genB runB totB srcB) a
      = a ISTERM * fpVal a genB + a ISSTEP * fpVal a runB + a DBL * fpVal a totB
        - fpVal a srcB := by
  simp only [srcSelHead, evalH_append, evalH_scale, selTerm_eval, fpVal_eq]; ring

/-- The six operand selects. -/
def selectGates : List VmConstraint2 :=
  [ cgH (accSelHead RUNX TOTX ACCX)
  , cgH (accSelHead RUNY TOTY ACCY)
  , cgH (accSelHead RUNZ TOTZ ACCZ)
  , cgH (srcSelHead GENX RUNX TOTX SRCX)
  , cgH (srcSelHead GENY RUNY TOTY SRCY)
  , cgH (srcSelHead GENZ RUNZ TOTZ SRCZ) ]

/-! ### §2c — THE TWO THREADS.

`PastaMsmWindowed`'s thread was unconditional (`nxt ACC = loc OUT`); here each of the two
accumulators advances only in the modes that touch it, and `RUN` RESETS to the RCB point at
infinity `O = (0 : 1 : 0)` on a doubling row. That reset is where a bucket would have been
cleared, and it costs one constant term in one window gate rather than a memory write. -/

/-- `k · (loc column)` inside a window expression. -/
def wSel (sel : Nat) (e : WindowExpr) : WindowExpr := .mul (.loc sel) e

/-- `nxt RUN = ISTERM·OUT + ISSTEP·RUN + DBL·O`, coordinate by coordinate. `oConst` is the
coordinate of `O`: `0` for `X` and `Z`, `1` for `Y`. -/
def runThreadBody (runB outB : Nat) (oConst : Int) : WindowExpr :=
  .add (wVal .nxt runB)
    (.mul (.const (-1))
      (.add (.add (wSel ISTERM (wVal .loc outB)) (wSel ISSTEP (wVal .loc runB)))
            (wSel DBL (.const oConst))))

/-- `nxt TOT = ISTERM·TOT + (ISSTEP + DBL)·OUT`. -/
def totThreadBody (totB outB : Nat) : WindowExpr :=
  .add (wVal .nxt totB)
    (.mul (.const (-1))
      (.add (wSel ISTERM (wVal .loc totB))
            (.mul (.add (.loc ISSTEP) (.loc DBL)) (wVal .loc outB))))

/-- The six thread gates. -/
def threadGatesK : List VmConstraint2 :=
  [ cw (runThreadBody RUNX OUTX 0)
  , cw (runThreadBody RUNY OUTY 1)
  , cw (runThreadBody RUNZ OUTZ 0)
  , cw (totThreadBody TOTX OUTX)
  , cw (totThreadBody TOTY OUTY)
  , cw (totThreadBody TOTZ OUTZ) ]

/-! ### §2d — THE SWEEP COUNTER, and why it needs no comparator.

`PastaMsmLayouts` §7.3 expected a SORT constraint, and a sort needs a comparator the IR has no
constructor for. It is not needed. `DGT` starts at `D` in each window, decrements by exactly
`ISSTEP` each row, and is re-pinned to `D` on a doubling row:

    `nxt DGT = (1 − DBL)·(DGT − ISSTEP) + DBL·D`

A monotone counter with a fixed number of rows per window forces exactly `D` step rows per window
without any row ever being compared to another. **The order the sort would have imposed is
imposed instead by `T_COVER`'s permutation**, which says every `(window, generator)` pair occurs
once at its declared level — and a permutation over a verifier-known list is not a comparator. -/

/-- `nxt DGT − ((1 − DBL)·(DGT − ISSTEP) + DBL·D)`. -/
def dgtThreadBody (levels : Nat) : WindowExpr :=
  .add (.nxt DGT)
    (.mul (.const (-1))
      (.add (.mul (.add (.const 1) (.mul (.const (-1)) (.loc DBL)))
                  (.add (.loc DGT) (.mul (.const (-1)) (.loc ISSTEP))))
            (.mul (.loc DBL) (.const (levels : Int)))))

/-- `nxt TIDX − (TIDX + 1)`: the row index advances by one, every row. -/
def tidxThreadBody : WindowExpr :=
  .add (.nxt TIDX) (.mul (.const (-1)) (.add (.loc TIDX) (.const 1)))

/-- `TIDX = 0` on the FIRST row. -/
def tidxStartGate : VmConstraint2 := .base (.boundary .first (.var TIDX))

/-- The three index gates. -/
def indexGates (levels : Nat) : List VmConstraint2 :=
  [ tidxStartGate, cw tidxThreadBody, cw (dgtThreadBody levels) ]

/-! ## §3 — THE THREE MANIFESTS, and the lookups that consume them.

Every one is `TableSem.exactPublicRows`, read through `DescriptorIR2.PublicLookupBalanced` — a
PERMUTATION of the declared list, not a containment. -/

/-- ⚑ Distinct wire ids per table, above every reserved id. **The distinctness is load-bearing**,
for the reason `PastaMsmBound.GEN_TID` records: `exact_public_bus_name` keys the LogUp bus by
ARITY since the 2026-08-02 Lean cutover, and the table id rides in the tuple as field 0 — so two
tables of the same arity in one batch separate by their id VALUE, and two tables sharing an id
would pool their capacity. -/
def SCHED_TID : TableId := .custom 50
def COVER_TID : TableId := .custom 51
def SRS_TID   : TableId := .custom 52

/-- `T_SCHED`'s arity: row key, doubling flag, window index. -/
def SCHED_TUP : Nat := 3
/-- `T_COVER`'s arity: window index, generator index, sweep level. -/
def COVER_TUP : Nat := 3
/-- `T_SRS`'s arity: generator index plus the 27 limb columns. -/
def SRS_TUP : Nat := 1 + PTLIMBS

/-- The `ISTERM` guard as an emitted expression: a non-term row emits the all-zero tuple, which
the manifest carries once per non-term row. -/
def isTermE : EmittedExpr := .var ISTERM

/-- `T_SCHED`'s tuple — UNGUARDED, because every row has a schedule. -/
def schedTuple : List EmittedExpr :=
  [ .add (.var TIDX) (.const 1), .var DBL, .add (.var WIN) (.const 1) ]

/-- `T_COVER`'s tuple, guarded: `(WIN+1, GIDX+1, DGT)` on a term row, all-zero otherwise. The `+1`
on the two index fields keeps the zero tuple OUT of the term key space. -/
def coverTuple : List EmittedExpr :=
  [ .mul isTermE (.add (.var WIN) (.const 1))
  , .mul isTermE (.add (.var GIDX) (.const 1))
  , .mul isTermE (.var DGT) ]

/-- `T_SRS`'s tuple, guarded: `(GIDX+1, GEN limbs)`. -/
def srsTuple : List EmittedExpr :=
  (.mul isTermE (.add (.var GIDX) (.const 1)))
    :: (List.range PTLIMBS).map (fun j => EmittedExpr.mul isTermE (.var (GENX + j)))

/-- ⚑ **The 27 published output limbs.** At the LAST row the window TOTAL's limb columns are pinned
to the descriptor's public inputs, so the claimed `C` is ON THE WIRE and a verifier COMPARES it
rather than reading it out of a trace it was handed.

Without this the descriptor would prove *some* MSM and bind its answer to nothing — which is
exactly the shape a forged-`sg` test cannot refute, and therefore the shape a forged-`sg` test
would silently pass. `.piBinding .last` is the same device `PastaMsmSliced.outPiGates` uses for its
slice partial. -/
def PI_OUT : Nat := 0

/-- The public-input count: the 27 limbs of the claimed commitment. -/
def PI_COUNT : Nat := 27

/-- The 27 emitted output bindings. -/
def outPiGates : List VmConstraint2 :=
  (List.range 27).map (fun i => .base (.piBinding .last (TOTX + i) (PI_OUT + i)))

/-- The three lookups. -/
def lookupGates : List VmConstraint2 :=
  [ .lookup ⟨SCHED_TID, schedTuple⟩
  , .lookup ⟨COVER_TID, coverTuple⟩
  , .lookup ⟨SRS_TID, srsTuple⟩ ]

/-! ### §3b — the manifest CONTENTS, as `def`s over the parameters.

Every one is a function of `(n, nbits, c, gens, scal)` alone, so what the descriptor declares is
the same object the kernel evaluates — not a re-transcription. -/

/-- Rows per window: `c` doublings, then `n` term rows and `2^c − 1` level folds. CONSTANT in the
scalars, which is exactly what makes `T_SCHED` verifier-known. -/
def winLen (n c : Nat) : Nat := c + n + levelsOf c

/-- The window a trace row belongs to. -/
def winAt (n c i : Nat) : Nat := i / winLen n c

/-- Whether a trace row is one of its window's leading `c` doubling rows. -/
def isDblAt (n c i : Nat) : Bool := decide (i % winLen n c < c)

/-- `T_SCHED`'s row for trace row `i`. -/
def schedRow (n c i : Nat) : List Nat :=
  [ i + 1, if isDblAt n c i then 1 else 0, winAt n c i + 1 ]

/-- `T_SCHED`'s whole manifest — one row per trace row, which is what the permutation demands. -/
def schedManifest (n nbits c : Nat) : List (List Nat) :=
  (List.range (bucketedRows n nbits c)).map (schedRow n c)

/-- The `c`-bit digit of `scal[i]` in window `w`, MSB-first over `windowsOf nbits c` windows —
the same convention `PastaMsmBound.scalarDigit` uses at one bit per plane. -/
def scalarDigitC (scal : List Nat) (nbits c w i : Nat) : Nat :=
  ((scal.getD i 0) / 2 ^ (c * (windowsOf nbits c - 1 - w))) % 2 ^ c

/-- ⚑ **`T_COVER`'s manifest** — the `W·n` real triples `(w+1, i+1, digit_w(s_i))`, then one
all-zero row for every non-term row of the trace. Its LENGTH is the trace height, because the
balance is a PERMUTATION and the lookup log has one entry per row.

**This one list is the entire routing.** It says: each generator is consumed exactly once per
window, at the sweep level equal to its digit — and nothing else is consumed at all. -/
def coverManifest (n nbits c : Nat) (scal : List Nat) : List (List Nat) :=
  ((List.range (windowsOf nbits c)).flatMap
      (fun w => (List.range n).map (fun i => [w + 1, i + 1, scalarDigitC scal nbits c w i])))
    ++ List.replicate (bucketedRows n nbits c - termRows n nbits c) (List.replicate COVER_TUP 0)

/-- `T_SRS`'s manifest: the real generator limbs, each declared once per window, then the
all-zero padding. -/
def srsManifest (n nbits c : Nat) (gens : List (Nat × Nat × Nat)) : List (List Nat) :=
  ((List.range (windowsOf nbits c)).flatMap
      (fun _ => (List.range n).map (fun i => (i + 1) :: limbsOfPt (gens.getD i (0, 0, 0)))))
    ++ List.replicate (bucketedRows n nbits c - termRows n nbits c) (List.replicate SRS_TUP 0)

/-- The three declared tables. -/
def bucketedTables (n nbits c : Nat) (gens : List (Nat × Nat × Nat)) (scal : List Nat) :
    List TableDef :=
  [ ⟨SCHED_TID, "pasta_msm_schedule", SCHED_TUP, .exactPublicRows (schedManifest n nbits c)⟩
  , ⟨COVER_TID, "pasta_msm_cover", COVER_TUP, .exactPublicRows (coverManifest n nbits c scal)⟩
  , ⟨SRS_TID, "pasta_msm_srs", SRS_TUP, .exactPublicRows (srsManifest n nbits c gens)⟩ ]

/-! ## §4 — THE EMITTED DESCRIPTOR. -/

/-- ⚑ **The bucketed MSM descriptor.** `PastaMsmWindowed.windowedRowDesc`'s 45 constraints
verbatim — so the RCB complete add, the conditional select and the doubling pins are the SAME
already-proved objects — plus 4 mode pins, 6 operand selects, 6 threads, 3 index gates and 3
lookups, and 27 output PI bindings. `94` constraints, a CONSTANT at every `(n, nbits, c)`. -/
def bucketedRowDesc (n nbits c : Nat) (gens : List (Nat × Nat × Nat)) (scal : List Nat) :
    EffectVmDescriptor2 :=
  { name        := "dregg-pasta-msm-bucketed-c" ++ toString c ++ "::v1"
  , traceWidth  := WK
  , piCount     := PI_COUNT
  , tables      := bucketedTables n nbits c gens scal
  , constraints := windowedRowDesc.constraints
                     ++ modeGates ++ selectGates ++ threadGatesK
                     ++ indexGates (levelsOf c) ++ lookupGates ++ outPiGates
  , hashSites   := []
  , ranges      := [] }

/-- ⚑ **Nothing was re-authored.** The windowed row template — and with it
`PastaCurveComplete.pallasCompleteAdd`'s 33 gates, which is the curve arithmetic the whole cone
shares — is still a PREFIX of the emitted list. -/
theorem bucketedRowDesc_extends_windowed (n nbits c : Nat)
    (gens : List (Nat × Nat × Nat)) (scal : List Nat) :
    windowedRowDesc.constraints <+: (bucketedRowDesc n nbits c gens scal).constraints :=
  ⟨modeGates ++ selectGates ++ threadGatesK ++ indexGates (levelsOf c) ++ lookupGates
     ++ outPiGates,
   by simp [bucketedRowDesc, List.append_assoc]⟩

/-- The emitted constraint count, and it does not depend on the size of the MSM. -/
theorem bucketedRowDesc_constraints_length (n nbits c : Nat)
    (gens : List (Nat × Nat × Nat)) (scal : List Nat) :
    (bucketedRowDesc n nbits c gens scal).constraints.length = 94 := by
  simp [bucketedRowDesc, modeGates, selectGates, threadGatesK, indexGates, lookupGates, outPiGates,
    Dregg2.Circuit.Emit.PastaMsmWindowed.windowedRowDesc_constraints_length]

/-- The three declared tables, and their arities. -/
theorem bucketedRowDesc_tables (n nbits c : Nat)
    (gens : List (Nat × Nat × Nat)) (scal : List Nat) :
    (bucketedRowDesc n nbits c gens scal).tables.length = 3
    ∧ ((bucketedRowDesc n nbits c gens scal).tables.map TableDef.arity) = [3, 3, 28] :=
  ⟨rfl, rfl⟩

/-! ### §4b — the deployed checker's OWN column predicate, discharged in the kernel.

`circuit/src/descriptor_ir2.rs` refuses a descriptor whose any constraint references a column
`≥ trace_width`. Here it is as a `decide` over the ACTUALLY EMITTED list — the same shape
`PastaMsmWindowed.windowedRowDesc_columns_in_bounds` has, and the check that
`PastaMsmAir.minaOpeningCheckDesc` fails. -/

/-- The largest column index a `WindowExpr` addresses (Rust `WindowExpr::max_var`). -/
def wMaxVar : WindowExpr → Nat
  | .loc c   => c + 1
  | .nxt c   => c + 1
  | .const _ => 0
  | .add a b => max (wMaxVar a) (wMaxVar b)
  | .mul a b => max (wMaxVar a) (wMaxVar b)

/-- The largest column index an `EmittedExpr` addresses. -/
def eMaxVar : EmittedExpr → Nat
  | .var c   => c + 1
  | .const _ => 0
  | .add a b => max (eMaxVar a) (eMaxVar b)
  | .mul a b => max (eMaxVar a) (eMaxVar b)

/-- The largest column index a `VmConstraint2` addresses. -/
def kMaxVar : VmConstraint2 → Nat
  | .base (.gate e) => eMaxVar e
  | .base (.boundary _ e) => eMaxVar e
  | .base (.piBinding _ col _) => col + 1
  | .base _ => 0
  | .lookup l => (l.tuple.map eMaxVar).foldl max 0
  | .windowGate w => wMaxVar w.body
  | _ => 0

/-- ⚑ **Every column any emitted constraint addresses is `< WK`** — the exact predicate the
deployed checker enforces, discharged before the prover ever sees the descriptor. Stated at a toy
parameter set because the constraint list is size-independent (`bucketedRowDesc_constraints_length`)
and so is the column set. -/
theorem bucketedRowDesc_columns_in_bounds :
    ((bucketedRowDesc 4 4 2 [] []).constraints.all
      (fun k => decide (kMaxVar k ≤ WK))) = true := by decide

/-- The PI SLOT a constraint addresses — a DIFFERENT index space from the columns, and the one a
column-only bound check structurally cannot see. -/
def kMaxPi : VmConstraint2 → Nat
  | .base (.piBinding _ _ k) => k + 1
  | _ => 0

/-- Every emitted `piBinding` addresses a PI slot below the declared `piCount`. -/
theorem bucketedRowDesc_pi_indices_in_bounds :
    ((bucketedRowDesc 4 4 2 [] []).constraints.all
      (fun k => decide (kMaxPi k ≤ PI_COUNT))) = true := by decide

/-! ## §5 — WHAT THE ROUTING FORCES.

Two theorems, both about the EMITTED manifests rather than about an intended reading of them. -/

/-- The manifest length IS the trace height, for all three tables — which is what
`PublicLookupBalanced` needs, since the lookup log has exactly one entry per row per lookup. A
mismatch here would make the permutation unsatisfiable at every witness, i.e. a descriptor that
refuses everything, which is the failure mode a length theorem exists to exclude. -/
theorem manifest_lengths_are_the_trace_height (n nbits c : Nat)
    (gens : List (Nat × Nat × Nat)) (scal : List Nat)
    (h : termRows n nbits c ≤ bucketedRows n nbits c) :
    (schedManifest n nbits c).length = bucketedRows n nbits c
    ∧ (coverManifest n nbits c scal).length = bucketedRows n nbits c
    ∧ (srsManifest n nbits c gens).length = bucketedRows n nbits c := by
  have hterm : termRows n nbits c = windowsOf nbits c * n := rfl
  rw [hterm] at h
  refine ⟨by simp [schedManifest], ?_, ?_⟩
  · have hc : (coverManifest n nbits c scal).length
        = windowsOf nbits c * n + (bucketedRows n nbits c - windowsOf nbits c * n) := by
      simp [coverManifest, List.length_flatMap, hterm]
    omega
  · have hs : (srsManifest n nbits c gens).length
        = windowsOf nbits c * n + (bucketedRows n nbits c - windowsOf nbits c * n) := by
      simp [srsManifest, List.length_flatMap, hterm]
    omega

/-- The hypothesis of the above, discharged: a window always has at least its `c` doubling rows and
its `2^c − 1` level folds on top of its `n` term rows. -/
theorem termRows_le_bucketedRows (n nbits c : Nat) :
    termRows n nbits c ≤ bucketedRows n nbits c := by
  simp only [termRows, bucketedRows, fusedAdds]
  exact Nat.mul_le_mul_left _ (by omega)

/-- ⚑ **THE COVERAGE PROPERTY, read off the emitted manifest.** `T_COVER` declares exactly one
triple per `(window, generator)` pair and nothing else but padding. Because
`PublicLookupBalanced` is a `Perm`, a satisfying trace's term rows are a REORDERING of this list:
every generator is folded exactly once in every window, at the sweep level the manifest names.

This is the statement `PastaMsmLayouts` §7.3 said the IR could not make. -/
theorem coverManifest_is_the_full_grid (n nbits c : Nat) (scal : List Nat) :
    (coverManifest n nbits c scal).take (termRows n nbits c)
      = (List.range (windowsOf nbits c)).flatMap
          (fun w => (List.range n).map
            (fun i => [w + 1, i + 1, scalarDigitC scal nbits c w i])) := by
  have hlen : ((List.range (windowsOf nbits c)).flatMap
      (fun w => (List.range n).map
        (fun i => [w + 1, i + 1, scalarDigitC scal nbits c w i]))).length
      = termRows n nbits c := by
    simp [termRows, List.length_flatMap]
  simp [coverManifest, ← hlen]

/-- …and every declared cover row carries a digit that really is a `c`-bit digit, so a manifest
cannot smuggle an out-of-range level past the sweep counter. -/
theorem coverManifest_digits_are_c_bit (scal : List Nat) (nbits c w i : Nat) :
    scalarDigitC scal nbits c w i < 2 ^ c :=
  Nat.mod_lt _ (Nat.two_pow_pos c)

/-! ## §6 — THE CELL BUDGET, and the one place a deployed cap really does bind.

`MAX_EXACT_PUBLIC_ROWS = 2^21`, `MAX_EXACT_PUBLIC_ARITY = 64`, `MAX_EXACT_PUBLIC_CELLS = 2^25`
(`circuit/src/descriptor_ir2.rs`). The cap is documented there as an ALLOCATION bound on the
verifier — *"a workload decision rather than a correctness one"* — not geometry. -/

/-- Declared manifest cells, per table. -/
def schedCells (n nbits c : Nat) : Nat := bucketedRows n nbits c * SCHED_TUP
def coverCells (n nbits c : Nat) : Nat := bucketedRows n nbits c * COVER_TUP
def srsCells (n nbits c : Nat) : Nat := bucketedRows n nbits c * SRS_TUP

/-- The deployed caps. -/
def MAX_EP_ROWS : Nat := 2097152
def MAX_EP_CELLS : Nat := 33554432
def MAX_EP_ARITY : Nat := 64

/-- Every manifest's ROW count clears the row cap at the real object — this is the same fact as
`fused_fits_one_instance`, because a permutation makes manifest rows and trace rows the same
number. -/
theorem manifest_rows_fit :
    bucketedRows STEP_SRS FULL_BITS BEST_C < MAX_EP_ROWS := by decide

/-- Every arity clears the arity cap. -/
theorem arities_fit : SCHED_TUP < MAX_EP_ARITY ∧ COVER_TUP < MAX_EP_ARITY
    ∧ SRS_TUP < MAX_EP_ARITY := by
  refine ⟨by decide, by decide, ?_⟩
  simp [SRS_TUP, PTLIMBS, numLimbs, MAX_EP_ARITY]

/-- The two narrow manifests clear the CELL cap comfortably. -/
theorem sched_and_cover_cells_fit :
    schedCells STEP_SRS FULL_BITS BEST_C < MAX_EP_CELLS
    ∧ coverCells STEP_SRS FULL_BITS BEST_C < MAX_EP_CELLS := by
  constructor <;> decide

/-- ⚑ **THE ONE CAP THAT BINDS, stated as the refutation it is.** At the real object the SRS
manifest declares `1,474,800 × 28 = 41,294,400` cells against the deployed `2^25 = 33,554,432`.
The descriptor would be REFUSED — not by geometry, and not by anything in this layout, but by an
allocation bound the file that sets it calls a workload decision.

Said plainly rather than routed around: **this is the one deployed number that has to move for the
full-width instance to parse**, and §7.2 prices the alternative that does not need it. -/
theorem srs_cells_exceed_the_deployed_cap :
    MAX_EP_CELLS < srsCells STEP_SRS FULL_BITS BEST_C := by decide

/-- …and the alternative that needs no cap change: split the 27 limb columns across TWO tables
keyed by the same generator index. Each half clears the cap, so the choice is between one constant
and one extra declared table. -/
theorem split_srs_cells_fit :
    bucketedRows STEP_SRS FULL_BITS BEST_C * 15 < MAX_EP_CELLS
    ∧ bucketedRows STEP_SRS FULL_BITS BEST_C * 14 < MAX_EP_CELLS := by
  constructor <;> decide

/-! ## §7 — ⚑ THE RESIDUALS, at CURRENT resolution.

**7.1 — the row count is not the only axis, and this file does not pretend it is.**
`fused_fits_one_instance` is a statement about ROWS. The committed area is `rows × width`:
`1,474,800 × 612 ≈ 9.03 · 10^8` cells of BabyBear, which is ~3.6 GB of main trace before any
low-degree extension — so "fits one instance" means *the two-adicity ceiling admits it*, NOT that
a box proves it. The four-way cut `PastaMsmSliced` exists for is therefore still buying something
real; what this file retracts is the claim that the ceiling FORCES a cut, and the claim that a
bucketed layout is inexpressible.

**7.2 — the gate these rows are denominated in is the UNSOUND one, unchanged.**
Every row here is one RCB complete add over `PastaField.fpMulCore`: one degree-2 gate of 81
cross-products, no limb ranges, no carry pins, `pastaLimbRange` emitted nowhere — so at
`p_babybear` its nine quotient limbs are free and the gate holds at every operand triple
(`PastaField` §6.4). A multiply sound at BabyBear is ≈`10^3` constraints, taking a complete add
from 33 to ≈`1.6 · 10^4`. **So `1,474,800` rows is the geometry of the unsound object**, exactly as
`PastaMsmSliced`'s `1,056,896` is. That does not soften the comparison — every layout in the table
is priced against the same gate — but it does mean the sound object is ~`10^3` further out, and no
layout choice reaches it.

**7.3 — the digits are declared, and the weld that derives them is BUILT.**
`T_COVER`'s manifest carries `scalarDigitC scal …` as a descriptor parameter, so this descriptor is
scalar-specialised. `PastaMsmScalarDerive.deriveRowDesc` already recomputes `s_i` from the block's
IPA challenges ON THE WIRE and is proved at `4 × 1024 × 2131`; welding it here replaces the
declared digit with a derived one and makes ONE verifying key check ANY Mina accumulator.

⚑ And the weld is CHEAPER in this layout than where it lives now, by construction. §6.3 of that
file measures its derivation block at 62.5% of everything committed, because the derivation is
repeated once per ROW and the bit-plane scan gives each term `planes = 256` rows. This layout gives
each term `windowsOf 255 13 = 20` rows. The redundancy factor drops 256 → 20.

⚑ **What is NOT stale in that file's §6.3, and the brief that sent me here had it half right.**
`TableBusOp::Provide` does exist and IS emitted — but only in the TABLE-AIR arm
(`descriptor_ir2.rs:3687`, reached from `Ir2Air::LeanTable`). The MAIN descriptor path still calls
`LookupBus::lookup_key` with multiplicity one and never `table_entry`, so a `provide` dual of
`Lookup` for an `EffectVmDescriptor2` is still absent. §6.3's parenthetical was true about the main
arm and wrong about the mechanism, and the mechanism is in a vocabulary the main descriptor cannot
reach. That remains an IR change.

**7.4 — ⚑ THE CONTROL THIS CIRCUIT DOES NOT PASS, and neither does the native oracle.**
A claim REBUILT around tampered challenges — new `u⃗`, recomputed `s`, recomputed `C` — is
accepted, here and natively, because the relation binds the PAIR `(s, C)` and both halves moved
together. This AIR forces that the trace computes `Σ s_i·g_i` over Mina's REAL generators and that
the answer is the declared `C`; it does not and cannot force that `u⃗` is the challenge vector of a
real Mina block. That binding is a transcript commitment, not an MSM constraint, and it lives
outside every object in this cone.

**7.5 — inherited without change.** P10 (passing ≠ knowing); the FRI floor; `srs.g` as the largest
piece of trusted data; RCB completeness cited from RCB'15 Thm 1 under the on-curve gate
`PastaMsmOnCurve` emits, which this descriptor does NOT yet compose (it extends `windowedRowDesc`,
not `onCurveRowDesc` — one prefix step below where the on-curve gate enters).
-/



/-! ## §8 — AXIOM HYGIENE, asserted rather than claimed. -/

#assert_axioms fused_at_step
#assert_axioms fused_fits_one_instance
#assert_axioms fusedBeatsNaive
#assert_axioms fusedBeatsBucketed
#assert_axioms fused_le_bucketed
#assert_axioms c_le_levels
#assert_axioms best_c_is_thirteen
#assert_axioms bucketedRowDesc_extends_windowed
#assert_axioms bucketedRowDesc_constraints_length
#assert_axioms bucketedRowDesc_columns_in_bounds
#assert_axioms bucketedRowDesc_pi_indices_in_bounds
#assert_axioms manifest_lengths_are_the_trace_height
#assert_axioms termRows_le_bucketedRows
#assert_axioms coverManifest_is_the_full_grid
#assert_axioms coverManifest_digits_are_c_bit
#assert_axioms srs_cells_exceed_the_deployed_cap
#assert_axioms split_srs_cells_fit
#assert_axioms manifest_rows_fit

end Dregg2.Circuit.Emit.PastaMsmBucketed
