/-
# Dregg2.Circuit.Emit.KimchiRootAirEval — `C_i`: the ROOT's AIR constraints at ζ, GENERATED

## ⚑ THE HOLE THIS RUNG IS FOR

`docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` rungs 1–5 authenticate a value; §3.15's DEEP quotient ties
that value to the CLAIMED out-of-domain evaluations `f(ζ)`. **Neither says the claimed evaluations
satisfy dregg's constraint system.** A verifier stopping there certifies that some low-degree
function takes some values at ζ — true of an arbitrary polynomial. §3.16 built everything AROUND
`C_i` and priced it `A + N·h` with `A = 14,175`, `h = 48` measured and **`N` uncounted**.

**`N` is now measured: 1093** — `circuit-prove/tests/root_air_constraint_census.rs`, from
`p3_batch_stark::symbolic::get_symbolic_constraints` over the root's seven AIRs at the deployed
shape. 901 base + 192 LogUp-extension. Per table: `Const 3 · Public 3 · Alu 146 · poseidon2-w16 337
· poseidon2-w24 501 · recompose 3 · expose_claim 100`. The census is cross-checked twice: its
column totals are the doc's 940 main / 175 prep, and its per-table preprocessed widths
`[2,2,59,24,36,2,50]` are the ones sitting in the real serialized root proof.

This file is the other half: the constraints THEMSELVES, compiled rather than hand-written.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored generation over a machine-checked lowering.** No Kimchi row here is
hand-written: every one is `packGen` output, and `airFold_forces` proves what the emitted rows
force. §5's `aluHeads` / `exposeClaimHeads` are EXTRACTOR OUTPUT, pasted verbatim — a human never
wrote a constraint. What is NOT proved is that those `Head`s are p3's constraints; that extraction
is a Rust-side seam, named in §7 and differentially checked, never called verified.

## ⚑ AND A DEFECT IN THE RUNG THIS BUILDS ON — the reason §1 exists

`KimchiLower`'s header scopes `lowerHead` as "precisely the verifier's `AIR.evalAtZeta` rung". Its
BODY does something else: `lowerHeadGens` ends in `Gen1.isZero`, so the emitted rows assert the head
**VANISHES**. At ζ that is FALSE for an honest proof. The constraint polynomials vanish on the trace
domain `H`; ζ is sampled OUTSIDE `H` precisely so that they do not, and the quotient
`Q = (Σ αⁱ Cᵢ)/Z_H` is only meaningful because `Cᵢ(ζ) ≠ 0`. A verifier built on `lowerHead` as
written would be **unsatisfiable on every honest proof** — and would have looked correct, because
`lowerHead_sound` is a true theorem about it.

The verifier needs the head's **VALUE**, to fold with α. §1 supplies it — the same straight-line
program with the terminal `isZero` dropped and the accumulator variable RETURNED — and its forcing
lemma is `lowerAcc_forces`, which `KimchiLower` already proved. The extension is three lines and the
proof was already in the tree; what was missing was noticing that a constraint-GATE lowering and a
constraint-EVALUATION lowering are different objects. `lowerHead` remains correct for its real use
(dregg-side gates, where the head must vanish); it was the SCOPING claim that was wrong.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`.
NEW file; the single import `Dregg2.Circuit.Emit.KimchiLower` carries `Head`, `KRow`, `rowsHold`
and `#assert_axioms` through `KimchiLower → KimchiTarget → AirBuilder → DescriptorIR2`.
-/
import Dregg2.Circuit.Emit.KimchiLower

namespace Dregg2.Circuit.Emit.KimchiRootAirEval

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.AirBuilder (Head evalH)
open Dregg2.Circuit.Emit.KimchiTarget
open Dregg2.Circuit.Emit.KimchiLower

set_option autoImplicit false
set_option maxRecDepth 20000

/-! ## §1 — `lowerHeadValue`: the head's VALUE, not its vanishing. -/

/-- The sub-gates that COMPUTE a `Head`'s value into a fresh variable: the constant pin and the term
accumulation, with no terminal `isZero`. -/
def lowerHeadValueGens (h : Head) (nv : Nat) : List Gen1 :=
  Gen1.const nv h.const :: (lowerAcc h.terms nv (nv + 1)).2.2

/-- The variable holding the head's value. -/
def lowerHeadValueOut (h : Head) (nv : Nat) : Nat := (lowerAcc h.terms nv (nv + 1)).1

/-- The first variable index still free after the computation. -/
def lowerHeadValueWm (h : Head) (nv : Nat) : Nat := (lowerAcc h.terms nv (nv + 1)).2.1

section Value

variable {R : Type} [CommRing R]

/-- **The value lowering is sound.** Any assignment satisfying the emitted sub-gates puts exactly
`headEvalR a h` in the output variable. `lowerHead_sound` is this computation followed by an
assertion; this is the computation on its own, which is what a VERIFIER needs. -/
theorem lowerHeadValue_forces (a : Nat → R) (h : Head) (nv : Nat)
    (hg : gensHold a (lowerHeadValueGens h nv)) :
    a (lowerHeadValueOut h nv) = headEvalR a h := by
  obtain ⟨hconst, hacc⟩ := gensHold_cons hg
  have h0 : a nv = ((h.const : ℤ) : R) := Gen1.const_forces a nv h.const hconst
  have hfin := lowerAcc_forces a h.terms nv (nv + 1) hacc
  rw [h0] at hfin
  simp only [lowerHeadValueOut, headEvalR]
  rw [hfin]
  ring

end Value

/-! ## §2 — the α-fold, which is the verifier's accumulator.

p3's `VerifierConstraintFolder` starts the accumulator at ZERO and runs `acc ← acc·α + C` once per
constraint (`p3-uni-stark/src/folder.rs`); the recursive twin is `plonky3-recursion@0a4a554
recursion/src/traits/air.rs:148-158` — `let mut acc = define_const(ZERO); … acc = mul_add(acc,
alpha, c)`. Two sub-gates per constraint: one multiplication and one two-input combination.

⚑ **A discrepancy this rung settles.** `bridge/mina-zkapp/src/AirEval.ts`'s `foldConstraints` seeds
the accumulator with `constraints[0]` and pays `N − 1` folds; p3 seeds with ZERO and pays `N`.
§3.16 corrected for it by subtracting one marginal price. The generator here matches p3 exactly —
`N` folds — so the correction is now structural rather than an adjustment applied by hand. -/

/-- The fold, threaded over a list of heads. `acc` is the accumulator variable so far, `al` the
variable holding α, `nv` the fresh-variable watermark. -/
def foldGo : List Head → Nat → Nat → Nat → Nat × Nat × List Gen1
  | [], acc, _, nv => (acc, nv, [])
  | h :: hs, acc, al, nv =>
      let nv1 := lowerHeadValueWm h nv
      let rest := foldGo hs (nv1 + 1) al (nv1 + 2)
      (rest.1, rest.2.1,
        lowerHeadValueGens h nv
          ++ (Gen1.mul acc al nv1
              :: Gen1.lin2 nv1 (lowerHeadValueOut h nv) (nv1 + 1) 1 1
              :: rest.2.2))

/-- The Horner value the fold computes, stated independently of the circuit. -/
def hornerValue {R : Type} [CommRing R] (a : Nat → R) (al : Nat) (hs : List Head) (init : R) : R :=
  hs.foldl (fun s h => s * a al + headEvalR a h) init

section Fold

variable {R : Type} [CommRing R]

/-- **The fold is sound.** Any assignment satisfying the emitted sub-gates puts p3's accumulator in
the output variable. Proved by INDUCTION over the constraint list, so it holds at every `N` rather
than at a fixture's `N` — a fold chain is exactly the shape a single-point KAT cannot audit, which
is the same lesson the sixteen FRI rounds and the four `degree_bits` each taught once. -/
theorem foldGo_forces (a : Nat → R) :
    ∀ (hs : List Head) (acc al nv : Nat), gensHold a (foldGo hs acc al nv).2.2 →
      a (foldGo hs acc al nv).1 = hornerValue a al hs (a acc) := by
  intro hs
  induction hs with
  | nil => intro acc al nv _; simp [foldGo, hornerValue]
  | cons h hs ih =>
    intro acc al nv hg
    simp only [foldGo] at hg ⊢
    obtain ⟨hg1, hg2⟩ := gensHold_append hg
    obtain ⟨hmul, hg3⟩ := gensHold_cons hg2
    obtain ⟨hlin, hg4⟩ := gensHold_cons hg3
    have hv : a (lowerHeadValueOut h nv) = headEvalR a h := lowerHeadValue_forces a h nv hg1
    have hm : a (lowerHeadValueWm h nv) = a acc * a al := Gen1.mul_forces a acc al _ hmul
    have hl : a (lowerHeadValueWm h nv + 1)
        = (1 : ℤ) * a (lowerHeadValueWm h nv) + (1 : ℤ) * a (lowerHeadValueOut h nv) :=
      Gen1.lin2_forces a _ _ _ 1 1 hlin
    have hrest := ih (lowerHeadValueWm h nv + 1) al (lowerHeadValueWm h nv + 2) hg4
    rw [hrest]
    simp only [hornerValue, List.foldl_cons]
    congr 1
    rw [hl, hm, hv]
    push_cast
    ring

end Fold

/-- **THE EMITTED PROGRAM.** Pin an accumulator to zero, then fold every constraint. `nv` is the
first fresh variable; the AIR's opened values and α occupy indices below it. -/
def airFoldGens (hs : List Head) (al nv : Nat) : List Gen1 :=
  Gen1.const nv 0 :: (foldGo hs nv al (nv + 1)).2.2

/-- The variable holding the verifier's accumulator. -/
def airFoldOut (hs : List Head) (al nv : Nat) : Nat := (foldGo hs nv al (nv + 1)).1

/-- **The emitted Kimchi circuit**, packed two sub-gates to a row. -/
def airFoldRows (hs : List Head) (al nv : Nat) : List KRow := packGen (airFoldGens hs al nv)

section Top

variable {R : Type} [CommRing R]

/-- **THE RUNG-7 THEOREM.**

Any assignment satisfying every Kimchi row this compiler emits makes the output variable hold
exactly `fold_i (acc·α + C_i)` from zero — the accumulator
`VerifierData::verify_constraints_with_lookups` compares against `quotient(ζ)·Z_H(ζ)`
(`p3-batch-stark/src/verifier/data.rs:96-100`).

Stated over the emitted object itself (`airFoldRows hs al nv` is the very list handed to the
backend), over `rowsHold` (whose generic case is welded to the reality-gated
`KimchiVerify.genericGateConstraint`), and at an ARBITRARY `CommRing` — so it holds over the
extension the challenge actually lives in, not only over ℤ.

⚑ **What it does NOT say.** It does not say the `hs` are p3's constraints (§7.1). It does not close
the verifier: the closing equality, the real preamble, mixed-height MMCS openings,
19-queries-not-1 and the undischarged FRI floor all stand. -/
theorem airFold_forces (a : Nat → R) (hs : List Head) (al nv : Nat)
    (hr : rowsHold a (airFoldRows hs al nv)) :
    a (airFoldOut hs al nv) = hornerValue a al hs 0 := by
  rw [airFoldRows, packGen_holds_iff] at hr
  simp only [airFoldGens] at hr
  obtain ⟨hzero, hrest⟩ := gensHold_cons hr
  have h0 : a nv = ((0 : ℤ) : R) := Gen1.const_forces a nv 0 hzero
  have hfold := foldGo_forces a hs nv al (nv + 1) hrest
  simp only [airFoldOut]
  rw [hfold, h0]
  norm_num

/-- The specialisation at dregg's own ℤ-valued assignments, where `headEvalR` is `evalH` — so the
two emissions agree on what the constraints MEAN, not merely on their shape. -/
theorem airFold_forces_evalH (a : Assignment) (hs : List Head) (al nv : Nat)
    (hr : rowsHold a (airFoldRows hs al nv)) :
    a (airFoldOut hs al nv) = hs.foldl (fun s h => s * a al + evalH h a) 0 := by
  have h := airFold_forces a hs al nv hr
  simpa [hornerValue, headEvalR_int] using h

end Top

/-! ## §3 — the cost model, as theorems over the emitted list. -/

/-- Sub-gates the VALUE lowering costs: `lowerHeadGenCount` less the terminal `isZero`. -/
def valueGenCount (h : Head) : Nat := 1 + (h.terms.map (fun t => prodGens t.2 + 1)).sum

theorem lowerHeadValueGens_length (h : Head) (nv : Nat) :
    (lowerHeadValueGens h nv).length = valueGenCount h := by
  simp only [lowerHeadValueGens, valueGenCount, List.length_cons, lowerAcc_length]
  omega

/-- The value lowering is exactly one sub-gate cheaper than the gate lowering — the `isZero`. -/
theorem valueGenCount_succ (h : Head) : valueGenCount h + 1 = lowerHeadGenCount h := by
  simp only [valueGenCount, lowerHeadGenCount]
  omega

/-- Sub-gates the whole fold costs: the zero pin, plus per constraint its value program and the two
fold gates. -/
def airFoldGenCount (hs : List Head) : Nat := 1 + (hs.map (fun h => valueGenCount h + 2)).sum

theorem foldGo_length : ∀ (hs : List Head) (acc al nv : Nat),
    (foldGo hs acc al nv).2.2.length = (hs.map (fun h => valueGenCount h + 2)).sum := by
  intro hs
  induction hs with
  | nil => intro acc al nv; rfl
  | cons h hs ih =>
    intro acc al nv
    simp only [foldGo, List.length_append, List.length_cons, List.map_cons, List.sum_cons,
      lowerHeadValueGens_length, ih]
    omega

theorem airFoldGens_length (hs : List Head) (al nv : Nat) :
    (airFoldGens hs al nv).length = airFoldGenCount hs := by
  simp only [airFoldGens, airFoldGenCount, List.length_cons, foldGo_length]
  omega

/-- **The row count is a THEOREM.** After packing, `⌈gens/2⌉` — the same halving `packGen_length`
prices, so the optimisation needs no re-audit here either. -/
theorem airFoldRows_length (hs : List Head) (al nv : Nat) :
    (airFoldRows hs al nv).length = (airFoldGenCount hs + 1) / 2 := by
  rw [airFoldRows, packGen_length, airFoldGens_length]

/-- **The expensive half.** `Gen1` is one operation on an EMULATED extension element, not one
half-row: dregg's values live in `BinomialExtensionField<BabyBear, 4>` and Kimchi's field is Pasta.
A `Gen1.mul` on two live extension values is a full extension multiply (≈31 o1js rows, §3.10/§3.15);
`Gen1.acc _ _ _ k` and `Gen1.lin2 _ _ _ 1 1` scale by a COMPILE-TIME base coefficient and add, which
`AirEval.ts`'s `extScaleConst` prices as free-modulo-reduction; `Gen1.const` is free. So the count
that PRICES `C_i` is the count of `Gen1.mul`s — which is what this is. Stating the sub-gate total in
rows without that conversion is exactly the error §2.4 made. -/
def extMulCount (gs : List Gen1) : Nat := (gs.filter (fun g => g.cm ≠ 0)).length

/-! ## §4 — anti-vacuity.

A soundness theorem over an emitted circuit is discharged for free if the circuit cannot be
satisfied. Three obligations, all met on the ACTUAL emitted object. -/

/-- Every row the fold emits carries a MODELLED gate, so `airFold_forces` is not discharged by
`KimchiTarget`'s fail-closed `False` on an unmodelled row. -/
theorem airFoldRows_all_modelled (hs : List Head) (al nv : Nat) :
    ∀ r ∈ airFoldRows hs al nv, r.gate.modelled = true :=
  packGen_all_modelled _

/-! ### §4.1 — a SATISFYING assignment, computed from the emitted program itself.

`runGens` executes the emitted list under the discipline the generator claims to obey: **every
sub-gate defines the NEXT fresh variable**. It `push`es rather than writing at an index, so a gate
that writes anywhere else cannot be executed and the whole run returns `none`. That makes the
evaluator a FRESHNESS AUDIT of the generator as well as a satisfiability certificate — and freshness
is the property `KimchiLower`'s own header says buys completeness while proving nothing about it.

⚑ The seed matters. Running with all inputs zero certifies satisfiability at a DEGENERATE point,
where every product vanishes and an aliased variable is indistinguishable from a fresh one. The
inputs are seeded with distinct non-zero values instead. -/

/-- Execute one sub-gate, requiring it to define the next fresh variable. -/
def stepGen (v : Array ℤ) (g : Gen1) : Option (Array ℤ) :=
  let l := v.getD g.l 0
  let r := v.getD g.r 0
  if g.co = -1 then
    if g.o = v.size then some (v.push (g.cl * l + g.cr * r + g.cm * (l * r) + g.cc)) else none
  else
    if g.l = v.size then some (v.push (-g.cc)) else none

/-- Run the whole straight-line program. `none` is an ALIASING report on the generator. -/
def runGens (v : Array ℤ) : List Gen1 → Option (Array ℤ)
  | [] => some v
  | g :: gs => match stepGen v g with
    | none => none
    | some v' => runGens v' gs

/-- A deterministic NON-DEGENERATE seeding of the `n` input variables. -/
def seedInputs (n : Nat) : Array ℤ :=
  (List.range n).foldl (fun v i => v.push (((7919 * i + 13) % 1000003 : Nat) : ℤ)) #[]

/-- Does every sub-gate hold at this assignment? -/
def gensAcceptB (v : Array ℤ) (gs : List Gen1) : Bool :=
  gs.all fun g =>
    decide (g.cl * v.getD g.l 0 + g.cr * v.getD g.r 0 + g.co * v.getD g.o 0
      + g.cm * (v.getD g.l 0 * v.getD g.r 0) + g.cc = 0)

/-- The Horner value, evaluated DIRECTLY — the independent oracle the circuit's output variable is
checked against, so the check spans the whole fold rather than one gate. -/
def hornerZ (v : Array ℤ) (al : Nat) (hs : List Head) : ℤ :=
  hs.foldl (fun s h => s * v.getD al 0 + evalH h (fun i => v.getD i 0)) 0

/-- Run the emitted program for `hs` over `nCols` seeded input columns, with α at column `nCols`. -/
def runTable (hs : List Head) (nCols : Nat) : Option (Array ℤ) :=
  runGens (seedInputs (nCols + 1)) (airFoldGens hs nCols (nCols + 1))

/-! ## §5 — THE GENERATED TABLES.

⚑ **Nothing below was written by hand.** Both lists are verbatim output of `emit_lean_heads` in
`circuit-prove/tests/root_air_constraint_census.rs`, which flattens
`p3_batch_stark::symbolic::get_symbolic_constraints` of the DEPLOYED AIR into `Head`'s
`Σ coeff·∏cols + const`. Coefficients are canonical BabyBear representatives, so `2013265920` is
`−1` and `2013265910` is `−11` (the extension's `W`).

Column numbering is the extractor's canonical order over the leaves the verifier holds at ζ: the
opened main and preprocessed values, the public values, and the three Lagrange selectors. It is a
per-table numbering; the legend is printed alongside the emission. -/

/-- **`expose_claim`** — the root's exposed-claim channel: 25 base constraints, 75 columns.
`ExposeClaimAir::<F,4>::new_with_preprocessed(25, _, 1)`, with 25 = `NUM_CHAIN_CLAIMS`
(`circuit-prove/src/ivc_turn_chain.rs:366,278`). Each lane pins one opened main value to one public
value under its preprocessed selector: `sel·(main − public)`. -/
def exposeClaimHeads : List Head :=
  [
    ⟨[(2013265920, [0, 1]), (1, [0, 2])], 0⟩,  -- C0
    ⟨[(2013265920, [3, 4]), (1, [3, 5])], 0⟩,  -- C1
    ⟨[(2013265920, [6, 7]), (1, [6, 8])], 0⟩,  -- C2
    ⟨[(2013265920, [9, 10]), (1, [9, 11])], 0⟩,  -- C3
    ⟨[(2013265920, [12, 13]), (1, [12, 14])], 0⟩,  -- C4
    ⟨[(2013265920, [15, 16]), (1, [15, 17])], 0⟩,  -- C5
    ⟨[(2013265920, [18, 19]), (1, [18, 20])], 0⟩,  -- C6
    ⟨[(2013265920, [21, 22]), (1, [21, 23])], 0⟩,  -- C7
    ⟨[(2013265920, [24, 25]), (1, [24, 26])], 0⟩,  -- C8
    ⟨[(2013265920, [27, 28]), (1, [27, 29])], 0⟩,  -- C9
    ⟨[(2013265920, [30, 31]), (1, [30, 32])], 0⟩,  -- C10
    ⟨[(2013265920, [33, 34]), (1, [33, 35])], 0⟩,  -- C11
    ⟨[(2013265920, [36, 37]), (1, [36, 38])], 0⟩,  -- C12
    ⟨[(2013265920, [39, 40]), (1, [39, 41])], 0⟩,  -- C13
    ⟨[(2013265920, [42, 43]), (1, [42, 44])], 0⟩,  -- C14
    ⟨[(2013265920, [45, 46]), (1, [45, 47])], 0⟩,  -- C15
    ⟨[(2013265920, [48, 49]), (1, [48, 50])], 0⟩,  -- C16
    ⟨[(2013265920, [51, 52]), (1, [51, 53])], 0⟩,  -- C17
    ⟨[(2013265920, [54, 55]), (1, [54, 56])], 0⟩,  -- C18
    ⟨[(2013265920, [57, 58]), (1, [57, 59])], 0⟩,  -- C19
    ⟨[(2013265920, [60, 61]), (1, [60, 62])], 0⟩,  -- C20
    ⟨[(2013265920, [63, 64]), (1, [63, 65])], 0⟩,  -- C21
    ⟨[(2013265920, [66, 67]), (1, [66, 68])], 0⟩,  -- C22
    ⟨[(2013265920, [69, 70]), (1, [69, 71])], 0⟩,  -- C23
    ⟨[(2013265920, [72, 73]), (1, [72, 74])], 0⟩   -- C24
  ]

/-- Columns `expose_claim` opens (the extractor's legend length). -/
def exposeClaimCols : Nat := 75

/-- **`Alu`** — the workhorse: 92 base constraints over 170 columns, at the deployed packing
(`alu_lanes = 4`, `horner_packed_steps = 2`, `W = 11`, from
`ProveNextLayerParams::default().table_packing = TablePacking::new(1, 4)`). Degree 3, 778 monomials.
This is the table whose `C_i` a hand-written verifier would have had to transcribe. -/
def aluHeads : List Head :=
  [
    ⟨[(1, [0, 1]), (1, [0, 2]), (2013265920, [0, 3])], 0⟩,  -- C0
    ⟨[(1, [0, 4]), (1, [0, 5]), (2013265920, [0, 6])], 0⟩,  -- C1
    ⟨[(1, [0, 7]), (1, [0, 8]), (2013265920, [0, 9])], 0⟩,  -- C2
    ⟨[(1, [0, 10]), (1, [0, 11]), (2013265920, [0, 12])], 0⟩,  -- C3
    ⟨[(2013265920, [0, 1, 2]), (1, [0, 3]), (2013265910, [0, 4, 11]), (2013265910, [0, 5, 10]), (2013265910, [0, 7, 8]), (2013265920, [1, 2, 13]), (2013265920, [1, 2, 14]), (2013265920, [1, 2, 15]), (2013265920, [1, 2, 16]), (1, [3, 13]), (1, [3, 14]), (1, [3, 15]), (1, [3, 16]), (2013265910, [4, 11, 13]), (2013265910, [4, 11, 14]), (2013265910, [4, 11, 15]), (2013265910, [4, 11, 16]), (2013265910, [5, 10, 13]), (2013265910, [5, 10, 14]), (2013265910, [5, 10, 15]), (2013265910, [5, 10, 16]), (2013265910, [7, 8, 13]), (2013265910, [7, 8, 14]), (2013265910, [7, 8, 15]), (2013265910, [7, 8, 16])], 0⟩,  -- C4
    ⟨[(2013265920, [0, 1, 5]), (2013265920, [0, 2, 4]), (1, [0, 6]), (2013265910, [0, 7, 11]), (2013265910, [0, 8, 10]), (2013265920, [1, 5, 13]), (2013265920, [1, 5, 14]), (2013265920, [1, 5, 15]), (2013265920, [1, 5, 16]), (2013265920, [2, 4, 13]), (2013265920, [2, 4, 14]), (2013265920, [2, 4, 15]), (2013265920, [2, 4, 16]), (1, [6, 13]), (1, [6, 14]), (1, [6, 15]), (1, [6, 16]), (2013265910, [7, 11, 13]), (2013265910, [7, 11, 14]), (2013265910, [7, 11, 15]), (2013265910, [7, 11, 16]), (2013265910, [8, 10, 13]), (2013265910, [8, 10, 14]), (2013265910, [8, 10, 15]), (2013265910, [8, 10, 16])], 0⟩,  -- C5
    ⟨[(2013265920, [0, 1, 8]), (2013265920, [0, 2, 7]), (2013265920, [0, 4, 5]), (1, [0, 9]), (2013265910, [0, 10, 11]), (2013265920, [1, 8, 13]), (2013265920, [1, 8, 14]), (2013265920, [1, 8, 15]), (2013265920, [1, 8, 16]), (2013265920, [2, 7, 13]), (2013265920, [2, 7, 14]), (2013265920, [2, 7, 15]), (2013265920, [2, 7, 16]), (2013265920, [4, 5, 13]), (2013265920, [4, 5, 14]), (2013265920, [4, 5, 15]), (2013265920, [4, 5, 16]), (1, [9, 13]), (1, [9, 14]), (1, [9, 15]), (1, [9, 16]), (2013265910, [10, 11, 13]), (2013265910, [10, 11, 14]), (2013265910, [10, 11, 15]), (2013265910, [10, 11, 16])], 0⟩,  -- C6
    ⟨[(2013265920, [0, 1, 11]), (2013265920, [0, 2, 10]), (2013265920, [0, 4, 8]), (2013265920, [0, 5, 7]), (1, [0, 12]), (2013265920, [1, 11, 13]), (2013265920, [1, 11, 14]), (2013265920, [1, 11, 15]), (2013265920, [1, 11, 16]), (2013265920, [2, 10, 13]), (2013265920, [2, 10, 14]), (2013265920, [2, 10, 15]), (2013265920, [2, 10, 16]), (2013265920, [4, 8, 13]), (2013265920, [4, 8, 14]), (2013265920, [4, 8, 15]), (2013265920, [4, 8, 16]), (2013265920, [5, 7, 13]), (2013265920, [5, 7, 14]), (2013265920, [5, 7, 15]), (2013265920, [5, 7, 16]), (1, [12, 13]), (1, [12, 14]), (1, [12, 15]), (1, [12, 16])], 0⟩,  -- C7
    ⟨[(1, [1, 1, 14]), (2013265920, [1, 14])], 0⟩,  -- C8
    ⟨[(1, [4, 14])], 0⟩,  -- C9
    ⟨[(1, [7, 14])], 0⟩,  -- C10
    ⟨[(1, [10, 14])], 0⟩,  -- C11
    ⟨[(1, [1, 2, 15]), (2013265920, [3, 15]), (11, [4, 11, 15]), (11, [5, 10, 15]), (11, [7, 8, 15]), (1, [15, 17])], 0⟩,  -- C12
    ⟨[(1, [1, 5, 15]), (1, [2, 4, 15]), (2013265920, [6, 15]), (11, [7, 11, 15]), (11, [8, 10, 15]), (1, [15, 18])], 0⟩,  -- C13
    ⟨[(1, [1, 8, 15]), (1, [2, 7, 15]), (1, [4, 5, 15]), (2013265920, [9, 15]), (11, [10, 11, 15]), (1, [15, 19])], 0⟩,  -- C14
    ⟨[(1, [1, 11, 15]), (1, [2, 10, 15]), (1, [4, 8, 15]), (1, [5, 7, 15]), (2013265920, [12, 15]), (1, [15, 20])], 0⟩,  -- C15
    ⟨[(2013265920, [2, 2, 21]), (2013265899, [5, 11, 21]), (2013265910, [8, 8, 21]), (1, [21, 22])], 0⟩,  -- C16
    ⟨[(2013265919, [2, 5, 21]), (2013265899, [8, 11, 21]), (1, [21, 23])], 0⟩,  -- C17
    ⟨[(2013265919, [2, 8, 21]), (2013265920, [5, 5, 21]), (2013265910, [11, 11, 21]), (1, [21, 24])], 0⟩,  -- C18
    ⟨[(2013265919, [2, 11, 21]), (2013265919, [5, 8, 21]), (1, [21, 25])], 0⟩,  -- C19
    ⟨[(1, [3, 26, 27]), (11, [6, 26, 28]), (11, [9, 26, 29]), (11, [12, 26, 30]), (1, [26, 31, 32]), (2013265920, [26, 32, 39]), (11, [26, 33, 34]), (2013265910, [26, 34, 40]), (11, [26, 35, 36]), (2013265910, [26, 36, 41]), (11, [26, 37, 38]), (2013265910, [26, 38, 42]), (1, [26, 43]), (2013265920, [26, 44]), (2013265920, [26, 45])], 0⟩,  -- C20
    ⟨[], 0⟩,  -- C21
    ⟨[(1, [3, 26, 30]), (1, [6, 26, 27]), (11, [9, 26, 28]), (11, [12, 26, 29]), (1, [26, 31, 38]), (1, [26, 32, 33]), (2013265920, [26, 32, 40]), (11, [26, 34, 35]), (2013265910, [26, 34, 41]), (11, [26, 36, 37]), (2013265910, [26, 36, 42]), (2013265920, [26, 38, 39]), (1, [26, 46]), (2013265920, [26, 47]), (2013265920, [26, 48])], 0⟩,  -- C22
    ⟨[], 0⟩,  -- C23
    ⟨[(1, [3, 26, 29]), (1, [6, 26, 30]), (1, [9, 26, 27]), (11, [12, 26, 28]), (1, [26, 31, 36]), (1, [26, 32, 35]), (2013265920, [26, 32, 41]), (1, [26, 33, 38]), (11, [26, 34, 37]), (2013265910, [26, 34, 42]), (2013265920, [26, 36, 39]), (2013265920, [26, 38, 40]), (1, [26, 49]), (2013265920, [26, 50]), (2013265920, [26, 51])], 0⟩,  -- C24
    ⟨[], 0⟩,  -- C25
    ⟨[(1, [3, 26, 28]), (1, [6, 26, 29]), (1, [9, 26, 30]), (1, [12, 26, 27]), (1, [26, 31, 34]), (1, [26, 32, 37]), (2013265920, [26, 32, 42]), (1, [26, 33, 36]), (2013265920, [26, 34, 39]), (1, [26, 35, 38]), (2013265920, [26, 36, 40]), (2013265920, [26, 38, 41]), (1, [26, 52]), (2013265920, [26, 53]), (2013265920, [26, 54])], 0⟩,  -- C26
    ⟨[], 0⟩,  -- C27
    ⟨[(2013265920, [3, 26, 32]), (1, [3, 32, 55]), (2013265910, [6, 26, 34]), (11, [6, 34, 55]), (2013265910, [9, 26, 36]), (11, [9, 36, 55]), (2013265910, [12, 26, 38]), (11, [12, 38, 55]), (2013265920, [26, 31]), (1, [26, 39]), (1, [26, 45]), (1, [31, 55]), (2013265920, [39, 55]), (2013265920, [45, 55])], 0⟩,  -- C28
    ⟨[(2013265920, [3, 26, 38]), (1, [3, 38, 55]), (2013265920, [6, 26, 32]), (1, [6, 32, 55]), (2013265910, [9, 26, 34]), (11, [9, 34, 55]), (2013265910, [12, 26, 36]), (11, [12, 36, 55]), (2013265920, [26, 33]), (1, [26, 40]), (1, [26, 48]), (1, [33, 55]), (2013265920, [40, 55]), (2013265920, [48, 55])], 0⟩,  -- C29
    ⟨[(2013265920, [3, 26, 36]), (1, [3, 36, 55]), (2013265920, [6, 26, 38]), (1, [6, 38, 55]), (2013265920, [9, 26, 32]), (1, [9, 32, 55]), (2013265910, [12, 26, 34]), (11, [12, 34, 55]), (2013265920, [26, 35]), (1, [26, 41]), (1, [26, 51]), (1, [35, 55]), (2013265920, [41, 55]), (2013265920, [51, 55])], 0⟩,  -- C30
    ⟨[(2013265920, [3, 26, 34]), (1, [3, 34, 55]), (2013265920, [6, 26, 36]), (1, [6, 36, 55]), (2013265920, [9, 26, 38]), (1, [9, 38, 55]), (2013265920, [12, 26, 32]), (1, [12, 32, 55]), (2013265920, [26, 37]), (1, [26, 42]), (1, [26, 54]), (1, [37, 55]), (2013265920, [42, 55]), (2013265920, [54, 55])], 0⟩,  -- C31
    ⟨[(1, [56, 57]), (1, [56, 58]), (2013265920, [56, 59])], 0⟩,  -- C32
    ⟨[(1, [56, 60]), (1, [56, 61]), (2013265920, [56, 62])], 0⟩,  -- C33
    ⟨[(1, [56, 63]), (1, [56, 64]), (2013265920, [56, 65])], 0⟩,  -- C34
    ⟨[(1, [56, 66]), (1, [56, 67]), (2013265920, [56, 68])], 0⟩,  -- C35
    ⟨[(2013265920, [56, 57, 58]), (1, [56, 59]), (2013265910, [56, 60, 67]), (2013265910, [56, 61, 66]), (2013265910, [56, 63, 64]), (2013265920, [57, 58, 69]), (2013265920, [57, 58, 70]), (2013265920, [57, 58, 71]), (2013265920, [57, 58, 72]), (1, [59, 69]), (1, [59, 70]), (1, [59, 71]), (1, [59, 72]), (2013265910, [60, 67, 69]), (2013265910, [60, 67, 70]), (2013265910, [60, 67, 71]), (2013265910, [60, 67, 72]), (2013265910, [61, 66, 69]), (2013265910, [61, 66, 70]), (2013265910, [61, 66, 71]), (2013265910, [61, 66, 72]), (2013265910, [63, 64, 69]), (2013265910, [63, 64, 70]), (2013265910, [63, 64, 71]), (2013265910, [63, 64, 72])], 0⟩,  -- C36
    ⟨[(2013265920, [56, 57, 61]), (2013265920, [56, 58, 60]), (1, [56, 62]), (2013265910, [56, 63, 67]), (2013265910, [56, 64, 66]), (2013265920, [57, 61, 69]), (2013265920, [57, 61, 70]), (2013265920, [57, 61, 71]), (2013265920, [57, 61, 72]), (2013265920, [58, 60, 69]), (2013265920, [58, 60, 70]), (2013265920, [58, 60, 71]), (2013265920, [58, 60, 72]), (1, [62, 69]), (1, [62, 70]), (1, [62, 71]), (1, [62, 72]), (2013265910, [63, 67, 69]), (2013265910, [63, 67, 70]), (2013265910, [63, 67, 71]), (2013265910, [63, 67, 72]), (2013265910, [64, 66, 69]), (2013265910, [64, 66, 70]), (2013265910, [64, 66, 71]), (2013265910, [64, 66, 72])], 0⟩,  -- C37
    ⟨[(2013265920, [56, 57, 64]), (2013265920, [56, 58, 63]), (2013265920, [56, 60, 61]), (1, [56, 65]), (2013265910, [56, 66, 67]), (2013265920, [57, 64, 69]), (2013265920, [57, 64, 70]), (2013265920, [57, 64, 71]), (2013265920, [57, 64, 72]), (2013265920, [58, 63, 69]), (2013265920, [58, 63, 70]), (2013265920, [58, 63, 71]), (2013265920, [58, 63, 72]), (2013265920, [60, 61, 69]), (2013265920, [60, 61, 70]), (2013265920, [60, 61, 71]), (2013265920, [60, 61, 72]), (1, [65, 69]), (1, [65, 70]), (1, [65, 71]), (1, [65, 72]), (2013265910, [66, 67, 69]), (2013265910, [66, 67, 70]), (2013265910, [66, 67, 71]), (2013265910, [66, 67, 72])], 0⟩,  -- C38
    ⟨[(2013265920, [56, 57, 67]), (2013265920, [56, 58, 66]), (2013265920, [56, 60, 64]), (2013265920, [56, 61, 63]), (1, [56, 68]), (2013265920, [57, 67, 69]), (2013265920, [57, 67, 70]), (2013265920, [57, 67, 71]), (2013265920, [57, 67, 72]), (2013265920, [58, 66, 69]), (2013265920, [58, 66, 70]), (2013265920, [58, 66, 71]), (2013265920, [58, 66, 72]), (2013265920, [60, 64, 69]), (2013265920, [60, 64, 70]), (2013265920, [60, 64, 71]), (2013265920, [60, 64, 72]), (2013265920, [61, 63, 69]), (2013265920, [61, 63, 70]), (2013265920, [61, 63, 71]), (2013265920, [61, 63, 72]), (1, [68, 69]), (1, [68, 70]), (1, [68, 71]), (1, [68, 72])], 0⟩,  -- C39
    ⟨[(1, [57, 57, 70]), (2013265920, [57, 70])], 0⟩,  -- C40
    ⟨[(1, [60, 70])], 0⟩,  -- C41
    ⟨[(1, [63, 70])], 0⟩,  -- C42
    ⟨[(1, [66, 70])], 0⟩,  -- C43
    ⟨[(1, [57, 58, 71]), (2013265920, [59, 71]), (11, [60, 67, 71]), (11, [61, 66, 71]), (11, [63, 64, 71]), (1, [71, 73])], 0⟩,  -- C44
    ⟨[(1, [57, 61, 71]), (1, [58, 60, 71]), (2013265920, [62, 71]), (11, [63, 67, 71]), (11, [64, 66, 71]), (1, [71, 74])], 0⟩,  -- C45
    ⟨[(1, [57, 64, 71]), (1, [58, 63, 71]), (1, [60, 61, 71]), (2013265920, [65, 71]), (11, [66, 67, 71]), (1, [71, 75])], 0⟩,  -- C46
    ⟨[(1, [57, 67, 71]), (1, [58, 66, 71]), (1, [60, 64, 71]), (1, [61, 63, 71]), (2013265920, [68, 71]), (1, [71, 76])], 0⟩,  -- C47
    ⟨[(1, [59, 77, 78]), (11, [62, 77, 79]), (11, [65, 77, 80]), (11, [68, 77, 81]), (1, [77, 82]), (2013265920, [77, 83]), (2013265920, [77, 84])], 0⟩,  -- C48
    ⟨[(1, [59, 77, 81]), (1, [62, 77, 78]), (11, [65, 77, 79]), (11, [68, 77, 80]), (1, [77, 85]), (2013265920, [77, 86]), (2013265920, [77, 87])], 0⟩,  -- C49
    ⟨[(1, [59, 77, 80]), (1, [62, 77, 81]), (1, [65, 77, 78]), (11, [68, 77, 79]), (1, [77, 88]), (2013265920, [77, 89]), (2013265920, [77, 90])], 0⟩,  -- C50
    ⟨[(1, [59, 77, 79]), (1, [62, 77, 80]), (1, [65, 77, 81]), (1, [68, 77, 78]), (1, [77, 91]), (2013265920, [77, 92]), (2013265920, [77, 93])], 0⟩,  -- C51
    ⟨[(1, [94, 95]), (1, [94, 96]), (2013265920, [94, 97])], 0⟩,  -- C52
    ⟨[(1, [94, 98]), (1, [94, 99]), (2013265920, [94, 100])], 0⟩,  -- C53
    ⟨[(1, [94, 101]), (1, [94, 102]), (2013265920, [94, 103])], 0⟩,  -- C54
    ⟨[(1, [94, 104]), (1, [94, 105]), (2013265920, [94, 106])], 0⟩,  -- C55
    ⟨[(2013265920, [94, 95, 96]), (1, [94, 97]), (2013265910, [94, 98, 105]), (2013265910, [94, 99, 104]), (2013265910, [94, 101, 102]), (2013265920, [95, 96, 107]), (2013265920, [95, 96, 108]), (2013265920, [95, 96, 109]), (2013265920, [95, 96, 110]), (1, [97, 107]), (1, [97, 108]), (1, [97, 109]), (1, [97, 110]), (2013265910, [98, 105, 107]), (2013265910, [98, 105, 108]), (2013265910, [98, 105, 109]), (2013265910, [98, 105, 110]), (2013265910, [99, 104, 107]), (2013265910, [99, 104, 108]), (2013265910, [99, 104, 109]), (2013265910, [99, 104, 110]), (2013265910, [101, 102, 107]), (2013265910, [101, 102, 108]), (2013265910, [101, 102, 109]), (2013265910, [101, 102, 110])], 0⟩,  -- C56
    ⟨[(2013265920, [94, 95, 99]), (2013265920, [94, 96, 98]), (1, [94, 100]), (2013265910, [94, 101, 105]), (2013265910, [94, 102, 104]), (2013265920, [95, 99, 107]), (2013265920, [95, 99, 108]), (2013265920, [95, 99, 109]), (2013265920, [95, 99, 110]), (2013265920, [96, 98, 107]), (2013265920, [96, 98, 108]), (2013265920, [96, 98, 109]), (2013265920, [96, 98, 110]), (1, [100, 107]), (1, [100, 108]), (1, [100, 109]), (1, [100, 110]), (2013265910, [101, 105, 107]), (2013265910, [101, 105, 108]), (2013265910, [101, 105, 109]), (2013265910, [101, 105, 110]), (2013265910, [102, 104, 107]), (2013265910, [102, 104, 108]), (2013265910, [102, 104, 109]), (2013265910, [102, 104, 110])], 0⟩,  -- C57
    ⟨[(2013265920, [94, 95, 102]), (2013265920, [94, 96, 101]), (2013265920, [94, 98, 99]), (1, [94, 103]), (2013265910, [94, 104, 105]), (2013265920, [95, 102, 107]), (2013265920, [95, 102, 108]), (2013265920, [95, 102, 109]), (2013265920, [95, 102, 110]), (2013265920, [96, 101, 107]), (2013265920, [96, 101, 108]), (2013265920, [96, 101, 109]), (2013265920, [96, 101, 110]), (2013265920, [98, 99, 107]), (2013265920, [98, 99, 108]), (2013265920, [98, 99, 109]), (2013265920, [98, 99, 110]), (1, [103, 107]), (1, [103, 108]), (1, [103, 109]), (1, [103, 110]), (2013265910, [104, 105, 107]), (2013265910, [104, 105, 108]), (2013265910, [104, 105, 109]), (2013265910, [104, 105, 110])], 0⟩,  -- C58
    ⟨[(2013265920, [94, 95, 105]), (2013265920, [94, 96, 104]), (2013265920, [94, 98, 102]), (2013265920, [94, 99, 101]), (1, [94, 106]), (2013265920, [95, 105, 107]), (2013265920, [95, 105, 108]), (2013265920, [95, 105, 109]), (2013265920, [95, 105, 110]), (2013265920, [96, 104, 107]), (2013265920, [96, 104, 108]), (2013265920, [96, 104, 109]), (2013265920, [96, 104, 110]), (2013265920, [98, 102, 107]), (2013265920, [98, 102, 108]), (2013265920, [98, 102, 109]), (2013265920, [98, 102, 110]), (2013265920, [99, 101, 107]), (2013265920, [99, 101, 108]), (2013265920, [99, 101, 109]), (2013265920, [99, 101, 110]), (1, [106, 107]), (1, [106, 108]), (1, [106, 109]), (1, [106, 110])], 0⟩,  -- C59
    ⟨[(1, [95, 95, 108]), (2013265920, [95, 108])], 0⟩,  -- C60
    ⟨[(1, [98, 108])], 0⟩,  -- C61
    ⟨[(1, [101, 108])], 0⟩,  -- C62
    ⟨[(1, [104, 108])], 0⟩,  -- C63
    ⟨[(1, [95, 96, 109]), (2013265920, [97, 109]), (11, [98, 105, 109]), (11, [99, 104, 109]), (11, [101, 102, 109]), (1, [109, 111])], 0⟩,  -- C64
    ⟨[(1, [95, 99, 109]), (1, [96, 98, 109]), (2013265920, [100, 109]), (11, [101, 105, 109]), (11, [102, 104, 109]), (1, [109, 112])], 0⟩,  -- C65
    ⟨[(1, [95, 102, 109]), (1, [96, 101, 109]), (1, [98, 99, 109]), (2013265920, [103, 109]), (11, [104, 105, 109]), (1, [109, 113])], 0⟩,  -- C66
    ⟨[(1, [95, 105, 109]), (1, [96, 104, 109]), (1, [98, 102, 109]), (1, [99, 101, 109]), (2013265920, [106, 109]), (1, [109, 114])], 0⟩,  -- C67
    ⟨[(1, [97, 115, 116]), (11, [100, 115, 117]), (11, [103, 115, 118]), (11, [106, 115, 119]), (1, [115, 120]), (2013265920, [115, 121]), (2013265920, [115, 122])], 0⟩,  -- C68
    ⟨[(1, [97, 115, 119]), (1, [100, 115, 116]), (11, [103, 115, 117]), (11, [106, 115, 118]), (1, [115, 123]), (2013265920, [115, 124]), (2013265920, [115, 125])], 0⟩,  -- C69
    ⟨[(1, [97, 115, 118]), (1, [100, 115, 119]), (1, [103, 115, 116]), (11, [106, 115, 117]), (1, [115, 126]), (2013265920, [115, 127]), (2013265920, [115, 128])], 0⟩,  -- C70
    ⟨[(1, [97, 115, 117]), (1, [100, 115, 118]), (1, [103, 115, 119]), (1, [106, 115, 116]), (1, [115, 129]), (2013265920, [115, 130]), (2013265920, [115, 131])], 0⟩,  -- C71
    ⟨[(1, [132, 133]), (1, [132, 134]), (2013265920, [132, 135])], 0⟩,  -- C72
    ⟨[(1, [132, 136]), (1, [132, 137]), (2013265920, [132, 138])], 0⟩,  -- C73
    ⟨[(1, [132, 139]), (1, [132, 140]), (2013265920, [132, 141])], 0⟩,  -- C74
    ⟨[(1, [132, 142]), (1, [132, 143]), (2013265920, [132, 144])], 0⟩,  -- C75
    ⟨[(2013265920, [132, 133, 134]), (1, [132, 135]), (2013265910, [132, 136, 143]), (2013265910, [132, 137, 142]), (2013265910, [132, 139, 140]), (2013265920, [133, 134, 145]), (2013265920, [133, 134, 146]), (2013265920, [133, 134, 147]), (2013265920, [133, 134, 148]), (1, [135, 145]), (1, [135, 146]), (1, [135, 147]), (1, [135, 148]), (2013265910, [136, 143, 145]), (2013265910, [136, 143, 146]), (2013265910, [136, 143, 147]), (2013265910, [136, 143, 148]), (2013265910, [137, 142, 145]), (2013265910, [137, 142, 146]), (2013265910, [137, 142, 147]), (2013265910, [137, 142, 148]), (2013265910, [139, 140, 145]), (2013265910, [139, 140, 146]), (2013265910, [139, 140, 147]), (2013265910, [139, 140, 148])], 0⟩,  -- C76
    ⟨[(2013265920, [132, 133, 137]), (2013265920, [132, 134, 136]), (1, [132, 138]), (2013265910, [132, 139, 143]), (2013265910, [132, 140, 142]), (2013265920, [133, 137, 145]), (2013265920, [133, 137, 146]), (2013265920, [133, 137, 147]), (2013265920, [133, 137, 148]), (2013265920, [134, 136, 145]), (2013265920, [134, 136, 146]), (2013265920, [134, 136, 147]), (2013265920, [134, 136, 148]), (1, [138, 145]), (1, [138, 146]), (1, [138, 147]), (1, [138, 148]), (2013265910, [139, 143, 145]), (2013265910, [139, 143, 146]), (2013265910, [139, 143, 147]), (2013265910, [139, 143, 148]), (2013265910, [140, 142, 145]), (2013265910, [140, 142, 146]), (2013265910, [140, 142, 147]), (2013265910, [140, 142, 148])], 0⟩,  -- C77
    ⟨[(2013265920, [132, 133, 140]), (2013265920, [132, 134, 139]), (2013265920, [132, 136, 137]), (1, [132, 141]), (2013265910, [132, 142, 143]), (2013265920, [133, 140, 145]), (2013265920, [133, 140, 146]), (2013265920, [133, 140, 147]), (2013265920, [133, 140, 148]), (2013265920, [134, 139, 145]), (2013265920, [134, 139, 146]), (2013265920, [134, 139, 147]), (2013265920, [134, 139, 148]), (2013265920, [136, 137, 145]), (2013265920, [136, 137, 146]), (2013265920, [136, 137, 147]), (2013265920, [136, 137, 148]), (1, [141, 145]), (1, [141, 146]), (1, [141, 147]), (1, [141, 148]), (2013265910, [142, 143, 145]), (2013265910, [142, 143, 146]), (2013265910, [142, 143, 147]), (2013265910, [142, 143, 148])], 0⟩,  -- C78
    ⟨[(2013265920, [132, 133, 143]), (2013265920, [132, 134, 142]), (2013265920, [132, 136, 140]), (2013265920, [132, 137, 139]), (1, [132, 144]), (2013265920, [133, 143, 145]), (2013265920, [133, 143, 146]), (2013265920, [133, 143, 147]), (2013265920, [133, 143, 148]), (2013265920, [134, 142, 145]), (2013265920, [134, 142, 146]), (2013265920, [134, 142, 147]), (2013265920, [134, 142, 148]), (2013265920, [136, 140, 145]), (2013265920, [136, 140, 146]), (2013265920, [136, 140, 147]), (2013265920, [136, 140, 148]), (2013265920, [137, 139, 145]), (2013265920, [137, 139, 146]), (2013265920, [137, 139, 147]), (2013265920, [137, 139, 148]), (1, [144, 145]), (1, [144, 146]), (1, [144, 147]), (1, [144, 148])], 0⟩,  -- C79
    ⟨[(1, [133, 133, 146]), (2013265920, [133, 146])], 0⟩,  -- C80
    ⟨[(1, [136, 146])], 0⟩,  -- C81
    ⟨[(1, [139, 146])], 0⟩,  -- C82
    ⟨[(1, [142, 146])], 0⟩,  -- C83
    ⟨[(1, [133, 134, 147]), (2013265920, [135, 147]), (11, [136, 143, 147]), (11, [137, 142, 147]), (11, [139, 140, 147]), (1, [147, 149])], 0⟩,  -- C84
    ⟨[(1, [133, 137, 147]), (1, [134, 136, 147]), (2013265920, [138, 147]), (11, [139, 143, 147]), (11, [140, 142, 147]), (1, [147, 150])], 0⟩,  -- C85
    ⟨[(1, [133, 140, 147]), (1, [134, 139, 147]), (1, [136, 137, 147]), (2013265920, [141, 147]), (11, [142, 143, 147]), (1, [147, 151])], 0⟩,  -- C86
    ⟨[(1, [133, 143, 147]), (1, [134, 142, 147]), (1, [136, 140, 147]), (1, [137, 139, 147]), (2013265920, [144, 147]), (1, [147, 152])], 0⟩,  -- C87
    ⟨[(1, [135, 153, 154]), (11, [138, 153, 155]), (11, [141, 153, 156]), (11, [144, 153, 157]), (1, [153, 158]), (2013265920, [153, 159]), (2013265920, [153, 160])], 0⟩,  -- C88
    ⟨[(1, [135, 153, 157]), (1, [138, 153, 154]), (11, [141, 153, 155]), (11, [144, 153, 156]), (1, [153, 161]), (2013265920, [153, 162]), (2013265920, [153, 163])], 0⟩,  -- C89
    ⟨[(1, [135, 153, 156]), (1, [138, 153, 157]), (1, [141, 153, 154]), (11, [144, 153, 155]), (1, [153, 164]), (2013265920, [153, 165]), (2013265920, [153, 166])], 0⟩,  -- C90
    ⟨[(1, [135, 153, 155]), (1, [138, 153, 156]), (1, [141, 153, 157]), (1, [144, 153, 154]), (1, [153, 167]), (2013265920, [153, 168]), (2013265920, [153, 169])], 0⟩   -- C91
  ]

/-- Columns `Alu` opens (the extractor's legend length). -/
def aluCols : Nat := 170

/-! ## §6 — THE MEASUREMENTS, on the actual emitted objects.

`airFoldRows_length` is a theorem, so these are its instances rather than independent readings — but
they are the numbers that go into the price, and a `#guard` is what stops the price and the compiler
from drifting apart. -/

/-! `expose_claim`: 176 sub-gates ⇒ 88 packed Kimchi rows, of which 75 are extension MULTIPLIES
(50 column products + 25 α-folds). -/
#guard airFoldGenCount exposeClaimHeads = 176
#guard (airFoldRows exposeClaimHeads exposeClaimCols (exposeClaimCols + 1)).length = 88
#guard extMulCount (airFoldGens exposeClaimHeads exposeClaimCols (exposeClaimCols + 1)) = 75

/-! `Alu`: 2,359 sub-gates ⇒ 1,180 packed rows, 1,396 extension multiplies
(1,304 column products + 92 α-folds). -/
#guard airFoldGenCount aluHeads = 2359
#guard (airFoldRows aluHeads aluCols (aluCols + 1)).length = 1180
#guard extMulCount (airFoldGens aluHeads aluCols (aluCols + 1)) = 1396

/-! ### §6.1 — the anti-vacuity run.

`runTable` executes the emitted straight-line program under the fresh-variable discipline and
`gensAcceptB` checks every sub-gate at the result. `hornerZ` then re-computes the accumulator
DIRECTLY from the heads and compares against the variable the circuit put it in — so the check spans
the whole 176-gate (resp. 2,359-gate) fold, not one gate of it. A fold chain is precisely the shape
a single-gate check cannot audit. -/

/-! The emitted program is a genuine straight-line program: every sub-gate defines the next fresh
variable, so `runGens` never has to write at an index. A `none` here would be an aliasing report. -/
#guard (runTable exposeClaimHeads exposeClaimCols).isSome
#guard (runTable aluHeads aluCols).isSome

/-! **A SATISFYING ASSIGNMENT EXISTS** for the emitted circuit, at a non-degenerate seeding. Without
this, `airFold_forces` would be a true statement about the empty set. -/
#guard match runTable exposeClaimHeads exposeClaimCols with
  | none => false
  | some v => gensAcceptB v (airFoldGens exposeClaimHeads exposeClaimCols (exposeClaimCols + 1))

#guard match runTable aluHeads aluCols with
  | none => false
  | some v => gensAcceptB v (airFoldGens aluHeads aluCols (aluCols + 1))

/-! **AND THE OUTPUT IS p3's ACCUMULATOR**, checked against an independent evaluation of the same
heads. This is `airFold_forces` instantiated at a concrete witness — the theorem's conclusion
observed, not merely implied. -/
#guard match runTable exposeClaimHeads exposeClaimCols with
  | none => false
  | some v =>
      v.getD (airFoldOut exposeClaimHeads exposeClaimCols (exposeClaimCols + 1)) 0
        = hornerZ v exposeClaimCols exposeClaimHeads

#guard match runTable aluHeads aluCols with
  | none => false
  | some v =>
      v.getD (airFoldOut aluHeads aluCols (aluCols + 1)) 0 = hornerZ v aluCols aluHeads

/-! ## §7 — THE RESIDUALS, at the resolution they are actually at.

**§7.1 — the extraction is a SEAM, not a theorem.** Nothing here proves §5's `Head`s are p3's
constraints. They are `to_head` output in `circuit-prove/tests/root_air_constraint_census.rs`,
flattening an `Arc`-shared `SymbolicExpression` DAG into a monomial sum. That extractor is checked
by `head_extractor_agrees_with_p3_evaluation`, a DIFFERENTIAL at pseudorandom assignments over all
901 base constraints of all seven tables. A differential is a confession, not a mitigation: it rules
out an extractor quietly wrong on these constraints and proves nothing about all inputs. Closing it
needs a Lean model of `SymbolicExpression` and a refinement of the flattening.

**§7.2 — ⚑ THE FLAT SOURCE LANGUAGE WAS THE COMPILER'S NEXT RUNG, AND IT IS NOW BUILT** —
`Dregg2.Circuit.Emit.KimchiDag`, which reaches all 901 base constraints at 2,433 DAG multiplies.
The measurement below is what forced it and is left standing because it is the argument.

**The measurement.**
All 901 of the root's base constraints ARE flat-`Head`-expressible — measured, not assumed. But
`Head` is FLAT and p3's constraints are a SHARED DAG, and flattening destroys the sharing:

| table | base | DAG multiplies | flat-`Head` multiplies | ratio |
|---|---:|---:|---:|---:|
| Alu | 92 | 356 | 1,304 | 3.7× |
| poseidon2-w16 | 316 | 958 | 243,849 | **254×** |
| poseidon2-w24 | 468 | 1,598 | 1,284,686 | **804×** |
| expose_claim | 25 | 25 | 50 | 2.0× |
| `Const`/`Public`/`recompose` | 0 | 0 | 0 | — |
| **Σ** | **901** | **2,937** | **1,529,889** | **521×** |

At ≈31 o1js rows per extension multiply (§3.10/§3.15) that is ≈91,000 rows through a
sharing-preserving lowering against ≈4.7 × 10⁷ through the flat one — the flat form ALONE exceeds
§3.14's ≈3.0 × 10⁷ whole-verifier budget. So the honest statement is not "the compiler cannot
express the Poseidon2 tables"; it is **"`Head` can express them and must not, and the next rung is a
DAG-shaped source language with a common-subexpression cache"** — which is exactly what p3's own
`SymbolicCompiler::compile_base` does (`recursion/src/traits/air.rs:150-156`, `base_cache`). The
lowering theorem for it is the same shape as `lowerHeadValue_forces`, one `Gen1` per DAG node.

**§7.3 — the LOOKUP constraints are not in this vocabulary.** 192 of the root's 1,093 are LogUp
permutation constraints over the CHALLENGE extension, carrying permutation columns and challenges
that `Head`'s `List Nat` does not name. Three of the seven tables — `Const`, `Public`, `recompose` —
have ZERO base constraints and are ENTIRELY lookups, so for them this rung covers nothing at all.

**§7.4 — the closing equality is §3.16's, not this file's.** `airFold_forces` produces the
accumulator; multiplying by `inv_vanishing(ζ)` and comparing against the recomposed quotient is
`AirEval.ts`'s `assertQuotientConsistency`. The two halves are NOT welded: one is a Lean theorem,
the other a TypeScript circuit, and nothing states they compose.

**§7.5 — the lane currency.** Everything above rides `packGen`, whose `packGen_holds_iff` is proved,
and is stated at an arbitrary `CommRing` — i.e. in EXTENSION-element operations. The lowering of one
extension element to Pasta lanes is `KimchiPoseidon2`'s `BB` layer, which interleaves `RangeCheck0`
rows, and for THAT backend the needed lemma is `KimchiLower`'s named-and-unproved
`renderOps_gens_sound`. So this rung is proved in the extension currency and NOT in the lane
currency.

**§7.6 — this does not make the verifier sound.** P10 stands. So do the real preamble, the
mixed-height MMCS openings, 19-queries-not-1, and the undischarged FRI/STARK floor.
-/

#assert_axioms lowerHeadValue_forces
#assert_axioms foldGo_forces
#assert_axioms airFold_forces
#assert_axioms airFold_forces_evalH
#assert_axioms airFoldRows_length
#assert_axioms airFoldGens_length
#assert_axioms airFoldRows_all_modelled
#assert_axioms lowerHeadValueGens_length
#assert_axioms valueGenCount_succ

end Dregg2.Circuit.Emit.KimchiRootAirEval
