/-
# Dregg2.Circuit.Emit.KimchiLower — the ARITHMETIC BACKEND: `Gen1` sub-gates ⟶ Kimchi rows

## ⚑ READ THIS FIRST — what this file is FOR, and the misreading it invites

The program this compiler exists to emit is **a Kimchi circuit that VERIFIES A DREGG STARK PROOF**:
input = commitments, openings, FRI layers and public inputs; body = Merkle-opening checks against
committed roots, per-layer fold consistency, the `DuplexChallenger` deriving every challenge and
query index, the DEEP/quotient binding, and the AIR evaluation at the queried points; output =
accept/reject. That circuit is POLYLOG in dregg's computation, which is the only reason it fits in
a few hundred Pickles steps.

It is **NOT** dregg's own AIRs re-hosted on Mina. Re-emitting the computation's constraint systems
is LINEAR in the trace, and it proves only "Mina recomputed the same thing" — no dregg proof is
consumed and no dregg state is attested.

This file is the **arithmetic substrate** for generating that verifier: the sub-gate vocabulary,
the forcing lemmas, and the two backends. `Gen1.mul`/`acc`/`scale`/`lin2` are what the Poseidon2
permutation generator, the Merkle-opening generator and the fold-consistency generator are all
built from.

**§9's `lowerHead` is one verifier RUNG, and it is the one that invites the misreading.** A STARK
verifier does evaluate dregg's AIR — `AIR.evalAtZeta`, priced at ≈3.5% of the budget in
`docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §3.14 — but it does so **at the opened points only, once**,
never per trace row. So `lowerHead` is legitimate here exactly and only under that discipline, and
`lowerHead_cost_is_per_point` below states the obligation rather than leaving it to a reader's
goodwill. Applied per row it would be the linear re-emission this file is not.

The reason the pass is written in Lean rather than as a script is `lowerHead_sound`: **any
assignment that satisfies the emitted Kimchi rows makes the source `Head` vanish** — a theorem over
the ACTUAL emitted object, not a differential over samples.

## The three-stage shape, because a compiler is not a function

  * **`Gen1`** — one generic SUB-gate, `cl·l + cr·r + co·o + cm·(l·r) + cc = 0`. This is the
    compiler's internal currency and it is HALF a Kimchi row: `generic.rs:55` sets
    `CONSTRAINTS = 2`, so one row carries two independent sub-gates on disjoint columns
    (`w₀w₁w₂ / c₀..c₄` and `w₃w₄w₅ / c₅..c₉`).
  * **the lowering** — `Head → List Gen1`, a straight-line program over fresh variables:
    one sub-gate per multiplication in a term's column product, one per accumulation step, one to
    pin the constant and one to assert the accumulator is zero.
  * **two backends** — `unpackGen` (one sub-gate per row) and `packGen` (two per row).
    `packGen_holds_iff`/`unpackGen_holds_iff` prove BOTH render the same conjunction, and
    `packGen_length` prices the difference at exactly `⌈n/2⌉` versus `n`. A packing pass whose
    equivalence is a theorem is the thing a hand-written circuit cannot offer.

## What crosses into `KOp`

Range checks are not expressible as generic sub-gates — `RangeCheck0` is its own gate with its own
ten bodies. `KOp` is the mixed instruction the later passes emit (`gen`, `rc0`, `zeroRow`), and
`renderOps` is the backend that turns a mixed program into rows, packing runs of `gen` and leaving
the rest alone. `KimchiPoseidon2` is its first consumer.

## Deliberately NOT here

`emitConstraint` is not touched: it targets the retired IR-v1 `EmittedDescriptor`, whose own header
records that no deployed path instantiates `LeanDescriptorAir`. The live source vocabulary is
`Head`/`EmittedExpr`, and `Head` is what this file consumes.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`.
NEW file; imports `KimchiTarget` (which imports `AirBuilder`).
-/
import Dregg2.Circuit.Emit.KimchiTarget

namespace Dregg2.Circuit.Emit.KimchiLower

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.AirBuilder (Head evalH evalTerm)
open Dregg2.Circuit.Emit.KimchiTarget

set_option autoImplicit false

/-! ## §1 — `Gen1`, half a Kimchi row. -/

/-- **One generic sub-gate.** `generic.rs:15` — `c₀·l + c₁·r + c₂·o + c₃·(l×r) + c₄ = 0`, with the
coefficient roles named (`generic.rs:29-31`): `cl` left, `cr` right, `co` out, `cm` mul, `cc`
const. Two of these fit in ONE `GateType::Generic` row. -/
structure Gen1 where
  l : Nat
  r : Nat
  o : Nat
  cl : ℤ
  cr : ℤ
  co : ℤ
  cm : ℤ
  cc : ℤ
  deriving Repr, DecidableEq, Inhabited

namespace Gen1

variable {R : Type} [CommRing R]

/-- The sub-gate's polynomial body. -/
def body (a : Nat → R) (g : Gen1) : R :=
  (g.cl : R) * a g.l + (g.cr : R) * a g.r + (g.co : R) * a g.o
    + (g.cm : R) * (a g.l * a g.r) + (g.cc : R)

/-- The sub-gate HOLDS when its body vanishes. -/
def holds (a : Nat → R) (g : Gen1) : Prop := g.body a = 0

/-- `o := l + k·r` — one accumulation step. -/
def acc (l r o : Nat) (k : ℤ) : Gen1 := ⟨l, r, o, 1, k, -1, 0, 0⟩

/-- `o := l · r` — one multiplication. -/
def mul (l r o : Nat) : Gen1 := ⟨l, r, o, 0, 0, -1, 1, 0⟩

/-- `v := k` — pin a variable to a constant. -/
def const (v : Nat) (k : ℤ) : Gen1 := ⟨v, 0, 0, 1, 0, 0, 0, -k⟩

/-- `v = 0` — assert a variable vanishes. -/
def isZero (v : Nat) : Gen1 := ⟨v, 0, 0, 1, 0, 0, 0, 0⟩

/-- `o := l + k` — add a constant. -/
def addConst (l o : Nat) (k : ℤ) : Gen1 := ⟨l, 0, o, 1, 0, -1, 0, k⟩

/-- `o := k · l` — scale by a constant. -/
def scale (l o : Nat) (k : ℤ) : Gen1 := ⟨l, 0, o, k, 0, -1, 0, 0⟩

/-- `o := cl·l + cr·r` — a two-input linear combination. -/
def lin2 (l r o : Nat) (cl cr : ℤ) : Gen1 := ⟨l, r, o, cl, cr, -1, 0, 0⟩

/-- `o := cl·l + cr·r + cc` — the same with the row's constant slot used. This is what a
SUBTRACTION costs in an integer-representative emulation: `cc` carries the multiple of the emulated
modulus that keeps the representative non-negative without moving its residue. Still ONE sub-gate,
because `generic.rs`'s `c₄` is already there. -/
def lin2c (l r o : Nat) (cl cr cc : ℤ) : Gen1 := ⟨l, r, o, cl, cr, -1, 0, cc⟩

theorem acc_forces (a : Nat → R) (l r o : Nat) (k : ℤ) (h : (acc l r o k).holds a) :
    a o = a l + (k : R) * a r := by
  have : (1 : R) * a l + (k : R) * a r + (-1 : R) * a o + (0 : R) * (a l * a r) + (0 : R) = 0 := by
    simpa [holds, body, acc] using h
  linear_combination -this

theorem mul_forces (a : Nat → R) (l r o : Nat) (h : (mul l r o).holds a) :
    a o = a l * a r := by
  have : (0 : R) * a l + (0 : R) * a r + (-1 : R) * a o + (1 : R) * (a l * a r) + (0 : R) = 0 := by
    simpa [holds, body, mul] using h
  linear_combination -this

theorem const_forces (a : Nat → R) (v : Nat) (k : ℤ) (h : (const v k).holds a) :
    a v = (k : R) := by
  have : (1 : R) * a v + (0 : R) * a 0 + (0 : R) * a 0 + (0 : R) * (a v * a 0) + ((-k : ℤ) : R)
      = 0 := by simpa [holds, body, const] using h
  push_cast at this
  linear_combination this

theorem isZero_forces (a : Nat → R) (v : Nat) (h : (isZero v).holds a) : a v = 0 := by
  have : (1 : R) * a v + (0 : R) * a 0 + (0 : R) * a 0 + (0 : R) * (a v * a 0) + (0 : R) = 0 := by
    simpa [holds, body, isZero] using h
  linear_combination this

theorem addConst_forces (a : Nat → R) (l o : Nat) (k : ℤ) (h : (addConst l o k).holds a) :
    a o = a l + (k : R) := by
  have : (1 : R) * a l + (0 : R) * a 0 + (-1 : R) * a o + (0 : R) * (a l * a 0) + (k : R) = 0 := by
    simpa [holds, body, addConst] using h
  linear_combination -this

theorem scale_forces (a : Nat → R) (l o : Nat) (k : ℤ) (h : (scale l o k).holds a) :
    a o = (k : R) * a l := by
  have : (k : R) * a l + (0 : R) * a 0 + (-1 : R) * a o + (0 : R) * (a l * a 0) + (0 : R) = 0 := by
    simpa [holds, body, scale] using h
  linear_combination -this

theorem lin2_forces (a : Nat → R) (l r o : Nat) (cl cr : ℤ) (h : (lin2 l r o cl cr).holds a) :
    a o = (cl : R) * a l + (cr : R) * a r := by
  have : (cl : R) * a l + (cr : R) * a r + (-1 : R) * a o + (0 : R) * (a l * a r) + (0 : R)
      = 0 := by simpa [holds, body, lin2] using h
  linear_combination -this

theorem lin2c_forces (a : Nat → R) (l r o : Nat) (cl cr cc : ℤ)
    (h : (lin2c l r o cl cr cc).holds a) :
    a o = (cl : R) * a l + (cr : R) * a r + (cc : R) := by
  have : (cl : R) * a l + (cr : R) * a r + (-1 : R) * a o + (0 : R) * (a l * a r) + (cc : R)
      = 0 := by simpa [holds, body, lin2c] using h
  linear_combination -this

end Gen1

/-- Every sub-gate of a program holds. -/
def gensHold {R : Type} [CommRing R] (a : Nat → R) (gs : List Gen1) : Prop :=
  ∀ g ∈ gs, g.holds a

theorem gensHold_append {R : Type} [CommRing R] {a : Nat → R} {gs hs : List Gen1}
    (h : gensHold a (gs ++ hs)) : gensHold a gs ∧ gensHold a hs :=
  ⟨fun g hg => h g (by simp [hg]), fun g hg => h g (by simp [hg])⟩

theorem gensHold_cons {R : Type} [CommRing R] {a : Nat → R} {g : Gen1} {gs : List Gen1}
    (h : gensHold a (g :: gs)) : g.holds a ∧ gensHold a gs :=
  ⟨h g (by simp), fun x hx => h x (by simp [hx])⟩

/-! ## §2 — the two backends, and the packing theorem.

`unpackGen` is the naive rendering (one sub-gate per row); `packGen` uses both halves. They agree on
MEANING and differ by exactly 2× in ROWS, and both facts are theorems — which is what lets the
compiler take the optimisation without anyone re-auditing the circuit. -/

/-- One sub-gate alone in a row (second half all-zero, hence identically satisfied). -/
def gen1Row (g : Gen1) : KRow := mkGeneric1 g.l g.r g.o g.cl g.cr g.co g.cm g.cc

/-- Two sub-gates sharing one row — `generic.rs:55`, `CONSTRAINTS = 2`. -/
def gen2Row (g h : Gen1) : KRow :=
  mkGeneric2 g.l g.r g.o g.cl g.cr g.co g.cm g.cc h.l h.r h.o h.cl h.cr h.co h.cm h.cc

theorem gen1Row_gate (g : Gen1) : (gen1Row g).gate = .generic := rfl
theorem gen2Row_gate (g h : Gen1) : (gen2Row g h).gate = .generic := rfl

/-- **A one-sub-gate row says exactly what the sub-gate says.** -/
theorem gen1Row_holds_iff {R : Type} [CommRing R] (a : Nat -> R) (g : Gen1) :
    (gen1Row g).holds a <-> g.holds a := by
  rw [gen1Row, mkGeneric1_holds_iff]
  rfl

/-- **A two-sub-gate row says exactly the CONJUNCTION.** The two halves live on disjoint witness
columns (`w0w1w2 / c0..c4` and `w3w4w5 / c5..c9`), so fusing them adds no interaction — which is
what makes the packing pass a pure win rather than a re-encoding. -/
theorem gen2Row_holds_iff {R : Type} [CommRing R] (a : Nat -> R) (g h : Gen1) :
    (gen2Row g h).holds a <-> (g.holds a /\ h.holds a) := by
  unfold KRow.holds
  rw [gen2Row, mkGeneric2_gate]
  simp only [mkGeneric2_body1, mkGeneric2_body2]
  rfl

theorem rowsHold_cons_iff {R : Type} [CommRing R] (a : Nat -> R) (r : KRow) (rs : List KRow) :
    rowsHold a (r :: rs) <-> (r.holds a /\ rowsHold a rs) := by
  simp [rowsHold, List.forall_mem_cons]

theorem gensHold_cons_iff {R : Type} [CommRing R] (a : Nat -> R) (g : Gen1) (gs : List Gen1) :
    gensHold a (g :: gs) <-> (g.holds a /\ gensHold a gs) := by
  simp [gensHold, List.forall_mem_cons]

/-- Naive backend: one Kimchi row per sub-gate, second half unused. -/
def unpackGen (gs : List Gen1) : List KRow := gs.map gen1Row

/-- **The packing pass**: two sub-gates per Kimchi row. -/
def packGen : List Gen1 -> List KRow
  | [] => []
  | [g] => [gen1Row g]
  | g :: h :: rest => gen2Row g h :: packGen rest

theorem unpackGen_length (gs : List Gen1) : (unpackGen gs).length = gs.length := by
  simp [unpackGen]

/-- **The packing saves exactly half a row per sub-gate**: `ceil(n/2)` rows for `n` sub-gates. -/
theorem packGen_length (gs : List Gen1) : (packGen gs).length = (gs.length + 1) / 2 := by
  induction gs using packGen.induct with
  | case1 => simp [packGen]
  | case2 g => simp [packGen]
  | case3 g h rest ih => simp only [packGen, List.length_cons, ih]; omega

theorem unpackGen_holds_iff {R : Type} [CommRing R] (a : Nat -> R) (gs : List Gen1) :
    rowsHold a (unpackGen gs) <-> gensHold a gs := by
  simp [unpackGen, rowsHold, gensHold, gen1Row_holds_iff]

/-- **The packing preserves MEANING.** A packed circuit is satisfied by exactly the assignments
that satisfy the unpacked one — the two backends are interchangeable and the compiler may take the
cheaper one without a re-audit. -/
theorem packGen_holds_iff {R : Type} [CommRing R] (a : Nat -> R) (gs : List Gen1) :
    rowsHold a (packGen gs) <-> gensHold a gs := by
  induction gs using packGen.induct with
  | case1 => simp [packGen, gensHold, rowsHold]
  | case2 g =>
    rw [packGen, rowsHold_cons_iff, gen1Row_holds_iff, gensHold_cons_iff]
    simp [rowsHold, gensHold]
  | case3 g h rest ih =>
    rw [packGen, rowsHold_cons_iff, gen2Row_holds_iff, ih, gensHold_cons_iff, gensHold_cons_iff]
    tauto

/-- Every row a generic backend emits carries a MODELLED gate — the anti-vacuity obligation
`KimchiTarget`'s fail-closed `holds` demands. -/
theorem packGen_all_modelled (gs : List Gen1) : ∀ r ∈ packGen gs, r.gate.modelled = true := by
  induction gs using packGen.induct with
  | case1 => intro r hr; cases hr
  | case2 g => intro r hr; simp only [packGen, List.mem_singleton] at hr; subst hr; rfl
  | case3 g h rest ih =>
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr2
    · rfl
    · exact ih r hr2

theorem unpackGen_all_modelled (gs : List Gen1) : ∀ r ∈ unpackGen gs, r.gate.modelled = true := by
  intro r hr
  simp only [unpackGen, List.mem_map] at hr
  obtain ⟨g, _, rfl⟩ := hr
  rfl

/-! ## §3 — the AIR-evaluation rung: `Head` ⟶ sub-gates.

⚑ **Scope, restated where the code is.** This lowers ONE `Head` to a straight-line program. Inside
the verifier it is invoked on the AIR's constraint polynomials **at the opened points** (ζ, ζω) on
values the proof supplied — a fixed, trace-independent number of invocations. It is NOT invoked per
trace row; doing so would make the emitted circuit linear in dregg's computation, which is the
whole thing the verification route exists to avoid.

`Head` is `Σ coeff·∏cols + const`. The straight-line program is:

  * pin a fresh accumulator to `const`;
  * for each term, build the column product with one multiplication sub-gate per extra column, then
    fold `acc ← acc + coeff·prod` with one accumulation sub-gate;
  * assert the final accumulator is zero.

Freshness is threaded as a watermark. Note that **soundness needs no freshness hypothesis**: each
sub-gate forces its output from its inputs, so a satisfying assignment propagates regardless of
aliasing. Freshness is what buys COMPLETENESS (that a witness exists), which is why `lowerHead_wm`
tracks the watermark separately. -/

/-- Fold a column product into an accumulator variable. `prodGo cols acc nv` returns the variable
holding `a acc · ∏ cols`, the new watermark, and the sub-gates. -/
def prodGo : List Nat → Nat → Nat → Nat × Nat × List Gen1
  | [], acc, nv => (acc, nv, [])
  | c :: rest, acc, nv =>
      let out := nv
      let (f, nv2, gs) := prodGo rest out (nv + 1)
      (f, nv2, Gen1.mul acc c out :: gs)

/-- Build the column product of one term. An EMPTY product needs a variable pinned to `1`; the
constant-folding pass named in §7 would remove those; until it lands they are emitted as written. -/
def lowerProd : List Nat → Nat → Nat × Nat × List Gen1
  | [], nv => (nv, nv + 1, [Gen1.const nv 1])
  | c :: rest, nv => prodGo rest c nv

/-- Accumulate the terms. `lowerAcc ts acc nv` returns the final accumulator variable, the
watermark, and the sub-gates. -/
def lowerAcc : List (ℤ × List Nat) → Nat → Nat → Nat × Nat × List Gen1
  | [], acc, nv => (acc, nv, [])
  | (k, cols) :: ts, acc, nv =>
      let (p, nv1, gs1) := lowerProd cols nv
      let out := nv1
      let (f, nv2, gs2) := lowerAcc ts out (nv1 + 1)
      (f, nv2, gs1 ++ (Gen1.acc acc p out k :: gs2))

/-- **THE LOWERING.** `Head → List Gen1`, starting fresh variables at `nv`. -/
def lowerHeadGens (h : Head) (nv : Nat) : List Gen1 :=
  Gen1.const nv h.const
    :: ((lowerAcc h.terms nv (nv + 1)).2.2 ++ [Gen1.isZero (lowerAcc h.terms nv (nv + 1)).1])

/-- The watermark after lowering — the first variable index still free. -/
def lowerHeadWm (h : Head) (nv : Nat) : Nat := (lowerAcc h.terms nv (nv + 1)).2.1

/-- **The lowered Kimchi circuit**, packed two sub-gates to a row. -/
def lowerHead (h : Head) (nv : Nat) : List KRow := packGen (lowerHeadGens h nv)

/-! ## §4 — the head's value in the target ring.

`evalH` is ℤ-valued because dregg's `Assignment` is. Kimchi lives over a Pasta field, so the
preservation statement has to be in the TARGET ring; `headEvalR` is `evalH` transported, and
`headEvalR_int` pins that the two agree when the target ring IS `ℤ`. -/

/-- `evalH` evaluated in an arbitrary `CommRing` at an `R`-valued assignment. -/
def headEvalR {R : Type} [CommRing R] (a : Nat → R) (h : Head) : R :=
  (h.terms.map (fun t => ((t.1 : ℤ) : R) * ((t.2.map a).prod))).sum + ((h.const : ℤ) : R)

theorem headEvalR_int (a : Assignment) (h : Head) : headEvalR a h = evalH h a := by
  simp only [headEvalR, evalH, Int.cast_id]
  rfl

/-! ## §5 — soundness: the emitted rows FORCE the head to vanish. -/

section Sound

variable {R : Type} [CommRing R]

theorem prodGo_forces (a : Nat → R) :
    ∀ (cols : List Nat) (acc nv : Nat), gensHold a (prodGo cols acc nv).2.2 →
      a (prodGo cols acc nv).1 = a acc * (cols.map a).prod := by
  intro cols
  induction cols with
  | nil => intro acc nv _; simp [prodGo]
  | cons c rest ih =>
    intro acc nv hg
    simp only [prodGo] at hg ⊢
    obtain ⟨hrow, hrest⟩ := gensHold_cons hg
    have hmul : a nv = a acc * a c := Gen1.mul_forces a acc c nv hrow
    have := ih nv (nv + 1) hrest
    rw [this, hmul, List.map_cons, List.prod_cons]
    ring

theorem lowerProd_forces (a : Nat → R) (cols : List Nat) (nv : Nat)
    (hg : gensHold a (lowerProd cols nv).2.2) :
    a (lowerProd cols nv).1 = (cols.map a).prod := by
  cases cols with
  | nil =>
    simp only [lowerProd] at hg ⊢
    have := Gen1.const_forces a nv 1 (hg _ (by simp))
    simpa using this
  | cons c rest =>
    simp only [lowerProd] at hg ⊢
    have := prodGo_forces a rest c nv hg
    rw [this]
    simp [List.prod_cons]

theorem lowerAcc_forces (a : Nat → R) :
    ∀ (ts : List (ℤ × List Nat)) (acc nv : Nat), gensHold a (lowerAcc ts acc nv).2.2 →
      a (lowerAcc ts acc nv).1
        = a acc + (ts.map (fun t => ((t.1 : ℤ) : R) * ((t.2.map a).prod))).sum := by
  intro ts
  induction ts with
  | nil => intro acc nv _; simp [lowerAcc]
  | cons t ts ih =>
    intro acc nv hg
    obtain ⟨k, cols⟩ := t
    simp only [lowerAcc] at hg ⊢
    obtain ⟨hg1, hg2⟩ := gensHold_append hg
    obtain ⟨hrow, hg3⟩ := gensHold_cons hg2
    have hp : a (lowerProd cols nv).1 = (cols.map a).prod := lowerProd_forces a cols nv hg1
    have hacc : a (lowerProd cols nv).2.1
        = a acc + (k : R) * a (lowerProd cols nv).1 :=
      Gen1.acc_forces a acc _ _ k hrow
    have hrest := ih (lowerProd cols nv).2.1 ((lowerProd cols nv).2.1 + 1) hg3
    rw [hrest, hacc, hp]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- **THE SEMANTICS-PRESERVATION THEOREM.**

Any assignment satisfying every Kimchi row that `lowerHead` emits makes the source `Head` evaluate
to zero in the target ring. Stated over the emitted object itself — `lowerHead h nv` is the very
list of `KRow`s handed to the backend — and over `rowsHold`, which is `KimchiTarget`'s per-row
`holds`, whose generic case is welded to the reality-gated `KimchiVerify.genericGateConstraint`.

This is the whole reason the compiler lives in Lean. A Rust or TypeScript emitter can be tested on
cases; it cannot state this. -/
theorem lowerHead_sound (a : Nat → R) (h : Head) (nv : Nat)
    (hr : rowsHold a (lowerHead h nv)) : headEvalR a h = 0 := by
  rw [lowerHead, packGen_holds_iff] at hr
  simp only [lowerHeadGens] at hr
  obtain ⟨hconst, hrest⟩ := gensHold_cons hr
  obtain ⟨hacc, hzero⟩ := gensHold_append hrest
  have h0 : a nv = ((h.const : ℤ) : R) := Gen1.const_forces a nv h.const hconst
  have hfin := lowerAcc_forces a h.terms nv (nv + 1) hacc
  have hz : a (lowerAcc h.terms nv (nv + 1)).1 = 0 :=
    Gen1.isZero_forces a _ (hzero _ (by simp))
  rw [hz, h0] at hfin
  unfold headEvalR
  linear_combination -hfin

/-- The same statement in dregg's own vocabulary: at an ℤ-valued assignment the emitted Kimchi
circuit forces `evalH h a = 0`, which is exactly what `cgH h` asserts on the dregg side. So the two
emissions agree on what they REFUSE. -/
theorem lowerHead_sound_evalH (a : Assignment) (h : Head) (nv : Nat)
    (hr : rowsHold a (lowerHead h nv)) : evalH h a = 0 := by
  have := lowerHead_sound a h nv hr
  rwa [headEvalR_int] at this

end Sound

/-! ## §6 — anti-vacuity, and the cost model. -/

/-- Every row the lowering emits is a MODELLED gate, so `lowerHead_sound` is not discharged by
`KimchiTarget`'s fail-closed `False` on an unmodelled row. -/
theorem lowerHead_all_modelled (h : Head) (nv : Nat) :
    ∀ r ∈ lowerHead h nv, r.gate.modelled = true :=
  packGen_all_modelled _

/-- Sub-gates a single column product costs: `n − 1` multiplications, or one constant pin for the
empty product. -/
def prodGens : List Nat → Nat
  | [] => 1
  | _ :: rest => rest.length

/-- **The compiler's cost function**, in SUB-GATES. One per multiplication, one per accumulation,
one to pin the constant, one to assert zero. -/
def lowerHeadGenCount (h : Head) : Nat :=
  2 + (h.terms.map (fun t => prodGens t.2 + 1)).sum

/-- **The compiler's cost function, in ROWS** — after packing. This is the number the differential
compares against o1js `getRows()`. -/
def lowerHeadRowCount (h : Head) : Nat := (lowerHeadGenCount h + 1) / 2

theorem prodGo_length : ∀ (cols : List Nat) (acc nv : Nat),
    (prodGo cols acc nv).2.2.length = cols.length := by
  intro cols
  induction cols with
  | nil => intro acc nv; rfl
  | cons c rest ih => intro acc nv; simp only [prodGo, List.length_cons]; rw [ih]

theorem lowerProd_length (cols : List Nat) (nv : Nat) :
    (lowerProd cols nv).2.2.length = prodGens cols := by
  cases cols with
  | nil => rfl
  | cons c rest => simp only [lowerProd, prodGens]; exact prodGo_length rest c nv

theorem lowerAcc_length : ∀ (ts : List (ℤ × List Nat)) (acc nv : Nat),
    (lowerAcc ts acc nv).2.2.length = (ts.map (fun t => prodGens t.2 + 1)).sum := by
  intro ts
  induction ts with
  | nil => intro acc nv; rfl
  | cons t ts ih =>
    intro acc nv
    obtain ⟨k, cols⟩ := t
    simp only [lowerAcc, List.length_append, List.length_cons, List.map_cons, List.sum_cons]
    rw [lowerProd_length, ih]
    omega

theorem lowerHeadGens_length (h : Head) (nv : Nat) :
    (lowerHeadGens h nv).length = lowerHeadGenCount h := by
  simp only [lowerHeadGens, lowerHeadGenCount, List.length_cons, List.length_append,
    List.length_nil, lowerAcc_length]
  omega

/-- **The row count is a THEOREM, not a measurement.** -/
theorem lowerHead_rowCount (h : Head) (nv : Nat) :
    (lowerHead h nv).length = lowerHeadRowCount h := by
  simp only [lowerHead, lowerHeadRowCount]
  rw [packGen_length, lowerHeadGens_length]

/-! ## §7 — NOT DONE: constant folding.

`Head` admits terms with an EMPTY column list — constants wearing a term's clothes, each costing
two sub-gates to express what `Head.const` already holds for free. The pass is one line
(`terms.filter (!·.2.isEmpty)`, sum the rest into `const`) and its correctness is
`headEvalR a (foldConsts h) = headEvalR a h`. It is NOT landed here: the proof did not close in this
pass, and an optimisation whose equivalence is unproved is exactly the thing this file exists to
not do. Named in the remainder, not shipped half-proved.
-/

/-! ## §8 — `KOp`: the mixed instruction, for passes that need a real range check.

A range check is not a generic sub-gate. `KOp` is what the gadget layer emits and `renderOps` is the
backend that packs runs of `gen` and passes the rest through. -/

/-- A compiler instruction. `gen` is half a generic row; `rc0` is a standalone 64-bit `RangeCheck0`
row (`range_check/gadget.rs:63-69`) on value column `v` with its twelve limb/crumb columns; `zeroRow`
is the companion `Zero` row a gadget sometimes needs. -/
inductive KOp where
  | gen (g : Gen1)
  | rc0 (v c1 c2 p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14 : Nat)
  | zeroRow
  deriving Repr, Inhabited

/-- **The mixed backend.** `pending` is a generic sub-gate still looking for a partner: two
consecutive `gen` ops share a row (`generic.rs:55`, `CONSTRAINTS = 2`), and anything else flushes
the pending half-row first.

Every case matches a CONCRETE op constructor rather than falling through an overlapping pattern.
That is not style: an "otherwise" case makes the generated induction principle carry a negative
hypothesis (`∀ h rest, ops ≠ .gen h :: rest → False`) that no `simp` can discharge, and the two
theorems below become unprovable as written. -/
def renderOpsGo : Option Gen1 → List KOp → List KRow
  | none, [] => []
  | some g, [] => [gen1Row g]
  | none, .gen g :: rest => renderOpsGo (some g) rest
  | some g, .gen h :: rest => gen2Row g h :: renderOpsGo none rest
  | none, .rc0 v a b p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14 :: rest =>
      mkRangeCheck0 v a b p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14 :: renderOpsGo none rest
  | some g, .rc0 v a b p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14 :: rest =>
      gen1Row g :: mkRangeCheck0 v a b p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14
        :: renderOpsGo none rest
  | none, .zeroRow :: rest => mkZero :: renderOpsGo none rest
  | some g, .zeroRow :: rest => gen1Row g :: mkZero :: renderOpsGo none rest

/-- Render an instruction program to Kimchi rows. -/
def renderOps (ops : List KOp) : List KRow := renderOpsGo none ops

/-- The sub-gates an op program asserts, with a possible pending one at the front. -/
def opsGensGo : Option Gen1 → List KOp → List Gen1
  | none, [] => []
  | some g, [] => [g]
  | none, .gen g :: rest => opsGensGo (some g) rest
  | some g, .gen h :: rest => g :: opsGensGo (some h) rest
  | none, _ :: rest => opsGensGo none rest
  | some g, _ :: rest => g :: opsGensGo none rest

/-- The sub-gates an op program asserts. -/
def opsGens (ops : List KOp) : List Gen1 := opsGensGo none ops

/-- Every row the mixed backend emits carries a MODELLED gate — the anti-vacuity obligation
`KimchiTarget`'s fail-closed `holds` demands. Without it, a soundness theorem over an emitted
circuit could be discharged by the circuit being unsatisfiable. -/
theorem renderOpsGo_all_modelled (p : Option Gen1) (ops : List KOp) :
    ∀ r ∈ renderOpsGo p ops, r.gate.modelled = true := by
  induction p, ops using renderOpsGo.induct with
  | case1 => intro r hr; cases hr
  | case2 g => intro r hr; simp only [renderOpsGo, List.mem_singleton] at hr; subst hr; rfl
  | case3 g rest ih => exact ih
  | case4 g h rest ih =>
    intro r hr
    simp only [renderOpsGo, List.mem_cons] at hr
    rcases hr with rfl | hr1
    · rfl
    · exact ih r hr1
  | case5 v a b p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14 rest ih =>
    intro r hr
    simp only [renderOpsGo, List.mem_cons] at hr
    rcases hr with rfl | hr1
    · rfl
    · exact ih r hr1
  | case6 g v a b p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14 rest ih =>
    intro r hr
    simp only [renderOpsGo, List.mem_cons] at hr
    rcases hr with rfl | hr1
    · rfl
    rcases hr1 with rfl | hr2
    · rfl
    · exact ih r hr2
  | case7 rest ih =>
    intro r hr
    simp only [renderOpsGo, List.mem_cons] at hr
    rcases hr with rfl | hr1
    · rfl
    · exact ih r hr1
  | case8 g rest ih =>
    intro r hr
    simp only [renderOpsGo, List.mem_cons] at hr
    rcases hr with rfl | hr1
    · rfl
    rcases hr1 with rfl | hr2
    · rfl
    · exact ih r hr2

theorem renderOps_all_modelled (ops : List KOp) :
    ∀ r ∈ renderOps ops, r.gate.modelled = true := renderOpsGo_all_modelled none ops

/-! ### NOT DONE: `renderOps_gens_sound`.

The statement is `rowsHold a (renderOps ops) → gensHold a (opsGens ops)` — the mixed backend's
analogue of `packGen_holds_iff`, and the direction through which a gadget's forcing lemma would
compose across an interposed range check. It is NOT proved here. `packGen_holds_iff` covers the
pure-generic case, which is what `lowerHead_sound` uses; the mixed case is the first item of the
remainder and nothing in this tree currently claims it. -/

#assert_axioms packGen_holds_iff
#assert_axioms packGen_length
#assert_axioms lowerHead_sound
#assert_axioms lowerHead_sound_evalH
#assert_axioms lowerHead_rowCount
#assert_axioms lowerHead_all_modelled
#assert_axioms Gen1.mul_forces
#assert_axioms Gen1.acc_forces

end Dregg2.Circuit.Emit.KimchiLower
