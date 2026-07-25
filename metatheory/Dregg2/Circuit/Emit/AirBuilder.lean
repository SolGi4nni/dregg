/-
# Dregg2.Circuit.Emit.AirBuilder — the GAME-FREE polynomial-head builder vocabulary for
Lean-authored AIRs.

## What this file IS

The Rust tree grew two copies of one "co-build harness": `dregg-automatafl/src/builder.rs` and
`param-compose/src/builder.rs` (whose own header says it is "a sibling of `dregg-automatafl`'s
builder … duplicated rather than shared"). Both hand-write AIR constraints in Rust, which is exactly
what the Lean-authored-AIR law forbids. The automatafl one is gone; its Lean replacement
(`AutomataflStepEmit` §3) re-authored the `Head` vocabulary INSIDE a game module, so the second
consumer (`ParamComposeEmit`) could not reuse it without importing a game.

This module is that vocabulary, hoisted and game-free:

  * `Head` — `Σ (coeff, cols) + constant`, the Rust `builder.rs::Head` shape;
  * `headToExpr` — the lowering to the IR-v2 gate `EmittedExpr`;
  * `evalH` + **`headToExpr_eval`** — the SEMANTIC bridge (`(headToExpr h).eval a = evalH h a`) every
    refinement proof rewrites with, proven once here instead of once per namespace (the
    `AutomataflStepCoord` header records the cost of NOT having it once: `AutomataflResolveEmit.Head`
    and `AutomataflStepEmit.Head` are distinct types, so every step-side `rw [headToExpr_eval]`
    failed);
  * the gadget families a hand-written Rust builder carries — boolean pins, the conditional-nonzero
    gate, bit-decomposition range checks, and the `forced_ge0` signed comparison.

## Named debt (not laundered)

`AutomataflStepEmit`/`AutomataflResolveEmit` still carry their own `Head` copies. Migrating them onto
this module is a mechanical, separately-verifiable change and is NOT done here (those files carry the
whole automatafl refinement surface; a rename sweep across them belongs in its own lane). What this
module DOES close is the forward direction: a new Lean-authored AIR no longer has a reason to
re-author the vocabulary a third time.

## Axiom hygiene

Definitions + genuinely-proven evaluation lemmas; `#assert_axioms`-clean. NEW file; imports
read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.AirBuilder

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2)

set_option autoImplicit false

/-! ## §1 — `Head`: the linear/product polynomial head. -/

/-- A polynomial head: `Σ (coeff, cols) + constant`. An empty `cols` is a constant term (the
Rust `Head { terms : Vec<(i128, Vec<usize>)>, constant : i128 }`). -/
structure Head where
  terms : List (ℤ × List Nat)
  const : ℤ

namespace Head

/-- The identically-zero head. -/
def zero : Head := ⟨[], 0⟩
/-- A pure constant head. -/
def c (k : ℤ) : Head := ⟨[], k⟩
/-- `coeff · col`. -/
def lin (coeff : ℤ) (col : Nat) : Head := ⟨[(coeff, [col])], 0⟩
/-- Append a linear term. -/
def addLin (h : Head) (coeff : ℤ) (col : Nat) : Head := ⟨h.terms ++ [(coeff, [col])], h.const⟩
/-- Append a product term `coeff · ∏ cols`. -/
def addProd (h : Head) (coeff : ℤ) (cols : List Nat) : Head := ⟨h.terms ++ [(coeff, cols)], h.const⟩
/-- Shift the constant. -/
def addConst (h : Head) (k : ℤ) : Head := ⟨h.terms, h.const + k⟩
/-- Scale the whole head. -/
def scale (h : Head) (k : ℤ) : Head := ⟨h.terms.map (fun t => (t.1 * k, t.2)), h.const * k⟩
/-- Sum two heads. -/
def append (h o : Head) : Head := ⟨h.terms ++ o.terms, h.const + o.const⟩
/-- Multiply the whole head by `k · col` (the `forced_ge0` `2·ib·d` shape). The head's own constant
becomes a linear term in `col`. -/
def mulByCol (h : Head) (k : ℤ) (col : Nat) : Head :=
  ⟨h.terms.map (fun t => (t.1 * k, col :: t.2)) ++ [(k * h.const, [col])], 0⟩

end Head

instance : Inhabited Head := ⟨Head.zero⟩

/-! ## §2 — Lowering a `Head` to the IR-v2 gate expression. -/

/-- The product `∏ vars` (empty product `= 1`), left-associated. -/
def varsProd : List Nat → EmittedExpr
  | []         => .const 1
  | co :: rest => rest.foldl (fun acc v => .mul acc (.var v)) (.var co)

/-- One term `coeff · ∏ cols` as an `EmittedExpr`. -/
def termToExpr : ℤ × List Nat → EmittedExpr
  | (coeff, [])   => .const coeff
  | (coeff, cols) => .mul (.const coeff) (varsProd cols)

/-- The component expression list a head lowers to (the constant term is elided when zero). -/
def headExprs (h : Head) : List EmittedExpr :=
  h.terms.map termToExpr ++ (if h.const = 0 then [] else [.const h.const])

/-- Left-folded sum of an expression list (`[]` ↦ the literal `0`). -/
def foldExprs : List EmittedExpr → EmittedExpr
  | []        => .const 0
  | e :: rest => rest.foldl (fun acc x => .add acc x) e

/-- Lower a `Head` to the gate `EmittedExpr`. -/
def headToExpr (h : Head) : EmittedExpr := foldExprs (headExprs h)

/-! ## §3 — The SEMANTIC bridge: `headToExpr` evaluates to the head's value. -/

/-- One term's value under an assignment: `coeff · ∏ a col`. -/
def evalTerm (a : Assignment) (t : ℤ × List Nat) : ℤ := t.1 * (t.2.map a).prod

/-- A head's value under an assignment. -/
def evalH (h : Head) (a : Assignment) : ℤ := (h.terms.map (evalTerm a)).sum + h.const

theorem varsProd_foldl (a : Assignment) (rest : List Nat) (e : EmittedExpr) :
    (rest.foldl (fun acc v => EmittedExpr.mul acc (.var v)) e).eval a
      = e.eval a * (rest.map a).prod := by
  induction rest generalizing e with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih, EmittedExpr.eval]
    ring

theorem varsProd_eval (a : Assignment) (cols : List Nat) :
    (varsProd cols).eval a = (cols.map a).prod := by
  cases cols with
  | nil => simp [varsProd, EmittedExpr.eval]
  | cons x xs =>
    simp only [varsProd, varsProd_foldl, List.map_cons, List.prod_cons, EmittedExpr.eval]

theorem termToExpr_eval (a : Assignment) (t : ℤ × List Nat) :
    (termToExpr t).eval a = evalTerm a t := by
  obtain ⟨k, cols⟩ := t
  cases cols with
  | nil => simp [termToExpr, evalTerm, EmittedExpr.eval]
  | cons x xs => simp [termToExpr, evalTerm, EmittedExpr.eval, varsProd_eval]

theorem foldExprs_foldl (a : Assignment) (rest : List EmittedExpr) (e : EmittedExpr) :
    (rest.foldl (fun acc x => EmittedExpr.add acc x) e).eval a
      = e.eval a + (rest.map (·.eval a)).sum := by
  induction rest generalizing e with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, EmittedExpr.eval]
    ring

theorem foldExprs_eval (a : Assignment) (es : List EmittedExpr) :
    (foldExprs es).eval a = (es.map (·.eval a)).sum := by
  cases es with
  | nil => simp [foldExprs, EmittedExpr.eval]
  | cons e rest =>
    simp only [foldExprs, foldExprs_foldl, List.map_cons, List.sum_cons]

/-- **THE BRIDGE.** The lowered gate expression evaluates to exactly the head's value — so a
satisfied gate IS the head equation, and a refinement proof never unfolds the lowering. -/
theorem headToExpr_eval (a : Assignment) (h : Head) : (headToExpr h).eval a = evalH h a := by
  simp only [headToExpr, foldExprs_eval, headExprs, List.map_append, List.sum_append,
    List.map_map, Function.comp_def, evalH]
  by_cases hc : h.const = 0
  · simp [hc, termToExpr_eval]
  · simp [hc, termToExpr_eval, EmittedExpr.eval]

/-! ### Incremental `evalH` laws (the rewrite surface a refinement proof lives on). -/

@[simp] theorem evalH_zero (a : Assignment) : evalH Head.zero a = 0 := by simp [evalH, Head.zero]

@[simp] theorem evalH_c (a : Assignment) (k : ℤ) : evalH (Head.c k) a = k := by
  simp [evalH, Head.c]

@[simp] theorem evalH_lin (a : Assignment) (k : ℤ) (co : Nat) :
    evalH (Head.lin k co) a = k * a co := by simp [evalH, Head.lin, evalTerm]

@[simp] theorem evalH_addLin (a : Assignment) (h : Head) (k : ℤ) (co : Nat) :
    evalH (h.addLin k co) a = evalH h a + k * a co := by
  simp only [evalH, Head.addLin, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, evalTerm, List.prod_cons, List.prod_nil]
  ring

@[simp] theorem evalH_addProd (a : Assignment) (h : Head) (k : ℤ) (cols : List Nat) :
    evalH (h.addProd k cols) a = evalH h a + k * (cols.map a).prod := by
  simp only [evalH, Head.addProd, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, evalTerm]
  ring

@[simp] theorem evalH_addConst (a : Assignment) (h : Head) (k : ℤ) :
    evalH (h.addConst k) a = evalH h a + k := by
  simp only [evalH, Head.addConst]; ring

@[simp] theorem evalH_append (a : Assignment) (h o : Head) :
    evalH (h.append o) a = evalH h a + evalH o a := by
  simp only [evalH, Head.append, List.map_append, List.sum_append]; ring

theorem evalTerm_scale (a : Assignment) (k : ℤ) (t : ℤ × List Nat) :
    evalTerm a (t.1 * k, t.2) = evalTerm a t * k := by
  simp only [evalTerm]; ring

@[simp] theorem evalH_scale (a : Assignment) (h : Head) (k : ℤ) :
    evalH (h.scale k) a = evalH h a * k := by
  simp only [evalH, Head.scale, List.map_map, Function.comp_def]
  have key : ∀ ts : List (ℤ × List Nat),
      (ts.map (fun t => evalTerm a (t.1 * k, t.2))).sum = (ts.map (evalTerm a)).sum * k := by
    intro ts
    induction ts with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, evalTerm_scale]; ring
  rw [key]; ring

theorem evalTerm_mulCol (a : Assignment) (k : ℤ) (col : Nat) (t : ℤ × List Nat) :
    evalTerm a (t.1 * k, col :: t.2) = k * a col * evalTerm a t := by
  simp only [evalTerm, List.map_cons, List.prod_cons]; ring

@[simp] theorem evalH_mulByCol (a : Assignment) (h : Head) (k : ℤ) (col : Nat) :
    evalH (h.mulByCol k col) a = k * a col * evalH h a := by
  simp only [evalH, Head.mulByCol, List.map_append, List.sum_append, List.map_map,
    Function.comp_def, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have key : ∀ ts : List (ℤ × List Nat),
      (ts.map (fun t => evalTerm a (t.1 * k, col :: t.2))).sum
        = k * a col * (ts.map (evalTerm a)).sum := by
    intro ts
    induction ts with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, evalTerm_mulCol]; ring
  rw [key]
  simp only [evalTerm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

/-- Folding a list of linear terms onto a head sums their values. -/
theorem evalH_foldl_addLin (a : Assignment) (h0 : Head) (k : ℤ) (cols : List Nat) :
    evalH (cols.foldl (fun h co => h.addLin k co) h0) a
      = evalH h0 a + k * (cols.map a).sum := by
  induction cols generalizing h0 with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, evalH_addLin, List.map_cons, List.sum_cons]
    ring

/-! ### Indexed fold laws — the shape an emitter's `List.range` loops actually produce.

An emitted sum is `(List.range n).foldl (fun h i => h.addLin k (col i)) h0`: the column is a FUNCTION
of the loop index, not the element. These four laws turn such a fold into a plain `List.sum`, which
is what a refinement proof composes. -/

/-- A fold of index-addressed linear terms with a FIXED coefficient. -/
theorem evalH_foldl_addLinF {α : Type} (a : Assignment) (h0 : Head) (k : ℤ) (xs : List α)
    (f : α → Nat) :
    evalH (xs.foldl (fun h x => h.addLin k (f x)) h0) a
      = evalH h0 a + k * (xs.map (fun x => a (f x))).sum := by
  induction xs generalizing h0 with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, evalH_addLin, List.map_cons, List.sum_cons]
    ring

/-- A fold of index-addressed linear terms with an INDEX-DEPENDENT coefficient (the `Σ q·selp_q`
param-index pin). -/
theorem evalH_foldl_addLinG {α : Type} (a : Assignment) (h0 : Head) (kf : α → ℤ) (xs : List α)
    (f : α → Nat) :
    evalH (xs.foldl (fun h x => h.addLin (kf x) (f x)) h0) a
      = evalH h0 a + (xs.map (fun x => kf x * a (f x))).sum := by
  induction xs generalizing h0 with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, evalH_addLin, List.map_cons, List.sum_cons]
    ring

/-- A fold of index-addressed PRODUCT terms with a fixed coefficient. -/
theorem evalH_foldl_addProdF {α : Type} (a : Assignment) (h0 : Head) (k : ℤ) (xs : List α)
    (g : α → List Nat) :
    evalH (xs.foldl (fun h x => h.addProd k (g x)) h0) a
      = evalH h0 a + k * (xs.map (fun x => ((g x).map a).prod)).sum := by
  induction xs generalizing h0 with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, evalH_addProd, List.map_cons, List.sum_cons]
    ring

/-- The DOUBLE fold — the degree-3 `Σ_j Σ_q sel_j·selp_q·param[j][q]` read. -/
theorem evalH_foldl_nested {α β : Type} (a : Assignment) (h0 : Head) (xs : List α) (ys : List β)
    (g : α → β → List Nat) :
    evalH (xs.foldl (fun h x => ys.foldl (fun h2 y => h2.addProd 1 (g x y)) h) h0) a
      = evalH h0 a + (xs.map (fun x => (ys.map (fun y => ((g x y).map a).prod)).sum)).sum := by
  induction xs generalizing h0 with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, evalH_foldl_addProdF, List.map_cons, List.sum_cons]
    ring

/-! ## §4 — The gadget families (what a hand-written Rust builder emits). -/

/-- A per-row gate from a raw expression. -/
def cg (e : EmittedExpr) : VmConstraint2 := .base (.gate e)

/-- A per-row gate from a `Head` (`head = 0`). -/
def cgH (h : Head) : VmConstraint2 := cg (headToExpr h)

/-- `x·(x−1)` — the boolean pin (`Builder::assert_binary`). -/
def gBin (co : Nat) : EmittedExpr := .mul (.var co) (.add (.var co) (.const (-1)))

/-- The boolean-pin constraint. -/
def binGate (co : Nat) : VmConstraint2 := cg (gBin co)

/-- `x·(x−1) = 0` iff `x ∈ {0,1}` — the pin genuinely BITES. -/
theorem gBin_eval_zero_iff (a : Assignment) (co : Nat) :
    (gBin co).eval a = 0 ↔ (a co = 0 ∨ a co = 1) := by
  simp only [gBin, EmittedExpr.eval, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by omega)

/-- **`condNonzero sel val inv`** — the `ConditionalNonzero` gate as a polynomial:
`sel · (1 − val · inv) = 0`. When `sel ≠ 0` this FORCES `val · inv = 1`, hence `val ≠ 0`; when
`sel = 0` it is free. Degree 3. -/
def condNonzeroHead (sel val inv : Nat) : Head :=
  (Head.lin 1 sel).addProd (-1) [sel, val, inv]

/-- The conditional-nonzero constraint. -/
def condNonzero (sel val inv : Nat) : VmConstraint2 := cgH (condNonzeroHead sel val inv)

/-- **The conditional-nonzero tooth BITES**: over ℤ, a satisfied gate with a nonzero selector
forces the value nonzero. -/
theorem condNonzero_forces (a : Assignment) (sel val inv : Nat)
    (hg : evalH (condNonzeroHead sel val inv) a = 0) (hsel : a sel ≠ 0) : a val ≠ 0 := by
  simp only [condNonzeroHead, evalH_addProd, evalH_lin, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil] at hg
  intro hv
  rw [hv] at hg
  simp at hg
  exact hsel hg

/-- The bit columns `[base, base+1, …, base+len−1]`. -/
def bitsFrom (base len : Nat) : List Nat := (List.range len).map (base + ·)

/-- **The range gadget** (`Builder::range_nonneg`): `rbits` boolean columns plus the recomposition
`term − Σ 2^t·b_t = 0`. A term outside `[0, 2^rbits)` has no satisfying bit assignment. -/
def rangeNonneg (term : Head) (bits : List Nat) : List VmConstraint2 :=
  bits.map binGate
  ++ [cgH ((bits.zipIdx.foldl (fun h (p : Nat × Nat) => h.addLin (-(2 ^ p.2 : ℤ)) p.1) term))]

/-- The `forced_ge0` comparison term `2·ge·d + ge − d − 1`, whose non-negativity over a bounded
range holds iff `ge = [d ≥ 0]` (`Builder::forced_ge0`). -/
def forcedGe0Term (ge : Nat) (d : Head) : Head :=
  (((d.mulByCol 2 ge).append (Head.lin 1 ge)).append (d.scale (-1))).addConst (-1)

/-- **The forced-comparison gadget**: a boolean `ge` column plus the range check on
`2·ge·d + ge − d − 1`. -/
def forcedGe0 (ge : Nat) (d : Head) (bits : List Nat) : List VmConstraint2 :=
  binGate ge :: rangeNonneg (forcedGe0Term ge d) bits

/-- The comparison term's value: `ge = 1` reads `d`, `ge = 0` reads `−d−1`. This is the whole
content of `forced_ge0` — exactly one of the two branches can land in `[0, 2^rbits)` when the
compared range is small relative to the field, which is why the caller must bound it. -/
theorem forcedGe0Term_eval (a : Assignment) (ge : Nat) (d : Head) :
    evalH (forcedGe0Term ge d) a = 2 * a ge * evalH d a + a ge - evalH d a - 1 := by
  simp only [forcedGe0Term, evalH_addConst, evalH_append, evalH_mulByCol, evalH_lin, evalH_scale]
  ring

/-- `ge = 1` ⇒ the comparison term IS `d`. -/
theorem forcedGe0Term_one (a : Assignment) (ge : Nat) (d : Head) (h : a ge = 1) :
    evalH (forcedGe0Term ge d) a = evalH d a := by
  rw [forcedGe0Term_eval, h]; ring

/-- `ge = 0` ⇒ the comparison term IS `−d−1`. -/
theorem forcedGe0Term_zero (a : Assignment) (ge : Nat) (d : Head) (h : a ge = 0) :
    evalH (forcedGe0Term ge d) a = -evalH d a - 1 := by
  rw [forcedGe0Term_eval, h]; ring

/-- A first-row PI binding (`col = pi[idx]`). -/
def pinPi (col idx : Nat) : VmConstraint2 := .base (.piBinding VmRow.first col idx)

#assert_axioms headToExpr_eval
#assert_axioms evalH_mulByCol
#assert_axioms gBin_eval_zero_iff
#assert_axioms condNonzero_forces
#assert_axioms forcedGe0Term_eval

end Dregg2.Circuit.Emit.AirBuilder
