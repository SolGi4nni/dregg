/-
# Dregg2.Circuit.Emit.AirNormalForm — ⚑ THE CORPUS INVARIANT: one canonical rendering of an
arithmetic body, stated once, DECIDED on the emitted object.

## The measured problem this answers

`docs/LOGIC-COMPILER-ASSESSMENT.md` §P2.5 measured that the hand-authored descriptor corpus
**contradicts itself about how to render a unit coefficient**: some descriptors write `x` bare,
some write `mul(const 1, x)`, and some carry BOTH shapes inside ONE descriptor. Byte-agreement
with a set that disagrees with itself is not a well-posed target for any canonical renderer, so
Phase 2 stopped at 8/76 byte-reachable and named the fix: **re-emit from the compiler; do not bend
`AirBuilder.headToExpr` toward one of the two shapes.** This module is the normal form that
re-emission emits INTO, plus the decidable verdict that says whether a descriptor is in it.

## ⚑ THE CANONICAL NORMAL FORM (the invariant, stated once)

An arithmetic body of a compiler-authored descriptor — a `.gate` body, a `.boundary` body, or a
`windowGate` body — is exactly what a polynomial HEAD lowers to:

    body  ::=  atom  |  add(body, atom)                  -- LEFT-nested spine, source order
    atom  ::=  mul(const c, prod)  |  const k            -- EVERY term carries its coefficient
    prod  ::=  leaf  |  mul(prod, leaf)                  -- LEFT-nested, leaf = var/loc/nxt

with four rules the shape does not by itself say:

1. ⚑ **A UNIT COEFFICIENT IS RENDERED `mul(const 1, x)`, NEVER BARE `x`.** This is the load-bearing
   choice and it is settled here for the whole corpus. Three reasons, in order of weight:
   * It is what `AirBuilder.headToExpr` — the ONE shared builder, and the thing 10 already-committed
     goldens ride on — produces. The alternative is bending the shared builder to imitate an
     inconsistent target, which §P2.5 measured as buying 8/76 → 21/76 while breaking those ten.
   * **Uniformity is what makes the invariant DECIDABLE by a two-line predicate.** With the bare
     form legal, `isTermAtom` has to accept a leaf, and then `add(var 5, var 6)` — a body with a
     dropped coefficient — is indistinguishable from a body that meant `1·x₅ + 1·x₆`. Every term
     carrying its coefficient is what makes "is this the compiler's output" a question a machine
     answers instead of a reader.
   * ⚑ **The Rust interpreter is INDIFFERENT, measured, both legs.** `LeanExpr::eval_expr`
     (`circuit/src/lean_descriptor_air.rs:127`) sends `Mul` to a field multiply and `Const(1)` to
     `F::one()`, so the evaluated polynomial is identical; and `LeanExpr::degree`
     (`:116`) is `Const => 0`, `Var => 1`, `Mul => sum`, so `mul(const 1, x)` has degree **1**,
     exactly as bare `x` does. `Ir2Air::Main::max_constraint_degree` returns `None`
     (`circuit/src/descriptor_ir2.rs:2829`) and lets p3's symbolic analysis infer the bound from
     that same algebra, so the FRI blowup and therefore the VK geometry do not move. The rendering
     costs bytes and nothing else.
2. **No like-term combination, no reassociation, no term reordering.** The head is exactly what
   `exprToHead` built from the source expression, in source order. A normalizer that collected
   `x + x` into `2·x` would make the emitted object stop being a transcription of what the author
   wrote, and the byte-diff of a source edit would stop being local.
3. **A zero head-constant is ELIDED; a zero-coefficient TERM is NOT.** `headExprs` drops the
   trailing `const 0` (it is the additive unit and carrying it is noise) but never drops a term.
   Dropping a `0·x` term would be the fail-open direction one level down: it removes a column
   reference the author wrote, and no byte-golden can see a body that says less.
4. **An empty body renders `const 0`**, never the empty string — a gate that constrains nothing is
   still a gate, and `foldExprs [] = .const 0` says so.

**What the invariant does NOT cover, deliberately: LOOKUP TUPLES.** A lookup tuple is not a
polynomial asserted to vanish — it is the tuple looked up, and its elements are the identity of the
queried row. Normalizing `var 3` to `mul(const 1, var 3)` there would change the wire bytes of a
chip query without changing anything about its meaning, and the chip tables are keyed on the bare
shape. `EffectLower.lowerLookupLeg` carries tuples through `CircuitEmit.emitExpr` (structure-
preserving) for exactly this reason.

## What is a THEOREM here and what is a `#guard`

* `headToExpr_isNormal` — **the gate rail is normal BY CONSTRUCTION**, for every head, proved. A
  descriptor whose gates come from `EffectLower.lowerConstraint` cannot be non-normal.
* `wHeadToWindow_isNormalW` — the same for the WINDOW rail, whose leaves are `loc`/`nxt`. This
  module supplies the window-side head (`WHead`) because `AirBuilder.Head` is over COLUMNS and
  cannot name a next-row leaf, so a window body had no canonical renderer at all before.
* `wHeadToWindow_eval` — and it is MEANING-PRESERVING, so the window rail's canonicalization is
  not a byte trick.
* `EffectVmDescriptor2.normalFormOk` — the DECIDABLE verdict over a whole emitted descriptor,
  `#guard`-pinned at BOTH poles here and once per re-emitted descriptor at its author. A verdict
  that cannot go red is decoration; §4 exhibits the red.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.EffectLowerCore
import Dregg2.Circuit.GateExpr

namespace Dregg2.Circuit.Emit.AirNormalForm

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmConstraint2 WindowExpr WindowConstraint)
open Dregg2.Circuit.Emit.AirBuilder
  (Head headToExpr headExprs foldExprs termToExpr varsProd evalH evalTerm headToExpr_eval)
open Dregg2.Circuit.GateExpr

set_option autoImplicit false

/-! ## §1+§2 — ⚑ THE SHAPE PREDICATE AND ITS BY-CONSTRUCTION PROOF, **DERIVED** (2026-08-06).

## What used to be here, and what it cost

§1 wrote out `isVarProd` / `isTermAtom` / `isNormal` over `EmittedExpr`; §3a wrote out
`isVarProdW` / `isTermAtomW` / `isNormalW` over `WindowExpr`. **Six definitions for one predicate**,
differing only in which leaf constructors they accept. §2 then proved the gate rail canonical by
construction in four lemmas, and §3a proved the *same statement* about the window rail in four more.

`Dregg2.Circuit.GateExpr` makes the leaf alphabet a PARAMETER (`GExpr L`, `GHead L`,
`gIsNormal`), so both rails are one predicate read through their view and normality-by-construction
is one proof for every alphabet. The invariant is UNCHANGED:

    body  ::=  atom  |  add(body, atom)                  -- LEFT-nested spine, source order
    atom  ::=  mul(const c, prod)  |  const k            -- EVERY term carries its coefficient
    prod  ::=  leaf  |  mul(prod, leaf)                  -- LEFT-nested, leaf = var/loc/nxt

and so is every emitted byte: `demoWCanonical_shape` below is still `rfl` on the same literal. -/

/-- A VAR PRODUCT: `varsProd cols` for a non-empty `cols` — a LEFT-nested `mul` chain of `var`
leaves. ⚑ Now `GateExpr.gIsVarProd` read through the `EmittedExpr` view. -/
def isVarProd (e : EmittedExpr) : Bool := gIsVarProd (ofEmitted e)

/-- A TERM ATOM: one summand of the spine — `mul(const c, prod)`, ⚑ INCLUDING `c = 1`, or a bare
constant. -/
def isTermAtom (e : EmittedExpr) : Bool := gIsTermAtom (ofEmitted e)

/-- ⚑ **THE NORMAL FORM**: a LEFT-nested `add` spine whose every summand is a term atom. -/
def isNormal (e : EmittedExpr) : Bool := gIsNormal (ofEmitted e)

/-- ⚑ **THE GATE RAIL IS CANONICAL BY CONSTRUCTION.** Every `AirBuilder.Head` lowers to a body in
the normal form — for EVERY head, not on a spot check. ⚑ The proof is now INHERITED: `AirBuilder`'s
renderer IS `gHeadToExpr` (`GateExpr.gHeadToExpr_emitted`), the fusion law moves the view outside,
and the alphabet-generic `gHeadToExpr_gIsNormal` closes it. The four supporting lemmas this section
used to carry are gone with it. -/
theorem headToExpr_isNormal (h : Head) : isNormal (headToExpr h) = true := by
  show gIsNormal (ofEmitted (headToExpr h)) = true
  rw [← Dregg2.Circuit.GateExpr.gHeadToExpr_emitted, ← render_gHeadToExpr, ofEmitted_render]
  exact gHeadToExpr_gIsNormal _

/-! ## §2b — ⚑ `gateBody`: the compiler's rendering of ONE source constraint, named.

A re-emitted descriptor's `_zero_iff` obligation used to be stated over a hand-written
`EmittedExpr` `def`. After re-emission the body is the COMPILER'S output, and the obligation must
be restated over THAT object — not deleted, not weakened. `gateBody` is the name that makes the
restatement a one-line rewrite: the theorem STATEMENT stays literally identical at each descriptor,
only the definition of the body moves from hand-written to compiled. -/

open Dregg2.Circuit (Constraint Assignment)
open Dregg2.Circuit.Emit.EffectLower (constraintHead lowerConstraint)

/-- **The gate body the compiler emits for a source constraint** — `headToExpr (lhs − rhs)`. -/
def gateBody (c : Constraint) : Dregg2.Exec.CircuitEmit.EmittedExpr :=
  headToExpr (constraintHead c)

/-- `lowerConstraint` IS a `.gate` at that body — so `gateBody` names a real emitted object rather
than a lookalike beside it. -/
theorem lowerConstraint_gateBody (c : Constraint) :
    lowerConstraint c = VmConstraint2.base (.gate (gateBody c)) := rfl

/-- ⚑ **THE COMPILED BODY MEANS THE SOURCE CONSTRAINT'S RESIDUAL.** This is the bridge every
re-emitted descriptor's `_zero_iff` rides on. -/
theorem gateBody_eval (c : Constraint) (a : Assignment) :
    (gateBody c).eval a = c.lhs.eval a - c.rhs.eval a := by
  simp only [gateBody, headToExpr_eval,
    Dregg2.Circuit.Emit.EffectLower.evalH_constraintHead]

/-- ⚑ **THE TOOTH, GENERICALLY.** The compiled gate body vanishes EXACTLY when the source equation
holds — both polarities, for every constraint, once instead of once per descriptor. -/
theorem gateBody_zero_iff (c : Constraint) (a : Assignment) :
    (gateBody c).eval a = 0 ↔ c.lhs.eval a = c.rhs.eval a := by
  rw [gateBody_eval]; omega

/-- …and it is canonical, by construction. -/
theorem gateBody_isNormal (c : Constraint) : isNormal (gateBody c) = true :=
  headToExpr_isNormal _

/-! ## §3 — ⚑ the WINDOW rail: **DERIVED**, not re-authored (2026-08-06).

## ⚑ WHAT THIS SECTION USED TO BE, AND WHY IT IS GONE

It carried `WLeaf`, `WLeaf.expr`, `WHead` + seven builder methods, `wVarsProd`, `wTermToExpr`,
`wHeadExprs`, `wFoldExprs`, `wHeadToWindow`, `isVarProdW`, `isTermAtomW`, `isNormalW`, `wEvalTerm`
and `wEvalH` — plus eleven supporting theorems — and every one of them was a line-for-line twin of
§1/§2's `Nat`-leaf version. The reason was stated right here, in this file:

> *"`AirBuilder.Head` is `Σ coeff · ∏ COLUMNS + const`: its leaves are current-row columns, so it
> has no name for the next-row leaf a `.transition` continuity gate reads. That is why window and
> boundary bodies had no canonical renderer at all … `WHead` closes that: same shape, same rendering
> rules, **leaves widened to `loc`/`nxt`**."*

**A leaf alphabet was a hard-coded `Nat`, and it cost ~26 declarations in this one file.** `WLeaf`
was already the right idea in the wrong place: it is the PARAMETER, not a local. It now lives in
`Dregg2.Circuit.GateExpr` where the parameter is, `WHead` IS `GHead WLeaf` — the same structure
`AirBuilder.Head` is — and every definition below is one line.

⚑ **NO EMITTED BYTE MOVES.** `demoWCanonical_shape` (§4a) is still `rfl` on the same literal, and
`wLinLoc` / `wLin` — the two shorthands the re-emitted descriptors actually call — are unchanged in
name, type and output. -/

/-- A window leaf: the current row's column, or the next row's. ⚑ Declared in `GateExpr`, where it
is the alphabet parameter rather than one file's local. -/
abbrev WLeaf := Dregg2.Circuit.GateExpr.WLeaf

/-- A two-row polynomial head: `Σ coeff · ∏ leaves + const`. ⚑ It IS `AirBuilder.Head`'s structure,
at a different alphabet — which is the whole content of the collapse. -/
abbrev WHead := Dregg2.Circuit.GateExpr.GHead WLeaf

/-- ⚑ **The window rail's canonical renderer** — `gHeadToExpr` at the `toWindow` view. -/
def wHeadToWindow (h : WHead) : WindowExpr := gHeadToExpr toWindow h

/-- ⚑ **THE NORMAL FORM on the window rail** — the SAME predicate as `isNormal`, read through the
window view instead of the one-row view. Not two invariants that agree; one invariant. -/
def isNormalW (e : WindowExpr) : Bool := gIsNormal (ofWindow e)

/-- A head's value under a row window. -/
def wEvalH (h : WHead) (env : VmRowEnv) : ℤ := gEvalH h (wEnv env)

/-- ⚑ **THE WINDOW RAIL IS CANONICAL BY CONSTRUCTION**, for every `WHead` — inherited from the
alphabet-generic proof, exactly as the gate rail is. -/
theorem wHeadToWindow_isNormalW (h : WHead) : isNormalW (wHeadToWindow h) = true := by
  show gIsNormal (ofWindow (gHeadToExpr toWindow h)) = true
  rw [← render_gHeadToExpr, ofWindow_render]
  exact gHeadToExpr_gIsNormal _

/-- ⚑ **THE WINDOW BRIDGE.** The canonical rendering evaluates to exactly the head's value, so
re-rendering a window body into normal form cannot change what the constraint says. ⚑ It and
`AirBuilder.headToExpr_eval` were the same theorem twice; this is the second one inherited from
`GateExpr.gHeadToExpr_eval`, along with the seven fold lemmas each rail used to carry. -/
theorem wHeadToWindow_eval (env : VmRowEnv) (h : WHead) :
    (wHeadToWindow h).eval env = wEvalH h env := by
  show (gHeadToExpr toWindow h).eval env = gEvalH h (wEnv env)
  rw [← render_gHeadToExpr, Dregg2.Circuit.GateExpr.eval_render_toWindow, gHeadToExpr_eval]

/-! ### §3c — the two authoring shorthands the re-emitted descriptors use. -/

/-- `Σ cᵢ·xᵢ + k` over CURRENT-row columns, canonically rendered. -/
def wLinLoc (terms : List (ℤ × Nat)) (k : ℤ) : WindowExpr :=
  wHeadToWindow ⟨terms.map (fun t => (t.1, [WLeaf.loc t.2])), k⟩

/-- `Σ cᵢ·(loc|nxt) + k`, canonically rendered — the continuity-gate shape. -/
def wLin (terms : List (ℤ × WLeaf)) (k : ℤ) : WindowExpr :=
  wHeadToWindow ⟨terms.map (fun t => (t.1, [t.2])), k⟩

theorem wLinLoc_isNormalW (terms : List (ℤ × Nat)) (k : ℤ) :
    isNormalW (wLinLoc terms k) = true := wHeadToWindow_isNormalW _

theorem wLin_isNormalW (terms : List (ℤ × WLeaf)) (k : ℤ) :
    isNormalW (wLin terms k) = true := wHeadToWindow_isNormalW _

/-! ## §3d — LOOKUP TUPLES: the source-side lift, so a chip tuple survives re-emission BYTE-EXACT.

A `LookupLeg.tuple` is a `List Circuit.Expr` (the framework's own gate AST) and the deployed chip
tuples are built by `DescriptorIR2`'s `chipLookupTuple*` helpers, which produce `EmittedExpr`. The
two grammars are the same four constructors, and `CircuitEmit.decodeExpr` is the structural
inverse — so a descriptor can feed its EXISTING tuple builder to the compiler with no
re-transcription, and `emitExpr_decodeExpr` proves the round trip lands on the same bytes.

⚠ This is a LIFT, not a normalization. Per the header, tuples are deliberately outside the normal
form: the chip bus is keyed on the bare tuple shape. -/

/-- Lift an emitted tuple back into the compiler's source grammar. -/
def liftTuple (t : List EmittedExpr) : List Dregg2.Circuit.Expr :=
  t.map Dregg2.Exec.CircuitEmit.decodeExpr

/-- The lift is EXACT: emitting the lifted tuple reproduces the original bytes. -/
theorem emitExpr_decodeExpr (e : EmittedExpr) :
    Dregg2.Exec.CircuitEmit.emitExpr (Dregg2.Exec.CircuitEmit.decodeExpr e) = e := by
  induction e with
  | var v => rfl
  | const c => rfl
  | add a b iha ihb =>
      simp [Dregg2.Exec.CircuitEmit.emitExpr, Dregg2.Exec.CircuitEmit.decodeExpr, iha, ihb]
  | mul a b iha ihb =>
      simp [Dregg2.Exec.CircuitEmit.emitExpr, Dregg2.Exec.CircuitEmit.decodeExpr, iha, ihb]

/-- ⚑ **THE TUPLE ROUND TRIP**, at the list level: a lookup leg built from an existing tuple
builder lowers to EXACTLY that tuple. This is what makes a chip-carrying descriptor's re-emission
move only its GATE bytes. -/
theorem liftTuple_emit (t : List EmittedExpr) :
    (liftTuple t).map Dregg2.Exec.CircuitEmit.emitExpr = t := by
  simp [liftTuple, List.map_map, Function.comp_def, emitExpr_decodeExpr]

/-! ## §4 — ⚑ THE DECIDABLE VERDICT over a whole emitted descriptor, and its RED pole. -/

/-- One constraint's verdict. `piBinding`/`transition` carry no polynomial; a `lookup`/`memOp`/
`mapOp`/`umemOp`/`proofBind` tuple is deliberately OUT of the invariant (see the header). -/
def constraintNormalOk : VmConstraint2 → Bool
  | .base (.gate b)         => isNormal b
  | .base (.boundary _ b)   => isNormal b
  | .windowGate w           => isNormalW w.body
  | _                       => true

/-- ⚑ **THE CORPUS INVARIANT, DECIDED.** Every arithmetic body of this descriptor is in the
canonical normal form. `#guard normalFormOk d == true` at a descriptor's author is a gate that goes
RED the moment a hand-shaped body re-enters it. -/
def normalFormOk (d : EffectVmDescriptor2) : Bool :=
  d.constraints.all constraintNormalOk

/-- How many of a descriptor's arithmetic bodies are NOT canonical — so a partial re-emission
reports a NUMBER rather than a bit. -/
def nonNormalCount (d : EffectVmDescriptor2) : Nat :=
  (d.constraints.filter (fun c => !constraintNormalOk c)).length

theorem normalFormOk_iff_zero (d : EffectVmDescriptor2) :
    normalFormOk d = true ↔ nonNormalCount d = 0 := by
  simp [normalFormOk, nonNormalCount, List.filter_eq_nil_iff, List.all_eq_true]

/-! ### §4a — both poles, executed. A verdict that cannot go red is decoration. -/

/-- The canonical rendering of `x₅ − x₄` (the continuity residual). -/
def demoCanonical : EmittedExpr :=
  headToExpr ⟨[(1, [5]), (-1, [4])], 0⟩

/-- ⚑ **THE RED POLE** — the SAME polynomial with the unit coefficient dropped. This is the shape
37 hand-authored descriptors use for one term and 58 use for another, byte-identical in meaning and
REFUSED here, which is the whole point of settling the question. -/
def demoBareUnit : EmittedExpr :=
  .add (.var 5) (.mul (.const (-1)) (.var 4))

#guard isNormal demoCanonical == true
#guard isNormal demoBareUnit == false

/-- …and they are genuinely the SAME POLYNOMIAL: the refusal is about RENDERING, never meaning.
Stated over EVERY assignment, so the invariant can never be read as a semantic restriction. -/
theorem demoBareUnit_same_polynomial (a : Dregg2.Circuit.Assignment) :
    demoCanonical.eval a = demoBareUnit.eval a := by
  simp only [demoCanonical, demoBareUnit, headToExpr_eval, EmittedExpr.eval, evalH]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, evalTerm,
    List.prod_cons, List.prod_nil]
  ring

/-- A RIGHT-nested spine — the other way a hand-written body drifts from the fold. -/
def demoRightNested : EmittedExpr :=
  .add (.mul (.const 1) (.var 5)) (.add (.mul (.const (-1)) (.var 4)) (.const 3))
#guard isNormal demoRightNested == false

-- Products, both poles: `mul(const 2, mul(var 1, var 2))` is canonical, `mul(var 1, const 2)` is not.
#guard isNormal (headToExpr ⟨[(2, [1, 2])], 0⟩) == true
#guard isNormal (.mul (.var 1) (.const 2)) == false
-- The head constant: elided at zero, written otherwise.
#guard headToExpr ⟨[(1, [0])], 0⟩ == EmittedExpr.mul (.const 1) (.var 0)
#guard headToExpr ⟨[(1, [0])], 5⟩
         == EmittedExpr.add (.mul (.const 1) (.var 0)) (.const 5)
-- An EMPTY head renders the literal `0`, and that is normal.
#guard headToExpr ⟨[], 0⟩ == EmittedExpr.const 0
#guard isNormal (headToExpr ⟨[], 0⟩) == true
-- A ZERO-COEFFICIENT term is NOT elided (dropping it would lose a column reference).
#guard headToExpr ⟨[(0, [3])], 0⟩ == EmittedExpr.mul (.const 0) (.var 3)

/-- The window rail's two poles, same shape. -/
def demoWCanonical : WindowExpr := wLin [(1, .nxt 0), (-1, .loc 2)] 0
def demoWBare : WindowExpr := .add (.nxt 0) (.mul (.const (-1)) (.loc 2))

#guard isNormalW demoWCanonical == true
#guard isNormalW demoWBare == false

/-- The canonical window rendering, pinned literally (`WindowExpr` has no `BEq`, so this is a
`theorem` by `rfl` rather than a `#guard` — same content, same refutability). -/
theorem demoWCanonical_shape :
    demoWCanonical
      = WindowExpr.add (.mul (.const 1) (.nxt 0)) (.mul (.const (-1)) (.loc 2)) := rfl

/-- A whole-descriptor verdict at both poles. -/
def demoDescOk : EffectVmDescriptor2 :=
  { name := "nf-demo-ok", traceWidth := 6, piCount := 1, tables := []
  , constraints := [ .base (.gate demoCanonical)
                   , .base (.boundary VmRow.last demoCanonical)
                   , .windowGate ⟨demoWCanonical, true⟩
                   , .base (.piBinding VmRow.first 4 0) ]
  , hashSites := [], ranges := [] }

def demoDescBad : EffectVmDescriptor2 :=
  { name := "nf-demo-bad", traceWidth := 6, piCount := 1, tables := []
  , constraints := [ .base (.gate demoBareUnit)
                   , .base (.boundary VmRow.last demoCanonical)
                   , .windowGate ⟨demoWBare, true⟩ ]
  , hashSites := [], ranges := [] }

#guard normalFormOk demoDescOk == true
#guard nonNormalCount demoDescOk == 0
#guard normalFormOk demoDescBad == false
#guard nonNormalCount demoDescBad == 2

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms headToExpr_isNormal
#assert_axioms wHeadToWindow_isNormalW
#assert_axioms wHeadToWindow_eval
#assert_axioms wLinLoc_isNormalW
#assert_axioms wLin_isNormalW
#assert_axioms emitExpr_decodeExpr
#assert_axioms liftTuple_emit
#assert_axioms normalFormOk_iff_zero
#assert_axioms demoBareUnit_same_polynomial
#assert_axioms demoWCanonical_shape

end Dregg2.Circuit.Emit.AirNormalForm
