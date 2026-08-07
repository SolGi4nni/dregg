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

/-! ## §4b — ⚑ THE PASS THAT REACHES THE END STATE, and it is ONE pass.

§2 and §3 say the two rails are canonical BY CONSTRUCTION — for bodies the compiler BUILT. §4 gives
a decidable verdict for bodies it did not. Between them sat the whole corpus: 23 of 113 descriptors
in the normal form, 18,290 of 41,264 arithmetic bodies outside it, and no way from one to the other
except re-authoring 90 descriptors by hand.

`GateExpr.gCanon` is the way: read a body back into a head (`gExprToHead`), render the head
canonically (`gHeadToExpr`). Both halves already existed; what did not exist was their composition
at an alphabet the WINDOW rail could use, which is why the window bodies had a builder and no
reader. This section is that composition at the two deployed rails, lifted to a whole descriptor.

## ⚑ "Converge the encodings, THEN canonicalize" is not two jobs — but the DELETION is separable

`gExprToHead` produces `Σ coeff · ∏ leaves + const`, and there is no intermediate object in which
an encoding is converged but a coefficient is still elided. That much is settled: one traversal.

⚠ **What does NOT follow, and what an earlier draft of this docblock claimed anyway, is that the
constant folding is inseparable from it.** `gCanon` folds because its vocabulary cannot represent
a `mul(const, const)` — not because folding needs a head. A 4-case structural fold outside the
head round-trip deletes all 5,075 dead subtrees (4,284 of them `mul(const -1, const 1)`) and buys
zero normality. See `GateExpr` §6c for both columns.

## ⚑ The price, measured over the checked-in corpus — ⚠ AND IT IS REVISION-SCOPED

At **git HEAD, 2026-08-06**: `1,963,410 → 2,142,886` AST nodes, **+179,476 (+9.14%)** over the 113
by-name descriptors, of which 90 change. `canonicalize_eval` / `canonicalizeW_eval` say that is
bytes and nothing else.

⚠ Quote that figure WITH its revision. The same measurement over the working tree two hours
earlier read `+188,154`, and over the working tree two hours later `+191,146` — not because the
pass changed but because sibling lanes re-emit descriptors continuously (27 by-name artifacts
differed from HEAD while this was being written). A corpus-wide total is a reading of a moving
object; take it at a fixed revision or do not take it.

⚑ **And the total hides the shape.** Of the 90 that change, **14 SHRINK** (−13,998 nodes, led by
`descent-custody-census-fixed8-v1` at −1,804 and the eight `pasta-rcb-sg-slice` variants at −1,222
each) and 76 grow (+193,474). None of the 14 is one of the three sub-programs whose semantic
fingerprints are Lean-pinned VK lane vectors, so a shrinkers-only subset is a real frontier point
and it avoids the cascade entirely. -/

open Dregg2.Circuit.GateExpr (gCanon gCanonAt gCanonAt_render gCanon_gIsNormal gCanon_eval
  gExprToHead gHeadToExpr evalG vEnv wEnv render_ofEmitted render_ofWindow ofEmitted_render
  ofWindow_render eval_render_toEmitted eval_render_toWindow toEmitted toWindow ofEmitted ofWindow)

/-- ⚑ **CANONICALIZE A ONE-ROW BODY** — `gCanon` at the `EmittedExpr` view. -/
def canonicalize (e : EmittedExpr) : EmittedExpr := gCanonAt toEmitted ofEmitted e

/-- ⚑ **CANONICALIZE A WINDOW BODY** — the same pass at the `loc`/`nxt` alphabet. This is the one
the pre-`GateExpr` shape could not express at all. -/
def canonicalizeW (w : WindowExpr) : WindowExpr := gCanonAt toWindow ofWindow w

/-- ⚑ **THE END STATE ON THE GATE RAIL, FOR EVERY BODY** — not a count over 113 files. -/
theorem canonicalize_isNormal (e : EmittedExpr) : isNormal (canonicalize e) = true := by
  show gIsNormal (ofEmitted (gCanonAt toEmitted ofEmitted e)) = true
  rw [gCanonAt_render, ofEmitted_render]
  exact gCanon_gIsNormal _

/-- ⚑ **AND IT SAYS THE SAME THING.** Every assignment, so the flag day can never be read as a
semantic change. -/
theorem canonicalize_eval (a : Dregg2.Circuit.Assignment) (e : EmittedExpr) :
    (canonicalize e).eval a = e.eval a := by
  show (gCanonAt toEmitted ofEmitted e).eval a = _
  rw [gCanonAt_render, eval_render_toEmitted, gCanon_eval]
  conv_rhs => rw [← render_ofEmitted e]
  rw [eval_render_toEmitted]

/-- The window rail's end state. -/
theorem canonicalizeW_isNormalW (w : WindowExpr) : isNormalW (canonicalizeW w) = true := by
  show gIsNormal (ofWindow (gCanonAt toWindow ofWindow w)) = true
  rw [gCanonAt_render, ofWindow_render]
  exact gCanon_gIsNormal _

/-- …and the window rail's bridge. -/
theorem canonicalizeW_eval (env : VmRowEnv) (w : WindowExpr) :
    (canonicalizeW w).eval env = w.eval env := by
  show (gCanonAt toWindow ofWindow w).eval env = _
  rw [gCanonAt_render, eval_render_toWindow, gCanon_eval]
  conv_rhs => rw [← render_ofWindow w]
  rw [eval_render_toWindow]

/-- ⚑ **ONE CONSTRAINT.** Only the three arithmetic bodies move; a lookup/memOp/mapOp/umemOp/
proofBind tuple is carried through UNTOUCHED, because the chip bus is keyed on the bare tuple shape
and normalizing there would move a chip query's wire bytes without changing its meaning (header). -/
def canonicalizeC : VmConstraint2 → VmConstraint2
  | .base (.gate b)         => .base (.gate (canonicalize b))
  | .base (.boundary r b)   => .base (.boundary r (canonicalize b))
  | .windowGate w           => .windowGate ⟨canonicalizeW w.body, w.onTransition⟩
  | c                       => c

/-- ⚑ **THE PASS, ON A WHOLE DESCRIPTOR.** -/
def canonicalizeDesc (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with constraints := d.constraints.map canonicalizeC }

theorem canonicalizeC_normalOk (c : VmConstraint2) :
    constraintNormalOk (canonicalizeC c) = true := by
  match c with
  | .base (.gate b)       => exact canonicalize_isNormal b
  | .base (.boundary r b) => exact canonicalize_isNormal b
  | .windowGate w         => exact canonicalizeW_isNormalW w.body
  | .base (.piBinding ..) => rfl
  | .base (.transition ..) => rfl
  | .lookup _    => rfl
  | .memOp _     => rfl
  | .mapOp _     => rfl
  | .umemOp _    => rfl
  | .proofBind _ => rfl
  | .chalGate _  => rfl

/-- ⚑⚑ **THE END STATE, AS A THEOREM.** Every descriptor is in the canonical normal form after ONE
pass. The corpus reading `23/113` is what this replaces, and it replaces it with a fact about EVERY
descriptor rather than a number about these ones. -/
theorem canonicalizeDesc_normalFormOk (d : EffectVmDescriptor2) :
    normalFormOk (canonicalizeDesc d) = true := by
  simp only [normalFormOk, canonicalizeDesc, List.all_eq_true, List.mem_map]
  rintro c ⟨c₀, _, rfl⟩
  exact canonicalizeC_normalOk c₀

theorem canonicalizeDesc_nonNormalCount (d : EffectVmDescriptor2) :
    nonNormalCount (canonicalizeDesc d) = 0 :=
  (normalFormOk_iff_zero _).mp (canonicalizeDesc_normalFormOk d)

/-- The pass touches only the arithmetic bodies: name, width, PI count, tables, hash sites and
ranges are carried through, and so is the constraint COUNT. A re-emission that dropped a constraint
would be invisible to `normalFormOk` — this is the conjunct that sees it. -/
theorem canonicalizeDesc_shape (d : EffectVmDescriptor2) :
    (canonicalizeDesc d).name = d.name
      ∧ (canonicalizeDesc d).traceWidth = d.traceWidth
      ∧ (canonicalizeDesc d).piCount = d.piCount
      ∧ (canonicalizeDesc d).tables = d.tables
      ∧ (canonicalizeDesc d).constraints.length = d.constraints.length :=
  ⟨rfl, rfl, rfl, rfl, List.length_map _⟩

/-! ### §4c — ⚑ the RED pole of the PASS. A canonicalizer that cannot be seen to act is decoration. -/

/-- The pass carries the non-canonical demo body to the canonical one — the exact byte change the
corpus re-emission makes, 18,290 times. -/
theorem canonicalize_demoBareUnit : canonicalize demoBareUnit = demoCanonical := by decide

/-- ⚑ And the constant fold, on the shape the corpus ships 4,284 times: `mul(const -1, const 1)` —
what a subtraction of one lowers to — is not deleted by a step, it is UNREPRESENTABLE in the head
the pass goes through, so it comes back as the literal. -/
theorem canonicalize_folds_dead_product :
    canonicalize (.add (.var 3) (.mul (.const (-1)) (.const 1)))
      = .add (.mul (.const 1) (.var 3)) (.const (-1)) := by decide

/-- …and the pass is a FIXED POINT on an already-canonical body, so a second emit run moves zero
bytes. (`gExprToHead_coeff_ne_zero` is why this can hold at all: with a zero-coefficient term in the
rendering, the second pass's `gMulHead` guard would drop it and the bytes would move again.) -/
theorem canonicalize_demoCanonical : canonicalize demoCanonical = demoCanonical := by decide

-- ⚠ `WindowExpr` has no `DecidableEq`, so this is `rfl` rather than `decide` — same content,
-- same refutability, exactly as `demoWCanonical_shape` above.
theorem canonicalizeW_demoWBare : canonicalizeW demoWBare = demoWCanonical := rfl

theorem canonicalizeDesc_demoDescBad_ok :
    normalFormOk (canonicalizeDesc demoDescBad) = true := by decide

/-! ## §4d — ⚑ THE FOLD AT THE TWO DEPLOYED RAILS, AND THE PASS THAT SHIPS.

§4 carries `canonicalize`, which is `gCanon` at these rails and is NOT applied by any emitter — it
is the byte-reachability option, priced at 90 rotations and three VK-lane cascades, kept proved on
disk for whenever that is worth paying. **This section is the other axis** (`GateExpr` §6c′).

## ⚠ IT IS ALSO NOT APPLIED YET, AND THE REASON IS MEASURED RATHER THAN CAUTIOUS

The pass was landed to be wired into `EmitByName.main`. The consumer enumeration that had to clear
first did not. Every one of the 26 emitter modules was scanned for a byte FACT — not just a byte
LITERAL — and **4 of the 26 carry one this pass breaks**:

| descriptor | the guard | why it breaks |
|---|---|---|
| `derivation` | `DerivationEmit.lean:401` `#guard emitVmJson2 derivationDesc == "…"` | full bytes |
| `field-delta-result-range` | `FieldDeltaRangeEmit.lean:75` `… == FIELD_DELTA_RANGE_GOLDEN` | full bytes |
| `dregg-shielded-spend-pinned-root-v1` | `ShieldedSpendDescriptor.lean:597` `… == SHIELDED_SPEND_PINNED_ROOT_GOLDEN` | full bytes |
| `faithful-note-spend-v2` | `FaithfulNoteSpendDescriptorPlan.lean:575` `…Json.length == 97665` | 97,665 → 96,665 |

⚠ **The other 22 are clean, and that is measured rather than assumed.** Their guards are structural
counts (`constraints.length`, `publicPins.length`, `tables.length`, `ranges.length`) which
`foldConstDesc_shape` preserves; `startsWith` guards over the JSON HEADER, which the fold never
touches; positive `.contains` of structural strings (`"window_gate"`, `"stage0_schedule"`); and —
the one that needed real checking — **8 NEGATIVE `.contains` guards forbidding a specific field
constant** (`1347571253`, `1430520837`, `68719403010`, `1346720313`, `1246122553`). A constant fold
MANUFACTURES literals that were not in the bytes before, so it could in principle satisfy one of
those. It does not: all 8 were folded and re-checked, and the forbidden constant is absent before
and after.

⚠ `shielded-whole-note-swap-substrate-v1` was in an earlier draft of this list and is NOT pinned —
its guard is a header `startsWith` that survives the fold. The list is 4.

Folding in `EmitByName.main` leaves those `#guard`s pinning the UNFOLDED bytes while the artifact
carries the FOLDED ones. Three of the four are welded to the artifact by
`scripts/check-emit-gate-weld.py` (the Rust `GOLDEN_JSON`s are `include_str!` of the artifact, so
they follow the emit; the Lean literal does not) and would go RED there. ⚠ **The `length` guard is
welded to nothing** — it would stay green while describing a file that no longer exists, which is
the worse failure of the two and the reason this stops rather than ships.

⚠ **None of this is a VK cascade** — `proof_bind` appears in exactly 6 constraints across 4
descriptors corpus-wide (`dregg-mina-lightclient-{link,verify}-v1`, `mina-wrap-conjunction{,
-unthreaded}`), none of them among the 26, and the four hand-entered lane vectors
(`CHAINLINK_VK_LANES`, `LINK_VK_LANES`, `CONJ_VK_LANES`, `ABSORB_VK_LANES`) all pin mina/pasta
descriptors this pass does not touch. The blocker is five escaped JSON literals, which is ordinary
work; it is named here rather than blown through so the re-emit and the re-pin land together.

⚑ **What it buys, measured at git HEAD `db577c93dc71d40dbab5326aec5876885dba3404`** over the 122
checked-in `by-name` descriptors: **1,958,542 → 1,948,364 AST nodes (−10,178)**, **26 of 122**
descriptors moving, **all 26 SHRINKING**, and **5,075 → 0** `mul(const, const)` subtrees.

⚠ **What it does NOT buy: normality.** Measured over the same 122 at the same revision, **22,976 →
22,976** normal bodies and **23 / 122 → 23 / 122** normal descriptors — *exactly zero change*. This
pass is not a phase of `canonicalize` and does not move the corpus toward it. `normalFormOk` is
untouched by it and no theorem here says otherwise.

⚠ **And it is not the whole corpus.** The 122 `by-name` artifacts are what `EmitByName` authors.
Measured at the same revision, **1,225 further dead subtrees** ship in **5 top-level** descriptors
(`dregg-cert-f-market4-ir2` 569, `dregg-cert-f-ir2` 455, `dregg-cert-qp-portfolio6-s3-ir2` 168,
`dregg-effectvm-capreshape-v1` 17, `dregg-effectvm-attenuateA-v1-genuine-nonamp` 16), authored by
emitters with their own `main`s. Two of those five are DEPLOYED effect-VM descriptors, so folding
them is a wider re-key than this pass's consumer enumeration cleared; it is named here as measured
remaining work rather than quietly rounded away. `table-airs` ships zero. -/

open Dregg2.Circuit.GateExpr (gFold gFold_eval gFoldAt) in
/-- ⚑ **FOLD A ONE-ROW BODY** — `gFold` at the `EmittedExpr` view. -/
def foldConst (e : EmittedExpr) : EmittedExpr := gFoldAt toEmitted ofEmitted e

open Dregg2.Circuit.GateExpr (gFold gFoldAt) in
/-- ⚑ **FOLD A WINDOW BODY** — the same pass at the `loc`/`nxt` alphabet. -/
def foldConstW (w : WindowExpr) : WindowExpr := gFoldAt toWindow ofWindow w

open Dregg2.Circuit.GateExpr (gFold gFold_eval gFoldAt) in
/-- ⚑ **THE FOLD SAYS THE SAME THING**, under every assignment — the licence for the re-emission
on the gate rail. -/
theorem foldConst_eval (a : Dregg2.Circuit.Assignment) (e : EmittedExpr) :
    (foldConst e).eval a = e.eval a := by
  show (Dregg2.Circuit.GateExpr.render toEmitted (gFold (ofEmitted e))).eval a = _
  rw [eval_render_toEmitted, gFold_eval]
  conv_rhs => rw [← render_ofEmitted e]
  rw [eval_render_toEmitted]

open Dregg2.Circuit.GateExpr (gFold gFold_eval gFoldAt) in
/-- …and the window rail's bridge. -/
theorem foldConstW_eval (env : VmRowEnv) (w : WindowExpr) :
    (foldConstW w).eval env = w.eval env := by
  show (Dregg2.Circuit.GateExpr.render toWindow (gFold (ofWindow w))).eval env = _
  rw [eval_render_toWindow, gFold_eval]
  conv_rhs => rw [← render_ofWindow w]
  rw [eval_render_toWindow]

/-- ⚑ **ONE CONSTRAINT.** Exactly `canonicalizeC`'s reach, and for exactly its reason: only the
three arithmetic bodies move, and a lookup/memOp/mapOp/umemOp/proofBind tuple is carried through
UNTOUCHED because the chip bus is keyed on the bare tuple shape. -/
def foldConstC : VmConstraint2 → VmConstraint2
  | .base (.gate b)         => .base (.gate (foldConst b))
  | .base (.boundary r b)   => .base (.boundary r (foldConst b))
  | .windowGate w           => .windowGate ⟨foldConstW w.body, w.onTransition⟩
  | c                       => c

/-- ⚑ **THE PASS, ON A WHOLE DESCRIPTOR** — what `EmitByName.main` applies. -/
def foldConstDesc (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with constraints := d.constraints.map foldConstC }

/-- The pass touches only the arithmetic bodies: name, width, PI count, tables and the constraint
COUNT are carried through. A re-emission that dropped a constraint would be invisible to a node
count — this is the conjunct that sees it. -/
theorem foldConstDesc_shape (d : EffectVmDescriptor2) :
    (foldConstDesc d).name = d.name
      ∧ (foldConstDesc d).traceWidth = d.traceWidth
      ∧ (foldConstDesc d).piCount = d.piCount
      ∧ (foldConstDesc d).tables = d.tables
      ∧ (foldConstDesc d).constraints.length = d.constraints.length :=
  ⟨rfl, rfl, rfl, rfl, List.length_map _⟩

/-! ### §4d′ — ⚑ the RED pole of the FOLD. -/

/-- The pass fires on the shape the corpus ships 4,284 times. -/
theorem foldConst_kills_dead_product :
    foldConst (.add (.var 3) (.mul (.const (-1)) (.const 1)))
      = .add (.var 3) (.const (-1)) := by decide

/-- ⚠ **AND IT IS NOT `canonicalize`.** On the same input the two passes disagree — the fold leaves
the bare `var 3` bare, the canonicalizer gives it its unit coefficient. Naming them as phases of one
another is what this theorem refuses. -/
theorem foldConst_ne_canonicalize :
    foldConst (.add (.var 3) (.mul (.const (-1)) (.const 1)))
      ≠ canonicalize (.add (.var 3) (.mul (.const (-1)) (.const 1))) := by decide

/-- ⚠ **AND IT BUYS NO NORMALITY** — the folded body is still not in the canonical normal form.
This is the corpus reading `23/122 → 23/122` as a fact about a body rather than a count. -/
theorem foldConst_not_isNormal :
    isNormal (foldConst (.add (.var 3) (.mul (.const (-1)) (.const 1)))) = false := by decide

/-- …and a second emit run moves zero bytes, on the descriptor pass, not just on `gFold`. -/
theorem foldConst_idem (e : EmittedExpr) : foldConst (foldConst e) = foldConst e := by
  show Dregg2.Circuit.GateExpr.render toEmitted
        (Dregg2.Circuit.GateExpr.gFold (ofEmitted (Dregg2.Circuit.GateExpr.render toEmitted
          (Dregg2.Circuit.GateExpr.gFold (ofEmitted e)))))
      = Dregg2.Circuit.GateExpr.render toEmitted (Dregg2.Circuit.GateExpr.gFold (ofEmitted e))
  rw [ofEmitted_render, Dregg2.Circuit.GateExpr.gFold_idem]

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
#assert_axioms canonicalize_isNormal
#assert_axioms canonicalize_eval
#assert_axioms canonicalizeW_isNormalW
#assert_axioms canonicalizeW_eval
#assert_axioms canonicalizeC_normalOk
#assert_axioms canonicalizeDesc_normalFormOk
#assert_axioms canonicalizeDesc_nonNormalCount
#assert_axioms canonicalizeDesc_shape
#assert_axioms canonicalize_demoBareUnit
#assert_axioms canonicalize_folds_dead_product
#assert_axioms canonicalize_demoCanonical
#assert_axioms canonicalizeW_demoWBare
#assert_axioms foldConst_eval
#assert_axioms foldConstW_eval
#assert_axioms foldConstDesc_shape
#assert_axioms foldConst_kills_dead_product
#assert_axioms foldConst_ne_canonicalize
#assert_axioms foldConst_not_isNormal
#assert_axioms foldConst_idem

end Dregg2.Circuit.Emit.AirNormalForm
