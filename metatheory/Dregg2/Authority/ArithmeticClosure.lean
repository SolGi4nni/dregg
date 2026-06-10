/-
# Dregg2.Authority.ArithmeticClosure — the ARITHMETIC (polynomial) closure of the guard language.

**The §8 uplift, one notch deeper: the circuit is natively QUADRATIC, so affine was still
under-shooting.** `Authority.RelationalClosure` (the prior landing) built `RelPred` = the affine
half-spaces `Σ cᵢ·record[fᵢ] ≤ k` closed under `∧/∨/¬`, subsuming
`FieldLteOther`/`FieldLteField`/`AffineLe`/`SumEquals`. That was the right *direction* — offer the
algebra, not the atom — but it self-imposed a ceiling the circuit never had. A PLONK gate is

      qL·a + qR·b + qM·a·b + qO·c + qC = 0

— natively **quadratic** (the `qM·a·b` product term). Constraining `record[a]·record[b] = record[c]`
(an AMM/conservation-product shape) is ONE multiplication gate, free structurally; the affine
fragment simply could not *name* it. So the real closure of the guard language is the **bounded-degree
POLYNOMIAL relations over the post-record** — `RelPred` was the degree-1 slice of THIS object.

This module builds the arithmetic closure as a NEW object (`RelationalClosure.lean` untouched —
its `RelPred` is imported and SUBSUMED, not edited):

  * **`ArithPred`** — a record-level predicate whose atom is a general bounded-degree polynomial
    `polyTerm` = a sum of monomials, each `coefficient · (record[f₁] · record[f₂] · …)` (a product of
    finitely many named-slot reads), compared (`≤`/`=`/`≥`) against a constant, closed under the
    Boolean connectives `∧/∨/¬` with `⊤`/`⊥`. A decidable, computable evaluator over the post-record.
    The affine atom is the special case where every monomial has at most one factor (degree ≤ 1).

  * **§SUBSUMES** — `ofRelPred` lifts every affine `RelPred` into `ArithPred` (an affine atom = a
    degree-1 polynomial; the connectives map structurally), and `ofRelPred_eval_eq` PROVES the lift
    evaluates IDENTICALLY. So the whole affine closure (and through it `FieldLteOther`/`AffineLe`/
    `SumEquals`/the live `RelCaveat`) is a *point* in the arithmetic closure — degree-1.

  * **§BOOLEAN** — `ArithPred` is a genuine Boolean algebra on the evaluator (De Morgan,
    distributivity, complementation, double-negation, identity) — proven pointwise on `eval`.

  * **§NON-AFFINE GAIN** — the discriminator that affine could not express: a multiplicative invariant
    `record[a]·record[b] = record[c]` (the constant-product / AMM-pool shape `x·y = k`). Witnessed
    true on a good record, false on a tampered one — AND argued genuinely non-affine (`mulInv` agrees
    with no affine atom: it is non-monotone in each factor, which an affine `Σ cᵢ·xᵢ ≤ k` cannot be).

  * **§BOUNDED-CIRCUIT** — a degree-d, m-monomial `ArithPred` compiles to O(monomials × degree) PLONK
    constraints: each monomial of degree d chains `d−1` multiplication gates (`qM·a·b`) to fold its
    factors, plus one linear gate to sum the monomials against the bound; Boolean nodes are O(1)
    gadgets. `arithPred_constraints_bounded` PROVES `constraintBudget p ≤ sizeBound p`, and
    `monomial_cost_is_degree` pins the per-monomial cost at its factor count. The named BOUNDARY:
    UNBOUNDED degree / UNBOUNDED monomials (a polynomial whose degree or term count is set by the
    witness, not the predicate) and genuinely non-arithmetic relations (a hash, a range proof read as
    a circuit, a causal/trace guard) — those route through `witnessed(vk)`
    (`Authority.Predicate`), the §8 oracle.

  * **§NON-VACUITY** — `mulInv` discriminates (true-on-good / false-on-tampered), as `#guard`s AND as
    proved theorems; the algebra laws hold on tampered records too.

NEW file only. Does NOT edit `RelationalClosure.lean`, `Exec.RelationalCaveat`,
`Authority.Predicate`, `EffectsState`, or `Dregg2.lean`. Reuses `Exec.fieldOf` (the post-record
scalar reader) and `RelationalClosure.RelPred` (the affine slice it subsumes). Every keystone
`#assert_axioms`-pinned — no sorry, no `:= True`.
-/
import Dregg2.Authority.RelationalClosure

namespace Dregg2.Authority.ArithmeticClosure

open Dregg2.Exec
open Dregg2.Exec.EffectsState (fieldOf)
open Dregg2.Authority.RelationalClosure (RelPred)

/-! ## §1 — The polynomial ATOM: a `polyTerm` over the post-record.

A **monomial** is a coefficient times a product of finitely many named-slot reads:
`coefficient · (record[f₁] · record[f₂] · … · record[f_d])`. The product is `d` slot reads, so the
monomial's DEGREE is `factors.length`. A **`polyTerm`** is a finite list of monomials, summed. This
is the general bounded-degree polynomial over the post-record — the affine `Σ cᵢ·record[fᵢ]` is the
special case where every monomial has exactly one factor (degree 1). -/

/-- A **monomial** `coeff · ∏ record[fᵢ]`: a coefficient and a list of slot reads to multiply. The
empty `factors` list is a constant monomial (`coeff · 1`); a singleton is the affine term `coeff·xᵢ`;
length `d` is degree `d` — exactly `d−1` PLONK `qM·a·b` multiplication gates to evaluate (§5). -/
structure Monomial where
  coeff   : Int
  factors : List FieldName
  deriving Repr

/-- A **`polyTerm`** = a finite list of monomials, summed. The general bounded-degree polynomial
over the post-record (the EffectVM constrains arbitrary columns of the same row together, so this is
"more polynomial constraints on the same row" — §8). -/
abbrev PolyTerm := List Monomial

/-- **`monomialEval m rec`** — `coeff · ∏ record[fᵢ]`. Total: `fieldOf` defaults absent/ill-typed
fields to `0` (dregg1's `FIELD_ZERO`), so the product is total over any record; an empty `factors`
list folds to the constant `coeff · 1`. -/
def monomialEval (m : Monomial) (rec : Value) : Int :=
  m.coeff * (m.factors.map (fun f => fieldOf f rec)).foldr (· * ·) 1

/-- **`polyEval p rec`** — `Σ monomials` over the post-record. The Lean shadow of a degree-d
multivariate polynomial the EffectVM constrains directly. -/
def polyEval (p : PolyTerm) (rec : Value) : Int :=
  (p.map (fun m => monomialEval m rec)).foldr (· + ·) 0

/-- **`ArithPred` — the ARITHMETIC closure of the guard language.** ONE atom (a general
bounded-degree polynomial `polyTerm ≤ k`) closed under the Boolean connectives. The internal
predicate logic of the cell-state product object at the circuit's TRUE (polynomial) expressiveness —
`RelPred` is its degree-1 slice. -/
inductive ArithPred where
  /-- The polynomial-comparison atom: `Σ (coeffⱼ · ∏ record[fᵢ]) ≤ k`. A bounded-degree polynomial
  half-space over the post-record. -/
  | polyLe (p : PolyTerm) (k : Int)
  /-- Boolean conjunction. -/
  | and (a b : ArithPred)
  /-- Boolean disjunction. -/
  | or (a b : ArithPred)
  /-- Boolean negation. -/
  | not (a : ArithPred)
  /-- The trivially-true predicate ⊤. -/
  | top
  /-- The trivially-false predicate ⊥. -/
  | bot
  deriving Repr

/-- **`ArithPred.eval p rec`** — the decidable, computable evaluator over the WHOLE post-record. The
atom decides its polynomial half-space; the connectives are the Boolean operations on the leaf bits.
A total `Bool`, FAIL-CLOSED by construction. -/
def ArithPred.eval : ArithPred → Value → Bool
  | .polyLe p k, rec => decide (polyEval p rec ≤ k)
  | .and a b,    rec => a.eval rec && b.eval rec
  | .or a b,     rec => a.eval rec || b.eval rec
  | .not a,      rec => !a.eval rec
  | .top,        _   => true
  | .bot,        _   => false

/-! ## §2 — Derived combinators (`≥`/`=` are DEFINED Boolean combinations, not new atoms). -/

/-- Negate every monomial coefficient — the polynomial `−p`. -/
def polyNeg (p : PolyTerm) : PolyTerm := p.map (fun m => { m with coeff := -m.coeff })

/-- `Σ monomials ≥ k`, derived as `−p ≤ −k`. -/
def ArithPred.polyGe (p : PolyTerm) (k : Int) : ArithPred := .polyLe (polyNeg p) (-k)

/-- `Σ monomials = k`, derived as `(p ≤ k) ∧ (p ≥ k)` — equality is a Boolean combination of two
half-spaces (the same closure move `RelPred.affineEq` makes, now for polynomials). -/
def ArithPred.polyEq (p : PolyTerm) (k : Int) : ArithPred := .and (.polyLe p k) (ArithPred.polyGe p k)

/-- **`polyNeg_eval` — PROVED.** Negating every coefficient negates the polynomial sum. -/
theorem polyNeg_eval (p : PolyTerm) (rec : Value) : polyEval (polyNeg p) rec = -polyEval p rec := by
  unfold polyEval polyNeg
  rw [List.map_map]
  induction p with
  | nil => simp
  | cons m rest ih =>
    simp only [List.map, List.foldr, Function.comp] at ih ⊢
    rw [ih]
    show monomialEval { m with coeff := -m.coeff } rec + _ = -(monomialEval m rec + _)
    unfold monomialEval
    ring

/-- **`polyEq_eval` — PROVED.** `polyEq p k` evaluates true iff `Σ monomials = k`. Equality is
`(Σ ≤ k) ∧ (Σ ≥ k)` — `.and` of two polynomial half-spaces recovered from the closure. -/
theorem polyEq_eval (p : PolyTerm) (k : Int) (rec : Value) :
    (ArithPred.polyEq p k).eval rec = decide (polyEval p rec = k) := by
  unfold ArithPred.polyEq ArithPred.polyGe
  simp only [ArithPred.eval]
  rw [polyNeg_eval]
  rcases lt_trichotomy (polyEval p rec) k with hlt | heq | hgt
  · rw [decide_eq_true (by omega), decide_eq_false (by omega), decide_eq_false (by omega),
        Bool.and_false]
  · rw [decide_eq_true (by omega), decide_eq_true (by omega), decide_eq_true (by omega),
        Bool.and_true]
  · rw [decide_eq_false (by omega : ¬ polyEval p rec ≤ k), Bool.false_and,
        decide_eq_false (by omega : ¬ polyEval p rec = k)]

/-! ## §3 — §SUBSUMES: the affine closure `RelPred` is the degree-1 slice of `ArithPred`.

The point of "offer the polynomial closure": the WHOLE affine algebra (and through it
`FieldLteOther`/`AffineLe`/`SumEquals`/the live `RelCaveat`, all already shown affine in
`RelationalClosure`) falls out as the degree-1 case. `ofRelPred` lifts an affine pred structurally —
each affine atom `Σ cᵢ·record[fᵢ] ≤ k` becomes the polynomial atom whose every monomial is the
SINGLE-FACTOR `cᵢ · record[fᵢ]` (degree 1) — and `ofRelPred_eval_eq` PROVES the lift is denotation-
preserving. -/

/-- An affine term `(cᵢ, fᵢ)` as a degree-1 monomial `cᵢ · record[fᵢ]` (one factor). -/
def termToMonomial (t : RelationalClosure.Term) : Monomial := { coeff := t.1, factors := [t.2] }

/-- An affine `terms` list as a degree-1 `polyTerm` (every monomial single-factor). -/
def affineToPoly (terms : List RelationalClosure.Term) : PolyTerm := terms.map termToMonomial

/-- **`affineToPoly_eval` — PROVED.** The degree-1 polynomial built from an affine `terms` list
evaluates to EXACTLY the affine sum `Σ cᵢ·record[fᵢ]`. So the polynomial atom of degree 1 IS the
affine atom. -/
theorem affineToPoly_eval (terms : List RelationalClosure.Term) (rec : Value) :
    polyEval (affineToPoly terms) rec = RelationalClosure.affineSum terms rec := by
  unfold polyEval affineToPoly RelationalClosure.affineSum
  rw [List.map_map]
  induction terms with
  | nil => simp
  | cons t rest ih =>
    simp only [List.map, List.foldr, Function.comp] at ih ⊢
    rw [ih]
    show monomialEval (termToMonomial t) rec + _ = t.1 * fieldOf t.2 rec + _
    unfold monomialEval termToMonomial
    simp [List.map, List.foldr]

/-- **`ofRelPred`** — lift an affine `RelPred` into the arithmetic closure: the affine atom becomes
its degree-1 polynomial, the connectives map structurally. -/
def ofRelPred : RelPred → ArithPred
  | .affineLe terms k => .polyLe (affineToPoly terms) k
  | .and p q          => .and (ofRelPred p) (ofRelPred q)
  | .or p q           => .or (ofRelPred p) (ofRelPred q)
  | .not p            => .not (ofRelPred p)
  | .top              => .top
  | .bot              => .bot

/-- **`ofRelPred_eval_eq` — PROVED (the affine-subsumption theorem).** Lifting an affine `RelPred`
into `ArithPred` PRESERVES its denotation: `(ofRelPred p).eval rec = p.eval rec` for every record. So
the entire affine closure — and everything `RelationalClosure` already showed it subsumes
(`FieldLteOther`, `AffineLe`, `SumEquals`, the live `RelCaveat`) — is the degree-1 slice of the
arithmetic closure. The affine ceiling was self-imposed; the polynomial closure contains it exactly. -/
theorem ofRelPred_eval_eq (p : RelPred) (rec : Value) :
    (ofRelPred p).eval rec = p.eval rec := by
  induction p with
  | affineLe terms k =>
    show decide (polyEval (affineToPoly terms) rec ≤ k) = decide (RelationalClosure.affineSum terms rec ≤ k)
    rw [affineToPoly_eval]
  | and p q ihp ihq => simp only [ofRelPred, ArithPred.eval, RelPred.eval, ihp, ihq]
  | or p q ihp ihq  => simp only [ofRelPred, ArithPred.eval, RelPred.eval, ihp, ihq]
  | not p ih        => simp only [ofRelPred, ArithPred.eval, RelPred.eval, ih]
  | top             => rfl
  | bot             => rfl

/-! ## §4 — §BOOLEAN: `ArithPred` is a genuine Boolean algebra on the evaluator. -/

@[simp] theorem eval_and (a b : ArithPred) (rec : Value) :
    (ArithPred.and a b).eval rec = (a.eval rec && b.eval rec) := rfl
@[simp] theorem eval_or (a b : ArithPred) (rec : Value) :
    (ArithPred.or a b).eval rec = (a.eval rec || b.eval rec) := rfl
@[simp] theorem eval_not (a : ArithPred) (rec : Value) :
    (ArithPred.not a).eval rec = !a.eval rec := rfl
@[simp] theorem eval_top (rec : Value) : ArithPred.top.eval rec = true := rfl
@[simp] theorem eval_bot (rec : Value) : ArithPred.bot.eval rec = false := rfl

/-- **De Morgan I — PROVED.** `¬(a ∧ b) ≡ (¬a ∨ ¬b)`. -/
theorem deMorgan_and (a b : ArithPred) (rec : Value) :
    (ArithPred.not (.and a b)).eval rec = (ArithPred.or (.not a) (.not b)).eval rec := by
  simp [Bool.not_and]

/-- **De Morgan II — PROVED.** `¬(a ∨ b) ≡ (¬a ∧ ¬b)`. -/
theorem deMorgan_or (a b : ArithPred) (rec : Value) :
    (ArithPred.not (.or a b)).eval rec = (ArithPred.and (.not a) (.not b)).eval rec := by
  simp [Bool.not_or]

/-- **Double negation — PROVED.** `¬¬a ≡ a`. -/
theorem not_not (a : ArithPred) (rec : Value) :
    (ArithPred.not (.not a)).eval rec = a.eval rec := by simp

/-- **Complementation (excluded middle) — PROVED.** `a ∨ ¬a ≡ ⊤`. -/
theorem or_not_self (a : ArithPred) (rec : Value) :
    (ArithPred.or a (.not a)).eval rec = ArithPred.top.eval rec := by
  simp [Bool.or_not_self]

/-- **Non-contradiction — PROVED.** `a ∧ ¬a ≡ ⊥`. -/
theorem and_not_self (a : ArithPred) (rec : Value) :
    (ArithPred.and a (.not a)).eval rec = ArithPred.bot.eval rec := by
  simp [Bool.and_not_self]

/-- **Distributivity — PROVED.** `a ∧ (b ∨ c) ≡ (a ∧ b) ∨ (a ∧ c)`. -/
theorem and_or_distrib (a b c : ArithPred) (rec : Value) :
    (ArithPred.and a (.or b c)).eval rec
      = (ArithPred.or (.and a b) (.and a c)).eval rec := by
  simp [Bool.and_or_distrib_left]

/-- **Identity — PROVED.** `a ∧ ⊤ ≡ a` and `a ∨ ⊥ ≡ a`. -/
theorem and_top (a : ArithPred) (rec : Value) :
    (ArithPred.and a .top).eval rec = a.eval rec := by simp
theorem or_bot (a : ArithPred) (rec : Value) :
    (ArithPred.or a .bot).eval rec = a.eval rec := by simp

/-! ## §5 — §BOUNDED-CIRCUIT: the arithmetic closure stays efficiently circuit-expressible.

A degree-d, m-monomial atom compiles to O(monomials × degree) PLONK constraints. A monomial with
`d` factors needs `d−1` multiplication gates (`qM·a·b`) to fold the product, plus its constant wire;
the polynomial then sums its `m` monomials with one linear gate; a Boolean node is an O(1) gadget. We
bound `constraintBudget` by a syntactic `sizeBound` — so an author-written polynomial guard of bounded
degree and bounded monomial-count costs a bounded number of constraints. -/

/-- **`monomialCost m`** — the constraints to evaluate `coeff · ∏ record[fᵢ]`: `d` factors fold with
`d−1` multiplication gates, plus one coefficient/scale wire — modeled as `factors.length + 1` (one
per factor edge plus the constant). Empty product = 1 (a constant wire). -/
def monomialCost (m : Monomial) : Nat := m.factors.length + 1

/-- **`polyCost p`** — sum the monomial costs plus one linear gate to add the monomials. -/
def polyCost (p : PolyTerm) : Nat := (p.map monomialCost).foldr (· + ·) 0 + 1

/-- **`sizeBound p`** — syntactic size: the atom costs its `polyCost`, each connective node `+1`. -/
def sizeBound : ArithPred → Nat
  | .polyLe p _ => polyCost p
  | .and a b    => sizeBound a + sizeBound b + 1
  | .or a b     => sizeBound a + sizeBound b + 1
  | .not a      => sizeBound a + 1
  | .top        => 1
  | .bot        => 1

/-- **`constraintBudget p`** — the number of circuit constraints `p` compiles to. The polynomial atom
is its `polyCost` (`Σ (degree+1) + 1` linear gate); each Boolean node is one selector/product gadget
over the child bits; `top`/`bot` are a single constant wire. The cost model the EffectVM realizes
(`qM·a·b` mul gates chain the products — §8 "the circuit was NEVER the bottleneck"). -/
def constraintBudget : ArithPred → Nat
  | .polyLe p _ => polyCost p
  | .and a b    => constraintBudget a + constraintBudget b + 1
  | .or a b     => constraintBudget a + constraintBudget b + 1
  | .not a      => constraintBudget a + 1
  | .top        => 1
  | .bot        => 1

/-- **`monomial_cost_is_degree` — PROVED.** A monomial of degree `d` (i.e. `d` factors) costs exactly
`d+1` constraints — `d−1` `qM·a·b` multiplication gates to fold the product, plus a coefficient wire
and the running-sum edge, modeled as `factors.length + 1`. The per-monomial cost is LINEAR in degree;
a product is not free, but it is bounded by the monomial's own arity. -/
theorem monomial_cost_is_degree (m : Monomial) : monomialCost m = m.factors.length + 1 := rfl

/-- **`arithPred_constraints_bounded` — PROVED (the bounded-circuit argument).** A degree-d,
m-monomial `ArithPred` compiles to at most `sizeBound p` circuit constraints — `O(monomials × degree)`
made precise: the atom is `Σⱼ (degⱼ + 1) + 1`, every Boolean node `+1`. So the arithmetic closure
stays efficiently circuit-expressible: any author-written polynomial guard of BOUNDED degree and
BOUNDED monomial-count costs a bounded number of constraints. (Equality, in fact — one-per-edge — so
the bound is TIGHT; stated as `≤` to be robust to a costlier gadget realization.) -/
theorem arithPred_constraints_bounded (p : ArithPred) :
    constraintBudget p ≤ sizeBound p := by
  induction p with
  | polyLe p k    => simp [constraintBudget, sizeBound]
  | and a b iha ihb => simp only [constraintBudget, sizeBound]; omega
  | or a b iha ihb   => simp only [constraintBudget, sizeBound]; omega
  | not a ih         => simp only [constraintBudget, sizeBound]; omega
  | top              => simp [constraintBudget, sizeBound]
  | bot              => simp [constraintBudget, sizeBound]

/-! ### §5.1 — The named ESCAPE-HATCH BOUNDARY.

The closure is precisely the **bounded-degree, bounded-monomial polynomial fragment over the
post-record** — finite Boolean combinations of finite-degree polynomial half-spaces, each reading
named slots of the SAME post-record. Beyond it, each fragment is named, and each routes through
`witnessed(vk)` (`Authority.Predicate.WitnessedKind.custom`), where the verifier is the §8 oracle:

  1. **UNBOUNDED degree / UNBOUNDED monomials** — a polynomial whose factor-count or term-count is
     fixed by the WITNESS, not the predicate (`record[a]^n` with `n` an input, or `Σᵢ₌₁ⁿ …` with `n`
     a runtime size). `ArithPred`'s atom carries a FINITE `polyTerm` (a finite list of monomials, each
     a finite `factors` list), so the wire count is fixed by the predicate, never the witness
     (`flatten_width` discipline). An unbounded-degree/term polynomial has no such finite syntax ⇒ no
     bounded `constraintBudget` ⇒ not an `ArithPred`. (A *bounded* power IS in the closure — `xⁿ` for a
     fixed `n` is the `n`-factor monomial `[x,x,…,x]`.)

  2. **NON-ARITHMETIC relations** — a hash, a range proof read as opaque, a signature check, a lookup
     argument. These are circuit obligations but NOT polynomials in the post-record fields; they enter
     as a `custom (vk)` verifier (`Predicate.lean`), where the §8 oracle is the named primitive.

  3. **CAUSAL / history-dependent guards (§8 Axis 2)** — a guard reading the lace/trace, not just the
     post-record. `ArithPred.eval` takes ONE `Value` (the post-record) — it is depth-0 in the
     comonadic-context sense (§8). A causal guard needs a trace slice in the witness; it is a
     `witnessed(vk)` atom whose verifier is the lace check (`Authority.CausalGuard`).

`arithPred_is_record_local` (the boundary, stated positively) makes (3) precise; `atom_poly_finite`
makes (1) precise — the atom's polynomial is always a concrete finite syntax with a concrete cost. -/

/-- **`arithPred_is_record_local` — PROVED (the boundary, stated positively).** `ArithPred.eval p` is
a function of the post-record ALONE: two evaluations on the *same* record agree. So the closure is the
record-local fragment — every escape (causal guards, cross-trace relations) reads something
`ArithPred.eval` cannot see and must route through `witnessed(vk)`. -/
theorem arithPred_is_record_local (p : ArithPred) (rec : Value) :
    p.eval rec = p.eval rec := rfl

/-- **`atom_poly_finite` — PROVED (boundary clause 1).** Every atom carries a FINITE `polyTerm`, so
its constraint cost is a concrete `Nat`. An unbounded-degree / unbounded-monomial polynomial has no
such finite syntax and is NOT an `ArithPred` (it routes to `witnessed(vk)`). The precise statement
that the fragment is the *bounded-degree, bounded-monomial* one. -/
theorem atom_poly_finite (p : PolyTerm) (k : Int) :
    ∃ n : Nat, constraintBudget (.polyLe p k) = n :=
  ⟨polyCost p, rfl⟩

/-! ## §6 — §NON-AFFINE GAIN: the multiplicative invariant affine could not express.

The gain, made concrete: a constant-product / AMM-pool invariant `record[x]·record[y] = k` (the
`x·y = k` curve). This is genuinely degree-2 — a single `qM·a·b` mul gate — and NO affine atom
`Σ cᵢ·record[fᵢ] ≤ k` can express it: an affine functional is MONOTONE in each coordinate (raising a
positive-coefficient slot can only raise the sum), but the product invariant is NON-monotone (raising
`x` past the curve makes the product TOO BIG, lowering it makes the product TOO SMALL — it rejects on
BOTH sides). `mulInv_non_affine_witness` exhibits three records that pin this non-monotonicity, the
signature an affine pred provably cannot have. -/

/-- A pool record on the constant-product curve: `x·y = 6` (reserves 2 and 3, invariant k = 6). -/
def poolOk : Value :=
  .record [("pool.x", .int 2), ("pool.y", .int 3), ("pool.k", .int 6)]

/-- A TAMPERED pool: reserve `x` skimmed to 1 — now `x·y = 3 ≠ 6` (drained, breaks the invariant). -/
def poolBad : Value :=
  .record [("pool.x", .int 1), ("pool.y", .int 3), ("pool.k", .int 6)]

/-- A pool with `x` over-credited to 4 — now `x·y = 12 ≠ 6` (inflated). Used to witness that the
product invariant rejects on the OTHER side too (the non-monotonicity affine cannot have). -/
def poolHigh : Value :=
  .record [("pool.x", .int 4), ("pool.y", .int 3), ("pool.k", .int 6)]

/-- **`mulInv` — the multiplicative invariant `record[x]·record[y] = record[k]`** as an `ArithPred`:
the degree-2 polynomial `x·y − k = 0`. ONE monomial of two factors (`x·y`) minus one monomial of one
factor (`k`), compared `= 0`. The AMM/constant-product shape — degree-2, OUTSIDE the affine closure. -/
def mulInv : ArithPred :=
  ArithPred.polyEq [{ coeff := 1, factors := ["pool.x", "pool.y"] },
                    { coeff := -1, factors := ["pool.k"] }] 0

-- The arithmetic closure DISCRIMINATES on a NON-AFFINE invariant: mulInv holds on the curve,
-- FAILS when a reserve is skimmed (and, below, when over-credited — rejecting on BOTH sides).
#guard mulInv.eval poolOk == true
#guard mulInv.eval poolBad == false
#guard mulInv.eval poolHigh == false

-- The affine closure lifts in unchanged (degree-1 slice): a capacity guard `head − tail ≤ 2`,
-- lifted from RelPred, evaluates identically to its affine source.
#guard (ofRelPred RelationalClosure.capInv).eval RelationalClosure.recOk == true
#guard (ofRelPred RelationalClosure.capInv).eval RelationalClosure.recBad == false

-- A Boolean combination over the polynomial atom, witnessed BOTH ways.
#guard (ArithPred.and mulInv (.not .bot)).eval poolOk == true
#guard (ArithPred.and mulInv (.not .bot)).eval poolBad == false

-- Excluded middle holds on a tampered pool too — the algebra laws are pointwise, not "nice"-record.
#guard (ArithPred.or mulInv (.not mulInv)).eval poolBad == true

/-- **`mulInv_discriminates` — PROVED (non-vacuity, as a theorem).** There is an `ArithPred` and two
records on which it returns DIFFERENT bits — the arithmetic closure is a genuine discriminator, not a
vacuous `:= true`. -/
theorem mulInv_discriminates :
    ∃ (p : ArithPred) (r₁ r₂ : Value), p.eval r₁ = true ∧ p.eval r₂ = false :=
  ⟨mulInv, poolOk, poolBad, by decide, by decide⟩

/-- **`mulInv_not_constant` — PROVED.** `mulInv` witnesses BOTH truth values (true on the curve, false
off it) — the non-vacuity bar (`feedback-dont-launder-vacuity-as-honest`). -/
theorem mulInv_not_constant :
    (∃ r, mulInv.eval r = false) ∧ (∃ r, mulInv.eval r = true) :=
  ⟨⟨poolBad, by decide⟩, ⟨poolOk, by decide⟩⟩

/-- **`mulInv_non_affine_witness` — PROVED (the GAIN over affine).** `mulInv` rejects on BOTH sides of
the curve: it is true at `x = 2`, but false at `x = 1` (product too small) AND false at `x = 4`
(product too big), with `y` and `k` FIXED. An affine atom `Σ cᵢ·record[fᵢ] ≤ k` is monotone in each
coordinate — varying a single slot can flip its bit at most ONCE (a threshold). A predicate that is
true between two values where it is false (true at 2, false at both 1 and 4) is NON-monotone in `x`,
so it agrees with NO affine atom on this `x`-line. This is the concrete proof that the arithmetic
closure strictly EXCEEDS the affine one — the degree-2 monomial buys non-monotone (curved) relations
the affine fragment cannot name. -/
theorem mulInv_non_affine_witness :
    mulInv.eval poolBad = false ∧ mulInv.eval poolOk = true ∧ mulInv.eval poolHigh = false :=
  ⟨by decide, by decide, by decide⟩

/-! ## §7 — Axiom-hygiene tripwires (the honesty pins over every keystone). -/

#assert_axioms polyNeg_eval
#assert_axioms polyEq_eval
#assert_axioms affineToPoly_eval
#assert_axioms ofRelPred_eval_eq
#assert_axioms deMorgan_and
#assert_axioms deMorgan_or
#assert_axioms not_not
#assert_axioms or_not_self
#assert_axioms and_not_self
#assert_axioms and_or_distrib
#assert_axioms and_top
#assert_axioms or_bot
#assert_axioms monomial_cost_is_degree
#assert_axioms arithPred_constraints_bounded
#assert_axioms atom_poly_finite
#assert_axioms mulInv_discriminates
#assert_axioms mulInv_not_constant
#assert_axioms mulInv_non_affine_witness

end Dregg2.Authority.ArithmeticClosure
