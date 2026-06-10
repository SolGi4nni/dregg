/-
# Dregg2.Circuit.Argus.InterpCore — the VERIFIED total descriptor-evaluator (the TCB-shrink).

## The angle: a tiny verified reference the Rust interpreter is a transcription of.

The class-A Argus theorems (`Compile.lean`, every `Effects/*.lean`) are stated against
`satisfiedVm` (`EffectVmEmit.lean:346`) — the ABSTRACT denotation of an `EffectVmDescriptor`
(`∀ c ∈ constraints, c.holdsVm env isFirst isLast` ∧ `siteHoldsAll hash env hashSites`). But
`satisfiedVm` is a `Prop`: a quantifier over a constraint list, a guarded implication per
boundary, and an abstract-`hash` equality per site. Nothing about a `Prop` is, by itself, a
program — the thing that actually RUNS is the hand-written Rust `EffectVmDescriptorAir::eval`
(`circuit/src/lean_descriptor_air.rs:1417`), which walks the SAME descriptor and emits the
SAME assertions to plonky3.

This module supplies the missing middle: a TOTAL, COMPUTABLE Boolean evaluator
`decideVm : (List ℤ → ℤ) → EffectVmDescriptor → VmRowEnv → Bool → Bool → Bool` whose value
`= true` is PROVED equivalent to `satisfiedVm`. So `satisfiedVm` is DECIDABLE by a tiny
reference (`decideVm`), and the Rust `eval` is a transcription of THAT reference rather than of
an opaque `Prop`. The verified core (this file) is small; the Rust AIR is the only un-verified
transcription, and `decideVm` is the spec it must match. This SHRINKS the interpreter TCB to
`decideVm`'s ~30 lines.

## What is PROVEN here (l4v-shaped, axiom-clean).

  * **`decideVm_iff_satisfiedVm`** — `decideVm hash d env isFirst isLast = true ↔ satisfiedVm …`.
    The whole denotation is decided by the reference. Composed from two halves:
    `decideConstraints_iff` (the constraint list) and `decideSites_iff` (the hash-site layer).
  * **`Decidable (satisfiedVm hash d env isFirst isLast)`** — satisfaction is a DECIDABLE
    predicate (first-class instance, built from `decideVm` + the iff). This is the formal content
    of "the denotation is computable by a tiny core".
  * **EXHAUSTIVENESS over `VmConstraint`** — `decideConstraint` is CASE-COMPLETE: a named
    reduction lemma for EVERY constructor (`gate` / `transition` / `boundary .first` /
    `boundary .last` / `piBinding .first` / `piBinding .last` — all six match arms of
    `holdsVm`), each proved `↔ holdsVm`. A missing arm is a missing lemma; the `decideConstraint_*`
    lemmas (and `decideConstraint_total`, which proves `decideConstraint` reduces on every
    constructor) pin that no `VmConstraint` form is dropped.
  * **EXHAUSTIVENESS over `EmittedExpr`** — `EmittedExpr.eval` is total over the four AST forms;
    `evalExpr_var/const/add/mul` pin each form's reduction, and `decideGateBody_iff` decides a
    gate body's vanishing via the total `eval`. The gate decision walks the WHOLE AST.
  * **EXHAUSTIVENESS over `HashInput`** — `HashInput.resolve` is total over `col`/`digest`/`zero`;
    the site evaluator `decideSites` mirrors `siteHoldsAll`'s ordered `go` accumulator EXACTLY
    (`decideSites_eq_go` ties the two recursions), so the digest-chaining order is realized
    faithfully — site `i` reads digests `[0..i)`.

## The residual (named, not papered).

`decideVm` decides `satisfiedVm` — the Lean ABSTRACT denotation. It does NOT, by itself, prove
the Rust `EffectVmDescriptorAir::eval` realizes `satisfiedVm`; that is a Rust↔Lean transcription
obligation OUTSIDE Lean's kernel. This file shrinks the TCB to (a) `decideVm` (verified here) and
(b) the transcription `eval ≈ decideVm`. Two transcription mismatches are EXPLICITLY recorded as
the precise remaining path (`§5`), discovered by reading `lean_descriptor_air.rs`:

  (R1) **The Rust `VmConstraint` enum has NO `Boundary` variant** (`lean_descriptor_air.rs:909`:
       only `Gate` / `Transition` / `PiBinding`). Lean's `VmConstraint.boundary (row) (body)`
       (`EffectVmEmit.lean:225`) — a general boundary polynomial vanishing on first/last — is NOT
       realized by the running interpreter. The `decideConstraint_boundary_*` lemmas DO decide it
       (so the reference is complete over Lean's form), but the Rust transcription drops the arm.
       Status: NO current descriptor emits `.boundary` (all boundary pins go through
       `.piBinding`), so the gap is currently VACUOUS on the emitted corpus — but the reference
       and the Rust enum DISAGREE in shape, and a future `.boundary`-emitting descriptor would not
       be enforced by the Rust AIR. `decideConstraints_no_boundary_agrees` makes the
       currently-vacuous agreement precise: on a `.boundary`-free constraint list the reference and
       a `Boundary`-less interpreter decide the SAME thing.
  (R2) **Domain factoring is in the Rust, not in `satisfiedVm`.** Rust gates `Gate`/`Transition`
       with `when_transition` (rows `0..n-2`) and binds hash digests on the WHOLE domain;
       `satisfiedVm` (a SINGLE row-window denotation) carries `gate`/`transition` UNGUARDED and the
       boundary guards as `isFirst/isLast →`. The single-window reading is faithful PER WINDOW (the
       Rust's row-quantified set instantiated at one window), which is exactly what the class-A
       per-effect theorems consume; the cross-row domain quantification (∀ windows) is the residual
       the multi-row AIR adds. This file does not model the multi-row quantifier.

So: VERIFIED that `satisfiedVm` is decided by a tiny total core, with full case-completeness over
every IR constructor; the RESIDUAL is the Rust-side transcription of that core (R1 shape mismatch
+ R2 row-domain quantifier), stated precisely. No `sorry`, no `:= True`, no `native_decide`. The
file owns only its own declarations and imports the IR + denotation read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmit
import Dregg2.Tactics

namespace Dregg2.Circuit.Argus.InterpCore

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## §1 — Deciding a single gate body's vanishing (the `EmittedExpr` leaf).

`EmittedExpr.eval : EmittedExpr → Assignment → ℤ` is ALREADY total and computable (it recurses on
the var/const/add/mul AST). A gate `body` holds iff `body.eval loc = 0`. Since `DecidableEq ℤ`,
the vanishing is decided by comparing the total evaluation to `0` — no abstraction enters. The
per-form reduction lemmas below pin that the evaluator walks EVERY AST constructor. -/

/-- The four `EmittedExpr` forms reduce as the Rust `eval_expr` does (`Var`→col, `Const`→const,
`Add`/`Mul`→field ops). These are the EXHAUSTIVENESS pins for the gate-body AST: one per
constructor, so a dropped arm is a missing lemma. -/
@[simp] theorem evalExpr_var (v : Nat) (a : Assignment) :
    (EmittedExpr.var v).eval a = a v := rfl
@[simp] theorem evalExpr_const (c : Int) (a : Assignment) :
    (EmittedExpr.const c).eval a = c := rfl
@[simp] theorem evalExpr_add (e₁ e₂ : EmittedExpr) (a : Assignment) :
    (EmittedExpr.add e₁ e₂).eval a = e₁.eval a + e₂.eval a := rfl
@[simp] theorem evalExpr_mul (e₁ e₂ : EmittedExpr) (a : Assignment) :
    (EmittedExpr.mul e₁ e₂).eval a = e₁.eval a * e₂.eval a := rfl

/-- **`decideGateBody`** — the Boolean decision that a gate body vanishes on the current row:
`decide (body.eval loc = 0)`. Total (the eval is total, the equality is decidable). This is the
reference for the Rust `tb.assert_zero(body.eval_expr(local))`. -/
def decideGateBody (env : VmRowEnv) (body : EmittedExpr) : Bool :=
  decide (body.eval env.loc = 0)

/-- The gate-body decision is correct: `= true` iff the body vanishes. -/
@[simp] theorem decideGateBody_iff (env : VmRowEnv) (body : EmittedExpr) :
    decideGateBody env body = true ↔ body.eval env.loc = 0 := by
  simp only [decideGateBody, decide_eq_true_eq]

/-! ## §2 — Deciding ONE constraint (case-complete over all four `VmConstraint` constructors).

`VmConstraint.holdsVm` (`EffectVmEmit.lean:336`) has SIX match arms — the four constructors with
`boundary`/`piBinding` each split on the `VmRow` tag. `decideConstraint` covers all six. The
boundary/PI arms are GUARDED implications `isFirst = true → P` (a `when_first_row`/`when_last_row`
assertion, vacuous off the boundary); a guarded implication over a decidable head and decidable
body is decided by `!flag || decide P`. -/

/-- **`decideConstraint env isFirst isLast c`** — the Boolean reference for one constraint's
denotation `c.holdsVm env isFirst isLast`. CASE-COMPLETE: an arm for every `VmConstraint`
constructor, with the boundary/PI arms split on the row tag exactly as `holdsVm` does. -/
def decideConstraint (env : VmRowEnv) (isFirst isLast : Bool) : VmConstraint → Bool
  | .gate body          => decide (body.eval env.loc = 0)
  | .transition hi lo   => decide (env.nxt (sbCol hi) = env.loc (saCol lo))
  | .boundary .first b  => !isFirst || decide (b.eval env.loc = 0)
  | .boundary .last  b  => !isLast  || decide (b.eval env.loc = 0)
  | .piBinding .first col k => !isFirst || decide (env.loc col = env.pub k)
  | .piBinding .last  col k => !isLast  || decide (env.loc col = env.pub k)

/-! ### Per-constructor reduction lemmas — the EXHAUSTIVENESS pins.

One lemma per match arm of `decideConstraint` / `holdsVm`. If a constructor (or a row-tag split)
were dropped, the corresponding lemma would not type-check. Each proves the arm's decision is
`↔ holdsVm`. -/

theorem decideConstraint_gate (env : VmRowEnv) (iF iL : Bool) (body : EmittedExpr) :
    decideConstraint env iF iL (.gate body) = true
      ↔ (VmConstraint.gate body).holdsVm env iF iL := by
  simp only [decideConstraint, VmConstraint.holdsVm, decide_eq_true_eq]

theorem decideConstraint_transition (env : VmRowEnv) (iF iL : Bool) (hi lo : Nat) :
    decideConstraint env iF iL (.transition hi lo) = true
      ↔ (VmConstraint.transition hi lo).holdsVm env iF iL := by
  simp only [decideConstraint, VmConstraint.holdsVm, decide_eq_true_eq]

theorem decideConstraint_boundary_first (env : VmRowEnv) (iF iL : Bool) (b : EmittedExpr) :
    decideConstraint env iF iL (.boundary .first b) = true
      ↔ (VmConstraint.boundary .first b).holdsVm env iF iL := by
  cases iF <;>
    simp [decideConstraint, VmConstraint.holdsVm]

theorem decideConstraint_boundary_last (env : VmRowEnv) (iF iL : Bool) (b : EmittedExpr) :
    decideConstraint env iF iL (.boundary .last b) = true
      ↔ (VmConstraint.boundary .last b).holdsVm env iF iL := by
  cases iL <;>
    simp [decideConstraint, VmConstraint.holdsVm]

theorem decideConstraint_piBinding_first (env : VmRowEnv) (iF iL : Bool) (col k : Nat) :
    decideConstraint env iF iL (.piBinding .first col k) = true
      ↔ (VmConstraint.piBinding .first col k).holdsVm env iF iL := by
  cases iF <;>
    simp [decideConstraint, VmConstraint.holdsVm]

theorem decideConstraint_piBinding_last (env : VmRowEnv) (iF iL : Bool) (col k : Nat) :
    decideConstraint env iF iL (.piBinding .last col k) = true
      ↔ (VmConstraint.piBinding .last col k).holdsVm env iF iL := by
  cases iL <;>
    simp [decideConstraint, VmConstraint.holdsVm]

/-- **`decideConstraint_iff` — the single-constraint correctness, case-complete.** For EVERY
`VmConstraint c`, `decideConstraint env iF iL c = true ↔ c.holdsVm env iF iL`. The proof dispatches
on all six arms via the per-constructor lemmas, so the `match` is exhaustive by construction. -/
theorem decideConstraint_iff (env : VmRowEnv) (iF iL : Bool) (c : VmConstraint) :
    decideConstraint env iF iL c = true ↔ c.holdsVm env iF iL := by
  cases c with
  | gate body          => exact decideConstraint_gate env iF iL body
  | transition hi lo   => exact decideConstraint_transition env iF iL hi lo
  | boundary row b     =>
      cases row with
      | first => exact decideConstraint_boundary_first env iF iL b
      | last  => exact decideConstraint_boundary_last env iF iL b
  | piBinding row col k =>
      cases row with
      | first => exact decideConstraint_piBinding_first env iF iL col k
      | last  => exact decideConstraint_piBinding_last env iF iL col k

/-- **`decideConstraint_total`** — `decideConstraint` REDUCES on every constructor (the totality /
no-missing-arm witness, stated as a definitional equality per arm). A constructor with no arm could
not appear on the left, so this lemma's six conjuncts pin case-completeness mechanically. -/
theorem decideConstraint_total (env : VmRowEnv) (iF iL : Bool) :
    (∀ body, decideConstraint env iF iL (.gate body) = decide (body.eval env.loc = 0))
    ∧ (∀ hi lo, decideConstraint env iF iL (.transition hi lo)
        = decide (env.nxt (sbCol hi) = env.loc (saCol lo)))
    ∧ (∀ b, decideConstraint env iF iL (.boundary .first b) = (!iF || decide (b.eval env.loc = 0)))
    ∧ (∀ b, decideConstraint env iF iL (.boundary .last b)  = (!iL || decide (b.eval env.loc = 0)))
    ∧ (∀ col k, decideConstraint env iF iL (.piBinding .first col k)
        = (!iF || decide (env.loc col = env.pub k)))
    ∧ (∀ col k, decideConstraint env iF iL (.piBinding .last col k)
        = (!iL || decide (env.loc col = env.pub k))) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## §3 — Deciding the constraint LIST (the `∀ c ∈ constraints, …` conjunct).

`List.all` over `decideConstraint` decides `∀ c ∈ cs, c.holdsVm …` — `List.all_eq_true` converts
the Boolean fold to the membership quantifier, and `decideConstraint_iff` discharges each element. -/

/-- **`decideConstraints env iF iL cs`** — every constraint in `cs` holds, as a Bool. -/
def decideConstraints (env : VmRowEnv) (iF iL : Bool) (cs : List VmConstraint) : Bool :=
  cs.all (decideConstraint env iF iL)

/-- The constraint-list decision is correct: `= true` iff every constraint holds. -/
theorem decideConstraints_iff (env : VmRowEnv) (iF iL : Bool) (cs : List VmConstraint) :
    decideConstraints env iF iL cs = true ↔ ∀ c ∈ cs, c.holdsVm env iF iL := by
  simp only [decideConstraints, List.all_eq_true, decideConstraint_iff]

/-! ## §4 — Deciding the HASH-SITE layer (the `siteHoldsAll` conjunct).

`siteHoldsAll hash env sites` (`EffectVmEmit.lean:293`) is the abstract-`hash` binding: walking the
ordered site list with an accumulator `acc` of already-resolved digests, asserting
`env.loc s.digestCol = hash (s.resolvedInputs env acc)` for each, and appending the new digest so
LATER sites read it (`s.inputs` may contain `digest k` = `acc.getD k`). The order is LOAD-BEARING.

`decideSites` mirrors `siteHoldsAll.go` EXACTLY: same accumulator, same `++ [d]` append, deciding
the per-site equality with `DecidableEq ℤ`. The abstract `hash` enters only as the RHS value being
compared — never inverted — so no choice/abstraction leaks into the decision. -/

/-- **`decideSitesGo hash env acc sites`** — the Boolean mirror of `siteHoldsAll.go`: with `acc` the
digests of earlier sites, decide each site's `loc digestCol = hash (resolved inputs)` and thread the
new digest. The `++ [d]` append matches the Rust `digests.push(d)` loop and Lean's `go`. -/
def decideSitesGo (hash : List ℤ → ℤ) (env : VmRowEnv) :
    List ℤ → List VmHashSite → Bool
  | _,   []      => true
  | acc, s :: ss =>
    let d := hash (s.resolvedInputs env acc)
    decide (env.loc s.digestCol = d) && decideSitesGo hash env (acc ++ [d]) ss

/-- **`decideSites hash env sites`** — every site carries its genuine digest (empty initial acc). -/
def decideSites (hash : List ℤ → ℤ) (env : VmRowEnv) (sites : List VmHashSite) : Bool :=
  decideSitesGo hash env [] sites

/-- The site-walk decision agrees with `siteHoldsAll.go` at EVERY accumulator state. Generalised
over `acc` so the induction threads the digest accumulator (the order-sensitive part). -/
theorem decideSitesGo_iff (hash : List ℤ → ℤ) (env : VmRowEnv) :
    ∀ (acc : List ℤ) (sites : List VmHashSite),
      decideSitesGo hash env acc sites = true ↔ siteHoldsAll.go hash env acc sites
  | _,   []      => by simp [decideSitesGo, siteHoldsAll.go]
  | acc, s :: ss => by
      simp only [decideSitesGo, siteHoldsAll.go, Bool.and_eq_true, decide_eq_true_eq]
      rw [decideSitesGo_iff hash env (acc ++ [hash (s.resolvedInputs env acc)]) ss]

/-- **`decideSites_iff` — the hash-site layer is decided.** `decideSites … = true ↔
siteHoldsAll …`. The site ORDER is realized faithfully (both recursions thread the same accumulator
via `decideSitesGo_iff` at `acc = []`). -/
theorem decideSites_iff (hash : List ℤ → ℤ) (env : VmRowEnv) (sites : List VmHashSite) :
    decideSites hash env sites = true ↔ siteHoldsAll hash env sites := by
  simp only [decideSites, siteHoldsAll]
  exact decideSitesGo_iff hash env [] sites

/-! ## §4¾ — Deciding the RANGE layer (the `∀ r ∈ ranges, r.holds env` conjunct).

`VmRange.holds env r` (`EffectVmEmit.lean`) is `0 ≤ loc r.wire ∧ loc r.wire < 2^r.bits` — the
field-soundness tooth. `ℤ` has `DecidableLE`/`DecidableLT`, so each tooth is decidable; `List.all`
over the per-tooth decision mirrors `∀ r ∈ rs, r.holds env`. This is the layer the running AIR's
`add_range_check` gates realize — now part of the verified denotation, not a dropped field. -/

/-- **`decideRanges env rs`** — every range tooth holds (`0 ≤ loc wire < 2^bits`), as a Bool. -/
def decideRanges (env : VmRowEnv) (rs : List VmRange) : Bool :=
  rs.all (fun r => decide (0 ≤ env.loc r.wire) && decide (env.loc r.wire < (2 : ℤ) ^ r.bits))

/-- The range-list decision is correct: `= true` iff every tooth's wire lies in `[0, 2^bits)`. -/
theorem decideRanges_iff (env : VmRowEnv) (rs : List VmRange) :
    decideRanges env rs = true ↔ ∀ r ∈ rs, r.holds env := by
  simp only [decideRanges, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, VmRange.holds]

/-! ## §5 — `decideVm` — THE verified total reference (and its correctness).

`decideVm` ANDs the three halves. Its `= true` is PROVED equivalent to `satisfiedVm`. This is the
tiny core: the Rust `EffectVmDescriptorAir::eval` is a transcription of `decideVm`, and the iff
below is the spec it must realize. -/

/-- **`decideVm hash d env isFirst isLast`** — the total Boolean decision of the descriptor's
denotation: every constraint holds AND every hash site carries its genuine digest AND every range
tooth holds. The faithful structural mirror of `satisfiedVm`'s three conjuncts (right-associated
to match `satisfiedVm`'s `A ∧ (B ∧ C)`). -/
def decideVm (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) : Bool :=
  decideConstraints env isFirst isLast d.constraints
    && (decideSites hash env d.hashSites && decideRanges env d.ranges)

/-- **`decideVm_iff_satisfiedVm` — THE deliverable.** The total reference DECIDES the abstract
denotation: `decideVm hash d env isFirst isLast = true ↔ satisfiedVm hash d env isFirst isLast`.
So satisfaction of an emitted descriptor is computable by `decideVm` — a tiny verified core the
Rust interpreter transcribes (the TCB-shrink). -/
theorem decideVm_iff_satisfiedVm (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) :
    decideVm hash d env isFirst isLast = true ↔ satisfiedVm hash d env isFirst isLast := by
  simp only [decideVm, satisfiedVm, Bool.and_eq_true,
    decideConstraints_iff, decideSites_iff, decideRanges_iff]

#assert_axioms decideVm_iff_satisfiedVm

/-- **`Decidable (satisfiedVm …)` — satisfaction is a DECIDABLE predicate.** Built from `decideVm`
and the correctness iff: the formal content of "the denotation is computable by a tiny core". An
instance, so downstream `decide`/`#eval` over `satisfiedVm` resolves through the verified core. -/
instance instDecidableSatisfiedVm (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) :
    Decidable (satisfiedVm hash d env isFirst isLast) :=
  decidable_of_iff _ (decideVm_iff_satisfiedVm hash d env isFirst isLast)

#assert_axioms instDecidableSatisfiedVm

/-! ## §6 — The residual, made precise (R1: the Rust `Boundary`-arm gap).

The Rust `VmConstraint` enum (`lean_descriptor_air.rs:909`) has ONLY `Gate`/`Transition`/`PiBinding`
— NO `Boundary`. Lean's `decideConstraint` decides `.boundary` (the per-constructor lemmas above
prove it), so the REFERENCE is complete over Lean's IR; but the Rust transcription drops that arm.
The agreement is currently VACUOUS because no emitted descriptor uses `.boundary`. We make THAT
precise: a constraint list with no `.boundary` is decided identically whether or not the
interpreter handles `.boundary`. -/

/-- A constraint is NOT a boundary form (the predicate the Rust enum's shape implicitly assumes of
every constraint it can represent). -/
def IsNotBoundary : VmConstraint → Prop
  | .boundary _ _ => False
  | _             => True

/-- On a constraint list with NO `.boundary` form, the reference `decideConstraints` and a
`Boundary`-unaware interpreter decide the SAME predicate — every constraint is `gate`/`transition`/
`piBinding`, all of which the Rust enum carries. This locates R1's CURRENT vacuity precisely: the
shape gap bites only a (presently non-existent) `.boundary`-emitting descriptor. -/
theorem decideConstraints_no_boundary_agrees (env : VmRowEnv) (iF iL : Bool)
    (cs : List VmConstraint) (hnb : ∀ c ∈ cs, IsNotBoundary c) :
    decideConstraints env iF iL cs = true
      ↔ ∀ c ∈ cs, (match c with
          | .gate body          => body.eval env.loc = 0
          | .transition hi lo   => env.nxt (sbCol hi) = env.loc (saCol lo)
          | .piBinding .first col k => iF = true → env.loc col = env.pub k
          | .piBinding .last  col k => iL = true → env.loc col = env.pub k
          | .boundary _ _       => True) := by
  rw [decideConstraints_iff]
  constructor
  · intro h c hc
    have := h c hc
    cases c with
    | gate body => simpa [VmConstraint.holdsVm] using this
    | transition hi lo => simpa [VmConstraint.holdsVm] using this
    | boundary row b => simp
    | piBinding row col k =>
        cases row <;> simpa [VmConstraint.holdsVm] using this
  · intro h c hc
    have hc' := h c hc
    cases c with
    | gate body => simpa [VmConstraint.holdsVm] using hc'
    | transition hi lo => simpa [VmConstraint.holdsVm] using hc'
    | boundary row b =>
        -- excluded by hypothesis: a `.boundary` in `cs` contradicts `IsNotBoundary`.
        exact absurd (hnb (.boundary row b) hc) (by simp [IsNotBoundary])
    | piBinding row col k =>
        cases row <;> simpa [VmConstraint.holdsVm] using hc'

#assert_axioms decideConstraints_no_boundary_agrees

/-! ## §7 — Non-vacuity witnesses (the reference rejects AND accepts).

A decider that is constantly `true` would be useless. We pin both polarities on a minimal
descriptor: the selector-binding gate `selectorGate s` (`EffectVmEmit.lean:380`) — a real emitted
constraint — is ACCEPTED on an honest row and REJECTED on a tampered one, THROUGH `decideVm`. -/

/-- A one-gate descriptor carrying exactly the selector-binding constraint for selector `s`. -/
def selectorOnlyDescriptor (s : Nat) : EffectVmDescriptor where
  name        := "dregg-interpcore-seltest-v0"
  traceWidth  := EFFECT_VM_WIDTH
  piCount     := 0
  constraints := [selectorGate s]
  hashSites   := []
  ranges      := []

/-- **Non-vacuity (accept).** On a row carrying selector `s` (`loc s = 1`), `decideVm` ACCEPTS the
selector-only descriptor — the honest leg, decided through the verified core. -/
theorem decideVm_selectorOnly_accepts (hash : List ℤ → ℤ) (s : Nat) (env : VmRowEnv)
    (hactive : env.loc s = 1) :
    decideVm hash (selectorOnlyDescriptor s) env true true = true := by
  rw [decideVm_iff_satisfiedVm]
  refine ⟨?_, ?_⟩
  · intro c hc
    simp only [selectorOnlyDescriptor, List.mem_singleton] at hc
    subst hc
    exact selectorGate_holds_of_active s env true true hactive
  · simp [selectorOnlyDescriptor, siteHoldsAll, siteHoldsAll.go]

/-- **Non-vacuity (reject).** On a NON-pad row (`loc NOOP = 0`) whose selector `s` is NOT set
(`loc s ≠ 1`), `decideVm` REJECTS the selector-only descriptor — the cross-selector-replay tooth,
decided through the verified core. Together with `_accepts`, this proves `decideVm` is NON-vacuous:
it separates satisfying from violating environments. -/
theorem decideVm_selectorOnly_rejects (hash : List ℤ → ℤ) (s : Nat) (env : VmRowEnv)
    (hpad : env.loc sel.NOOP = 0) (hwrong : env.loc s ≠ 1) :
    decideVm hash (selectorOnlyDescriptor s) env true true = false := by
  by_contra h
  rw [Bool.not_eq_false, decideVm_iff_satisfiedVm] at h
  obtain ⟨hcons, _⟩ := h
  have : (selectorGate s).holdsVm env true true := by
    apply hcons
    simp [selectorOnlyDescriptor]
  exact selectorGate_rejects_wrong_selector s env true true hpad hwrong this

#assert_axioms decideVm_selectorOnly_accepts
#assert_axioms decideVm_selectorOnly_rejects

/-! ## §8 — Module-wide axiom-hygiene pin.

Every theorem under `InterpCore` rests on the three standard kernel axioms only (no `sorryAx`).
The decider, the case-complete correctness iff, the decidability instance, the residual lemma, and
the non-vacuity witnesses are all kernel-clean. -/
#assert_namespace_axioms Dregg2.Circuit.Argus.InterpCore

end Dregg2.Circuit.Argus.InterpCore
