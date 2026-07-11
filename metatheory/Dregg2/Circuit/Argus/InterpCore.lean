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

## The Rust transcription edge (outside the kernel, pinned differentially — not carried).

`decideVm` decides `satisfiedVm` — the Lean ABSTRACT denotation. It does NOT, by itself, prove
the Rust `EffectVmDescriptorAir::eval` realizes `satisfiedVm`; that is a Rust↔Lean transcription
obligation OUTSIDE Lean's kernel. The TCB is (a) `decideVm` (verified here) and (b) the
transcription `eval ≈ decideVm`. (b) is held by a differential battery, layer by layer:

  * **Arm shape (the old "R1").** The Rust `VmConstraint` enum carries ALL of Lean's forms —
    `Gate` / `Transition` / `Boundary{First,Last}` / `PiBinding{First,Last}`
    (`lean_descriptor_air.rs`; the `Boundary` arm is a `when_first_row`/`when_last_row`-guarded
    `assert_zero`, witnessed both polarities through the real prover in
    `boundary_form_realized_both_polarities`). [TOMBSTONE: the enum once had NO `Boundary` arm,
    and §6 below stated the agreement only over boundary-FREE lists — a vacuity on the emitted
    corpus. That statement is retired; §6 now states the FULL-arm agreement.]
  * **Row domain (the old "R2").** `satisfiedVm`/`decideVm` is a SINGLE row-window denotation;
    the multi-row AIR quantifies windows over the trace with the `when_transition` factoring —
    `gate`/`transition` enforced on windows `r < n−1`, `boundary`/`piBinding` at the unique
    `isFirst`/`isLast` windows, hash sites + ranges on EVERY row. The factoring belongs to the
    LIFT, not the reference: `decideVm` carries `gate`/`transition` UNGUARDED on every window
    (including `isLast = true` — the golden corpus pins exactly that). The lift is pinned by the
    generated exhaustive differential (`circuit/tests/effect_vm_descriptor_exhaustive_
    differential.rs`: AIR ≡ the factored multi-row reference on every IR form, both polarities).
  * **The verdicts of `decideVm` ITSELF (the golden leg).** `Argus/InterpGolden.lean` computes
    `decideVm`'s verdicts IN LEAN over a 35-case corpus — every constraint arm, every expr /
    hash-input form, all four `isFirst`/`isLast` settings (incl. the single-row window),
    on-row/off-row boundary legs, the ℤ-only negative-range leg — and
    `lean_descriptor_air.rs::tests::lean_decide_vm_golden_corpus_agrees` re-decides the SAME
    bytes (descriptors via the `EmitRoundtrip`-proven `emitVmJson` codec) with an exact ℤ
    transcription, arm for arm.

So: VERIFIED that `satisfiedVm` is decided by a tiny total core, with full case-completeness over
every IR constructor; the Rust transcription of that core is differential-pinned at every layer
(arm shape · row domain · verdict golden). The
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
  decide (body.eval env.loc ≡ 0 [ZMOD 2013265921])

/-- The gate-body decision is correct: `= true` iff the body vanishes mod p. -/
@[simp] theorem decideGateBody_iff (env : VmRowEnv) (body : EmittedExpr) :
    decideGateBody env body = true ↔ body.eval env.loc ≡ 0 [ZMOD 2013265921] := by
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
  | .gate body          => isLast || decide (body.eval env.loc ≡ 0 [ZMOD 2013265921])
  | .transition hi lo   => isLast || decide (env.nxt (sbCol hi) ≡ env.loc (saCol lo) [ZMOD 2013265921])
  | .boundary .first b  => !isFirst || decide (b.eval env.loc ≡ 0 [ZMOD 2013265921])
  | .boundary .last  b  => !isLast  || decide (b.eval env.loc ≡ 0 [ZMOD 2013265921])
  | .piBinding .first col k => !isFirst || decide (env.loc col ≡ env.pub k [ZMOD 2013265921])
  | .piBinding .last  col k => !isLast  || decide (env.loc col ≡ env.pub k [ZMOD 2013265921])

/-! ### Per-constructor reduction lemmas — the EXHAUSTIVENESS pins.

One lemma per match arm of `decideConstraint` / `holdsVm`. If a constructor (or a row-tag split)
were dropped, the corresponding lemma would not type-check. Each proves the arm's decision is
`↔ holdsVm`. -/

theorem decideConstraint_gate (env : VmRowEnv) (iF iL : Bool) (body : EmittedExpr) :
    decideConstraint env iF iL (.gate body) = true
      ↔ (VmConstraint.gate body).holdsVm env iF iL := by
  cases iL <;>
    simp [decideConstraint, VmConstraint.holdsVm]

theorem decideConstraint_transition (env : VmRowEnv) (iF iL : Bool) (hi lo : Nat) :
    decideConstraint env iF iL (.transition hi lo) = true
      ↔ (VmConstraint.transition hi lo).holdsVm env iF iL := by
  cases iL <;>
    simp [decideConstraint, VmConstraint.holdsVm]

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
    (∀ body, decideConstraint env iF iL (.gate body)
        = (iL || decide (body.eval env.loc ≡ 0 [ZMOD 2013265921])))
    ∧ (∀ hi lo, decideConstraint env iF iL (.transition hi lo)
        = (iL || decide (env.nxt (sbCol hi) ≡ env.loc (saCol lo) [ZMOD 2013265921])))
    ∧ (∀ b, decideConstraint env iF iL (.boundary .first b)
        = (!iF || decide (b.eval env.loc ≡ 0 [ZMOD 2013265921])))
    ∧ (∀ b, decideConstraint env iF iL (.boundary .last b)
        = (!iL || decide (b.eval env.loc ≡ 0 [ZMOD 2013265921])))
    ∧ (∀ col k, decideConstraint env iF iL (.piBinding .first col k)
        = (!iF || decide (env.loc col ≡ env.pub k [ZMOD 2013265921])))
    ∧ (∀ col k, decideConstraint env iF iL (.piBinding .last col k)
        = (!iL || decide (env.loc col ≡ env.pub k [ZMOD 2013265921]))) :=
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

/-! ## §6 — The FULL-arm agreement (the de-vacuified R1 statement).

TOMBSTONE — what stood here: `decideConstraints_no_boundary_agrees`, stated over constraint lists
with NO `.boundary` form (an `IsNotBoundary` hypothesis narrowing the agreement to the arms the
then-`Boundary`-less Rust enum could represent, with the boundary arm read as `True`). That was
the precise record of a SHAPE GAP: the agreement held only because no v1 descriptor emitted
`.boundary`. The gap is closed — `lean_descriptor_air.rs::VmConstraint::Boundary { row, body }`
realizes Lean's `VmConstraint.boundary` as a `when_first_row`/`when_last_row`-guarded
`assert_zero`, accept AND reject witnessed through the real prover
(`boundary_form_realized_both_polarities`) and through the generated exhaustive differential —
so the hypothesis-narrowed statement is RETIRED and replaced by the agreement over EVERY
constraint list, the boundary arm carrying its REAL guarded semantics. One match arm per Rust
match arm: this is the explicit per-arm shape the interpreter transcribes (and the golden corpus
`Argus/InterpGolden.lean` pins verdict-by-verdict). -/

/-- **The full-arm agreement.** For EVERY constraint list — boundary forms included — the
reference `decideConstraints` decides exactly the per-arm predicate the (now arm-complete) Rust
interpreter transcribes: `isLast`-guarded `gate`/`transition` (the deployed `when_transition()` —
they bind on every row but the last) and `isFirst`/`isLast`-guarded `boundary`/`piBinding`.
Non-vacuous on `.boundary`-carrying lists (contrast the tombstoned predecessor, which assumed them
away). -/
theorem decideConstraints_decides_all_arms (env : VmRowEnv) (iF iL : Bool)
    (cs : List VmConstraint) :
    decideConstraints env iF iL cs = true
      ↔ ∀ c ∈ cs, (match c with
          | .gate body          => iL = false → body.eval env.loc ≡ 0 [ZMOD 2013265921]
          | .transition hi lo   => iL = false → env.nxt (sbCol hi) ≡ env.loc (saCol lo) [ZMOD 2013265921]
          | .boundary .first b  => iF = true → b.eval env.loc ≡ 0 [ZMOD 2013265921]
          | .boundary .last  b  => iL = true → b.eval env.loc ≡ 0 [ZMOD 2013265921]
          | .piBinding .first col k => iF = true → env.loc col ≡ env.pub k [ZMOD 2013265921]
          | .piBinding .last  col k => iL = true → env.loc col ≡ env.pub k [ZMOD 2013265921]) := by
  rw [decideConstraints_iff]
  constructor
  · intro h c hc
    have hcc := h c hc
    cases c with
    | gate body => cases iL <;> simp_all [VmConstraint.holdsVm]
    | transition hi lo => cases iL <;> simp_all [VmConstraint.holdsVm]
    | boundary row b => cases row <;> exact hcc
    | piBinding row col k => cases row <;> exact hcc
  · intro h c hc
    have hcc := h c hc
    cases c with
    | gate body => cases iL <;> simp_all [VmConstraint.holdsVm]
    | transition hi lo => cases iL <;> simp_all [VmConstraint.holdsVm]
    | boundary row b => cases row <;> exact hcc
    | piBinding row col k => cases row <;> exact hcc

#assert_axioms decideConstraints_decides_all_arms

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

/-- **Non-vacuity (reject).** On a NON-pad TRANSITION row (`isLast = false`, `loc NOOP = 0`) whose
selector `s` is NOT set (`loc s ≠ 1`), `decideVm` REJECTS the selector-only descriptor — the
cross-selector-replay tooth, decided through the verified core. The `isLast = false` guard is
FAITHFUL: `selectorGate` is a `.gate`, evaluated by the deployed circuit under `when_transition()`,
so it binds on every row but the last; the rejection tooth fires exactly on the transition domain.
Together with `_accepts`, this proves `decideVm` is NON-vacuous: it separates satisfying from
violating environments. -/
theorem decideVm_selectorOnly_rejects (hash : List ℤ → ℤ) (s : Nat) (env : VmRowEnv)
    (hs : 0 ≤ env.loc s ∧ env.loc s < 2013265921)
    (hpad : env.loc sel.NOOP = 0) (hwrong : env.loc s ≠ 1) :
    decideVm hash (selectorOnlyDescriptor s) env true false = false := by
  by_contra h
  rw [Bool.not_eq_false, decideVm_iff_satisfiedVm] at h
  obtain ⟨hcons, _⟩ := h
  have : (selectorGate s).holdsVm env true false := by
    apply hcons
    simp [selectorOnlyDescriptor]
  exact selectorGate_rejects_wrong_selector s env true false rfl hs hpad hwrong this

#assert_axioms decideVm_selectorOnly_accepts
#assert_axioms decideVm_selectorOnly_rejects

/-! ### Boundary-arm non-vacuity (the §6 de-vacuification's teeth).

The full-arm agreement would still be cheap if the boundary arm never separated environments.
These three pin the `.boundary` semantics THROUGH `decideVm`, on a minimal boundary-only
descriptor (the Lean mirror of the Rust prover test `boundary_form_realized_both_polarities`):
accepted on an honest boundary row, REJECTED on a violating one, and VACUOUS off the boundary
row (the `isFirst →` guard) — the three legs the golden corpus carries as
`boundary-first-{accept,reject,vacuous}*`. -/

/-- A descriptor whose ONLY constraint is a first-row boundary equality `loc i = loc j`, in the
emitter's canonical `a + (−1)·b` body shape. -/
def boundaryOnlyDescriptor (i j : Nat) : EffectVmDescriptor where
  name        := "dregg-interpcore-boundarytest-v0"
  traceWidth  := EFFECT_VM_WIDTH
  piCount     := 0
  constraints := [.boundary .first (.add (.var i) (.mul (.const (-1)) (.var j)))]
  hashSites   := []
  ranges      := []

/-- **Boundary non-vacuity (accept).** On a first row whose cells agree, `decideVm` ACCEPTS the
boundary-only descriptor. -/
theorem decideVm_boundaryOnly_accepts (hash : List ℤ → ℤ) (i j : Nat) (env : VmRowEnv)
    (iL : Bool) (h : env.loc i = env.loc j) :
    decideVm hash (boundaryOnlyDescriptor i j) env true iL = true := by
  simp [decideVm, decideConstraints, decideConstraint, boundaryOnlyDescriptor,
    decideSites, decideSitesGo, decideRanges]
  -- ⊢ env.loc i + -env.loc j ≡ 0 [ZMOD 2013265921]
  rw [Int.modEq_zero_iff_dvd]
  exact ⟨0, by omega⟩

/-- **Boundary non-vacuity (reject).** On a first row whose CANONICAL cells DISAGREE, `decideVm`
REJECTS the boundary-only descriptor — the boundary arm separates environments. The canonicality
hypotheses (`loc i`, `loc j` ∈ `[0, p)`) are FAITHFUL to the field denotation: distinctness must be
witnessed in the canonical residue window, since `≡ 0 [ZMOD p]` would otherwise be satisfiable by a
nonzero multiple of `p` (the deployed range-checks supply exactly this canonicality). -/
theorem decideVm_boundaryOnly_rejects (hash : List ℤ → ℤ) (i j : Nat) (env : VmRowEnv)
    (iL : Bool)
    (hi : 0 ≤ env.loc i ∧ env.loc i < 2013265921)
    (hj : 0 ≤ env.loc j ∧ env.loc j < 2013265921)
    (h : env.loc i ≠ env.loc j) :
    decideVm hash (boundaryOnlyDescriptor i j) env true iL = false := by
  simp [decideVm, decideConstraints, decideConstraint, boundaryOnlyDescriptor,
    decideSites, decideSitesGo, decideRanges]
  -- ⊢ ¬ env.loc i + -env.loc j ≡ 0 [ZMOD 2013265921]
  rw [Int.modEq_zero_iff_dvd]
  rintro ⟨k, hk⟩
  obtain ⟨hi0, hi1⟩ := hi
  obtain ⟨hj0, hj1⟩ := hj
  omega

/-- **Boundary guard vacuity (off-row).** Off the first row (`isFirst = false`) the boundary
constraint imposes NOTHING — `decideVm` accepts however broken the cells are. Exactly the
`when_first_row` semantics the Rust arm transcribes. -/
theorem decideVm_boundaryOnly_off_row_vacuous (hash : List ℤ → ℤ) (i j : Nat) (env : VmRowEnv)
    (iL : Bool) :
    decideVm hash (boundaryOnlyDescriptor i j) env false iL = true := by
  simp [decideVm, decideConstraints, decideConstraint, boundaryOnlyDescriptor,
    decideSites, decideSitesGo, decideRanges]

#assert_axioms decideVm_boundaryOnly_accepts
#assert_axioms decideVm_boundaryOnly_rejects
#assert_axioms decideVm_boundaryOnly_off_row_vacuous

/-! ## §8 — Module-wide axiom-hygiene pin.

Every theorem under `InterpCore` rests on the three standard kernel axioms only.
The decider, the case-complete correctness iff, the decidability instance, the residual lemma, and
the non-vacuity witnesses are all kernel-clean. -/
#assert_namespace_axioms Dregg2.Circuit.Argus.InterpCore

end Dregg2.Circuit.Argus.InterpCore
