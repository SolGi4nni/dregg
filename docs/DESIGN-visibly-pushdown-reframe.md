# Should the parse-as-derivation / templater work be recast on visibly pushdown / nested-word automata?

An honest assessment, not advocacy. The question: does recasting dregg's bracket/Dyck parse
circuit and the guarded handlebars templater on **visibly pushdown languages** (VPL) / **nested-word
automata** (Alur–Madhusudan) make the uniqueness / round-trip **inverse wall** dissolve *for free*,
because VPL determinizability gives a unique run?

Short answer: **the language claim is largely true, the free-inverse claim is false.** The inverse
does not fall out for free. VPL determinism gives a unique *run*; unique *data recovery* still needs
one more argument, and that argument's precondition is exactly the `Excludes` / `Separated`
side-condition that dregg already proves — renamed, not removed. The value of the recast is real but
different: it **names** the wall as a well-understood closed-class boundary and unlocks **decidable
template equivalence**, which the current general-CFG substrate provably cannot have.

Grounded on the objects at HEAD:
`metatheory/Dregg2/Crypto/{Handlebars,HandlebarsGuarded,HandlebarsUniqueness,HandlebarsGuardedUniqueness,Hypergraph,DfaAsCert,CfgCompact,Cfg}.lean`
and `circuit/src/dsl/dyck_stack.rs`.

---

## 0. The automata theory, stated so the claims can be checked against it

A **visibly pushdown automaton** (VPA) fixes a partition of the input alphabet
`Σ = Σ_call ⊎ Σ_return ⊎ Σ_internal`. The stack action is a function of the symbol's **class**, not
the state: read a call ⇒ push exactly one symbol; read a return ⇒ pop exactly one (or hit empty
stack); read an internal ⇒ do not touch the stack. The decisive consequence is that **the stack
height at every input position is a function of the input word alone** (the number of currently
unmatched calls), independent of the run. From that one fact the VPL closure results follow: VPLs are
closed under union, intersection, **complement**; nondeterministic VPAs **determinize** (with a
`2^{O(n^2)}` blowup); equivalence and inclusion are **decidable** (EXPTIME-complete). General CFLs
have none of these — CFL equivalence is undecidable, CFLs are not closed under intersection or
complement. **Nested-word automata** are the equivalent machine: a nested word is a linear string
plus a *nesting relation* matching each call to its return.

Two subtleties that the thesis turns on, flagged now:

1. **The partition is a property of the alphabet, uniform across positions.** A symbol is a call, a
   return, or internal — you cannot have "this occurrence of `c` is a return but that occurrence is
   internal." For a VPA to even *read* a raw string it must know each symbol's class.
2. **Determinism is over the *typed* word.** "Unique run" presupposes the nesting relation is already
   fixed by the input's visible typing. It says nothing about strings whose nesting is *ambiguous* —
   those are not well-typed nested words at all.

The one-pair Dyck language `D₁` (balanced `[`/`]`) is *the* paradigm VPL: `[ ∈ Σ_call`, `] ∈ Σ_return`.

---

## 1. Claim A — is the current language actually visibly pushdown?

**Split verdict. The *languages* are (Dyck) or sub-VPL (flat templater); the *machines that dregg
ships* are not VPAs, and the templater deliberately uses non-visible generality that VPL forbids.**

### 1a. The Dyck circuit: VPL *language*, non-visible *machine*

The grammar is `S → [ S ] | ε` over `{op, cl}` (`Cfg.lean:192-201`, `dyck`, rules `rBracket`/`rEmpty`).
Its language is `{[ⁿ ]ⁿ : n ≥ 0}` — the single-nesting *chain*, a **proper subset** of the full
one-pair Dyck language `D₁` (which also contains `[][]` and needs a concatenation rule `S → [S]S`
or `S → SS` the shipped grammar lacks). Both are VPLs (`call = [`, `return = ]`), so at the
*language* level Claim A is **true** either way — but the shipped grammar is the chain, not `D₁`.

But the circuit `dyck_stack.rs` is **not a VPA**. It is a replay of a **leftmost CFG derivation**
(`CfgCompact.Replay`, `CfgCompact.lean:48-56`), a general pushdown machine whose step alphabet is
`{rule, term, done}` (`dyck_stack.rs`, `IS_RULE`/`IS_TERM`/`IS_DONE`, `col` module `:141-150`). The
stack action on a row is determined by the **certificate**, not the input symbol:

- A `rule` row pops the nonterminal top `S` and pushes the RHS, chosen by `RULE_ID`
  (`dyck_stack.rs:151`, selectors `SEL_BRACKET`/`SEL_EMPTY` `:159-162`). This row **consumes no
  input** — it is an LL-expansion ε-move whose choice (`rBracket` vs `rEmpty`) is the prover's.
  A VPA has no prover-chosen ε stack moves; it does exactly one stack action *per input symbol*.
- A `term` row pops the matched terminal top (`gated(IS_TERM, Equality{STACK0, INPUT_TOKEN})`,
  `:626-631`) and advances the tape. On the **input alphabet**, both `op` and `cl` do the *same*
  stack action here (pop the matched terminal). The push happens only on the non-consuming `rule`
  rows.

So the circuit's "the stack action is determined by the symbol" holds only at the **rule/step**
level, not the **input-symbol** level — which is the opposite of the visibly-pushdown discipline. The
evidence the prompt points at (the depth deltas `+2/−1/−1/0` at `:651-667`, the depth↔occupancy tooth
at `occupancy_tooth` `:394-413`, the rule-membership gate `(RULE_ID−1)(RULE_ID−2)==0` at `:602-620`)
pins the derivation's stack faithfully, but it pins a **general LL replay**, not a VPA. A genuine VPA
circuit for `D₁` would be *strictly simpler*: one row per input symbol, `depth += 1` on `op`,
`depth −= 1` on `cl`, a stack holding only pending returns — no nonterminal `S`, no `RULE_ID`, no
`SEL_*`, no `push_with_remainder_shift` (`:458-477`). That is a **reshape**, an opportunity Claim A
correctly identifies, not a property the current circuit already has.

Where **general-CFG generality is used that a VPL would forbid**: the substrate is not even
CFG-specific — `Hypergraph.Cert` is parametric over an *arbitrary* relation `R` (`Hypergraph.lean:46`),
and `cfg_parse_via_reduction` instantiates it at `g.Produces` for an *arbitrary* grammar
(`Hypergraph.lean:134-138`). The prover-chosen `rule` rows are exactly the epsilon-expansion
nondeterminism VPAs remove. The language is a VPL; the machine ranges over all of CFG (indeed all of
`ReflTransGen R`).

### 1b. The flat templater: sub-VPL (regular), nesting only under composition

The guarded templater's induced object is explicitly **not** even a CFG:
`HandlebarsGuarded.lean:26-30, 101-103` note the alphabet is `Value` (infinite), so each hole is a
**regular leaf** and `gLang` is an *ordered concatenation of regular leaves* (`:97-99`). A finite
concatenation of regular languages is **regular** — sub-VPL. A flat separated spine
(`SepSpine`/`spineTemplate`, `HandlebarsGuardedUniqueness.lean:107-119`) has no nesting at all; a DFA
suffices, which is why `DfaAsCert` (`DfaAsCert.lean`) already exists as the regular leaf of the
substrate. VPL is *overkill* for the flat templater.

Nesting appears only under **composition** (`HandlebarsCompose`, template-inside-hole). And there the
boundary is *not* announced by a distinctive output bracket: `abutting_ambiguous`
(`HandlebarsGuardedUniqueness.lean:439-457`) is precisely a nesting whose boundary is invisible — two
abutting `star any` holes, output `[data, brace]`, with no marker saying where one hole ends. That is
the **non-visibly-nested** case. So the templater deliberately *uses* the generality VPL forbids, and
uses it exactly where the inverse is false.

---

## 2. Claim B — does the inverse fall out *for free*?

**No — partly. Determinism gives a unique *run*; unique *data recovery* needs a further step, whose
precondition is the `Excludes`/`Separated` side-condition itself. The wall is re-expressed as the VPL
boundary, not dissolved.**

The precise chain:

**(i) To pose the output as a nested word you must fix the partition — and its faithfulness *is*
`Excludes`.** Classifying the delimiter symbol `c` as a return requires that `c` appear *only* at
boundaries, never as hole content. That is verbatim `Excludes g c`
(`HandlebarsGuardedUniqueness.lean:99-101`: "no `g`-satisfying word contains `c`"). When a hole's
guard permits `c` (`star any`), the *same* output has `c`s that are sometimes boundaries and sometimes
content — the uniform partition (subtlety 0.1) cannot be assigned. `abutting_ambiguous` is exactly an
output that *cannot be typed* as a nested word with a unique nesting: `brace` is internal in both
readings, and there is no nesting relation to be deterministic *about*. VPA determinism does not reach
this case; the ambiguity is *pre-parse*, in whether the string determines its own nesting.

**(ii) Even granted the partition, unique-run ⇒ unique-data still takes an argument, and it is
`split_unique`.** Given a faithful partition, the boundary positions are a function of the word
(subtlety 0.1: stack height is determined by the input), so the internal runs between boundaries are
forced, so each hole's data is forced. But that *is* the content of
`split_unique`/`brace_split_unique` (`HandlebarsGuardedUniqueness.lean:78-92`,
`HandlebarsUniqueness.lean:78-92`): "the delimiter `c` cannot occur inside a `c`-free prefix, so it is
located identically in both decompositions." The Lean proof is the hand-rolled specialization of
"visible boundary ⇒ forced split." The VPA framework would supply this uniformly — but it does **not**
supply it *without the side-condition*; the side-condition (`Excludes`) is the **hypothesis** that
makes the output a well-typed nested word in the first place. `guarded_render_injective`
(`:221-228`) takes `SeparatedTemplate T` as a hypothesis for exactly this reason.

**(iii) There is even a step past unique-run: run → segmentation → per-hole data.** Injectivity is of
`render : (hole → data) → output`. A unique run yields a unique *segmentation*; mapping segments back
to hole-ids (bijectively, in order) is the spine induction `spine_render_injective_aux` (`:173-206`).
Minor, but it confirms the recovery is not literally read off the run.

**Therefore Claim B's own insight is correct — "the delimiter-guarding *is* visible-pushdown-ness" —
and that is exactly why the wall does not dissolve.** The class where `render` is injective
(`Separated`) coincides with the class that is visibly nested. VPL does not *eliminate* the boundary;
it *explains* it: the wall is the frontier of a closed, determinizable, decidable-equivalence class.
`abutting_ambiguous` is not an artifact dregg failed to prove past — it is the genuine VPL boundary,
where the visible partition provably cannot be assigned. The side-condition is **renamed to a
principled class, not removed.** That is a real epistemic gain (classify the seam — it is the VPL
boundary, with known upper/lower bounds) but it is not *free*, and it does not move the frontier of
what is *provable*.

---

## 3. The concrete recast — a nested-word / VPA leaf on `Hypergraph.Cert R`

A VPA formulation over the alphabet:

- **Σ_call** — opening structural delimiters. Dyck: `op` (`[`). Composition: the frame that opens a
  nested sub-template.
- **Σ_return** — closing delimiters / separators. Dyck: `cl` (`]`). Spine: each single-symbol
  delimiter `c` of `SepSpine.cons` (`HandlebarsGuardedUniqueness.lean:110-111`) — the symbol every
  non-final hole's guard must `Exclude`.
- **Σ_internal** — the guard-recognized data (`dataVal` and the rest of `Value`), the hole content.

**Does it slot onto `Hypergraph.Cert R`? Yes, cleanly, as a *third sibling* of the two existing
instantiations.** `Cert R` is relation-parametric (`Hypergraph.lean:46-47`) and `bridge`
(`:88-93`) holds for any `R`. `DfaAsCert` already instantiates it at the regular step relation
`delta a b := b.state = a.next` (`DfaAsCert.lean:55`, keystone `dfaAccepts_as_cert:79-91`); CFG
parsing instantiates it at `g.Produces`. `regular_and_cf_share_substrate` (`DfaAsCert.lean:126-134`)
exhibits the two side by side. A VPA sits **between** them: *proposed* `R_vpa` is a step relation over
`(state, stack)` configs whose stack action is a function of the current symbol's *class* — a
`delta`-shaped step (regular control) carrying a stack whose push/pop is class-driven. So:

    REGULAR       Cert delta        (no stack)                          -- DfaAsCert (exists)
    VISIBLY-PD    Cert R_vpa        (stack action = f(symbol class))    -- PROPOSED, this doc
    CONTEXT-FREE  Cert g.Produces   (prover-chosen rule stack action)   -- Hypergraph (exists)

This is the strongest structural argument *for* doing at least a slice: the recast is one more
`Hypergraph.bridge` instance, and it lands the visibly-pushdown level of the Chomsky hierarchy onto
the *same certificate substrate* that already carries the regular and context-free levels — the
`regex ⊗ CFG` picture of `docs/DESIGN-composed-attestation-architecture.md`, with the VPL rung made
explicit.

**What it unlocks that the current substrate lacks:**

- **Decidable template equivalence / inclusion.** This is the genuinely new payoff. CFL equivalence
  is *undecidable*, so the general-CFG substrate (`g.Produces` for arbitrary `g`) *provably cannot*
  decide "do templates `T₁`, `T₂` generate the same language?" or "is every output of `T₁` also an
  output of `T₂`?". VPL equivalence *is* decidable. On the visibly-nested fragment those questions
  become answerable — a real capability the current objects do not and cannot have.
- **Boolean closure at the *nested* level.** Regular boolean closure the guards already have —
  `PredRE` carries `inter`/`neg` and the matcher is verified (`HandlebarsGuarded.lean`,
  `noDoubleBraceRE := neg BB`). What VPL adds is closure over the **composed/nested** structure:
  intersecting or complementing two *nested* templates, i.e. the `inter`-refines-outer-guard algebra
  the `guarded_compose` residual (`HandlebarsGuarded.lean:406-409`) and `HandlebarsCompose` want.
- **Determinism → the parse-uniqueness `parse_sat_imp_replay` slice 3 is reaching for** (the
  `dyck_stack.rs` "still out of slice" note, `:58-63`) — but see §2: this gives unique-run, and the
  data-recovery step remains.

---

## 4. Where it breaks / what it costs

**1. Infinite alphabet.** Classical VPL theory (determinizability, complement, decidable equivalence)
is stated for a **finite** alphabet. Dregg's guard alphabet is `Value`, **infinite**
(`HandlebarsGuarded.lean:26-30` states this outright). Over a data-rich alphabet you need **symbolic
VPA** or **register / nominal automata** on top, and the headline results *degrade*: symbolic
automata preserve closure and decidable equivalence *only if* the leaf theory is boolean-closed with
decidable emptiness (`PredRE` plausibly qualifies — that is itself a slice to prove, not a free
inheritance); **register automata lose determinizability and closure under complement outright.** So
the marquee VPL wins do **not** transfer for free to the full guard alphabet. They transfer cleanly
only to the **finite** fragment — which the Dyck circuit already has: it pins every stack cell to the
symbol grid `{EMPTY, S, op, cl}` (`dyck_stack.rs`, `symbol_grid` `:311-313`, `vanishing_on_grid`
`:278-299`). That finite fragment is where a first slice belongs.

**2. Context-free guards.** VPL requires the internal (data) language and the boundary structure to be
visibly *separated*. A guard that is itself **context-free** — a hole whose data must carry its own
nesting not aligned with the outer call/return partition — breaks the uniform partition (the same
symbol is a boundary outside and structural inside). Dregg's guards are currently *regular* (`PredRE`),
so this is not a live break for the flat templater, but nested composition with structurally
overlapping delimiters would hit it.

**3. The ambiguous class is real and wanted.** `abutting_ambiguous` is not a defect to legislate away.
Generation soundness holds for **all** guards (`guarded_render_mem_language`,
`HandlebarsGuarded.lean:145-149`); only the *inverse* needs `Separated`. Two adjacent free-form fields
are a legitimate template. A VPL recast covers exactly the **visibly-nested = invertible** fragment —
a *strict subset* of the templater's generation surface. It is a lens on the invertible sub-class, not
a replacement for the templater.

**4. The circuit is a derivation replay, not a VPA.** Recasting `dyck_stack.rs` to a genuine VPA
changes the wire format and the proof obligation: `parse_sat_imp_replay` is stated against
`CfgCompact.Replay` (`CfgCompact.lean:48-56`), and a VPA circuit would need its own SAT⇒SEM refinement
against VPA semantics. Cost: a parallel circuit plus a parallel Lean refinement. Benefit (for Dyck
specifically): a strictly narrower circuit. Work, not free.

---

## 5. Verdict and recommendation

**The thesis is partly right, and its wrong half is the load-bearing one.**

- **Claim A: true at the language level, false at the machine level.** the shipped chain language `{[ⁿ]ⁿ}` (and full `D₁`) is a VPL and the templater's
  `Separated` class is essentially the visibly-nested class — but the shipped Dyck circuit is a general
  LL/derivation replay whose stack action is certificate-determined, and the flat templater is *regular*
  (sub-VPL), with visible nesting only under composition and *non-visible* nesting deliberately
  supported.
- **Claim B: the inverse does *not* fall out for free.** VPL determinism gives a unique run; unique data
  recovery still needs the boundary-at-forced-position argument (`split_unique`), whose precondition —
  the delimiter is visible, never hole content — *is* `Excludes`/`Separated`, renamed not removed. VPL
  **explains** the wall as a closed-class boundary; it does not eliminate it. `abutting_ambiguous` is
  the genuine VPL boundary.

**Recommendation: worth a *narrow* slice, not a wholesale rebuild.** The recast does not advance what is
provable, but it (a) relocates the residual onto a named, well-understood shelf — the VPL boundary,
with decidable equivalence above it and provable ambiguity below — and (b) unlocks one capability the
current substrate provably *cannot* have: **decidable template equivalence / inclusion** on the
visibly-nested fragment.

**First concrete slice, if yes:** instantiate `Hypergraph.Cert R` at a visibly-pushdown step relation
`R_vpa`, a third sibling to `DfaAsCert.delta` and `g.Produces`, **over the finite symbol grid the Dyck
circuit already pins** (`{EMPTY, S, op, cl}`). Finite alphabet ⇒ classical VPL theory applies cleanly
⇒ determinism yields the parse-uniqueness the slice-3 refinement wants, and the boolean/equivalence
closure becomes available at the Dyck level. Concurrently, **reframe the docstrings** of `Excludes` /
`Separated` (`HandlebarsGuardedUniqueness.lean:99-131`) to *name* the condition as
"visible-partition faithfulness — the delimiter is a genuine return symbol, never internal," so the
wall is correctly identified as the VPL boundary rather than an ad-hoc guard restriction.

**Do NOT** attempt to lift the infinite-`Value` guard alphabet to VPL wholesale: that needs
symbolic/register automata and forfeits the free determinizability, complement, and decidable-
equivalence results that are the entire reason to reach for VPL. The clean win lives at the finite
fragment; the infinite fragment keeps the honest residuals it already carries.

---

*Register note: this document changes no code and closes no proof. It classifies a seam
(per the standing practice: a named seam is not a hole — verify before optimism as well as pessimism).
The classification: the uniqueness wall is the visibly-pushdown / nested-word boundary; determinism
does not cross it for free, but the crossing is now named, and one capability (decidable equivalence)
lies on the far side that the general-CFG substrate cannot reach.*
