# ERE≤ Lean Formalization — Reuse Assessment for dregg Boolean Matching

> **SUPERSEDED — kept as historical context.** This note's *recommendation* (PORT
> the ERE≤ artifact — vendor + re-elaborate at v4.30.0) was **not taken**, and its
> headline "the middle theorem `derivativeCompile ≡ tableDfa` doesn't exist and is
> months of new automata theory" **has been crossed by a different route.** The
> decision of record is `DERIVATIVE-MATCHING-DESIGN.md` §0: **reference-only** —
> re-prove a lookaround-free derivative tower *over dregg's own `Pred`* (never
> import `RE α`), which dissolves both blockers this doc rates (no license, no
> toolchain bump). And the "missing middle theorem" is now **built and
> `#assert_axioms`-clean** in `metatheory/Dregg2/Crypto/Deriv/`: `der_finite`
> (`Finiteness.lean:298`), the `tableDfa_faithful` + `determinizer_faithful` close
> (`TableDfa.lean:133` / `Powerset.lean:150`), and the Thompson/left factor
> `ThompsonRecognizes` closed for the full Thompson fragment (`thompson_recognizes`,
> `Thompson.lean:751`). **What stays accurate below** is the artifact census — the
> 13-file/2761-line ERE≤ theory is real, sorry-free, on a v4.24-rc1 toolchain, and
> its EBA shape genuinely aligns with dregg's `Pred` (§1). Read this doc for *that*
> census; read `DERIVATIVE-MATCHING-DESIGN.md` for what was actually built.

Read-only research note. Decides whether re-grounding dregg's boolean matching on the
Zhuchko et al. extended-regex (ERE≤) Lean theory is a days-scale weld or a months-scale
project. Nothing in dregg's kernel / circuit / Lean was changed to produce this.

Artifact assessed: `github.com/ezhuchko/extended-regexes` (cloned to a scratch location
OUTSIDE this tree). Owner-confirmed free-use (published through the Zhuchko et al. 2024 /
RE# POPL'25 line). All claims below were checked against the actual Lean source, not the
paper or README.

---

## 1. What the formalization actually contains (cited to real files/decls)

13 Lean files under `Regex/`, 2761 lines total. **`sorry`-free, `admit`-free, no `axiom`
declarations, no `native_decide`** (full scan: clean). It is Lean 4 + mathlib.

### The Effective Boolean Algebra — `Regex/EBA.lean` (64 lines)
- `class Denotation (α σ)` — `denote : α → σ → Bool`.
- `class EffectiveBooleanAlgebra α σ extends Denotation, Bot, Top, Min, Max, HasCompl`
  with the five denotation laws (`denote_bot/top/compl/inf/sup`). This is mathlib's
  `Bot/Top/Min/Max/HasCompl` interface, NOT a bespoke lattice.
- `inductive BA α` (free boolean algebra: `atom/top/bot/and/or/not`) + an
  `EffectiveBooleanAlgebra (BA α) σ` instance. The free BA is the directly reusable atom
  layer.

This EBA is the same shape as dregg's `Pred` algebra
(`metatheory/Dregg2/Exec/PredAlgebra.lean:120` — `inductive Pred` over `StateConstraint`
atoms with `and/or/not/allOf/anyOf/tt/ff` and `Pred.eval : Pred → Value → Value → Bool`).
Both are "free boolean algebra over predicate atoms, folded to `Bool` against a context."
This is the strongest conceptual alignment in the whole comparison.

### Regexes with lookarounds — `Regex/Definitions.lean` (84 lines)
- `inductive RE α` with 11 constructors: `ε`, `Pred (e:α)`, `Alternation ⋓`,
  `Intersection ⋒`, `Concatenation ⬝`, `Star *`, `Negation ~`, `Lookahead ?=`,
  `Lookbehind ?<=`, `NegLookahead ?!`, `NegLookbehind ?<!`. Intersection AND complement
  AND four lookarounds — the full ERE≤ surface.
- `RE.reverse` (the reversal that swaps look-ahead/behind) and `repeat_cat` (bounded-loop
  encoding of `Star`).

### Match semantics (`models`, `⊫`) — `Regex/Models.lean` (59 lines)
- `RE.models (sp : Span σ) (R : RE α) : Prop` — the classical denotational matching
  relation, defined on **spans/locations** (a word split into left context / match /
  right context) rather than plain words, terminating by `star_metric`. `notation ⊫`.

### Symbolic location-derivatives (`der`, `null`, `existsMatch`, `derives`, `⊢`) — `Regex/Derives.lean` (113 lines)
- `mutual` block: `null` (nullability at a location), `existsMatch` (look-around match
  existence), and `der : RE α → Loc σ → {r : RE α // lookaround_height r ≤ lookaround_height R}`
  — the **symbolic location-derivative**, returning a subtype carrying a height bound so
  the mutual recursion is well-founded. The derivative is defined directly against EBA
  `denote` on the read symbol (`if denote φ a then ε else Pred ⊥`).
- `derives (sp) (R) : Bool` — iterates `der` along the match, `notation ⊢`.

### The correctness theorem (`⊢ ↔ ⊫`) — `Regex/Correctness.lean` (428 lines)
- **`theorem correctness {R : RE α} : sp ⊢ R ↔ sp ⊫ R`** (line 375). Real, complete, by
  induction on `R` with `termination_by star_metric R`. Backed by per-constructor lemmas
  (`derives_Eps/Pred/Alt/Inter/Negation/Cat/Star/Lookahead/Lookbehind/NegLookahead/NegLookbehind`,
  `derives_to_existsMatch`, `derives_reversal`). This is the genuine keystone: the
  derivative algorithm decides the denotational semantics.

### Top-level algorithm — `Regex/MatchingAlgorithm.lean` (624 lines)
- `maxMatchEnd` / the `llmatch` longest-match driver, with
  `maxMatchEnd_matches : maxMatchEnd r x = some sp_out → sp_out ⊢ r` and split lemmas.
- Plus `Reversal.lean`, `EliminationNegLookarounds.lean`, `Rewrites.lean`,
  `Metrics.lean` (the `star_metric`/height metrics powering every `termination_by`),
  `Span.lean`, `Models/ModelsReasoning.lean`.

### Toolchain / mathlib (the version reality)
| | extended-regexes | dregg `metatheory/` |
|---|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.24.0-rc1` | `leanprover/lean4:v4.30.0` |
| mathlib | git `efcc0aa5d8cb…` (lake-manifest) | local path `../../../src/mathlib4` @ `1c2b90b1…` (≈ v4.30.0) |
| build root | `lakefile.lean`, `lean_lib Regex` | `lakefile.toml`, libs `Dregg2`/`Metatheory`/`Polis` |

**Six minor-version gap (4.24-rc1 → 4.30.0), and a release-candidate at that.** This is
the real blocker (see §2). README staleness note: it tells you to typecheck `Regex.lean`,
but no such aggregator file exists in the repo — harmless, but it means there is no single
"build everything" entry to copy.

---

## 2. Reuse path into dregg's Lean — import vs port vs re-derive

**Import as a lake dependency: NO.** Two hard reasons.
1. **Toolchain mismatch.** A `require` pulls the dependency's own toolchain expectations;
   mixing `v4.24.0-rc1` mathlib objects into a `v4.30.0` build does not work. dregg pins
   mathlib to a *local path* at the v4.30.0 revision precisely to avoid registry churn;
   adding a second mathlib at `efcc0aa5` would be a conflicting transitive `require`.
   Lake will not co-resolve two mathlib revisions for one build.
2. Even setting versions aside, dregg's `lakefile.toml` globs whole subtrees into three
   libs; a vendored `Regex` lib would need its own `[[lean_lib]]` stanza. That part is
   trivial — the version conflict is the wall.

**Port (vendor + re-elaborate at v4.30.0): YES, this is the route.** The theory uses only
ordinary mathlib (`Order.BooleanAlgebra.Defs/Basic`, `Data.Prod.Lex`, standard
`termination_by`/`decreasing_by`, `simp`, `omega`/`linarith`-style closers). There is no
exotic mathlib surface (no `native_decide`, no heavy category theory, no analysis) that
would rot badly across six minor versions. Expect the usual port friction: renamed simp
lemmas, `Prod.Lex` API drift, `simp` set changes, and possibly the well-founded
`decreasing_by` scripts in the `mutual` block (`Derives.lean:41-56`) needing re-tuning —
those hand-driven `Prod.Lex.right`/`linarith` proofs are the most version-fragile spot.
**Vendor the 13 files into a new `Metatheory/ERE/` (or a sibling lib), fix elaboration
against the pinned v4.30.0 mathlib, keep them sorry-free.** Days of mechanical work for
someone fluent in mathlib version bumps; not research.

**Re-derive from scratch: not warranted.** The proofs exist and are clean; re-deriving
`correctness` would discard 428 lines of finished, peer-reviewed work for no gain.

Recommended: **PORT (vendor + re-elaborate)**, gated behind the realization that the
imported theory does not yet contain the lemma dregg actually wants (see §3).

---

## 3. First-weld feasibility — `derivativeCompile ≡ tableDfa`

The research recommendation's low-risk first weld: the FilterTree *compiler* uses
derivatives, the in-circuit DFA-AIR is unchanged, and the payoff is a Lean equivalence
lemma `derivativeCompile ≡ tableDfa`.

### The honest gap: the two halves live in two different worlds, and neither side has the bridge.

**dregg's side is table-DFA, end to end — no derivatives anywhere.**
- `dfa/src/compiler.rs`: `Pattern` (combinators `Word/Range/AnyByte/Bit/Seq/All/Any/Offset/
  Repeat/BytesAt/PrefixOf`) → `pattern_to_nfa` → `.determinize()` (subset construction) →
  `Dfa { transitions: Vec<StateId> /* [state*256+byte] */, accepting, start }`. The
  `All` combinator IS regex intersection; `PrefixOf` is `inner . any*`. This is a
  **classical Thompson-NFA + powerset DFA**, not a Brzozowski/derivative construction.
- `dfa/src/air.rs` + `metatheory/Dregg2/Crypto/Dfa.lean`: the in-circuit AIR. Lean models
  it as `DfaAccepts δ q₀ accept trace` and proves
  **`dfa_bridge : Satisfies dfaCircuit … ↔ DfaAccepts δ q₀ accept trace`** (Dfa.lean) —
  i.e. "the AIR accepts ⟺ a valid accepting run of the transition relation δ exists."
- `FilterTree` (`dfa/src/filter.rs:82`) composes these table-DFAs by intersection and
  recompiles on revocation. It does **not** use derivatives today — the research doc's
  premise ("the FilterTree compiler uses derivatives") describes a *proposed* re-grounding,
  not the current code.
- The codebase contains **zero** occurrences of regex/Brzozowski derivatives (full scan).

**ERE≤'s side is derivative, end to end — no DFA/table anywhere.**
- The formalization proves `der`/`derives` ↔ `models` (`correctness`). It contains
  **zero** occurrences of `dfa`/`automaton`/`table`/`transition`/`nfa` (full scan). There
  is no determinization, no transition table, no powerset construction, no notion of a
  finite state set.

**So `derivativeCompile ≡ tableDfa` is NOT proved, and ERE≤ does not supply the pieces
for it.** What ERE≤ gives you is the *left* edge (`der` is correct w.r.t. `models`). What
dregg's `Dfa.lean` gives you is the *right* edge (the table-DFA AIR is correct w.r.t.
`DfaAccepts`). The weld needs a **third, currently-nonexistent theorem** in the middle:
that compiling a `Pred`/`RE` by repeated `der` to a fixpoint yields a finite automaton
whose `δ`/accepting set equals the powerset DFA dregg builds — i.e. that the set of
derivative-states is finite and that the derivative transition function equals dregg's
`transitions` table on `accept`/`δ`. This is the **classic "finitely many derivatives ⇒
DFA" theorem** (the Brzozowski finiteness result, modulo similarity/ACI normalization),
and it is exactly the part NOT present in the artifact.

### Size of the gap
- **Reuse for the left edge:** import-ready (after the port). `correctness` is done.
- **The actual weld lemma:** a genuine new development, not a wiring exercise. You must:
  1. Define the derivative-to-DFA construction in Lean (a `RE`/`Pred` → finite automaton
     compiler driven by `der`), with a finiteness argument (derivatives-up-to-similarity
     is finite). ERE≤ deliberately works on locations/spans and never bounds the *number*
     of distinct derivatives, so this finiteness is new work, not a corollary.
  2. Prove that construction's automaton matches dregg's `transitions`/`accepting`
     (`compiler.rs` powerset DFA) — a determinization-equivalence proof bridging two
     different state representations (derivative-class vs powerset-of-NFA-states).
  3. Only then chain `correctness` (ERE↔models) ∘ (new derivative-DFA equivalence) ∘
     `dfa_bridge` (table-DFA-AIR↔DfaAccepts) into the end-to-end statement dregg wants.

Steps (1)–(2) are the months-scale core. They are real theorems about automata finiteness
and determinization, not mathlib-bump mechanics.

---

## 4. Integration risks (honest)

1. **The middle theorem doesn't exist** (the dominant risk). The artifact proves
   derivative↔denotational; dregg proves table-DFA↔AIR. The derivative↔table-DFA bridge —
   the literal `derivativeCompile ≡ tableDfa` deliverable — is absent on both sides. This
   is the wall, and it is months, not days.
2. **Two state representations.** ERE≤ has no finite state set at all (it rewrites the
   regex itself); dregg has `StateId : u32` powerset states. Any equivalence must reconcile
   "derivative expression up to ACI-similarity" with "set of NFA states." This is where
   derivative-DFA proofs classically get hard (the similarity/normalization quotient).
3. **Toolchain port friction** (days, bounded). v4.24-rc1 → v4.30.0 mathlib bump; the
   `mutual`-block `decreasing_by` scripts (`Derives.lean`) and `Prod.Lex` usage are the
   fragile spots. Tractable but not free; an `-rc1` source base is slightly worse than a
   stable tag.
4. **Char-alphabet vs byte-alphabet vs symbolic-Pred.** ERE≤'s running examples use
   `Denotation Char Char`; dregg's table DFA is byte-indexed (`[state*256+byte]`) and its
   real predicate atoms are `StateConstraint` over `Value`. The EBA abstraction makes this
   a re-instantiation rather than a rewrite, but the alphabet mismatch (256-byte table vs
   abstract `σ`) must be pinned down for the AIR side specifically.
5. **Circuit invariance claim must hold.** The pitch is "DFA-AIR is unchanged." That is
   true *if* the weld stays a compiler-side equivalence lemma and the deployed `transitions`
   table / `Dfa.lean` `dfa_bridge` are not touched. The moment the derivative path produces
   a *different* table than the powerset path, the "unchanged AIR" premise breaks — so the
   equivalence (step 2 above) is load-bearing for the no-circuit-change promise, not
   optional polish.
6. **No `Pred`-level integration yet.** dregg's boolean matching that's actually
   security-load-bearing is the `Pred` algebra over `StateConstraint`/`Value`
   (`PredAlgebra.lean`, `CaveatConvergence.lean`), not byte-regex. Re-grounding *that* on
   ERE≤ is a larger story than the FilterTree/DFA first weld; the EBA alignment (§1) makes
   it plausible but it is out of scope for the "first weld" and should not be conflated
   with it.

---

## Verdict

**Not cleanly reusable for the first weld as stated.** The ERE≤ formalization is genuine,
clean, sorry-free, and its `correctness : ⊢ ↔ ⊫` theorem plus the EBA layer are worth
vendoring (port, not import — six-minor-version mathlib gap). But the artifact contains
**no DFA, no transition table, no determinization, and no finiteness-of-derivatives
result**, while dregg's boolean matching is table-DFA from the compiler through the AIR.
The advertised payoff lemma `derivativeCompile ≡ tableDfa` is therefore **not present and
not a corollary of anything ERE≤ proves** — it requires a new derivative-to-DFA
finiteness + determinization-equivalence development that bridges two representations that
neither codebase currently relates.

- **Port the theory:** days (mathlib bump mechanics).
- **The first weld itself (`derivativeCompile ≡ tableDfa`):** months (real automata
  theorems: derivative finiteness + powerset-equivalence), and load-bearing for the
  "unchanged AIR" promise.

The exact integration wall is the **missing derivative↔table-DFA bridge**, on both sides
of the would-be weld.
