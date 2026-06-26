# Re-Grounding dregg's Matching Layer on a Boolean-Closed Derivative Algebra

dregg has **at least four** independent "boolean matching" surfaces, each
re-deriving the same operators (intersection, complement, union) over a
different carrier, with different closure proofs and different in-circuit
stories. This document asks one question: **can RE#/ERE≤'s boolean-closed
symbolic-derivative algebra — closed under `&`/`~`/lookaround, input-linear,
and Lean-formalized — serve as the *one* foundation those surfaces share?**

This is a design/research doc for the owner to decide on. It does not propose a
landing; it lays out the case, the reusable Lean artifact, the in-circuit
split (which the prior eval `REGEX-AUTOMATON-EVAL.md` already settled for the
DFA face), a staged re-grounding design, and an honest account of what is
uncertain. Nothing here is built; several claims below are explicitly flagged
as *unverified*.

---

## 1. The case — dregg's scattered matching surfaces

The owner's framing is correct: three (really four) subsystems are all boolean
matching, and they do not share an algebra.

### 1.1 The predicate / caveat algebra (slot policy + token authority)

This is the surface with the **strongest** existing boolean closure — it is
already a proven Boolean algebra, in both Lean and Rust.

- **`Pred`** (`metatheory/Dregg2/Exec/PredAlgebra.lean:127`): the uniform
  Boolean predicate algebra — atoms (`StateConstraint`) plus
  `tt`/`ff`/`and`/`or`/`not`/`allOf`/`anyOf`, with `not` at **every** level
  (the module header `:1-27` states the intent: replace the forked 2-level
  grammars with "the Heyting algebra done properly"). Old corpora embed as a
  no-op (`Pred.ofConstraint_eval`, `:245`), so existing proofs lift. Boolean
  laws are proven `#assert_axioms`-clean (`:680-706`): double-negation
  collapse `eval_not_not` (`:266` — Boolean, not merely intuitionistic),
  De Morgan (`:279`,`:284`). The evaluator `Pred.eval : Pred → Value → Value →
  Bool` (`:190`) denotes over a **single `(old, new)` transition** of a slot
  write.
- **Two fully-closed sibling algebras** with explicit complement laws proven:
  `ArithmeticClosure.lean` (`or_not_self` excluded middle `:251`,
  `and_not_self` non-contradiction `:259`) and `RelationalClosure.lean`
  (`:236`,`:244`) — over `Value`, single-frame.
- **`CaveatPred`** (the macaroon/biscuit token layer,
  `metatheory/Dregg2/Authority/Caveat.lean:66`): the reified caveat AST, the
  **same connective shape** `and`/`or`/`not`/`tt`/`ff` (`:83-89`), but denoting
  over a **request context `Ctx`** (time/height/sender), not the `(old,new)`
  transition. `Token.admits` = meet ⋀ of all caveats (`:149`);
  `attenuate_narrows` (`:162`) proves appending a caveat only narrows the
  admissible set (the Heyting residual). The header `:46-60` is explicit that
  this **deliberately is NOT aliased to `Pred`** ("a literal alias would be
  unsound" — different denotation domains, transition-vs-context).
- **The Rust executor twin**: `cell/src/program/types.rs:521`
  `SimpleStateConstraint` carries `Not(Box<...>)` (`:589`), the rustdoc
  (`:500-520`) explicitly lifting "the predicate algebra from distributive
  lattice to Heyting algebra"; `Implies(P,Q) == AnyOf([Not(P),Q])` is derived,
  not a variant (`:509-512`).

**Boolean operators this surface needs:** intersection (`and`/`allOf`; token
meet ⋀), complement (`not` — the no-self-transfer tooth `not(digFieldEq from
to)` at `PredAlgebra.lean:427`, the reactive `Changed`/`Unchanged` complements
`:169-182`), union (`or`/`anyOf`). All present, all proven.

### 1.2 The cap-authority lattice (a *different* algebra)

Separate from the predicate algebra: `cell/src/permissions.rs:5`
`AuthRequired {None,Signature,Proof,Either,Impossible,Custom}` with a lattice
order `is_narrower_or_equal` (`:52`) — Impossible=⊥, None=⊤, distinct `Custom`
vk_hashes **incomparable**. `is_attenuation(held,granted)` (`capability.rs:741`)
= `granted.is_narrower_or_equal(held)`. Action attenuation = set intersection:
`ActionSet::intersect` (`token/src/action_set.rs:166`).

**Boolean operators it needs:** intersection (meet / `ActionSet::intersect`).
It has **no complement** — there is no negation of a capability, and `Custom`
vk_hashes are incomparable, so it is **not even a complemented lattice**. This
is a real divergence from §1.1, not an oversight; a capability is monotone-only
by design.

### 1.3 The FilterTree / intent-matcher (the DFA face)

The capability-secure revocation and routing/gossip surface:
`dfa/src/filter.rs:88` `FilterTree` composes filters by **intersection along
every root→leaf path** (`compile_subtree` → `dfa_intersection`, `:134-145`);
`revoke` (`:125`) flips a node to accept-all (intersection identity) and
`compile_combined` rebuilds. A k-deep tree is a k-fold DFA product,
`O(∏|S_i|)` — the actual state-explosion site. The compiler
(`dfa/src/compiler.rs`) is eager Thompson-NFA → subset-construction → flat
`Dfa` table; intersection is `dfa_intersection` (a Cartesian product), and
**complement does not exist** (`Pattern` `:369-395` has `All`/`Any`/`PrefixOf`,
no `Not`). A capability-secure *deny* filter (match everything except a revoked
namespace) is therefore currently **inexpressible**.

**Boolean operators it needs:** intersection (have it, eager/explosive),
complement (want it for deny-filters, don't have it), union.

### 1.4 The shape of the problem

Three carriers — `(old,new)` transitions, request contexts, and byte/symbol
sequences — each want `&`/`~`/`|`, each prove (or fail to prove) closure
separately, and only one of them (FilterTree) is sequence-shaped. The Datalog
token-verification path (`token/src/datalog_verify.rs`) is a *fifth* engine
entirely: positive-only authorization rules + a fixpoint + injected deny-facts,
where negation is stratified deny-rules, not algebraic complement.

**The unifying observation:** every §1.1/§1.3 algebra is a reified, decidable,
eval-folded inductive AST closed under `and`/`or`/`not` — i.e. each is already
presented as a **Boolean algebra of characteristic functions** (`Value → Value
→ Bool`, `Ctx → Bool`, `[Symbol] → Bool`). That is *exactly* the carrier a
Brzozowski/Antimirov derivative construction lives over. The gap is that
§1.1's algebras are boolean over a **single frame**, while a derivative algebra
is boolean over a **sequence** — and FilterTree is the only surface that is
already sequence-shaped (and it has the explosion and the missing complement).

---

## 2. RE#/ERE≤ as the unifying foundation

Source: RE#, Varatalu/Veanes/Ernits, POPL'25 / Proc. ACM PL 9 Art.1 — on disk
at `/Users/ember/Desktop/3704837.pdf`.

### 2.1 What the algebra is

RE# is a symbolic Antimirov/Brzozowski-**derivative** matcher for the class
RE# ⊆ ERE≤, defined modulo a character theory `𝒜 = (Σ, Ψ, ⟦·⟧, ⊥, ⊤, ∨, ∧, ¬)`
— an **Effective Boolean Algebra (EBA)** (§3). Three properties make it a
candidate foundation:

- **Native boolean closure.** Intersection and complement are *constructors in
  the derivative*, not a separate product/determinize pass:
  `δ_x(R & S) = δ_x(R) & δ_x(S)`, `δ_x(~R) = ~δ_x(R)`, `δ_x(R | S) = δ_x(R) |
  δ_x(S)`. The "state" is the derivative-regex itself; the matcher is a lazy
  DFA that materializes only reached states. This is precisely the operator set
  §1.3 realizes today as eager product (`&`) and *not at all* (`~`).
- **Input-linearity** (Thm 4): `LLMatch` is linear in `|s|` for a single match.
  *Caveat carried forward from the eval:* the regex-size state space can still
  grow super-exponentially in the worst case (RE# §5); laziness defers the
  powerset wall, it does not repeal it.
- **Lookaround Normal Form** (Thm 1): `LNF(R) ≡ (?<=B)·E·(?=A)` — lookbehinds
  before, lookaheads after, the single-pass restriction that keeps it linear.
  dregg has no lookaround need today (REGEX-AUTOMATON-EVAL.md §7), but the
  *shape* is suggestive: a positive/negative lookbehind = "this turn is valid
  only if prior history matched B," a lookahead = "...only if a continuation
  exists" — which is the partial-turn/promise context-condition shape
  (memory: a promise-hole is a nullifier). The negative-lookaround-elimination
  theorem (`nla_elim`) reduces negatives to positive-context + complement,
  matching dregg's inexpressibility-as-safety preference. This axis is the
  least-relevant and most-speculative; flagged as such.

### 2.2 The Lean formalization — what it actually proves, and is it reusable

The ERE≤ derivative theory is formalized in Lean 4 by Zhuchko, Veanes, Ebner,
"Lean Formalization of Extended Regular Expression Matching with Lookarounds,"
CPP'24 (DOI 10.1145/3636501.3636959), open-source at
**github.com/ezhuchko/extended-regexes** (Lean 4, package `regex`). RE# cites
it as the *foundational theory of ERE≤* whose theorems it reuses.

What the repo contains (read at HEAD via the survey):

- **`EBA.lean`**: `class EffectiveBooleanAlgebra α σ extends Denotation, Bot,
  Top, Min, Max, HasCompl` with the denotation laws (`denote_bot/top/compl/
  inf/sup`) + a freely-generated `inductive BA` instance. **This is the same
  abstraction as dregg's `Pred`** — a denotation plus `⊥⊤⊓⊔ᶜ` with laws.
- **`Definitions.lean:14`**: `inductive RE` with 11 ctors — `ε`, `Pred`,
  `Alternation ⋓`, **`Intersection ⋒`**, `Concatenation ⬝`, `Star`,
  **`Negation ~`**, and the four lookarounds.
- **`Models.lean:17`** `RE.models : Span → RE → Prop` (`⊫`, declarative span
  semantics) vs **`Derives.lean`** where `null`/`existsMatch`/`der`/`derives`
  (`⊢`) are all `def … : Bool` (computable; `der` returns a height-bounded
  subtype for well-foundedness).
- **The keystone, `Correctness.lean:375`**:
  `theorem correctness : sp ⊢ R ↔ sp ⊫ R` — the *computable derivative
  matcher equals the declarative semantics*, with per-constructor lemmas
  including `derives_Inter`, `derives_Negation`, the four lookaround lemmas,
  and `derives_reversal` (`:427`).
- **POSIX correctness** (`MatchingAlgorithm.lean`: `maxMatchEnd_matches/_max/
  _no_match`) and **negative-lookaround elimination**
  (`EliminationNegLookarounds.lean`: `nla_elim`).
- Toolchain `leanprover/lean4:v4.24.0-rc1`; **depends on full mathlib4**.
- Follow-ups by the same group: ITP'25 "Finiteness of Symbolic Derivatives in
  Lean" (`ezhuchko/finiteness-derivatives` — the derivative state-set is
  finite, i.e. the DFA terminates) and PLDI'26 "EREQ"
  (`ezhuchko/ereq-derivatives`, quantifiers).

**Why this matters for dregg specifically:** the `correctness : ⊢ ↔ ⊫` theorem
is the *exact* shape dregg keeps reaching for — a computable function proven
equal to a declarative semantics — the "two gates provably agree" /
denotational-differential pattern (memory: byte-identity-is-not-faithfulness;
the executor⟺spec⟺circuit triangle). dregg already has the EBA *carrier*
(`Pred`); the repo has the derivative *tower* and its correctness proof on top.

---

## 3. The in-circuit split (settled by the prior eval)

This was already evaluated in `docs/deos/REGEX-AUTOMATON-EVAL.md` (POPL-paper-
grounded, `regex-automata`-grounded, AIR-grounded). The conclusion this doc
adopts wholesale and does not re-litigate:

- **The derivative algebra belongs in the *compiler*, not the AIR.** A STARK
  AIR wants a fixed, low-degree, data-independent per-row constraint set. The
  deployed `dregg-dfa-routing-v1` AIR (`circuit/src/dsl/dfa_routing.rs`) gives
  exactly that: one `TableFunction` lookup per row, binding the run to a rolling
  Poseidon2 commitment over the committed table. A derivative *rewrite step*
  `q' = δ_a(q)` is an AST manipulation of unbounded/variable shape — strictly
  worse in-circuit. So: derivatives compile the table out-of-circuit; the flat
  DFA-AIR proves the verdict in-circuit (REGEX-AUTOMATON-EVAL.md §2.3, §4, §5).
- **The Lean trust boundary starts at the flat table.** The Lean model
  `metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean` models only a `TableDfa`:
  `air_run_is_table_run`/`air_final_state_is_classification` (`:254-268`) and
  the crypto pivot `route_commitment_binds_trace` (`:418-436`, two satisfying
  traces with equal table+route commitment ⇒ identical hash chains under
  collision-freedom). All `#assert_axioms`-clean (`:568-577`). The proof is
  **table-opaque** — it does not care *how* the table was built — so a
  derivative compiler that emits the same flat `Dfa` (`compiler.rs:32-41`)
  inherits the entire proof untouched. This is the seam that makes re-grounding
  a *swap behind a stable boundary*, not a circuit rewrite.
- **The one in-circuit win is the symbolic alphabet.** RE#'s `K`-bit EBA
  predicates → fewer symbol *classes* → smaller AIR degree
  (`table_degree=(|states|-1)+(|symbols|-1)`, `dfa_routing.rs:198`). This is
  the *only* piece that touches the circuit + the Lean model, changes
  `vk_hash`, and must be name-gated as a new descriptor and re-grounded in Lean
  (REGEX-AUTOMATON-EVAL.md §6.1, §7) — real circuit+proof work, not plumbing.

**The honest open gap from the eval (§3 of its risks):** there is today **no
Lean equivalence theorem** linking a derivative-compiled DFA to the `TableDfa`
the proof trusts. The chain `Pattern → Nfa → determinize → Dfa` is *unverified
Rust*. A faithful re-grounding wants a new lemma `derivativeCompile P ≡ tableDfa`
that the existing `air_run_is_table_run` consumes — otherwise the boolean
*semantics* (does this table really equal `R & S`?) is an untrusted Rust gap
under an otherwise-clean proof. **This lemma is exactly what the
extended-regexes `correctness` theorem would supply** if ported — the single
biggest reason to care about the Lean reuse.

---

## 4. A concrete re-grounding design + staged path

### 4.1 What unifies, and what stays separate (an honest scoping)

| Surface | Carrier | Re-ground? | Why |
|---|---|---|---|
| **FilterTree / intent / routing** (§1.3) | byte/symbol sequences | **Yes — primary.** Derivative compiler for `&`/`~`/`\|`, emitting the same flat `Dfa`. | Already sequence-shaped; has the explosion *and* the missing complement. The natural home for ERE≤. |
| **Predicate `Pred`** (§1.1) | single `(old,new)` frame | **Partial — as the EBA instance** under a lifted sequence layer (a turn-*trace* of frames). | Already a boolean algebra of `Value→Value→Bool`; would become the per-symbol acceptance test, with `der` stepping one turn. *Unverified that the lift is sound.* |
| **`CaveatPred`** (§1.1) | request `Ctx` | **Maybe — same EBA, different σ.** | Shares connective shape but a deliberately distinct denotation domain; unifying needs reconciling `Ctx` vs `(old,new)` under one σ. The temporal floors/ceilings *are* a 1-frame degenerate of a trace lookbehind. |
| **Cap-authority lattice** (§1.2) | capability tokens | **No.** | No complement, incomparable Custom vk_hashes — not a complemented lattice; monotone-by-design. Welding it in would be wrong. |
| **Datalog verify** (§1.4) | fact sets + fixpoint | **No (bridge, don't subsume).** | Stratified deny-rules ≠ algebraic complement; a separate engine with its own STARK path. |
| **The DFA-AIR + `TableDfa` Lean** (§3) | flat table | **Unchanged.** | The trust boundary; derivatives feed it, they do not replace it. |

The key discipline (memory: house-capacities drift): a derivative re-grounding
lives at dregg's **read/query/policy face** (like the rhizomatic slotting), NOT
the kernel. ERE≤ has zero notion of δ-balance, capabilities, or nullifiers.
Over-claiming a "derivative kernel" would repeat the Rust-periphery-mistaken-
for-protocol scar.

### 4.2 The Lean-reuse strategy ("weld not build")

The cleanest move, if licensing clears (§4.4): **instantiate the repo's
`EffectiveBooleanAlgebra` with dregg's own denotation**, and inherit the
derivative + `correctness` tower over dregg's character theory. Both are
Lean4 + mathlib4, so it is a *port*, not a translation. Concretely, three
candidate σ instantiations, in increasing order of risk:

1. **σ := byte / symbol-class** (FilterTree). Direct: dregg's routing alphabet
   *is* RE#'s Σ. This is the path the eval already endorses. The payoff is the
   `derivativeCompile ≡ tableDfa` lemma (§3) and a `Pattern::Not` combinator.
2. **σ := `(old, new) : Value` transition** (`Pred` over a turn-trace). Lift
   `Pred : Value→Value→Bool` to the `RE.Pred` ctor's per-location predicate;
   `der` then steps one *turn* at a time, and `correctness` proves the streaming
   matcher equals the declarative trace-predicate. The reactive
   `Monotonic`/`Unchanged`/`Changed` atoms (`PredAlgebra.lean:169-182`) are
   exactly the "remember the previous frame" residual state a derivative
   automaton threads — a hint this lift is natural. **Unverified**: their `Pred`
   ctor carries a single predicate per location, so a 2-state caveat needs σ to
   *be* the `(old,new)` pair, and lookbehind's `reversal` then reverses
   turn-order (meaningful, but needs checking).
3. **σ := `Ctx`** (CaveatPred). Same EBA, request-context denotation. Reconciles
   §1.1's two algebras under one carrier if and only if a common σ embeds both —
   the hardest and least-certain unification.

The pull is that **`attenuate_narrows` / `CaveatPred.refines`
(`Caveat.lean:162`,`:271`) is already a decidable refinement (language-
inclusion) order** — the very thing a derivative-based equivalence/inclusion
check computes structurally. Re-grounding would replace the per-context
`refines` proof with derivative-based decision (and connects to the proven
right-skew/Büchi-game *decidable flow/policy refinement* result — memory
flow-algebra-right-skew).

### 4.3 The staged path (additive-then-cutover, circuit never changes shape)

This sequences the always-good, low-risk pieces first; the speculative
unifications last and only on demand. Stages 1–3 are lifted from
REGEX-AUTOMATON-EVAL.md §6; stages 0 and 4–5 are this doc's additions.

- **Stage 0 — license + port spike (gating).** Ask upstream for a license
  (§4.4). Spike: vendor `extended-regexes` into the metatheory, align toolchain
  (their `v4.24.0-rc1` + mathlib vs dregg's `Dregg2/*` l4v-shaped tree), and
  get `correctness` building. *No code lands until this is green.*
- **Stage 1 — symbol-class AIR (in-circuit, name-gated).** Map bytes → small
  category ids before the DFA (RE#'s EBA idea at coarse granularity); shrinks
  `|symbols|` and the AIR degree. New descriptor, new `vk_hash`, re-grounded in
  `DfaAcceptanceAir`. *The only circuit+proof work.*
- **Stage 2 — lazy determinization (out-of-circuit).** Replace eager
  `pattern_to_nfa().determinize()` with a lazy determinizer (cache budget +
  give-up, `regex-automata`-hybrid-modeled); same `Dfa` output, same AIR.
  `Dfa::table_size_bytes` becomes the enforced budget.
- **Stage 3 — derivative `&`/`~` compiler + `Pattern::Not` (out-of-circuit,
  the payoff).** Swap `dfa_intersection` for the RE#-style derivative front-end;
  add `Pattern::Not` so deny-filters are expressible. Retires the `FilterTree`
  explosion. Still emits a flat `Dfa`.
- **Stage 4 — the equivalence lemma (the faithfulness close).** Prove (or port)
  `derivativeCompile P ≡ tableDfa` so the boolean semantics is no longer an
  untrusted Rust gap under the clean AIR proof. **This is the stage that
  consumes the ported `correctness` theorem and is the real reason to do the
  Lean port at all.**
- **Stage 5 — predicate/caveat lift (speculative, last).** Only if §4.2(2)/(3)
  prove sound: lift `Pred`/`CaveatPred` to span-indexed recognizers over
  turn-traces, unifying §1.1's frame-algebras with the sequence algebra.

### 4.4 Risks and open questions (honest)

- **NO LICENSE — the single hard blocker.** `github.com/ezhuchko/extended-
  regexes` has no LICENSE file (gh api 404). Reuse/port is *legally blocked*
  until upstream adds one (MIT/Apache). This is an **ember-decision / outreach
  item**, not technical. Stage 0 cannot start without it.
- **Semantics mismatch: strings vs turn-traces.** ERE≤ matches `List σ` with
  one predicate per location; dregg's real object is a regex over a *sequence of
  transitions*. Instantiating σ := `(old,new)` is *plausible but unverified*
  (§4.2(2)); the reversal/lookbehind interaction with turn-order is the first
  thing to check.
- **No equivalence theorem today.** Until Stage 4, the boolean semantics of the
  compiled table is untrusted Rust under a clean AIR (§3). This is the
  faithfulness gap, and it is the whole point.
- **Executable-but-nonlinear.** The Lean repo gives *correctness*, not
  *performance*. RE#'s input-linearity comes from LNF + .NET engineering
  (mintermization, lazy DFA, prefilters) that the Lean artifact does NOT
  contain. dregg would inherit a verified-but-slow matcher and own the perf
  engineering itself.
- **Finiteness is a *separate* artifact.** Termination/finiteness of the
  derivative state-set (needed for any DFA/circuit size bound) lives in the
  *later* ITP'25 `finiteness-derivatives` repo, not `extended-regexes`. A real
  port pulls both, and they may track different Lean/mathlib revs — a
  version-alignment cost against dregg's own toolchain.
- **mathlib weight.** The repo requires full mathlib4. dregg's `Dregg2/*` is
  l4v-shaped; a port inherits mathlib's build weight and version constraints,
  which may or may not already be compatible.
- **Complement does not escape determinization.** RE# makes `~R` a native
  derivative, but settling it into a *committed* DFA still needs a total
  deterministic automaton; a complement of a Unicode-heavy / deeply-intersected
  pattern can still blow up `num_states`. The resource bound + give-up policy is
  the safety net, not a proof of small size (REGEX-AUTOMATON-EVAL.md §7).
- **Right-skew non-distributivity.** The trace/online-sim semantics is *proven*
  right-skewed — choice ⊔ does NOT left-distribute over compose ⋆ (memory
  flow-algebra-right-skew). A naive Kleene-algebra/derivative re-grounding that
  assumes full distributivity would be **unsound for the reactive rung**. Any
  Stage 5 lift must respect this, not assume a free Kleene algebra.
- **Reifying ≠ forcing in-circuit (the genuinely hard frontier).** `Caveat.lean`
  is explicit (`:57-60`): reifying a caveat is an *expressiveness* gain, not a
  *soundness* gain — "the circuit still binds an aggregate `caveatBit` and
  trusts the executor's decision." A boolean/derivative caveat algebra inherits
  this: making policy structurally inspectable ≠ forcing it in the light-client
  circuit. In-circuit forcing is orthogonal to the boolean closure and stays
  hard.
- **The opaque escape arm.** `Caveat.opaque (Ctx→Bool)` (`Caveat.lean:113`,
  `:127`) and the witnessed/ZK predicates (`cell/src/predicate.rs`
  `Custom{vk_hash}`) are NOT introspectable — a derivative algebra cannot see
  inside them. Re-grounding shrinks the opaque surface, it does not eliminate
  it.
- **Don't over-rotate.** The deployed router is 4 states / 4 symbols
  (`dfa_routing.rs:537`). The explosion is a *latent* `FilterTree`-deep-
  intersection risk, not a live fire. The staging deliberately lands the cheap
  always-good pieces (symbol classes, lazy compile) first and the derivative
  rewrite only when an intersection-heavy filter tree actually demands it.

---

## 5. Bottom line

dregg already *has* the Boolean-algebra carrier (`Pred`/`CaveatPred`/the closure
modules — proven `#assert_axioms`-clean) and the stable in-circuit trust
boundary (the table-opaque `TableDfa` proof). What it lacks is **(a) the
sequence/derivative layer that would unify the frame-algebras with the
sequence-matcher, (b) `~` for the FilterTree, and (c) a Lean equivalence theorem
making the compiled boolean semantics trusted.** ERE≤'s formalization is a
near-exact fit for (a) and (c) — same EBA abstraction, same `⊢ ↔ ⊫` correctness
shape, Lean4+mathlib — and RE#'s derivative algebra is the right *compiler* for
(b) (the eval already proved it is the *wrong* in-circuit transition).

The move is a **weld, not a build** — *if* the license clears. The
recommendation: pursue Stage 0 (license + port spike) as the gating decision,
land Stages 1–3 (they are good independent of the unification), and treat the
predicate/caveat lift (Stage 5) as a genuine open research question, not a
foregone conclusion — the turn-trace σ instantiation and the right-skew
non-distributivity are real, unverified frontiers.

### Cited sources

- RE# paper: `/Users/ember/Desktop/3704837.pdf` (POPL'25, Proc. ACM PL 9 Art.1).
- ERE≤ Lean: `github.com/ezhuchko/extended-regexes` (CPP'24, DOI
  10.1145/3636501.3636959); follow-ups `ezhuchko/finiteness-derivatives`
  (ITP'25), `ezhuchko/ereq-derivatives` (PLDI'26).
- Predicate algebra: `metatheory/Dregg2/Exec/PredAlgebra.lean`,
  `Dregg2/Authority/{ArithmeticClosure,RelationalClosure,Caveat}.lean`,
  `cell/src/program/types.rs`, `cell/src/{permissions,capability}.rs`,
  `token/src/{action_set,datalog_verify}.rs`.
- DFA face: `dfa/src/{filter,compiler}.rs`, `circuit/src/dsl/dfa_routing.rs`,
  `metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean`,
  `cell/src/predicate.rs`, `turn/src/executor/membership_verifier.rs`.
- The settled in-circuit split: `docs/deos/REGEX-AUTOMATON-EVAL.md`.
