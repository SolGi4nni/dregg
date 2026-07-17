# In-Circuit Pattern-Matching Automaton Evaluation for `dregg-dfa`

What automaton should `dregg-dfa` run **inside the STARK** when it proves "input `I`
was classified by the governance-bound pattern table `C`"? The dispatch automaton
is the load-bearing object: it gates routing (`router.rs`), capability-secure
revocation (`filter.rs::FilterTree`), and gossip topic visibility
(`filter.rs::TopicFilter`). The owner's question is whether the current
NFA→DFA-then-prove pipeline should be re-architected toward an NFA-direct or
derivative-based automaton, because subset construction can explode the state
count — and the in-circuit cost is a direct function of that state count.

This document grounds the answer in three things: the actual `dregg-dfa` impl, the
RE# paper (POPL 2025), and burntsushi's `regex-automata`. It is an evaluation, not
a build order. The headline up front, then the evidence.

## Recommendation (TL;DR)

**Keep the compiled DFA as the in-circuit prover, but split compilation from
proving and add an out-of-circuit derivative front-end for the operators that make
the DFA explode (intersection and complement).** Concretely:

1. **In-circuit: keep the DFA AIR.** The deployed
   `dregg-dfa-routing-v1` AIR (`circuit/src/dsl/dfa_routing.rs`) proves one DFA
   transition per symbol with a *fixed per-row constraint set*, and binds the run
   to a rolling Poseidon2 commitment over the table. An NFA-direct or
   derivative-step automaton does **not** beat this *in-circuit*: it trades the
   DFA's "big table, cheap row" for "small table, expensive row," and the
   expensive row is worse for a STARK, where per-row constraint count and degree
   are the dominant cost and must be *fixed and data-independent*. (Detail in
   §4 and §5.)

2. **Out-of-circuit: adopt RE#-style symbolic derivatives as the *compiler* for
   `Pattern::All` (intersection) and a complement combinator.** *(BUILT — this
   half of the recommendation has landed, see `dfa/src/derivative.rs` and
   `DERIVATIVE-MATCHING-DESIGN.md`.)* The pattern that actually blows up
   `dregg-dfa` is the `FilterTree` intersection/complement case (`filter.rs`),
   not literal routes. RE#'s derivative algebra makes intersection and complement
   *first-class, native derivative rules* (`δ_x(R&S) = δ_x(R) & δ_x(S)`,
   `δ_x(~R) = ~δ_x(R)`) and determinizes *lazily, on demand*, only materializing
   the DFA states an actual input reaches. That is strictly better than the old
   eager product-then-determinize (`dfa_intersection` + `determinize`) for
   building the *committed table* that the circuit then consumes.
   `dfa/src/derivative.rs` realizes exactly this (`Re::and` = the derivative
   `inter` constructor, `Re::complement`, `der b`), and `FilterTree` now folds
   its subtree with `Re::and` instead of eager `dfa_intersection`
   (`filter.rs:90-93,168`).

3. **The honest tradeoff:** this keeps the circuit unchanged (low risk, the AIR is
   already Lean-backed and `#assert_axioms`-clean per the route-commitment pivot)
   while attacking the explosion at the compiler, where it belongs. The residual
   risk is that complement still requires a *total deterministic* automaton, so a
   complement of a Unicode-heavy or deeply-intersected pattern can still produce a
   large committed table — derivatives shrink the *typical* blowup and the *build
   cost*, they do not repeal the worst case. dregg's own escape hatch already
   exists: patterns are byte-oriented, route tables are tiny (the deployed router
   is 4 states / 4 symbols), and the resource bound `Dfa::table_size_bytes` is
   already a guard.

The rest of this document is the evidence for each clause.

---

## 1. What `dregg-dfa` runs in-circuit today

### 1.1 The compile pipeline (`dfa/src/compiler.rs`)

`Pattern::compile()` is `pattern_to_nfa(self).determinize()` (`compiler.rs:441`).
The flow is the textbook one:

- **Thompson NFA construction** with explicit ε-states. `Nfa` holds
  `byte_transitions: HashMap<u8, Vec<StateId>>` and `epsilon: Vec<StateId>` per
  state (`compiler.rs:147-158`); combinators `concat`/`union`/`star`
  (`compiler.rs:222-279`) wire ε-edges in the standard Thompson shape. The NFA is
  **byte-oriented** (alphabet = 256 byte values), same as `regex-automata`.
- **Subset construction** (`Nfa::determinize`, `compiler.rs:294-360`): the
  classic powerset worklist — each DFA state is a `BTreeSet<StateId>` of NFA
  states, ε-closures via `epsilon_closure` (`compiler.rs:281-292`), and a flat
  transition table `transitions[state*256 + byte] -> next_state`.
- **Intersection** (`Pattern::All`) is a **DFA product**: compile each part to a
  DFA, then `dfa_intersection` two-by-two (`compiler.rs:519-541`, the product at
  `compiler.rs:619-683`), then re-NFA-ify (`dfa_to_nfa`) so it composes. The
  product state set is the Cartesian product `|S_A| × |S_B|`.

The crucial property: **the in-circuit object is the *final DFA's flat
transition table*** — `Vec<StateId>` of length `num_states * 256`. Everything the
circuit proves is "this run is a path through *that committed table*."

### 1.2 The deployed in-circuit AIR (`circuit/src/dsl/dfa_routing.rs`)

The production circuit is `dregg-dfa-routing-v1`. Per symbol it proves one
transition with these constraints (`dfa_routing.rs:137-193`), faithful to the Lean
model `Dregg2.Crypto.DfaAcceptanceAir`:

- **C1 entry hash**: `entry_hash == hash_4_to_1(current, symbol, next, 0)`.
- **TABLE (GAP-A)**: `next == step(current, symbol)` via a **bivariate
  `TableFunction`** interpolation over the transition grid, plus two
  `vanishing_on_grid` range constraints pinning `current`/`symbol` to the grid.
- **C2 continuity**: `next_row.current_state == this_row.next_state`.
- **C3 accumulation**: rolling Poseidon2 hash `next.running ==
  hash_2_to_1(this.running, next.entry_hash)`, seeded with the table commitment.
- **B1/B2/B3 boundaries**: bind `initial_state` / `final_state` /
  `route_commitment` to public inputs.

This is the cost model that decides the whole question, so read the degree note at
`dfa_routing.rs:196-200` carefully:

```
table_degree = (|states|-1) + (|symbols|-1)
range_degree = max(|states|, |symbols|)
max_degree   = max(table_degree, range_degree, 2)
```

**The AIR's constraint *degree* — the dominant STARK cost driver — grows linearly
in the number of distinct states and symbols.** And `compute_table_commitment`
(`dfa_routing.rs:336-361`) Merkle-hashes *every* `(state, symbol, next)` triple,
so the commitment work grows with `|states| * |symbols|`. The deployed router is
tiny (4 states, 4 symbols — `dfa_routing.rs:537-547`), so this is cheap *today*.
The question is whether it stays cheap, and that is exactly a question about state
explosion.

> The standalone `dfa/src/air.rs` AIR and `air.rs`
> (`AirTraceRow{step,state,byte,next_state}`, the flat-table lookup variant)
> are the same shape minus the route-commitment chain. `air.rs::verify_acceptance`
> is the out-of-circuit re-check the cell-side `DfaAcceptanceVerifier`
> (`WitnessedPredicateKind::Dfa`) runs.

### 1.3 The actual explosion case: `FilterTree` (`dfa/src/filter.rs`)

Literal routes do **not** explode: a union of N disjoint literals is ~linear in
total literal length (the `many_routes_stress_passes_u8_cap` test builds 80 routes
and lands in the low thousands of states). The worst case is `FilterTree`
(`filter.rs:88-146`): it composes filters by **intersection along every root→leaf
path** (`compile_subtree` → `dfa_intersection`, `filter.rs:134-145`), and
revocation recompiles the combined intersection. Each intersection is a product;
a chain of `k` filters is a `k`-fold product, `O(∏ |S_i|)` states in the worst
case. **This** is the structural state-explosion the owner is worried about, and
it is intersection-driven — precisely the operator RE# makes cheap.

There is now a complement combinator: `Pattern::Not(Box<Pattern>)`
(`compiler.rs:404`, constructor `Pattern::not` at `:453`, routed through the
derivative path via `has_not` at `:461`). A capability-secure "deny" filter
(match everything *except* a revoked namespace) is therefore expressible today —
it compiles through `dfa/src/derivative.rs` (`Re::complement`), since complement
is the operator that forces determinization-blowup and so must NOT go through the
eager `pattern_to_nfa` path (`compiler.rs:692-698` rejects a bare `Not` there).

---

## 2. RE# (Varatalu, Veanes, Ernits — POPL 2025)

Source: `3704837.pdf`, *RE#: High-Performance Derivative-Based Regex Matching with
Intersection, Complement, and Restricted Lookarounds*.

### 2.1 The model

RE# is a **symbolic Antimirov/Brzozowski-derivative** matcher built on an
**Effective Boolean Algebra (EBA)** for the character theory (`§3`, `§4.1`). Two
ideas matter for us:

- **Symbolic alphabet.** Transitions are not over 256 concrete bytes but over
  *predicates* in a Boolean algebra `𝒜 = (Σ, Ψ, ⟦·⟧, ⊥, ⊤, ∨, ∧, ¬)`. In .NET's
  implementation the predicates are a `K`-bit bitvector algebra (`K ≤ 64`,
  `§4`), so a character class is one `O(1)` bitwise op, *independent of alphabet
  size*. This is why RE# handles the full Unicode plane without the byte-level
  UTF-8 automaton blowup that dregg's and `regex-automata`'s byte NFAs incur.
- **Derivatives with native Booleans.** The derivative `δ_x(R)` (the regex that
  matches the rest of the input after consuming location `x`) is defined
  structurally (`§4.7`), and crucially:

  ```
  δ_x(R & S) = δ_x(R) & δ_x(S)      (intersection)
  δ_x(~R)    = ~ δ_x(R)             (complement)
  δ_x(R | S) = δ_x(R) | δ_x(S)      (union)
  ```

  Intersection and complement are **just more constructors in the derivative**,
  not a separate product/determinization pass. The "state" is *the derivative
  regex itself*. The matcher caches derivative-regexes as DFA states with
  `δ_a(q)` as the transition function and *lazily* discovers states as input
  drives them (`§5`: "derivatives are computed lazily and cached in a DFA with
  regexes internalized as states").

- **Restricted lookarounds** via *location* derivatives and a Lookaround Normal
  Form `LNF(R) = (?<=B)·E·(?=A)` (Theorem 1, `§4.2-4.10`). Lookbehinds only
  before the match, lookaheads only after — the "single-pass" restriction that
  keeps it input-linear. dregg has no lookaround need today, so this is the
  least-relevant axis; note it only for completeness.

### 2.2 Performance claims (and their scope)

- **Baseline:** ">71% faster than the next fastest engine in Rust" on the
  BurntSushi/rebar benchmarks, taking overall first place (`Abstract`, `§1`,
  Table 4a: `2.54/1.48 ≈ 1.716`). The "next fastest in Rust" is the `regex` crate
  (i.e. `regex-automata`). This is a *real, audited* artifact (ACM badges).
- **Extensions:** on intersection/complement/lookaround-heavy benchmarks RE#
  "outperforms all other engines often by several orders of magnitude" (`§1`,
  Fig. 2). The comparison there is mostly against *backtracking* engines that
  blow up on these features — so "orders of magnitude" is real but is largely
  "linear automaton vs. exponential backtracker," not "RE# vs. another linear
  automaton."
- **Complexity (Theorem 4, InputLinearity):** `LLMatch` is **linear in `|s|`**
  for a single match. But read the honest caveat in `§5` (just after the
  precompile discussion): *"the state space can still grow **super-exponentially**
  with respect to the size of the regex in the worst case"* and `LLMatches` (all
  matches) "may in the worst case be quadratic in `|s|`." Input-linearity is in
  the *input*; the *regex-size* blowup is the same powerset wall, deferred and
  usually avoided by laziness, not eliminated.

### 2.3 Is a derivative-step amenable to a STARK AIR? — the honest assessment

**This is the crux, and the honest answer is: not as a drop-in replacement for the
DFA AIR, and probably net-negative in-circuit.** Reasons, grounded in the AIR
shape from §1.2:

1. **A STARK AIR wants a *fixed, data-independent* per-row constraint set.** The
   DFA row is exactly that: one `TableFunction` lookup of fixed degree. A
   *derivative step* `q' = δ_a(q)` is a *symbolic rewrite of an AST-shaped state*
   (a derivative regex), whose size and structure vary per step. To put that
   in-circuit you must either (a) commit the derivative-DFA's materialized
   transition table — at which point **you are back to the DFA AIR**, having paid
   the determinization out-of-circuit (this is the good idea, see §5), or (b)
   prove the rewrite itself in-circuit, which means circuitizing AST manipulation
   with a worst-case unbounded node count per step. Option (b) is a *much* harder
   and larger circuit than the current one, with data-dependent structure that
   STARKs handle poorly.

2. **The symbolic EBA predicate is the genuinely good in-circuit idea, but it is
   orthogonal to "DFA vs. derivative."** RE#'s `K`-bit bitvector character
   predicate (`§4`) maps *beautifully* to a field-friendly in-circuit test: a
   byte-class membership becomes a small fixed bitwise/range constraint instead
   of a 256-wide table column. dregg's AIR already gestures at this — the
   `TableFunction` works over a *grid of distinct symbols*, and the deployed
   router uses 4 symbol *categories*, not 256 bytes. **Adopting RE#'s symbolic
   alphabet (proving over symbol *classes* rather than raw bytes) is a real
   in-circuit win and is compatible with keeping the DFA AIR.** It shrinks
   `|symbols|`, which directly shrinks the AIR degree (`§1.2`).

3. **Intersection/complement as derivative rules pay off at *compile* time, not
   prove time.** `δ_x(R&S) = δ_x(R)&δ_x(S)` means the *combined* automaton is
   discovered lazily without ever materializing the full product — exactly the
   `FilterTree` blowup we want to avoid. But the *circuit* still consumes the
   committed table of whatever states the input reached. So the derivative
   algebra belongs in the **compiler that produces the committed table**, not in
   the AIR.

**Verdict on RE# for dregg:** adopt the *derivative algebra* as an out-of-circuit
compiler for intersection/complement, and adopt the *symbolic-alphabet* idea to
shrink the in-circuit symbol grid. Do **not** try to run a derivative-rewrite step
as the in-circuit transition — it loses to the flat-table DFA AIR.

---

## 3. `regex-automata` (burntsushi) — the NFA-direct reference

Source: the `regex` crate's engine library, `regex-automata 0.4.14`
(unpacked from the local mirror).

### 3.1 The components

- **Thompson NFA** (`src/nfa/thompson/nfa.rs`). Byte-oriented (alphabet = 256
  bytes; Unicode pre-compiled to byte-level UTF-8 automata). `State` enum
  (`nfa.rs:1514`): `ByteRange` (the consuming workhorse), `Sparse`/`Dense`
  (compact byte-transition encodings), `Look` (conditional ε for anchors/word
  boundaries), `Union`/`BinaryUnion` (unconditional ε, ordered for leftmost-first
  priority), `Capture` (ε with a side-effect: record offset into a slot),
  `Fail`, `Match`. **Size is linear in the pattern** *after bounded repetitions
  are expanded* (`nfa.rs:107-115`) — the crate's explicit headline contrast with
  DFAs.
- **PikeVM** (`src/nfa/thompson/pikevm.rs`). The NFA-direct simulation. It tracks
  an **active state-SET per byte** in a `SparseSet` (`pikevm.rs:1996-2023`) sized
  to `|NFA states|`, with insertion-order dedup. Per byte: ε-closure
  (`epsilon_closure`, `pikevm.rs:1611`) of the active set, then step every state
  over the byte. **Per-byte cost = `O(|NFA states| + |ε-edges|)`** — proportional
  to the NFA size, *not* constant. It uniquely resolves capture groups. The
  crate's own framing: a DFA is "to a first approximation about an order of
  magnitude faster" (`nfa.rs:101-105`); the PikeVM's win is no build-time blowup
  and full capability.
- **Lazy/hybrid DFA** (`src/hybrid/dfa.rs`). Determinizes *one transition at a
  time* and caches states (≤ one new DFA state per input byte → `O(m·n)` search).
  Fixed cache budget; on overflow it **flushes the entire cache**
  (`try_clear_cache`, `dfa.rs:2360`) and, if thrashing past
  `minimum_cache_clear_count`, **gives up** (→ meta engine falls back to PikeVM).
- **Dense vs sparse DFA** (`src/dfa/{dense,sparse}.rs`). Dense = flat premultiplied
  table, `O(1)` per byte, big. Sparse = per-state transition scan, ~3-5× slower
  per byte, smaller bytes-per-state — **but the *state count* is still
  exponential in the worst case** (`dense.rs:1356`); sparse shrinks the constant,
  not the number of states. Byte equivalence classes (`ByteClasses`) collapse the
  256-byte alphabet to only the discriminating classes — the same idea as RE#'s
  symbolic alphabet, at a coarser granularity.

### 3.2 The decisive fact: no intersection, no complement

I grepped the entire `regex-automata` source: **there is no automaton-level
intersection, complement, or negation API at any layer.** The only `intersect` is
`LookSet::intersect` (a bitset op over look-assertion flags); the only `negate` is
the negated-word-boundary assertion. Multi-pattern support (`new_many`,
`which_overlapping_matches`) is **union/alternation only**.

So a system that needs intersection/complement — which dregg does, via
`FilterTree` — **cannot get them from `regex-automata`** and must build them
itself:

- **Intersection** = product construction (state-set size *multiplies*). This is
  exactly what dregg's `dfa_intersection` already does.
- **Complement** = determinize, *complete* the transition function (add a sink),
  then flip accept/non-accept. NFA complement is **not** "negate the accept set" —
  it forces determinization, reintroducing the `2^n` blowup. This is the single
  strongest argument *against* a naive NFA-direct rewrite for dregg: the moment
  you need complement, the NFA's linear-size advantage evaporates.

### 3.3 What dregg should learn from it

- **The byte-class / equivalence-class idea** (and RE#'s symbolic-alphabet
  generalization of it) is the portable win: shrink the in-circuit symbol grid.
- **The lazy-DFA model is the right *compiler* strategy** for building the
  committed table: materialize only the states an input reaches, with a cache
  budget and an explicit "give up → bigger table or reject" policy. dregg's
  `Dfa::table_size_bytes` resource bound is the seed of this.
- **The PikeVM (NFA-direct) is the wrong *prover* model** for a STARK: its
  per-byte cost is `O(|NFA states|)` and *data-dependent* (the active set varies),
  which is precisely what an AIR cannot cheaply express as fixed per-row
  constraints.

---

## 4. NFA-direct in-circuit vs. the DFA — the core question

Could we prove an **NFA state-set transition per byte** in-circuit instead of a DFA
edge, getting a representation that is *linear in the pattern* with no explosion?

**In principle yes; in practice it loses to the DFA AIR for dregg's patterns.**
The reasoning:

- **Representation size: NFA wins.** The NFA is linear in the (expanded) pattern;
  the DFA can be exponential. So the *committed object* is smaller for the NFA.
- **Per-byte AIR cost: DFA wins decisively.** The DFA row is **one** transition
  with a **fixed** constraint set (`TableFunction` + 2 range polys, §1.2). The
  NFA row must prove a *bounded state-SET transition*: for each currently-active
  NFA state, follow its byte-transition and ε-closure, union into the next set.
  That is `O(|NFA states|)` constraints *per row*, and the set membership is
  data-dependent. To make it fixed-cost you must allocate the *worst-case* set
  width (= `|NFA states|`) in every row — so you pay `|NFA states|` columns × ε-
  closure constraints on *every* byte, even when the active set is tiny. For any
  non-trivial pattern this is far more per-row work than the single DFA lookup.
- **ε-closure in-circuit is the killer.** ε-closure is a transitive-closure
  fixpoint (`epsilon_closure`, both in dregg's `compiler.rs:281` and
  `pikevm.rs:1611`). Proving a fixpoint in a fixed-degree AIR requires either
  unrolling to a worst-case bound (more columns/rows) or a permutation/lookup
  argument over the ε-edge relation — a substantially more complex circuit than
  the current one, and one with no Lean model today.

**The hybrid/lazy option is the actual resolution:** don't choose NFA-vs-DFA
*in-circuit*. Determinize **lazily** *out-of-circuit* (RE#-style or
`regex-automata`-hybrid-style), materializing only the reachable states for the
patterns and inputs in play, then commit *that* small DFA and prove it with the
existing flat-table AIR. This captures the NFA's "don't pay for states you never
visit" without paying the NFA's per-row cost in the circuit.

For dregg's *actual* patterns:

- **Route tables** (`router.rs`): unions of literals + prefix wildcards. These
  don't explode; the DFA is already small and the current pipeline is fine.
- **`FilterTree`** (`filter.rs`): k-fold intersection (+ wanted complement). This
  is where the DFA product explodes — and where lazy *derivative* compilation
  (§2) is the right fix, feeding the same DFA AIR.

---

## 5. Tradeoff table

Per-byte cost is the in-circuit constraint cost of one input symbol. "AIR
complexity" is how hard it is to express as a fixed, low-degree, data-independent
constraint system (the thing STARKs are cheap at).

| Axis | Compiled DFA (today) | NFA-direct (PikeVM-style) in-circuit | Symbolic derivatives (RE#) in-circuit | **Lazy-DFA compile + DFA AIR (recommended)** |
|---|---|---|---|---|
| **Per-byte in-circuit cost** | 1 fixed-degree table lookup (§1.2) — cheapest | `O(\|NFA states\|)` set-transition + ε-closure, **data-dependent** | derivative AST rewrite, **unbounded/data-dependent** | 1 fixed-degree table lookup (same as DFA) |
| **Representation / committed size** | `num_states × \|symbols\|`; **exponential worst case** | **linear in pattern** | derivative-states: **lazy, usually small; super-exp worst case** (§2.2) | only the *reached* states; lazy → typically small |
| **AIR complexity** | Low; already Lean-backed, `#assert_axioms`-clean | High (ε-closure fixpoint, variable set width) | Very high (circuitize AST rewriting) | Low — **unchanged AIR** |
| **Intersection** | DFA product, state-set **multiplies** (`dfa_intersection`) | NFA product, active-set multiplies; helps size not per-row | **native** `δ(R&S)=δR&δS`, lazy — best at compile | native at compile, flat DFA in-circuit |
| **Complement** | not supported; would need determinize+complete+flip | **forces determinization → `2^n`** (kills NFA advantage) | **native** `δ(~R)=~δR`, but still needs total DFA to settle | native at compile; flat DFA in-circuit |
| **Alphabet handling** | 256-byte grid, or symbol *categories* (router uses 4) | 256-byte (UTF-8 expansion for Unicode) | **symbolic `K`-bit predicates, `O(1)`, Unicode-clean** | adopt symbolic symbol classes → smaller AIR degree |
| **Worst-case input complexity** | linear in `\|input\|` | linear in `\|input\|`, larger constant | linear (single match); quadratic (all matches) | linear in `\|input\|` |
| **Build cost** | eager subset construction (+ eager product for `&`) | linear build | **lazy**, only reachable states | **lazy**, only reachable states |
| **Fit for STARK** | **Best** (fixed row, low degree) | Poor (variable row, fixpoint) | Poor in-circuit / **Best as compiler** | **Best** |

---

## 6. Migration path

Low-risk, staged, additive-then-cutover — the circuit never changes shape, so the
Lean model and the deployed `vk_hash` stay valid throughout.

1. **Symbol-class AIR (small, high-value, in-circuit).** Generalize the
   `dregg-dfa-routing-v1` symbol axis from raw bytes to *symbol categories* (it
   already supports a `b_values` grid of distinct symbols, §1.2). Compile a
   `ByteClasses`/RE#-EBA-style classifier that maps bytes → small category ids
   before the DFA, shrinking `|symbols|` and thus the AIR degree. This is the one
   change that touches the circuit; gate it behind a new descriptor name so the
   old `vk_hash` survives.

2. **Lazy determinization in the compiler (out-of-circuit).** Replace
   `Pattern::compile`'s eager `pattern_to_nfa().determinize()` with a lazy
   determinizer that materializes only reachable states, modeled on
   `regex-automata`'s hybrid DFA (cache budget + give-up). Output is the *same*
   `Dfa` struct (`compiler.rs:32-41`) → the same committed table → the same AIR.
   `Dfa::table_size_bytes` becomes the enforced budget.

3. ✅ **DONE — Derivative-based intersection/complement (out-of-circuit, the
   payoff).** Behind the `FilterTree` and `Pattern::All` API, the eager
   `dfa_intersection` product was swapped for an RE#-style derivative compiler:
   states are derivative-regexes (`Re`), `δ(R&S)=δR&δS` / `δ(~R)=~δR`, lazily
   explored — all in `dfa/src/derivative.rs` (`Re::and`, `Re::complement`,
   `der b`, byte-class boundaries for lazy determinization). `Pattern::Not`
   (`compiler.rs:404`) makes capability-secure *deny* filters expressible, and
   `FilterTree` folds with `Re::and` (`filter.rs:90-93,168`). The output is still
   a flat `Dfa` for the existing AIR. This is the change that retired the
   `FilterTree` explosion.

4. **Keep the DFA AIR as the prover throughout.** No NFA-direct or
   derivative-rewrite in-circuit. Ever-larger committed tables are bounded by the
   resource guard, and the lazy compiler keeps them small for real patterns.

---

## 7. Honest risks and non-goals

- **Complement does not escape determinization.** RE# makes `~R` a native
  derivative, but *settling* it into a committed DFA still requires a total
  deterministic automaton. A complement of a Unicode-heavy or deeply-intersected
  pattern can still produce a large committed table. Derivatives shrink the
  *typical* case and the *build cost*; they do not repeal the worst case. The
  resource bound (`table_size_bytes`) and an explicit "give up → reject the
  filter" policy are the safety net, not a proof of small size.
- **The symbolic-alphabet AIR change is the only in-circuit work, and it changes
  the `vk_hash`.** It must be name-gated (new descriptor) and re-grounded in the
  Lean model (`Dregg2.Crypto.DfaAcceptanceAir`), since the AIR currently proves
  over a literal `(state, symbol, next)` grid. This is real circuit + proof work,
  not just plumbing — scope it honestly.
- **RE#'s lookaround machinery is out of scope.** dregg has no lookaround need
  today; the LNF / location-derivative apparatus (`§4.8-4.10`) is the bulk of the
  paper's complexity and buys dregg nothing now. Adopt the derivative *Boolean
  algebra* (`&`, `~`, `|` rules) and the *symbolic alphabet*, not the lookaround
  normal form.
- **`regex-automata` is a model, not a dependency to vendor.** Its PikeVM/hybrid
  code is the reference for the lazy-determinization *strategy*; we do not adopt
  its NFA-direct *runtime* (wrong for STARK) and it gives us no intersection/
  complement anyway (§3.2). The crate confirms the negative result as much as it
  offers a positive one.
- **Don't over-rotate on a problem dregg may not have at scale.** The deployed
  router is 4 states. The explosion is a `FilterTree`-with-deep-intersection
  *latent* risk, not a live fire. The recommendation is sequenced so the cheap,
  always-good piece (symbol classes, lazy compile) lands first and the
  derivative rewrite lands only when an intersection-heavy filter tree actually
  demands it.

---

## 8. Bottom line for the owner's three questions

1. **Is NFA→DFA inefficient (state explosion)?** Yes, *for the
   intersection/complement case* (`FilterTree`), and the in-circuit cost tracks
   the state count directly (the AIR degree grows with `|states|`+`|symbols|`,
   `dfa_routing.rs:196`). Literal route tables don't explode.

2. **Is there an efficient NFA/derivative automaton we can run DIRECTLY
   in-circuit?** **No — running an NFA state-set transition or a derivative
   rewrite *directly in the AIR* loses to the flat-table DFA**, because a STARK
   wants fixed, low-degree, data-independent per-row constraints, and both
   NFA-direct (ε-closure fixpoint, variable active set) and derivative-rewrite
   (unbounded AST manipulation) violate that. The DFA AIR is the right prover.

3. **Evaluate RE#.** RE# is the right *idea in the wrong layer* for the circuit:
   its derivative algebra makes intersection/complement native and lazy — adopt it
   as the **out-of-circuit compiler** that builds the committed DFA table, and
   adopt its **symbolic alphabet** to shrink the in-circuit symbol grid. Do not
   run its derivative step in-circuit.

**So: an NFA/derivative automaton does *not* beat the DFA *in-circuit* for our
patterns — but a derivative-based *compiler* feeding the existing DFA AIR beats the
current eager product-then-determinize *out of circuit*, which is where the
explosion actually lives.**
