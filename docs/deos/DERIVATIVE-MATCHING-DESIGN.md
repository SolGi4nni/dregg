# dregg's Own Boolean-Closed Derivative-Matching Theory — over `Pred`

Read-only design/research doc. It designs a Brzozowski/Antimirov **symbolic
derivative** theory for matching, **built over dregg's existing `Pred` algebra**
(`metatheory/Dregg2/Exec/PredAlgebra.lean`), proven in dregg's own Lean — using
the Zhuchko–Veanes–Ebner ERE≤ formalization at `~/dev/_research/extended-regexes`
purely as a **proven blueprint / reference architecture**, never as a code
dependency. Nothing in dregg's kernel, effects, circuit, or Lean was changed to
produce it. Several claims are flagged *unverified* / *to-be-checked*; this is a
plan for the owner to decide on, not a landing.

The owner's stance, made precise: **dregg's `Pred` is already the EBA shape**
(a free Boolean algebra over predicate atoms, folded to `Bool` against a
context, closed under `and`/`or`/`not` with the De Morgan + double-negation laws
*already proven* `#assert_axioms`-clean — `PredAlgebra.lean:259-299`). So the
right move is not "adopt ERE≤'s `EffectiveBooleanAlgebra` typeclass and vendor
the `Regex/*` tree" (the route the two prior docs `BOOLEAN-MATCHING-REGROUND.md`
and `ERE-FORMALIZATION-ASSESSMENT.md` assessed, and which carries a hard
NO-LICENSE blocker and a six-minor-version mathlib-bump cost). It is to **prove
the derivative tower over OUR `Pred`, in OUR `Dregg2/*` tree**, with ERE≤'s
finished proof *architecture* as the map of what to prove and how.

The decisive consequence of this re-stance: because we re-prove fresh over our
own carrier, **both blockers the prior docs hit disappear** — there is no
upstream artifact to license (ERE≤ is read, not imported:
`ERE-FORMALIZATION-ASSESSMENT.md` §4.4 / §2 are mooted), and there is no
`v4.24.0-rc1 → v4.30.0` toolchain conflict (everything elaborates against
dregg's pinned mathlib from day one). What we inherit from ERE≤ is *the proof
shape*, which is free to read. What we pay for is re-deriving it over a richer,
stateful carrier — and the one genuinely-new theorem neither side has
(§3 below).

---

## 0. Where this sits relative to the prior docs

| Doc | Stance on ERE≤ | Carrier | Blocker it hit |
|---|---|---|---|
| `BOOLEAN-MATCHING-REGROUND.md` | **adopt** EBA typeclass + vendor `Regex/*` | re-instantiate ERE≤'s `RE α` at dregg σ | NO-LICENSE (§4.4); turn-trace σ unverified |
| `ERE-FORMALIZATION-ASSESSMENT.md` | **port** (vendor + re-elaborate) | same | mathlib 4.24-rc1→4.30 bump; **the middle theorem is absent on both sides** |
| **this doc** | **reference only** — re-prove over `Pred` | dregg's own `Pred` (no `RE α` import) | none from licensing/toolchain; cost is the fresh re-proof + the new finiteness/determinization bridge |

All three agree on the structural facts (the EBA alignment; the in-circuit split
settled by `REGEX-AUTOMATON-EVAL.md`; the missing `derivativeCompile ≡ tableDfa`
bridge). This doc differs only in **how** to get the bridge: not by importing
`correctness`, but by building a dregg-native `der`/`derives`/`correctness` over
`Pred` and then proving the new determinization-equivalence on top of *that*.

---

## 1. `der` / `derives` over dregg's `Pred` (the symbol/location derivative)

### 1.1 The two carriers, side by side

ERE≤'s derivative tower (`Regex/Derives.lean`) is parameterized by an
`EffectiveBooleanAlgebra α σ` and reads **one symbol `a : σ`** per step. Its
predicate leaf is decided by `denote φ a : Bool` (`Derives.lean:72`):

```
der (Pred φ) (_, a::_) = if denote φ a then ε else Pred ⊥
```

dregg's `Pred` (`PredAlgebra.lean:127-183`) is **already** the freely-generated
Boolean algebra (`atom`/`tt`/`ff`/`and`/`or`/`not`/`allOf`/`anyOf` + the typed
leaf atoms), and `Pred.eval : Pred → Value → Value → Bool` (`:190`) is its
denotation. The structural difference that drives this entire design:

> **dregg's `Pred` denotes over a `(old, new) : Value` *transition* (two frames),
> ERE≤'s `denote φ a` denotes over a *single* symbol `a : σ`.**

So before a derivative theory exists, we must choose what "the symbol the
derivative reads" *is* for dregg. There are two faithful choices, and the design
deliberately separates them (the first is the safe, primary one):

- **σ := `Value` (a single frame), `Pred` used statelessly.** A `Pred` whose
  atoms read only the `new` frame (`symEq`/`digEq`/`symMemberOf`/`memberOf`/the
  range/affine atoms — every atom that ignores `old`) is exactly a `σ → Bool`
  predicate over `σ := Value`. This is the direct re-instantiation of ERE≤: the
  derivative reads one `Value` at a time, the leaf test is `Pred.eval φ
  (.record []) a` (old = empty). **This is the primary, safe carrier.**

- **σ := `(old, new) : Value` (a transition pair), `Pred` used statefully.** The
  reactive atoms (`symUnchanged`/`digUnchanged`/`symChanged`/`digChanged`,
  `:169-182`) genuinely read both frames. To match a *sequence of turns* with
  these, the symbol the derivative consumes must *be* the pair `(prevFrame,
  curFrame)`, and the automaton must thread the previous frame as residual
  state. This is the speculative carrier (§5); it is where the right-skew risk
  lives, and it is explicitly NOT part of the load-bearing first cut.

The rest of §1–§4 is written for **σ := `Value` (the stateless single-frame
carrier)** unless noted. §5 handles the stateful lift as a separate, gated
research stage.

### 1.2 The regex layer dregg must add (the genuinely new inductive)

`Pred` is a Boolean algebra over *one frame*. It has no sequencing. To get a
matcher over `List Value`, dregg needs a **regex-over-`Pred`** inductive — the
analog of ERE≤'s `RE α`, but with `Pred` as the leaf instead of an abstract
`α`. Proposed (a dregg-native decl, NOT an import of `RE`):

```lean
inductive PredRE where
  | ε                              -- empty match
  | sym   (φ : Pred)               -- one frame satisfying φ   (ERE≤'s `Pred φ`)
  | alt   (l r : PredRE)           -- ⋓
  | inter (l r : PredRE)           -- ⋒   (native intersection — the FilterTree product)
  | cat   (l r : PredRE)           -- ⬝
  | star  (r : PredRE)             -- *
  | neg   (r : PredRE)             -- ~   (native complement — the missing deny-filter)
```

This is **ERE≤'s `RE α` minus the four lookarounds**. dregg has no lookaround
need today (`REGEX-AUTOMATON-EVAL.md §7`; the prior docs concur), and dropping
them is a major simplification: the entire `existsMatch` mutual-recursion, the
`lookaround_height` subtype on `der`, the `der_termination_metric`'s 0/1 Nat
trick, and the four `derives_Look*` lemmas all vanish. The termination metric
collapses from ERE≤'s 4-tuple lex (`Metrics.lean:109`) to ERE≤'s simpler
`star_metric : Nat ×ₗ Nat` (`Metrics.lean:46`) alone. **This is a re-instantiation
that is strictly easier than the source**, because we instantiate to the
lookaround-free fragment that ERE≤ already supports as a sub-case.

`sym φ` carries a *whole `Pred`*, not an EBA atom — so the boolean closure of
`Pred` (the De Morgan / double-negation laws already proven) sits *inside* the
leaf, and the regex layer adds the *orthogonal* sequence-level Boolean closure
(`inter`/`neg` over `PredRE`). Two Boolean layers, cleanly separated: per-frame
predicate closure (have it, proven) and per-sequence regex closure (new).

### 1.3 `null` / `der` / `derives` — direct re-instantiation vs what differs

**`null : PredRE → Bool`** (nullability — does the regex match the empty word).
Direct re-instantiation of `Derives.lean:27`, minus lookarounds and minus the
location argument (without lookarounds, nullability is *location-independent*):

```lean
def null : PredRE → Bool
  | .ε        => true
  | .sym _    => false
  | .alt l r  => null l || null r
  | .inter l r => null l && null r
  | .cat l r  => null l && null r
  | .star _   => true
  | .neg r    => !(null r)
```

**Difference from ERE≤:** ERE≤'s `null` takes a location `x` because lookarounds
make nullability context-dependent (`null (?= R) x = existsMatch R x`). Ours
does not — a strict simplification.

**`der : Value → PredRE → PredRE`** (the symbol/location derivative). The direct
re-instantiation of `Derives.lean:65`, with the leaf decided by `Pred.eval`
instead of `denote`, and **no height-bounded subtype** (we have no lookaround, so
`der` does not appear inside a mutual `existsMatch`, so the well-foundedness
trick that forces the `{r // lookaround_height r ≤ …}` subtype is unnecessary):

```lean
def der (a : Value) : PredRE → PredRE
  | .ε        => .sym .ff                         -- ε has no derivative → ∅
  | .sym φ    => if φ.eval (.record []) a then .ε else .sym .ff   -- the leaf: Pred.eval, old = empty
  | .alt l r  => .alt (der a l) (der a r)
  | .inter l r => .inter (der a l) (der a r)       -- native intersection (FilterTree's `&`)
  | .neg r    => .neg (der a r)                     -- native complement (the deny-filter `~`)
  | .cat l r  => if null l
                 then .alt (.cat (der a l) r) (der a r)
                 else .cat (der a l) r
  | .star r   => .cat (der a r) (.star r)
```

| Arm | vs ERE≤ (`Derives.lean`) | Verdict |
|---|---|---|
| `ε`, `alt`, `inter`, `neg`, `cat`, `star` | **identical shape** (`:67,84-97`) | direct re-instantiation |
| `sym φ` leaf | `φ.eval (.record []) a` replaces `denote φ a` (`:72`) | re-instantiation; the ONLY semantic swap |
| return type | plain `PredRE`, not the height subtype (`:65`) | **simpler** — no lookaround mutual recursion |
| `null` arg | none (location-free) | **simpler** |
| lookarounds | dropped | **simpler** — 4 ctors + `existsMatch` + 4 lemmas gone |

**`derives : List Value → PredRE → Bool`** (iterate `der` along the word, then
check `null`). Direct re-instantiation of `Derives.lean:107`:

```lean
def derives : List Value → PredRE → Bool
  | [],      R => null R
  | a :: as, R => derives as (der a R)
```

terminating trivially on the list (`derives` recurses on a structurally smaller
list — no metric needed; ERE≤'s `termination_by sp.2.1` is the same idea over a
span).

**The denotational semantics (`⊫`, the spec side).** Re-instantiate ERE≤'s
`models`/`⊫` (`Models.lean`) for `PredRE` over `List Value` — a `Prop`-valued
matching relation: `ε` matches `[]`; `sym φ` matches `[a]` iff `φ.eval ∅ a`;
`cat` splits the word; `star` is the finite-iteration union; `inter`/`alt`/`neg`
are set ∩/∪/complement of the matched languages. Because we have no lookarounds,
this is the *classical* regex denotation, simpler than `Models.lean`'s
span-indexed one.

### 1.4 What is genuinely re-used vs re-proven (the honest split)

- **Re-used as *blueprint* (read-only, no import):** the *shape* of `null`/`der`/
  `derives`, the `cat` nullability split, the `star → cat (der r) (star r)`
  unfolding, and crucially the **correctness proof architecture** (§4).
- **Re-instantiated (mechanical):** the leaf swap `denote φ a ↦ φ.eval ∅ a`.
- **Re-proven fresh over `Pred` (the work):** every `derives_*` lemma and
  `correctness`, because they are stated over *our* `PredRE`/`Pred`/`List Value`,
  not ERE≤'s `RE α`/`Span σ`. They are *easier* than ERE≤'s (no lookaround
  cases) but they are not free — Lean does not transport a proof across a
  different inductive. This is the "re-derive, don't import" cost, and it is
  bounded (the lookaround-free fragment).

---

## 2. Re-grounding the FilterTree: intersection / complement as `der`-constructors

### 2.1 What the FilterTree does today, and the two gaps

`dfa/src/filter.rs:88` `FilterTree` composes filters by **intersection along
every root→leaf path**: `compile_subtree` (`:134`) folds children via
`dfa_intersection` (`compiler.rs:619`), the explicit **product construction**.
`revoke` (`:125`) flips a node to accept-all and `compile_combined` rebuilds.
Two facts about the current code:

- **Intersection is an eager DFA product.** A k-deep tree is a k-fold product,
  `O(∏|S_i|)` states — the genuine state-explosion site
  (`BOOLEAN-MATCHING-REGROUND.md §1.3`).
- **Complement does not exist.** `Pattern` (`compiler.rs:369-395`) has
  `All`/`Any`/`PrefixOf` but **no `Not`** — a capability-secure *deny* filter
  ("match everything except a revoked namespace") is *inexpressible* today.

### 2.2 The re-grounding

In the derivative theory, **intersection and complement are constructors in the
derivative, not a separate product/determinize pass** — this is the whole point
of choosing derivatives (cf. ERE≤ `der (L ⋒ R) = der L ⋒ der R`,
`der (~ R) = ~ der R`, `Derives.lean:89-97`):

```
der a (inter l r) = inter (der a l) (der a r)     -- replaces dfa_intersection's product
der a (neg r)     = neg   (der a r)               -- the NEW deny-filter, no analog today
```

The FilterTree re-ground:

- A `FilterNode`'s filter becomes a `PredRE` (over `σ := Value`, or over `σ :=
  byte` for the routing alphabet — see below), not a compiled `Dfa`.
- `compile_combined` becomes a fold with the `inter` constructor (`revoke` = drop
  the node from the `inter`, exactly as today it flips to accept-all).
- A revoked-namespace deny-filter becomes `inter base (neg revokedNS)` — newly
  expressible.
- **The flat `Dfa` is still emitted** by determinizing the derivative automaton
  (§3) — so the in-circuit DFA-AIR (`circuit/src/dsl/dfa_routing.rs`,
  `metatheory/Dregg2/Crypto/Dfa.lean`) **is untouched**. The derivative lives in
  the *compiler*; the table-DFA lives in the *circuit*. This is the split
  `REGEX-AUTOMATON-EVAL.md` already settled and the prior docs adopt wholesale.

> **The in-circuit DFA stays exactly as-is.** `Dfa.lean`'s `dfa_bridge`
> (`:134`), `DfaAccepts` (`:66`), the `Statement`/`DfaVerifierKernel`/
> `dfa_verify_sound` (`:191`) cascade, and the deployed AIR all consume a flat
> `δ`/transition table. Nothing in this design edits them. The derivative theory
> is a *new way to build the table*, proven equivalent to the old way (§3) so the
> table is byte-identical and the AIR proof transfers verbatim.

### 2.3 The byte alphabet vs `Value` alphabet

For the **routing/gossip FilterTree** the alphabet is bytes (the table is
`[state*256+byte]`, `compiler.rs:35`). Here `σ := byte` and the `sym` leaf is a
byte-class predicate (`Range(low,high)` is a `Pred` over a byte). This is the
*directly endorsed* path (`REGEX-AUTOMATON-EVAL.md §6` symbol-classes;
`BOOLEAN-MATCHING-REGROUND.md §4.2(1)`) — dregg's routing alphabet *is* the
derivative theory's Σ, and it needs no stateful `(old,new)` carrier. The
`Value`-frame carrier (§1.1) is for the *policy/caveat* face (§5), not routing.

---

## 3. The load-bearing new theorem: `derivativeCompile ≡ tableDfa`

This is the theorem **neither side has** (`ERE-FORMALIZATION-ASSESSMENT.md` §3:
"the middle theorem doesn't exist… months, not days"; `BOOLEAN-MATCHING-REGROUND.md`
§3 "the honest open gap"). It is the entire reason to do the Lean work, and it is
where the *honest difficulty* lives.

### 3.1 The statement (precise, over `Pred`)

Two halves, chained through three edges:

**Edge A (re-proven fresh, §4) — `correctness`:**
```lean
theorem correctness (R : PredRE) (w : List Value) :
    derives w R = true ↔ Matches w R       -- ⊢ ↔ ⊫, over PredRE / List Value
```
the dregg-native re-instantiation of ERE≤'s `correctness` (`Correctness.lean:375`).

**Edge B (the genuinely new development) — derivative-finiteness + determinization:**
```lean
-- The set of derivatives reachable from R, quotiented by similarity ~ (ACI: associativity,
-- commutativity, idempotence of alt/inter), is FINITE.
theorem der_finite (R : PredRE) :
    (reachableDerivs R).Finite                         -- Brzozowski finiteness, up to ~

-- The derivative automaton: states = similarity-classes of derivatives, δ = der, accept = null.
def derivativeDfa (R : PredRE) (alphabet : List Value) : TableDfa := …

-- It accepts EXACTLY `derives`:
theorem derivativeDfa_correct (R : PredRE) (w : List Value) :
    (derivativeDfa R Σ).run w ∈ accepting ↔ derives w R = true

-- And it is EQUAL (same δ table, same accepting set) to the powerset DFA dregg's
-- compiler.rs builds from the equivalent Pattern:
theorem derivativeCompile_eq_tableDfa (R : PredRE) :
    (derivativeDfa R Σ).normalize = (patternOf R).compile.toTableDfa   -- ≡ compiler.rs powerset DFA
```

**Edge C (already proven, `Dfa.lean`) — `dfa_bridge`:** the table-DFA AIR accepts
iff `DfaAccepts δ q₀ accept trace` (`Dfa.lean:134`).

Chaining A ∘ (B's `derivativeDfa_correct` + `derivativeCompile_eq_tableDfa`) ∘ C
gives the end-to-end statement dregg wants: **the boolean semantics of the
compiled table is trusted** — "does this `δ` table really equal `R & ~S`?" is now
a theorem, not an untrusted Rust gap under an otherwise-clean AIR proof.

### 3.2 The proof strategy

1. **`der_finite` (the hard core).** The classic Brzozowski result:
   syntactically distinct derivatives are infinite, but **up to similarity ~
   (associativity/commutativity/idempotence of `alt`/`inter`, and the `~~R ≃ R`,
   `∅`-absorption rules)** there are finitely many. Strategy: define a
   normalization `norm : PredRE → PredRE` (a confluent ACI-rewrite to a canonical
   form), prove `der a R ≃ der a (norm R)` and `norm` has finite range on the
   derivative-closure of any fixed `R`. This is the part ERE≤ *deliberately does
   not prove* (`ERE-FORMALIZATION-ASSESSMENT.md` §3: ERE≤ "never bounds the
   *number* of distinct derivatives") — and it is the part the *later* repo
   `ezhuchko/finiteness-derivatives` (ITP'25) handles, but **over ERE≤'s `RE α`,
   not our `PredRE`** — so even that artifact is reference-only here.

2. **`derivativeDfa_correct`.** Once states are finite similarity-classes, the
   automaton is well-defined; correctness against `derives` is an induction on
   `w` using `der`'s definition and `null` at the end — this *does* transport
   cleanly from Edge A's lemmas (it is essentially "running the DFA = iterating
   `der`," which is the definition).

3. **`derivativeCompile_eq_tableDfa` (the determinization-equivalence — the
   second hard core).** Prove the derivative-class automaton and dregg's
   *powerset-of-NFA-states* automaton (`compiler.rs:determinize`) are the **same
   minimal DFA** (both are reachable-state-minimal w.r.t. the same language).
   Strategy: prove both recognize the same language (Edge A + the powerset DFA's
   own correctness — itself currently *unproven Rust*, a sub-gap), then invoke
   DFA minimization uniqueness.

   > **Update — the subset/determinization factor is now mechanized**
   > (`metatheory/Dregg2/Crypto/Deriv/Thompson.lean`). The `pattern_to_nfa().
   > determinize()` pipeline factors as *Thompson-construction correctness ∘
   > subset-construction correctness*. The right factor — `compiler.rs::Nfa::
   > determinize` = the ε-closure powerset construction — is closed end-to-end by
   > importing mathlib's *verified* `εNFA.toNFA_correct` (ε-elimination) +
   > `NFA.toDFA_correct` (subset construction): `determinizedTable_accepts` proves
   > the deployed flat-table fold (`ofDFA`, = mathlib `DFA.eval`) recognizes
   > exactly the Thompson ε-NFA's language, and `legacy_determinized_faithful`
   > carries that to `Matches`-faithful via `correctness`, generic over the
   > `Set σ` subset-state space (`tableDfa_faithful'`). The remaining LEFT factor
   > is isolated as the single obligation `ThompsonRecognizes M R := ∀ w, w ∈
   > M.accepts ↔ derives w R` — Thompson-construction correctness — which mathlib
   > does **not** provide (it routes regex→language through Brzozowski derivatives,
   > not Thompson). It is shown *inhabited* (non-vacuous) by `symENfa_recognizes`
   > for the canonical single-symbol automaton, but the inductive
   > `accepts (thompson R) = Matches R` over the concat/star/union sub-automata
   > (the ε-closure-across-the-join reasoning) is the genuine remaining wall.

   **Honest sub-risk:** dregg's `determinize` is
   *not* minimized (it is reachable-subset, which can have non-minimal states),
   so the equality is up to a state-bijection on the reachable fragment, not
   literal table equality — the theorem likely reads `…  ≃  …` (language/bisim
   equivalence) rather than `=`, which is **enough for the AIR**: the AIR proof
   (`Dfa.lean`) is *table-opaque* (`BOOLEAN-MATCHING-REGROUND.md §3`: "it does
   not care *how* the table was built"), so language-equivalence of the emitted
   table suffices to transfer it.

### 3.3 Honest difficulty

- **Months-scale, two hard theorems** (`der_finite` + the determinization
  equivalence), exactly as `ERE-FORMALIZATION-ASSESSMENT.md` §4 rates them —
  *and that rating was for the easier import route*. Re-proving over the richer
  `Pred` carrier is **at least as hard**, with one mitigation (no lookarounds)
  and one aggravation (a `Value`/transition leaf is heavier than a `Char` leaf).
- **Two state representations must be reconciled** (`ERE-FORMALIZATION-ASSESSMENT.md`
  §4.2): "derivative-class up to similarity" vs "set of NFA states." The
  similarity/normalization quotient is where derivative-DFA proofs classically
  get hard. This does not get easier by owning the carrier.
- **A sub-gap inside the gap:** `compiler.rs`'s powerset `determinize` is itself
  *unverified Rust*. The clean end-to-end theorem ideally re-proves (or models)
  the powerset construction in Lean too, OR routes everything through the
  derivative automaton as the *single* source of truth and deletes the powerset
  path for the matched-language claim. The latter is cleaner but is a Rust
  rewrite, not just a proof.
- **What is genuinely tractable:** Edges A and C, and `derivativeDfa_correct`
  (step 2). The wall is `der_finite` (step 1) and the determinization
  equivalence (step 3).

---

## 4. Port-as-reference: what transfers from ERE≤'s proof architecture

ERE≤ is read as a **map of the proof**, not a dependency. What transfers:

### 4.1 Transfers as architecture (re-prove the same shape over `Pred`)

- **The `correctness` induction structure** (`Correctness.lean:375-422`):
  induction on the regex with `termination_by star_metric R`, discharging each
  constructor via a dedicated `derives_<ctor>` lemma. We re-prove
  `derives_Alt`/`derives_Inter`/`derives_Negation`/`derives_Cat`/`derives_Star`/
  `derives_Eps`/`derives_Pred` — the **seven we keep**, dropping the four
  `derives_Look*`. The proofs of these seven over `PredRE` follow the ERE≤
  proofs of the same seven nearly line-for-line (they never touch lookarounds).
- **`star_metric` termination** (`Metrics.lean:46`, `star_metric : Nat ×ₗ Nat`):
  re-instantiates *directly* for `PredRE` — `star`/`cat`/`alt`/`inter`/`neg` have
  identical metric arms (`Metrics.lean:50-58`), and the `star_metric_<ctor>`
  decrease lemmas (`Metrics.lean:225-319`) re-prove unchanged. **We drop the
  entire `der_termination_metric` 4-tuple** (`Metrics.lean:109`) and the
  `lookaround_height` machinery (`Metrics.lean:30`) — they exist *only* for the
  `der`-inside-`existsMatch` mutual recursion, which we do not have.
- **The `derives_Cat` split proof** (`Correctness.lean:241-287`): the most
  intricate lemma (the `null l` case-split, the `u₁/u₂` word-split induction).
  Re-proves over `PredRE`/`List Value` with the *same* structure; this is the
  one lemma where the reference is most valuable (it is fiddly and ERE≤ has it
  finished).
- **The `derives_Negation` Boolean step** (`Correctness.lean:229`): trivial over
  our carrier because `Pred`'s `eval_not`/`eval_not_not` (`PredAlgebra.lean:263,
  266`) are *already proven* — the Boolean-algebra ground the negation lemma
  stands on is in place, unlike ERE≤ which leans on mathlib's `BooleanAlgebra`.

### 4.2 Must be re-proven fresh (no transfer)

- **Everything, formally** — Lean does not transport a proof across `RE α →
  PredRE`. "Transfers as architecture" means *the human reads the ERE≤ proof and
  writes the analogous dregg proof*, not that `lake` reuses anything.
- **The `sym φ` leaf lemmas** (`derives_Pred`, `Correctness.lean:35`): re-proven
  with `Pred.eval` and `Pred.eval_*` admit-characterizations (`PredAlgebra.lean:
  310-405`) replacing `denote`. The `Pred` admit-chars are an *asset* here — they
  give the leaf's truth condition as a proven `iff` for free.
- **`der_finite` + `derivativeCompile_eq_tableDfa` (§3):** **NOT in ERE≤ at all.**
  No transfer of any kind — these are net-new theorems. The ITP'25
  `finiteness-derivatives` repo is the *reference* for `der_finite`'s strategy,
  but it too is over `RE α` and must be re-instantiated.

### 4.3 The clean win from owning the carrier

Because `Pred`'s Boolean laws are *already* `#assert_axioms`-clean
(`PredAlgebra.lean:680-706`), the leaf-level Boolean reasoning that ERE≤ imports
from mathlib's `BooleanAlgebra` is, for us, *dregg-native and already proven*. We
do not inherit mathlib's full `Order.BooleanAlgebra` weight at the leaf — only at
the regex-`star_metric` `Prod.Lex` level (a small, bounded mathlib surface, per
`ERE-FORMALIZATION-ASSESSMENT.md` §2: "no exotic mathlib surface"). This is a
real reduction in mathlib dependency versus the port route.

---

## 5. Staged path + honest scope, risks, and the right-skew hazard

### 5.1 Staged path (additive-then-cutover; the circuit never changes shape)

Lands the always-good, low-risk pieces first; the speculative stateful lift last.

- **Stage 0 — `PredRE` + `der`/`derives` + `Matches`, with non-vacuity
  `#guard`s.** Define the inductive and the three functions over `σ := Value`
  (and a `σ := byte` instance for routing); ship `#guard`/`by decide` witnesses
  that `der`/`derives` admit and reject real words (the dregg discipline:
  non-vacuity both polarities, mirroring `PredAlgebra.lean:489-508`). *No
  correctness yet, no circuit touch.* Pure new Lean, disjoint file.
- **Stage 1 — `correctness : derives ↔ Matches` (Edge A).** Re-prove the seven
  `derives_<ctor>` lemmas + `correctness` over `PredRE`, `star_metric`
  termination. This is the bounded, reference-guided port (§4) — weeks, not
  months. Delivers a *verified streaming matcher* (verified, not yet fast).
- **Stage 2 — `Pattern::Not` + derivative `inter`/`neg` compiler (Rust,
  out-of-circuit, the FilterTree payoff).** Add `Pattern::Not` (`compiler.rs`),
  swap the FilterTree's eager `dfa_intersection` fold for the derivative
  front-end emitting the same flat `Dfa`. Deny-filters become expressible. Still
  emits a flat `Dfa`; AIR untouched.
- **Stage 3 — `der_finite` (Edge B, hard core #1).** The Brzozowski
  finiteness-up-to-similarity theorem over `PredRE`. Months. Reference:
  `finiteness-derivatives` (ITP'25), read-only.
- **Stage 4 — `derivativeCompile_eq_tableDfa` (Edge B, hard core #2 + the
  faithfulness close).** The determinization-equivalence (likely up to
  language/bisim, which suffices for the table-opaque AIR). Chains A ∘ B ∘ C into
  the end-to-end "compiled boolean semantics is trusted" theorem. **This is the
  whole reason to do the Lean work.** Months.
- **Stage 5 — the stateful `(old,new)` lift (speculative, gated, last).** Only if
  the σ-instantiation proves sound: lift `Pred` to `σ := (Value × Value)` so the
  reactive atoms work, with the previous frame threaded as derivative residual
  state. This is the policy/caveat-trace unification (`BOOLEAN-MATCHING-REGROUND.md`
  §4.2(2), §4.3 Stage 5) — and the right-skew hazard (§5.3) lives *entirely*
  here.

Stages 0–2 are good independent of the unification (a verified matcher + the
missing deny-filter). Stages 3–4 are the load-bearing faithfulness close. Stage 5
is a genuine open research question, not a foregone conclusion.

### 5.2 What stays exactly as-is

- **The in-circuit DFA-AIR** (`circuit/src/dsl/dfa_routing.rs`, `Dfa.lean`'s
  `dfa_bridge`/`DfaAccepts`/`DfaVerifierKernel`/`dfa_verify_sound`/`dfa_dial_wired`
  cascade, `vk_hash`). The derivative theory feeds the table; it does not replace
  it. (The one exception that *would* touch the circuit — a symbol-class alphabet
  shrinking AIR degree — is `REGEX-AUTOMATON-EVAL.md`'s Stage 1 and is **out of
  scope here**; it is orthogonal circuit+proof work, name-gated as a new
  descriptor, not part of this derivative design.)
- **The cap-authority lattice** (`cell/src/permissions.rs`,
  `token/src/action_set.rs`): no complement, incomparable Custom vk_hashes — not
  a complemented lattice, monotone-by-design. Welding it in would be wrong
  (`BOOLEAN-MATCHING-REGROUND.md §1.2`).
- **The Datalog token-verification path** (`token/src/datalog_verify.rs`):
  stratified deny-rules ≠ algebraic complement; a separate engine. Bridge, don't
  subsume.
- **`Pred` itself** (`PredAlgebra.lean`): unchanged. `PredRE` sits *on top of* it
  with `Pred` as the leaf; the existing `Pred.eval`/closure laws/`PredCaveat`
  executor adapter (`:556-619`) are all untouched and re-used as-is.

### 5.3 The right-skew hazard (the load-bearing soundness risk for Stage 5)

dregg's flow/affordance composition is **proven right-skewed** — a
right-skewed Kleene algebra with distributive meets (RSKA_d⊓):
`flow_choice_right_skewed` (`metatheory/Dregg2/Deos/FlowAlgebra.lean`, committed
`a0dec4932`) proves `(P⋆R)⊔(Q⋆R) ≤ (P⊔Q)⋆R` holds but the **converse FAILS**.
So **choice ⊔ does NOT left-distribute over compose ⋆**. A naive Kleene-algebra /
derivative re-grounding that *assumes full distributivity* would be **unsound for
the reactive rung**.

**Why a derivative matcher does not, by itself, trip this — and the precise line
not to cross.** The subtlety from `FlowAlgebra.lean` (and the memory note) is
exact and decisive here:

> The right-skew separation is **NOT in the trace LANGUAGE** — both sides denote
> the *same set* (`flow_choice_languages_equal`, the dregg Example 1.1). It lives
> in the **online step-by-step simulation** order: the early-branch side must
> commit P-vs-Q *before* R runs (no lookahead), so it cannot *simulate* the late
> side that chooses *after* observing R's output. The right-skew is the algebraic
> shadow of the **reactive rung** (the `TransitionGate`'s old+new read).

A Brzozowski derivative over `PredRE` is a **language/membership** construction:
`derives w R` decides *word membership in the matched language*, and `correctness`
proves exactly `derives ↔ Matches` (a *language* equality). Stages 0–4 live
entirely in the language world, where `(alt)`/`(cat)` *do* satisfy the regex
identities (the matched language of `(P|Q)·R` *is* the union — that is precisely
`flow_choice_languages_equal`). **So the derivative theory is sound exactly
because it stays in the language regime the right-skew leaves alone.**

The hazard is *only* Stage 5, and only if it overreaches. The line not to cross:

- ✅ **Safe (Stages 0–4):** use derivatives to decide *language membership /
  inclusion / equivalence* of `PredRE`s. This is the FilterTree's actual job
  (does this word match this filter) and the `attenuate_narrows` /
  `CaveatPred.refines` *language-inclusion* order — both are language-level.
- ❌ **Unsound if attempted naively (Stage 5 overreach):** use a free-Kleene
  derivative identity to decide the *online simulation / refinement* order of
  reactive flows — i.e. to claim `(P|Q)·R ≃ P·R | Q·R` as *processes*, not as
  languages. The right-skew says that equation is **false at the simulation
  level**. The reactive `(old,new)` carrier of Stage 5 is *exactly* the
  late-binding mechanism the right-skew is the shadow of.
- **The mandated design constraint for Stage 5:** the stateful lift must thread
  the previous frame as **derivative residual state with NO lookahead** (commit
  on each frame as it is read), which is *automatically* the early-binding,
  right-skewed semantics — it physically cannot simulate the late-binding side,
  so it *cannot* accidentally assume the false converse. And the *decision
  procedure* for reactive refinement is **already built and is NOT a
  derivative/Kleene lift**: `FlowRefine.lean`'s `decideRefines` (committed
  `87f7879e7`, sound+complete `decideRefines_iff`, via the simulation-game
  `dupSim_iff_sim`) decides the *simulation* order directly. So Stage 5 must
  **route reactive-refinement questions to `decideRefines`, and use the
  derivative matcher only for language questions** — never conflate the two. This
  is the single most important soundness constraint in the design.

### 5.4 Other honest risks

- **`der_finite` + determinization-equivalence are months, not days** (§3.3) —
  the dominant cost, and not reduced by owning the carrier (only the *licensing*
  and *toolchain* costs are reduced by the reference-only stance).
- **The powerset `determinize` is unverified Rust** (§3.2 sub-gap). The cleanest
  end state routes the matched-language claim through the *derivative* automaton
  as the single source of truth; reconciling it with the deployed powerset table
  is the determinization-equivalence's real content.
- **Verified ≠ fast.** ERE≤'s input-linearity (Thm 4) comes from LNF + .NET
  engineering (mintermization, lazy DFA, prefilters) that the Lean artifact does
  not contain — and we are not even porting the Lean artifact. dregg would own a
  verified-but-naive matcher and all the perf engineering itself
  (`BOOLEAN-MATCHING-REGROUND.md §4.4`).
- **Complement does not escape determinization.** `neg R` is a native derivative
  constructor, but settling it into a *committed* DFA still needs a total
  deterministic automaton; a complement of a deeply-intersected pattern can still
  blow up `num_states`. The `Dfa::table_size_bytes` budget + give-up is the
  safety net, not a proof of small size.
- **The opaque escape arm.** `Pred` atoms that are themselves opaque (the
  witnessed/ZK `Custom{vk_hash}` predicates, `cell/src/predicate.rs`; the
  caveat `opaque` arm) are NOT introspectable — a derivative algebra cannot see
  inside them, so it shrinks but does not eliminate the opaque surface.
- **Don't over-rotate.** The deployed router is 4 states / 4 symbols
  (`dfa_routing.rs`). The explosion is a *latent* `FilterTree`-deep-intersection
  risk, not a live fire. Stages 0–2 (verified matcher + deny-filter) are the
  cheap always-good pieces; Stages 3–5 land only when an intersection-heavy
  filter tree (or the policy-trace unification) actually demands them.

---

## 6. Bottom line

dregg already owns the EBA carrier (`Pred`, with its Boolean laws proven
`#assert_axioms`-clean) and the stable in-circuit trust boundary (the
table-opaque `Dfa.lean` `dfa_bridge`). The **reference-only stance** — re-prove a
lookaround-free derivative tower (`PredRE`/`der`/`derives`/`correctness`) *over
`Pred`*, in dregg's own Lean, using ERE≤'s `Regex/*` as a read-only proof map —
**dissolves the two blockers** the adopt/port routes hit (no licensing,
no toolchain conflict) and inherits the proof *architecture* for free, paying
only the bounded cost of re-deriving the lookaround-free fragment (Stages 0–1,
weeks).

What remains genuinely hard is unchanged by the stance and is the whole point:
the **load-bearing new theorem `derivativeCompile ≡ tableDfa`** (§3) — Brzozowski
**finiteness-up-to-similarity** (`der_finite`) plus the **determinization-
equivalence** to dregg's powerset table — months of real automata theory that
neither codebase has, that bridges "derivative-class" and "powerset-of-NFA-state"
representations, and that makes the compiled boolean semantics *trusted* under
the otherwise-clean AIR proof. The recommendation: land Stages 0–2 (a verified
`PredRE` matcher + the missing `Pattern::Not` deny-filter — good independent of
everything), then invest in Stages 3–4 (the faithfulness close), and treat Stage
5 (the reactive `(old,new)` lift) as a gated open research question whose **single
binding soundness constraint** is the right-skew: derivatives decide *language*
questions, `decideRefines` decides *reactive-simulation* questions, and the two
must never be conflated.

### Cited sources

- ERE≤ blueprint (read-only, no import): `~/dev/_research/extended-regexes/Regex/`
  — `Derives.lean` (`null`/`der`/`existsMatch`/`derives`), `Correctness.lean:375`
  (`correctness : sp ⊢ R ↔ sp ⊫ R`, the per-ctor lemmas), `Metrics.lean:46`
  (`star_metric`), `EBA.lean` (`EffectiveBooleanAlgebra`/`BA`),
  `Definitions.lean:14` (`RE α`). CPP'24, DOI 10.1145/3636501.3636959;
  finiteness in the later `ezhuchko/finiteness-derivatives` (ITP'25, reference
  for `der_finite`).
- dregg's `Pred`: `metatheory/Dregg2/Exec/PredAlgebra.lean` (`Pred` `:127`,
  `Pred.eval` `:190`, Boolean laws `:259-299`, admit-chars `:310-405`,
  `PredCaveat`/executor adapter `:556-619`, `#assert_axioms` `:680-706`).
- The DFA face (unchanged): `dfa/src/filter.rs` (`FilterTree`),
  `dfa/src/compiler.rs` (`Pattern`/`determinize`/`dfa_intersection`),
  `metatheory/Dregg2/Crypto/Dfa.lean` (`dfa_bridge`/`DfaAccepts`/`DfaVerifierKernel`),
  `circuit/src/dsl/dfa_routing.rs` (deployed AIR).
- The right-skew constraint: `metatheory/Dregg2/Deos/FlowAlgebra.lean`
  (`flow_choice_right_skewed`, `flow_choice_languages_equal`, `a0dec4932`),
  `metatheory/Dregg2/Deos/FlowRefine.lean` (`decideRefines`/`decideRefines_iff`,
  `87f7879e7`).
- Prior docs (this doc takes a different stance from): `docs/deos/{BOOLEAN-MATCHING-REGROUND,
  ERE-FORMALIZATION-ASSESSMENT,REGEX-AUTOMATON-EVAL}.md` — adopt/port assessments;
  the in-circuit split they settle is adopted wholesale.
</content>
</invoke>
