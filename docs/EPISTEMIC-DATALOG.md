# Dregg as a distributed epistemic Datalog — fact, fiction, and the query frontend

*(2026-06-11. Prompted by "dregg is like a distributed epistemic datalog —
fact or fiction?" The answer is substantially FACT, and the line where it
becomes fiction is exactly where dregg's linear-resource layer lives — which
is illuminating, not a flaw. This doc states the split and designs the query
frontend it licenses.)*

## The verdict: substantially FACT

### FACT 1 — the authorization layer is Datalog-descended
The token lineage is macaroon → **biscuit** → the derivation circuit, and
biscuit's caveats/checks ARE Datalog. DREGG3 §0: "the token became the proof
system." `dregg-dsl-runtime` is that Datalog-ish predicate engine. The
policy/caveat language descends from Datalog; it does not merely resemble it.

### FACT 2 — the coordination grading IS the CALM theorem (and it is proved)
CALM (Hellerstein/Ameloot): a distributed computation is coordination-free iff
expressible in **monotone Datalog**. dregg's I-confluence classifier grades
exactly this, and `DreggCalculus.modality_price_monotone` ("grow-only ⇒
coordination-free") is CALM instantiated, machine-checked. The "distributed"
in the phrase is carried by a *proved* monotone-Datalog story.

### FACT 3 — the receipt graph is a distributed, append-only, attested EDB
Strands + receipts are ground facts (attested who-did-what); append-only =
monotone. `AttestedQuery` / non-omission gives what no Datalog DB has: a query
answer that is **provably complete** (`server_cannot_omit` + the MMR index).
A fact-base with proof-of-no-omission.

### FACT 4 — "epistemic" is exact, not decoration
The K/E/D/C tower (`Epistemic.lean`) makes knowledge *constructive*: a fact is
indexed by *who can exhibit a verifying witness*. `K_alice(balance(c,100))`
holds iff alice holds the receipt that proves it. That is epistemic logic
programming — facts graded by provability.

## Where it becomes FICTION (and why that boundary is the good part)

The **executor is not a Datalog engine**: the kernel is 3 verbs + guards with
imperative-guarded state evolution, not Horn-clause fixpoint. And **resources
are linear** — you can *spend* a coin; Datalog facts only accumulate, never
un-derive. Linear resource is exactly what monotone Datalog cannot express.

So the clean statement: **the monotone / epistemic / coordination layer is
Datalog; the linear-resource layer is not — and that non-Datalog half is
precisely the linear-logic / transcendental-syntax thread**
(`docs/TRANSCENDENTAL-SYNTAX-BRIDGE.md`). dregg = epistemic Datalog for
authority-and-queries + a linear substructural layer for resources, meeting at
the guard algebra. The phrase puts its finger on the monotone half exactly.

## The query frontend (buildable on what exists)

A logic-program / query-vs-DB console over the receipt fact-base. The pieces
already exist; this is assembly:

- **The DB**: the receipt/cell fact-base (blocklace + receipts + cell state).
- **The engine**: `dregg-dsl-runtime` (the biscuit-Datalog descendant) as the
  query evaluator over extracted ground facts.
- **The killer feature** (no Datalog DB has it): answers carry `AttestedQuery`
  completeness certificates — *"this result provably omitted nothing."*
- **The query planner is the classifier**: it annotates each query as monotone
  (coordination-free — answerable from any node's partial view, cacheable) vs
  finalized-state-dependent. CALM as a UX affordance.
- **The epistemic surface**: `?- knows(alice, owns(C))` resolves to "alice
  holds a witness," not merely "it's true."

### The fact schema (derived from receipts — the EDB)
Ground predicates extracted from the receipt graph + cell state, e.g.:
`created(Agent, Cell, Height)` · `transfer(From, To, Asset, Amount, Height)` ·
`balance(Cell, Asset, Amount, Height)` · `granted(From, To, Cap, Height)` ·
`revoked(Cap, Height)` · `member(Council, Agent)` · `program(Cell, Predicate)`.
All append-only / height-stamped — monotone by construction.

### Derived predicates (the IDB — rules, stratified)
`owns(X,C) :- created(X,C,_), not transferred_away(C,_).`
`reachable_cap(A,Cap) :- granted(_,A,Cap,_), not revoked(Cap,_).`
`can_certify(Council,Prop) :- member(Council,A), knows(A,Prop) [E_G fold].`
Stratification + the monotone/non-monotone split is decided by the classifier;
negation-over-revocation is the canonical non-monotone (needs finality) case —
the place the UX says "this answer is only as fresh as height H."

### The surfaces
- **CLI**: `dregg query '?- transfer(From, me, A, _), A > 100.'` → answer rows
  + a completeness certificate + the coordination tier.
- **Shell place**: a "Query" console in the starbridge shell — write rules over
  the live receipt graph; results render with the proof-of-completeness badge
  and the monotone/finalized annotation; cross-link rows into the cell/receipt
  inspectors.

### Staging
- **Q1 (prototype, no proofs yet)**: a new `dregg-query` leaf crate — a
  Datalog-ish parser + the fact-extractor over the node's existing
  /api/receipts + /api/cell endpoints + `dregg-dsl-runtime` evaluation. CLI
  `dregg query`. Uncertified answers; the classifier annotation from day one.
- **Q2 (the killer feature)**: wire `AttestedQuery` so answers carry the
  non-omission certificate — a node endpoint serving the MMR-range openings,
  the SDK/CLI verifying them. This is what makes it *dregg's* query layer and
  not just a Datalog-over-JSON toy.
- **Q3**: the epistemic predicates (`knows`/`can_certify`) over the K/E/D/C
  machinery; the shell "Query" place.

Q1 is a contained leaf-crate build; Q2 is the differentiator and reuses the
non-omission machinery already proved. Nothing here is on a flag-day path —
it is additive product surface over verified substrate.
