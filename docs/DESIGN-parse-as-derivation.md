# DESIGN — Parse as Derivation

**Status:** design + feasibility spike. Marks **BUILT** (deployed, cited `file:line`) vs
**PROPOSED** (this design). Present tense = exists today; "proposed" = to build.

## Thesis

A grammar/template parse *is* a derivation. A CFG production `r : NT → symbols` is a
derivation rule; a leftmost parse (`CfgCompact.Replay`) is a rule-application chain. So a
proof-producing templater does **not** need a bespoke parser circuit — it routes the parse
through the **deployed derivation circuit**, extended to carry the CFG stack in columns.

- **Factor deep:** `N ≤ MAX_STEPS=32` production firings + a depth-`D` stack ride **one** dense
  STARK proof.
- **Fold shallow:** `aggregate_tree` composes chunks only when a chain exceeds the `N` step
  budget (`MAX_DELEGATION_DEPTH=100` total).

This is an **extension of deployed code**, not a greenfield circuit. The rest of this doc
proves that claim against the actual substrate.

---

## The substrate (BUILT — verified at HEAD)

### The single-step derivation AIR
- `circuit/src/derivation_air.rs:11` — `DERIVATION_AIR_WIDTH = 371`. Column map
  (`derivation_air.rs:32` `mod col`): `RULE_ID=0`, `BODY_HASH_START=1..8`,
  `BODY_MEMBERSHIP_START=9..16`, `HEAD_PRED=17`, `HEAD_TERM_START=18..21`, `DERIVED_HASH=22`,
  `SUB_VALUE_START=23..30`, `BODY_ROOT_START=31..38`, then head-substitution selectors and the
  eq/memberof/gte/lt side-condition machinery.
- `circuit/src/dsl/derivation.rs:74` — `derivation_circuit_descriptor()` encodes **C1–C28** as a
  `CircuitDescriptor` (`EXTENDED_TRACE_WIDTH = 379`, `max_degree = 8`, `public_input_count = 6`).
  The load-bearing gate is **C4** (`derivation.rs:113`, `ConstraintExpr::Hash`): `DERIVED_HASH ==
  hash_fact(HEAD_PRED, HEAD_TERM[0..3])`, arithmetized by the real in-circuit Poseidon2 gadget so a
  forged `derived_hash` is UNSAT (`derivation.rs:944` `prove_derivation_p3` routes through the
  audited `p3-batch-stark`).

### The multi-step chain
- `circuit/src/multi_step_witness.rs:18` — `MAX_STEPS = 32`, `:30` `MAX_DELEGATION_DEPTH = 100`.
- `circuit/src/dsl/derivation.rs:968` — `MULTI_STEP_DSL_WIDTH = 384` (379 base + 5 chaining cols).
  `:971` `mod multi_col`: `STEP_INDEX=379`, `ACCUMULATED_HASH=380`, `PREV_ACCUMULATED=381`,
  `IS_FINAL_STEP=382`, `IS_ACTIVE=383`.
- `circuit/src/dsl/derivation.rs:994` — `generate_multi_step_trace_dsl` lays out one 384-col
  derivation row per step and fills the chaining columns from
  `MultiStepWitness::compute_accumulated_hashes` (`multi_step_witness.rs:83`), the linear fold
  `acc_i = hash_2_to_1(acc_{i-1}, derived_hash_i)`.

> **Honest gap in the substrate (matters below).** The multi-step chaining columns are laid out
> in the *trace*, but I could not find a deployed descriptor that *constrains* them.
> `MultiStepDerivationAir::constraints()` returns `vec![]` (`multi_step_witness.rs:146`,
> "Constraints evaluated by DSL runtime"), and no derivation-specific multi-step
> `CircuitDescriptor` wires `Transition`/`ChainedHash2to1` over `ACCUMULATED_HASH`/`STEP_INDEX`.
> So the inter-row accumulator chain for the *derivation* circuit is **columns-present,
> constraints-absent** at the descriptor level today. The primitives to bind it are deployed
> elsewhere (next paragraph); assembling the multi-step derivation descriptor is the **first**
> concrete work item, and the stack extension rides on top of it.

### The inter-row primitives ARE deployed (the decisive precedent)
The DSL constraint language (`circuit/src/dsl/circuit.rs`) has windowed/transition forms, and
they are **used in shipped descriptors**:
- `ConstraintExpr::Transition { next_col, local_col }` (`circuit.rs:135`): `next[next_col] ==
  local[local_col]`, degree 1 (`circuit.rs:827`). Deployed in `note_spending.rs:292`.
- `ConstraintExpr::SeedHash2to1` / `ChainedHash2to1` (`circuit.rs:250`): `next[output] ==
  hash_2_to_1(local[seed], next[input])` — an in-circuit accumulator hash step.
- **`circuit/src/dsl/dfa_routing.rs:126` `dfa_routing_descriptor` — the template.** A deployed
  automaton chain: columns `CURRENT_STATE, SYMBOL, NEXT_STATE, ENTRY_HASH, RUNNING_HASH, IS_FIRST`
  (`dfa_routing.rs:69`). It threads state across rows with `Transition { next_col: CURRENT_STATE,
  local_col: NEXT_STATE }` (`dfa_routing.rs:173`), accumulates with `ChainedHash2to1`
  (`:178`), PI-seeds the chain with `SeedHash2to1` (`:185`), and validates each `(state,
  symbol) → next_state` step with a `TableFunction` transition-table lookup (`:164`).

**dfa_routing is a working, deployed, inter-row state-threaded + accumulated + table-checked
chain.** The stack extension is: *thread `D` stack cells instead of one `CURRENT_STATE`, and let
the "transition table" be the grammar's rule table.* That reframes the whole build as engineering
on a proven pattern.

### The denotational specs (BUILT — proven Lean, circuit-disconnected today)
- `Dregg2/Crypto/CfgCompact.lean:48` — `Replay` (the leftmost pushdown machine as an inductive:
  `done` / `term` (match a terminal on the stack top against the next input token) / `rule`
  (pop nonterminal `r.input`, push `r.output`)). `:81` `compact_sound : ReplayAccepts g rs input →
  input ∈ g.language`. `:90` `compact_to_chain` ties it to `CfgAccepts`.
- `Dregg2/Crypto/Hypergraph.lean:88` — `bridge : (∃ c, Cert R start goal c) ↔ ReflTransGen R start
  goal` (generic reduction). `:134` `cfg_parse_via_reduction` instantiates it at `g.Produces`:
  parse ⟺ reduction chain.
- `Dregg2/Crypto/Handlebars.lean:283` — `render_mem_language : safe T d → render T d ∈
  (handlebarsToGrammar T).language` (template = grammar; safe render ⇒ language member). `:308`
  `injectionFree_of_verify` ties it to the CFG-verifier STARK.
- `Dregg2/Circuit/Emit/DerivationRefine.lean:331` — `derivation_sat_imp_valid` (**the proven
  template** for §3's refinement): a trace satisfying `derivationDesc` witnesses the genuine
  `DerivationStepValid` relation on boundary row 0, under a named Poseidon2 chip carrier
  (`ChipTableSound`) and a range-check envelope (`DerivationCanon`), with concrete
  satisfying/rejecting witnesses for non-vacuity.

---

## 1. The mapping: a grammar-rule firing as a derivation row

A **Datalog** rule-firing row (what the deployed AIR asserts today) says: *the body atoms hash to
membership leaves authenticated against the committed state root `pi[0]`; the head predicate +
terms are the substitution applied to the rule; `DERIVED_HASH = hash_fact(head)`; side conditions
hold.* A **grammar** production firing `r : NT_in → sym_out` needs to assert: *the stack top is
`NT_in`; `r` is a rule of the grammar; the RHS `sym_out` is pushed (popping `NT_in`).*

| derivation column (BUILT) | grammar-rule use (PROPOSED) | fit |
|---|---|---|
| `RULE_ID` (`col:38`) | production id | **direct** |
| `HEAD_PRED` (`col:41`) | LHS nonterminal `NT_in` (the symbol popped) | **adapter** (identity re-read: LHS, not a derived head predicate) |
| `DERIVED_HASH` (`col:43`) + C4 chip | per-step **commitment** `hash_fact(rule_id, NT_in, rhs…)`, folded into the running/accumulated hash | **direct** (reuse C4 verbatim as the step commitment) |
| `BODY_HASH*/BODY_MEMBERSHIP*/BODY_ROOT*` (`col:39,40,45`) + C5/C6b | consumed object = the single stack-top nonterminal; "membership" = "top == `NT_in`" **and** "`r ∈ g.rules`" | **adapter** → the deployed **policy-root** (`derivation_air.rs:259` `compute_policy_root`) / `TableFunction` rule-table lookup (dfa_routing precedent) |
| `HEAD_TERM[0..3]` + `SUB_VALUE*` + substitution selectors (C8/C10) | attributed-grammar term binding (typed holes: a hole's value bound to the production) | **direct, optional** (unused for plain CFG; a bonus for typed templates) |
| `eq/memberof/gte/lt` side conditions (C11–C24) | attribute constraints on a production (e.g. hole-type equality, length bounds) | **direct, optional** |
| **RHS symbol sequence `sym_out` (the push)** | the pushed stack content | **genuine new element** — this is the stack extension (§2); the single-row head (1 pred + ≤4 terms) does **not** carry a variable-length symbol string |

**Verdict on the fit.** The row's *identity + step-commitment* columns fit **directly** (RULE_ID,
LHS via HEAD_PRED, DERIVED_HASH via C4). Rule-membership fits via a **deployed adapter** (policy
root / `TableFunction`, exactly dfa_routing's transition-table check). The RHS/push is **not** a
mismatch — it is the part the deployed single-row circuit was never meant to hold, and it is
precisely what the stack extension adds. Net: **adapter-able, riding a deployed precedent**, with
one honestly-new structural element (the stack).

---

## 2. The stack extension (PROPOSED)

Extend the multi-step layout (`multi_col`, currently 5 chaining cols) with a bounded stack.

**New columns** (appended after `MULTI_STEP_DSL_WIDTH = 384`):
- `STACK[0..D-1]` — `D` symbol-id cells (top at index `0`). `D` = max supported nesting depth.
- `STACK_DEPTH` — current depth (pointer), range-checked `0 ≤ STACK_DEPTH ≤ D`.
- `STEP_KIND` — selector in `{rule, term, done}` (two binary flags, à la `IS_FINAL_STEP`).
- `PUSH[0..W-1]` — the RHS buffer, `W` = max RHS length; `PUSH_COUNT` ≤ W.
- `INPUT_POS` — input-tape pointer; the input word is a PI-committed tape (or a
  `SeedHash2to1`-seeded running commitment, as dfa_routing commits its route).

**New constraints** (all from deployed `ConstraintExpr` variants):
- **`rule` step** (`STEP_KIND = rule`, gated):
  - top matches LHS: `STACK[0] == HEAD_PRED` (a `Gated` `Equality`, exactly C12's shape).
  - `r ∈ g.rules`: `TableFunction` lookup `(RULE_ID) → (NT_in, rhs…)` (dfa_routing `:164`).
  - **stack threading** (the heart): `next.STACK` = `local.STACK` with `STACK[0]` popped and
    `PUSH[0..PUSH_COUNT)` pushed. For fixed `D, W` this is a family of `Transition`-style
    gated equalities `next[STACK[i]] - shift_i(local.STACK, PUSH) == 0`
    — the multi-cell generalization of dfa_routing's single `Transition{CURRENT_STATE ←
    NEXT_STATE}` (`:173`). `STACK_DEPTH` updates by `−1 + PUSH_COUNT`.
- **`term` step** (`STEP_KIND = term`, gated): `STACK[0]` is a terminal equal to the input token
  at `INPUT_POS` (equality gate against the input-tape lookup); pop (`next.STACK` = shift-down);
  `INPUT_POS` advances by 1 (`Transition` on the pointer).
- **`done` step**: `STACK_DEPTH == 0` and `INPUT_POS == input_len` (boundary PI pins, C6-shaped).
- **accumulator (reused verbatim):** `ACCUMULATED_HASH` keeps folding `DERIVED_HASH` (now the
  production-step commitment) via `ChainedHash2to1` — **orthogonal** to the stack columns.

**Cost.** Extra columns `≈ D + W + 3` (e.g. `D=16, W=4` → ~23 new cols on top of 384 ≈ **407**).
Degree: the stack-threading equalities are degree 1 (`Transition`) → +1 under `Gated` = degree 2,
well under the descriptor's `max_degree = 8` (`derivation.rs:699`). The `TableFunction` rule-table
lookup and the input-tape lookup are the same complexity class dfa_routing already ships.

**Is it an extension of the deployed chain?** Yes. dfa_routing proves inter-row state threading +
accumulator + table lookup is a deployed pattern; the multi-step derivation trace already lays out
`STEP_INDEX/ACCUMULATED_HASH/IS_FINAL_STEP/IS_ACTIVE`. The stack is "`D` threaded cells instead of
one." **Caveat (from the substrate gap):** the multi-step *derivation* accumulator constraints
must be authored first (they are columns-present/constraints-absent today) — dfa_routing is the
line-for-line template. That authoring is step 1; the stack columns are step 2 on top.

---

## 3. The refinement (PROPOSED) — the SAT⇒SEM tie-back

Shape mirrors `DerivationRefine.derivation_sat_imp_valid` (`DerivationRefine.lean:331`), but the
parse bridge is **multi-row inductive** where the derivation refinement is single-boundary-row.

**New per-row relation `ParseStepValid` (analogue of `DerivationStepValid`, `:125`):** a row env
witnesses a valid `Replay` step — `rule`: `STACK[0] = NT_in ∧ rule ∈ table ∧ next.STACK = pop∘push`;
`term`: `STACK[0] = input[INPUT_POS] ∧ next.STACK = pop ∧ next.INPUT_POS = INPUT_POS+1`; `done`:
depth 0, input consumed. Extracted per-gate exactly as §4 of `DerivationRefine` extracts C1–C24
(`der_gate0`, `der_pi0`, `bin_of_gate`, `eq_of_modEq_canon`, the `DerivationCanon` range envelope,
the `lift_cN` membership plumbing — **all reused**).

**The whole-descriptor bridge `parse_sat_imp_replay` (NEW):**
```
Satisfied2 hash parseDesc … t  ∧  ChipTableSound …  ∧  RuleTableSound …
  →  Replay g (rulesOf t) (inputOf t) [Symbol.nonterminal g.initial]
```
Then compose with the **proven** denotational stack:
- `CfgCompact.compact_sound` (`CfgCompact.lean:81`) → `input ∈ g.language`.
- `Hypergraph.cfg_parse_via_reduction` (`Hypergraph.lean:134`) → the reduction chain.
- `Handlebars.render_mem_language` / `injectionFree` (`Handlebars.lean:283,296`): the parse
  certificate is the **converse witness** to safe-render — it supplies the `∃ d` decomposition
  named as the round-trip RESIDUAL in `Handlebars.lean:326`. (Uniqueness still needs the
  delimiter-guarded unambiguity side-condition — out of scope for the *soundness* direction.)

**Reused vs new.**
- *Reused:* `Satisfied2` acceptance; the row-gate extraction lemmas + canonicality-envelope
  pattern; the C4 chip carrier (`ChipTableSound`) now over the step-commitment hash; the
  non-vacuity method (concrete satisfying + rejecting witnesses, `witTrace*`); the entire
  `CfgCompact`/`Hypergraph`/`Handlebars` proven layer as the semantic target.
- *New:* the `ParseStepValid` teeth for stack threading + input match; and — the real burden — a
  **multi-row induction** turning per-row `ParseStepValid` into a `Replay` run, with the stack as
  the inductive invariant. `derivation_sat_imp_valid` only fires on row 0; the parse bridge is a
  genuine transition-relation induction across all active rows.

---

## 4. Factor deep, fold shallow

- **Factor deep (dense):** `N ≤ 32` production firings **+** a depth-`D` stack ride **one** STARK.
  Width ≈ `384 + D + W + 3`. Bounds: **nesting depth ≤ D**, **chain length ≤ N** per proof.
- **Fold shallow (aggregate):** a parse with `> N` total firings splits into `⌈firings/N⌉` dense
  proofs; `circuit-prove/src/ivc_turn_chain.rs:3532 aggregate_tree` composes them
  (`MAX_DELEGATION_DEPTH = 100` caps the composed chain). The stack **state** at a chunk boundary is
  carried as a PI (chunk `k`'s final `STACK`/`STACK_DEPTH`/`INPUT_POS` == chunk `k+1`'s initial) —
  the same boundary-PI stitch delegation already uses for `ACCUMULATED_HASH`.
- **The tradeoff, stated:** `D` (width, buys nesting depth) × `N` (width×rows, buys chain length);
  fold multiplies chain length past `N` at aggregation cost. Pick `D` to the grammar's max nesting
  (e.g. bracket/tag depth), `N` to amortize per-proof fixed cost, and fold only when a chain
  exceeds `N`. Do **not** grow `D` for long-but-shallow inputs (that is fold's job) and do **not**
  fold for deeply-nested-but-short inputs (that is `D`'s job).

This is exactly the prompt's discipline: **factor deep** (dense N+stack), **fold shallow**
(aggregate only above budget). Not a per-rule fold, not a DFA (the stack is what a DFA lacks), not
a bespoke pushdown AIR (it is the derivation AIR + threaded stack columns).

---

## 5. FEASIBILITY VERDICT

**A bounded extension of deployed code — weeks for the first slice — with one isolated
multi-month-*risk* item (the multi-row inductive refinement proof), not a multi-month build.**

Why weeks, not months:
- Every **circuit primitive** already ships and is exercised in production descriptors:
  `Transition` (`note_spending.rs:292`), `SeedHash2to1`/`ChainedHash2to1` + `TableFunction`
  (`dfa_routing.rs:164,173,178,185`), the C4 hash-fact commitment (`derivation.rs:113`), the
  multi-step column layout + trace generator (`derivation.rs:994`), the audited prover
  (`prove_vm_descriptor2`), and `aggregate_tree`. **No new prover, field, or FRI.**
- **dfa_routing is a deployed working precedent** for an inter-row state-threaded, accumulated,
  table-checked chain. The stack extension is "thread `D` cells instead of 1" — engineering on a
  proven pattern.
- The **denotational target is already proven** (`CfgCompact.Replay`/`compact_sound`,
  `Hypergraph.bridge`, `Handlebars.render_mem_language`) and shaped for the tie-back.

Hard parts (honest):
1. **The multi-row inductive refinement (§3) is genuinely new.** `derivation_sat_imp_valid`
   extracts on boundary row 0 only; assembling per-row `ParseStepValid` into a `Replay` run is a
   transition-relation induction with the stack as invariant. This is the real proof-effort risk
   (weeks→month).
2. **The multi-step *derivation* accumulator chain is columns-present/constraints-absent today**
   (`MultiStepDerivationAir::constraints() == vec![]`, `multi_step_witness.rs:146`; no derivation
   multi-step descriptor found). Authoring it (from `Transition`/`ChainedHash2to1`, following
   dfa_routing) is a prerequisite step, not free.
3. **Variable-length RHS push.** The single-row head carries 1 pred + ≤4 terms, not a symbol
   string; the `PUSH` buffer + shift constraints are new, and the pop∘push shift is the fiddliest
   arithmetic (bounded `W`, gated by the rule-table row).
4. **Input-tape matching.** A terminal-match step needs an input-tape commitment + pointer +
   advance discipline (new columns; straightforward equality-gate + `Transition`, but new).
5. **Bounded depth `D` is a real expressiveness limit.** Any parse nesting deeper than `D` at some
   point is unprovable in one dense proof (must fold, carrying stack state across the seam).
   `D × N` sets the width×length envelope.
6. **Uniqueness/ambiguity is *not* needed for soundness** (parse-cert ⇒ membership), but the
   templater's full round-trip (`Handlebars.lean:326` residual) still needs delimiter-guarded
   unambiguity — flagged, out of scope here.

**Smallest first slice** (a spike, not the full circuit):
- Fixed **`D = 2`** stack, the **3-rule Dyck grammar already in Lean** (`CfgCompact.lean`
  `Reference`: `S → [S] | ε`), routed through an extended multi-step descriptor of **2–3 rows**
  proving acceptance of `[]`.
- Wire: (a) `TableFunction` rule table; (b) the `D=2` stack threaded by `Transition`-style gated
  equalities (pop∘push); (c) the running commitment via `ChainedHash2to1` (reused); (d) `INPUT_POS`
  advance on the `term` step.
- **Tamper canary** (the gate that makes it real): mutate a stack cell / `RULE_ID` / input token and
  show `Satisfied2` **rejects** — the analogue of `DerivationRefine.witTrace_not_satisfies`
  (`DerivationRefine.lean:598`). Prove SAT for the honest run, UNSAT for each tamper, as a Rust
  differential/tamper test mirroring `circuit-prove/tests/derivation_emit_audit_extra.rs`.
- **Defer** the Lean inductive bridge (§3) to slice 2. Slice 1 is the **circuit spike +
  tamper tests**; it de-risks the whole design by proving the stack threads and the tamper bites
  before any inductive-proof investment.

---

## Appendix — one-line status ledger

| element | status |
|---|---|
| single-step derivation AIR (C1–C28), C4 hash-fact | **BUILT** `derivation.rs:74,113` |
| multi-step column layout + trace generator | **BUILT** `derivation.rs:968,994` |
| multi-step *derivation* accumulator constraints | **GAP** (columns present, constraints absent) `multi_step_witness.rs:146` |
| inter-row `Transition` / `SeedHash2to1` / `TableFunction` primitives | **BUILT & deployed** `dfa_routing.rs:164,173,185`; `note_spending.rs:292` |
| `aggregate_tree` fold | **BUILT** `ivc_turn_chain.rs:3532` |
| `Replay` / `compact_sound` / `bridge` / `render_mem_language` | **BUILT (proven Lean)** `CfgCompact.lean:81`, `Hypergraph.lean:88`, `Handlebars.lean:283` |
| SAT⇒SEM refinement template | **BUILT** `DerivationRefine.lean:331` |
| grammar-rule → derivation-row mapping | **PROPOSED** (§1: adapter-able) |
| bounded-`D` stack columns + threading constraints | **PROPOSED** (§2) |
| multi-row `parse_sat_imp_replay` induction | **PROPOSED, hard** (§3, §5.1) |
| depth-2 Dyck spike + tamper canary | **PROPOSED first slice** (§5) |
