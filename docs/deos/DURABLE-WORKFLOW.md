# The durable verified workflow — what a deos app *is*

A deos app is a **cap-mandated, verified, durable workflow**: a multi-step process
that runs to completion exactly once even across crashes (durable, à la DBOS),
where each step is admitted only by a capability its actor actually holds
(attenuable, à la ocap), each step's effect is a verified turn whose post-state the
substrate re-validates before it can become state (unforgeable + conserving, à la
dregg), each step is surfaced to its actor as a fireable affordance (interactive, à
la the web / htmx-on-crack), and the whole process is delegated by one attenuable
**mandate** that bounds what every step in it may do.

`DEOS-APPS.md` §2 names the open question this answers: *"There is no deos app
MODEL… a set of cells exposing affordances, rendered as surfaces, distributed across
the web-of-cells, rehydratable, with agents as first-class users. The framework must
DEFINE that shape."* The shape is **the durable verified workflow** — and it is not a
new construct. It is four established surfaces of the one kernel, observed to be the
same object:

| Borrowed from | The piece | dregg gives it back as |
| --- | --- | --- |
| **DBOS** | durable execution (checkpoint each step; crash → replay; exactly-once) | the verified-write spine, checkpointing **verified turns** instead of opaque step outputs (`pg-dregg/src/workflow.rs`) |
| **ocap** | an attenuable, offline-verifiable, sub-delegable mandate that bounds who may act | the `CompartmentWorkflowMandate` — a charter cell whose admit-table the executor enforces inline (`metatheory/Dregg2/Apps/CompartmentWorkflowMandate.lean`) |
| **zk / the kernel** | every state change is a proof-carrying, conservation-respecting turn | the `Workflow.exec` step + its machine-checked guarantees (`metatheory/Dregg2/Protocol/Workflow.lean`) |
| **the web** | declarative, server-rendered, progressively-enhanced interaction | a workflow step **is** a sequenced cap∧state affordance fire — the deos surface renders the choreography (`metatheory/Dregg2/Deos/WorkflowBridge.lean`) |

> **deos runs on dregg runs in robigalia** (`DEOS.md`). A durable workflow runs on
> the verified state; the surface renders it; the mandate delegates it. Nothing in
> this composition adds authority the kernel does not already prove.

This document teaches what is, in present tense. Each claim is tagged **PROVEN** (a
machine-checked theorem of the Lean metatheory), **ENFORCED** (a runtime gate of the
`pg-dregg` Rust substrate, tested), or **RUNNABLE** (an integrated exemplar you can
execute). The honest scope line is §7.

---

## 1. A workflow step is a verified turn

The atom of the whole construction is one step. Its meaning is fixed by
`Workflow.exec` (`metatheory/Dregg2/Protocol/Workflow.lean:80`): a step commits
**only** when, fail-closed, three conjuncts hold —

1. the actor is the step's `authorizedParty` (the capability/role check —
   `:44`),
2. the workflow is in the step's `precond` phase (the choreography order —
   `:50`),
3. an attestation `verify`s through the `CryptoKernel` portal (the signature — and,
   because it routes through `verify`, it may be a ZK proof: attest authorization
   without revealing the witness).

On commit it advances `precond → postPhase` and appends an attested receipt. The
value proposition is four **PROVEN** theorems over this one definition:

- `exec_authorized` (`:92`) — a step commits only if taken by its authorized party;
  no unauthorized party can ever advance the workflow.
- `exec_in_order` (`:103`) — a step commits only in its required phase; the
  choreography cannot be skipped. Its headline corollary `merge_requires_approved`
  (`:137`): the CI bot can merge only from `approved`, which only the reviewer's
  `approve` produces.
- `exec_attested` (`:114`) — every committed step carries a verified attestation.
- `exec_appends` (`:125`) — a committed step only ever *appends* its receipt; prior
  history is never rewritten (the audit trail is append-only, tamper-evident).

This is the unit the rest of the stack makes **durable** (§4), **delegated** (§3),
**rendered** (§2), and **composed** (§5).

---

## 2. A step *is* an affordance fire — the surface renders the choreography

The web's interaction model is the right UX: a cell declares affordances (named,
typed effect-templates), and an interaction is a verified turn — "the button is a
cap-gated effect, the fragment is the attested post-state surface, and *who may press
it* is decided by held capabilities, not a session cookie" (`DEOS.md`, "htmx on
crack"). The question is whether the workflow choreography and the deos surface are
the *same* object or two things kept in sync. `WorkflowBridge.lean` proves they are
the same object — the surface is the choreography **rendered**, not forked.

The projection (`metatheory/Dregg2/Deos/WorkflowBridge.lean`): each workflow
`StepKind` maps to a deos `GatedAffordance` (`stepGated`, `:165`) whose two gates ARE
the step's two non-crypto teeth —

- **the cap-gate IS the authorization** — `capGate_iff_authorized` (`:174`, **PROVEN**):
  the genuine `Affordance.fireGate` (the proven `required ⊆ held` lattice) passes iff
  the actor is the step's `authorizedParty`. An unauthorized actor holds `[]` and is
  refused.
- **the state-gate IS the phase precondition** — `stateGate_iff_phase` (`:198`,
  **PROVEN**): the genuine `RecordProgram.admitsCtx` (the same executor's state gate)
  admits the cell iff its phase is the step's `precond`.

The two keystones tie it together:

- `workflowStep_is_gatedAffordance` (`:227`, **PROVEN**) — the gated fire commits iff
  the actor is the authorized party AND the cell is in the precond phase. A workflow
  step's `(authorizedParty, precond)` pair **is** a deos cap∧state button.
- `workflow_fires_iff_affordance_fires` (`:251`, **PROVEN**) — the executor step and
  the deos button agree exactly: `exec` commits iff the gated fire commits AND the
  attestation verifies. The crypto leg is the only thing `exec` carries beyond the
  cap∧state button.

The phase *advance* (`precond → postPhase`) is likewise a deos `ReactiveAffordance`'s
`TransitionGate` (`phaseTransition_is_reactiveAffordance`, `:375`, **PROVEN**): a fire
keyed to the *shape* of `old → new`, not a property of `new` alone. Its
`reactive_wrong_phase_refuses` (`:394`) is the choreography edge — you cannot reach
`approved` by a non-`submitted → approved` move.

The refusal teeth carry through in **both polarities** (the bridge does not soften the
guarantees): `gated_cap_fail_is_unauthorized` (`:283`, the cap tooth),
`gated_state_fail_is_out_of_order` (`:297`, the skip tooth), and the headline
`gated_merge_requires_approved` (`:311`) — the `merge` button is *dark* in every phase
but `approved`. The worked 3-party review/CI workflow (author submits → reviewer
approves → CI merges) has biting `#guard` teeth in every corner (`:419`–`:483`):
authorized∧in-phase fires; the wrong actor's button is dark even in the right phase;
the right actor's button is dark in the wrong phase. The module is `#assert_all_clean`
(`:489`) — no `sorry`, no `native_decide`.

So the deos rendering of a durable workflow is the genuine kernel surface: the agent
sees exactly the steps its caps authorize, in the phase the choreography permits.
Progressive enhancement becomes progressive *attenuation*.

---

## 3. The mandate — one attenuable token that delegates the whole workflow

A durable workflow is *delegated*. The delegation is a **charter / mandate**: one
capability cell that bounds what every step in the workflow may do, and that can be
attenuated and sub-delegated like any ocap. `CompartmentWorkflowMandate`
(`metatheory/Dregg2/Apps/CompartmentWorkflowMandate.lean`) is the verified shape of
that mandate on the *real* `RecordKernelState`.

The mandate cell carries a `step_cursor` (a replay-safe `MonotonicSequence` that
advances `+1` per phase) and an immutable `commitment_anchor` binding it to its
compartment. The static charter `charterMandate3` (review → redact → sign) couples
**DAG-prerequisite** checks (`stepAdmissible`) with **compartment clearance**
(`stepClearanceOK` over `Authority/ClearanceGraph`). The mandate's published per-slot
program (`mandateCaveats`, `:54`) bakes the admission table directly into the cell, so
the executor enforces the full DAG ∧ clearance admission **inline** — an out-of-DAG or
under-cleared advance is simply absent from the table and the executor rejects it.

The load-bearing guarantees (the "ungated crown"):

- **Step legality forever** — `cwm_step_legal_forever` (`:133`, **PROVEN**): along the
  *entire* unbounded stream of admitted ticks, under *every* adversarial schedule, the
  cursor stays within the charter.
- **Rejection teeth, fail-closed** — completing a step before its prerequisites is
  rejected (`cwm_illegal_dag_rejected`, `:70`); insufficient clearance is rejected
  (`cwm_clearance_violation_rejected`, `:86`); an illegal cursor *jump* is rejected by
  the executor's caveat on `step_cursor` (`cwm_illegal_dag_rejected_exec`, `:146`).
- **Commit-iff-admit** — `cwm_commit_iff_admit` (`:180`, **PROVEN**): the running
  executor's caveat gate and the off-line admission predicate decide the *same*
  transitions. The internalization is exact — there is no out-of-band policy the
  executor fails to enforce.
- **Conservation** — `cwm_pay_supply_forever` (`:199`, **PROVEN**): along every
  schedule, the payment-asset supply never drifts. Mandate-metadata writes are
  balance-neutral (`cwm_advance_conserves`, `:193`).
- **Compartment binding for life** — the immutable `commitmentAnchorSlot` caveat is
  carried along every forest (`cwmCompartment_traj_carries`, `:285`); the literal
  anchor value is pinned along anchor-safe schedules (`cwmCompartmentStrong_traj_carries`,
  `:302`).

A per-step **spend policy** rides the same charter (Stingray `Slice`): a per-step fee
debits a budget slice, and the budget genuinely exhausts (`cwm_step_fee_fits_slice`
`:333` / `cwm_double_step_fee_exhausts_slice` `:338`). The module pins non-vacuity
with worked `#guard` witnesses (review → redact → sign on a live cell, `:348`–`:400`)
and `#assert_axioms` on every keystone (`:404`).

The mandate is what makes a durable workflow an *ocap*: the right to run the workflow
is a token, the token bounds every step, and **adoption is attenuation** — a delegate
provably holds strictly less than its grantor (the no-amplification discipline, the
kernel's `attenuate_subset`).

---

## 4. Durable execution — DBOS's shape, over verified turns

DBOS gives an application durable execution on PostgreSQL: a workflow's steps are
checkpointed, and after a crash the workflow replays from its last completed step —
exactly-once, no orchestrator, nothing but postgres. That is real and good
(`PG-DREGG-VS-DBOS.md` §2). But a DBOS step is ordinary code issuing an ordinary
`UPDATE`, so DBOS *trusts the writer*: a step with the bug `UPDATE balances SET amount
= amount + 1000000` executes, and DBOS faithfully makes it execute exactly once. Value
is forged, durably.

`pg-dregg/src/workflow.rs` is the durable surface that runs the **same** DBOS shape
where a step is admitted only through the three-gate verified-write spine
(`WorkflowEngine::submit`, `:499`):

1. **GATE 1 — AUTHZ** (`:502`): the acting agent's capability must admit `submit` on
   its cell. This is the real `authz::decide` evaluating exactly the `submit_gate` RLS
   policy (`WITH CHECK (dregg_admits('submit', actor))`), fail-closed on an unbound
   actor.
2. **GATE 2 — CHAIN** (`:537`): the produced `MirrorBatch` must chain onto the durable
   head via the real `RootChain` anti-substitution tooth — accepted only if its ordinal
   is next-expected AND its `prev_root` equals the head root. **ENFORCED**: a
   forged/reordered/substituted batch is refused.
3. **GATE 3 — APPLY + LOG** (`:550`): one logical commit — the in-process state
   advances and the verified turn is appended. In a postgres deployment the chain-gate
   and the `INSERT INTO dregg.commit_log` are the *same* transaction, so a turn is
   durable iff it committed.

A bare `UPDATE` has no way in. The durable variants checkpoint to an external
`DurableLog` (`:755`, the `dregg.commit_log` seam): `run_durable` (`:819`) submits each
step through the full spine and appends the admitted batch the instant it commits;
`resume_durable` (`:831`) skips the already-committed prefix and checkpoints only the
tail; `recover_from_durable` (`:877`) rebuilds the engine from the durable log alone,
**re-validating every persisted turn on the way up** (`try_recover_with` re-runs the
chain tooth — a restored store is self-checking) and resuming at the head. A corrupted
log fails recovery *closed* at the first broken link (`RecoverError::Chain`, `:889`).

So `pg-dregg` is "DBOS, but every step is a verified turn": durable like DBOS, *and*
unforgeable + attenuable + conserving + receipted (`PG-DREGG-VS-DBOS.md` §3, the
property table). The `WorkflowBridge` (§2) and `Workflow.exec` (§1) supply the
*meaning* of one such step; `pg-dregg/src/workflow.rs` supplies the *durable, runnable*
face on the postgres-shaped spine. The same properties are proven by the `#[test]`s in
`src/workflow.rs` and exercised through real pg18 SQL by the `#[pg_test]`s in
`src/lib.rs` (`cargo pgrx test pg18`).

---

## 5. Composition — flows are right-skewed, and refinement is the bar

Durable workflows compose. A **flow** is a state-threaded, nondeterministic
computation built from atomic affordance fires by three operators — **choice** `⊔`
(offer both branches), **sequential composition** `⋆` (do one flow, then the next on
its post-state), and **meet** `⊓` (admit what both admit). `FlowAlgebra.lean`
(`metatheory/Dregg2/Deos/FlowAlgebra.lean`) pins the law of that algebra.

The headline (`flow_choice_right_skewed`, `:467`, **PROVEN**): choice does **not**
fully left-distribute over composition. The half `(P ⋆ R) ⊔ (Q ⋆ R) ≤ (P ⊔ Q) ⋆ R`
holds (`flow_choice_halfdistrib`, `:339`) but the converse fails. dregg's flow algebra
is a **right-skewed Kleene algebra with distributive meets** (RSKA_d⊓, à la Pradic,
arXiv:2408.14999); the distributive meet is discharged here too
(`flow_meet_semilattice`, `:268`).

Why this matters for a *workflow*: the order is **online step-by-step simulation**
(`Flow.Sim`, `:188`), not offline trace language — the simulator commits its branch
*online*, with no lookahead onto which move will be demanded next. The right-skew is
the algebraic shadow of the **reactive rung**: in `(P ⊔ Q) ⋆ R`, `R` runs first and
the `P`-vs-`Q` branch is taken *after*, reading `R`'s output (the late binding —
exactly the `TransitionGate.link` reading `new`); in `(P ⋆ R) ⊔ (Q ⋆ R)` the branch
commits *before* `R` runs. The separation is invisible to a coarser semantics:
`flow_choice_languages_equal` (`:599`) proves both sides denote the *same* trace
language (the dregg form of Pradic's Example 1.1) — a language-only semantics would
*wrongly* conclude the algebra distributes. The skew lives one rung up, in the online
order, and the module pins its non-vacuity (`:603`–`:628`, `#assert_all_clean` at
`:634`).

The payoff (a named follow-on, `FLOW-COMPOSITION-ALGEBRA.md` §Payoff, **not** yet
built): if the flow algebra is right-skewed (it is), then *"does flow/policy A refine
B"* is a decidable question via Pradic's simulation-game characterization of RSKA_d⊓
(Theorem 1.4: `e ≤ f` iff Duplicator wins `SG(∅ | {e} ⊢ f)`). The ARGUS "refines" bar
— *does this protocol evolution refine the spec?* — inherits a decision procedure with
known complexity. This module pins the *precondition* of that payoff as a theorem; the
decision procedure itself is the follow-on.

---

## 6. The integrated story, runnable

`pg-dregg/examples/durable_workflow.rs` is the four surfaces above, integrated and
**RUNNABLE** with no postgres and no live node:

```text
cargo run --example durable_workflow
```

A four-step treasury workflow (treasury mints → funds Alice → Alice spends → Alice
spends more) runs THROUGH the spine, each verified turn checkpointed to a `MemLog`
(the in-process `dregg.commit_log` stand-in). The arc, each beat asserting its
load-bearing property:

1. **Durable run** — four verified turns commit and checkpoint; reads are free SQL over
   the materialized mirror; every turn is receipted (ord0→treasury … ord3→alice).
2. **The unforgeable gate** — an unbound actor (the money-printing bug) is REFUSED by
   AUTHZ (deny-by-default); a bound actor presenting *someone else's* token is REFUSED
   (no amplification — `granted ⊆ held`). The head does not move; nothing leaks.
3. **Crash** — the engine is dropped after two steps; only the durable log survives.
4. **Recovery** — the engine is rebuilt from the log alone, re-validating every
   persisted turn on the way up, resuming at the head.
5. **Exactly-once resume** — the committed prefix is *skipped, never re-applied*; only
   the uncommitted tail runs. Two mechanisms agree: the index-skip (fast path) and the
   chain tooth (the backstop — a stale replay of a committed step cannot chain). The
   end state matches the uninterrupted run exactly.
6. **Conservation** — Σ balances == the genesis total, through crash + recovery +
   resume (value is a property of the verified turn, not a thing a step can fat-finger).
7. **Tampered log** — a substituted durable root fails recovery *closed*, caught as the
   first broken chain link.

This is built entirely ON `pg-dregg/src/workflow.rs` (the `WorkflowEngine`,
`run_durable`, `recover_from_durable`, `resume_durable`, the `DurableLog` seam) — it
does not reinvent any of it. The flagship `pg-dregg/examples/supply_chain.rs` is the
same shape at four-party agentic scale (`PG-DREGG-VS-DBOS.md` §4), and the live-pg
surface is `cargo pgrx test pg18`.

---

## 7. Honest scope — proven vs enforced vs runnable

The strength of each claim is tagged inline above; this is the consolidated line.

**PROVEN (machine-checked Lean, axiom-clean / `#assert_axioms`):** the *meaning* of a
durable verified workflow.

- A workflow step is a capability-gated, protocol-ordered, attested turn, and no
  unauthorized or out-of-order step can ever commit — `Protocol/Workflow.lean`
  (`exec_authorized`, `exec_in_order`, `merge_requires_approved`, `exec_appends`).
- That step IS a sequenced cap∧state affordance fire — the deos surface renders the
  choreography, it does not fork it — `Deos/WorkflowBridge.lean`
  (`workflowStep_is_gatedAffordance`, `workflow_fires_iff_affordance_fires`,
  `phaseTransition_is_reactiveAffordance`).
- The mandate keeps the workflow legal forever, fail-closed on illegal/under-cleared
  steps, conserving, compartment-bound, with commit-iff-admit internalization —
  `Apps/CompartmentWorkflowMandate.lean` (`cwm_step_legal_forever`,
  `cwm_commit_iff_admit`, `cwm_pay_supply_forever`).
- The flow-composition algebra is right-skewed (RSKA_d⊓), the precondition of a
  decidable refinement bar — `Deos/FlowAlgebra.lean` (`flow_choice_right_skewed`,
  `flow_choice_halfdistrib`).

**ENFORCED (the `pg-dregg` Rust substrate, `cargo test` + `cargo pgrx test pg18`):** the
*durable, capability-secure runtime* of one such workflow.

- The verified-write spine (`AUTHZ → CHAIN → APPLY`) is the one door; a forged /
  reordered / substituted batch is refused by the gate, and in postgres by the
  `dregg.commit_log` trigger (`PG-DREGG-VS-DBOS.md` §6, Tier C).
- Durable run / crash-recover (re-validating the chain) / exactly-once resume over the
  `DurableLog` seam — `src/workflow.rs`.

**RUNNABLE (an executable exemplar, `cargo run --example durable_workflow`, green):** the
two integrated, end to end without postgres — `examples/durable_workflow.rs`.

**The honest doc-vs-runnable line.** The exemplar is a faithful executable model of the
verified semantics, not the verified artifact itself. `durable_workflow.rs` drives the
**real** `WorkflowEngine` and its **real** AUTHZ (`authz::decide`) and CHAIN
(`RootChain`) gates — those are the shipped, tested Rust substrate — over an in-process
`MemLog` standing in for `dregg.commit_log`. The *meaning* it choreographs (a step is a
cap∧state-gated, protocol-ordered, conserving turn; recovery is exactly-once) is what
the Lean theorems prove; the exemplar is the durable, postgres-shaped *face* of that
semantics, runnable. It does not claim the postgres layer or the Rust engine is itself
formally verified — that is the in-backend-executor frontier (`PG-DREGG-VS-DBOS.md` §6,
Tier D, the north star, named not done). What is shipped and enforced *today* is the
verified-write **chain** discipline; what is **proven** is the *meaning* of the turn it
carries; the exemplar is where you watch the two meet.

---

## Where it lives

- **Meaning (Lean):** `metatheory/Dregg2/Protocol/Workflow.lean` (the verified step),
  `metatheory/Dregg2/Deos/WorkflowBridge.lean` (step = affordance fire),
  `metatheory/Dregg2/Apps/CompartmentWorkflowMandate.lean` (the mandate),
  `metatheory/Dregg2/Deos/FlowAlgebra.lean` (the composition algebra).
- **Runtime (Rust):** `pg-dregg/src/workflow.rs` (the durable verified-write spine).
- **Exemplar (Rust):** `pg-dregg/examples/durable_workflow.rs` (the integrated story).
- **Companions:** `PG-DREGG-VS-DBOS.md` (the durability comparison),
  `FLOW-COMPOSITION-ALGEBRA.md` (the algebra), `DEOS.md` (the deos brand + the
  htmx-on-crack model), `DEOS-APPS.md` (the app-model gap this answers),
  `WEB-CELLS.md` (the web-of-cells surface a workflow's affordances render into).
