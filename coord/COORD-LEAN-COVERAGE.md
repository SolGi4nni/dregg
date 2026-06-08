# `dregg-coord` ⟷ verified Lean coverage ledger

This crate's load-bearing coordination semantics are modelled and proved in
`metatheory/Dregg2/Coord/*.lean` and `metatheory/Dregg2/Distributed/EntangledJoint.lean`, with a
Rust differential (`coord/src/coord_diff.rs`, `coord/src/entangled_diff.rs`) pinning that the
verified Lean models ARE the semantics the running code computes. This ledger maps each Rust source
region to its verified model so we can see, at a glance, what is covered and what residual lives only
in Rust.

## The three coordination layers (per `coord/src/lib.rs`)

| Layer | Rust source | Verified Lean | Differential |
|-------|-------------|---------------|--------------|
| **1. Causal chaining** (happened-before DAG) | `types/src/causal.rs::CausalDag` (re-exported `causal::CausalDag`) | `Dregg2/Coord/CausalOrder.lean` | `coord_diff.rs::causal_order_diff` |
| **2a. Atomic forest application** (post-commit fold) | `atomic.rs::Coordinator::commit` → `TurnExecutor::execute` | `Dregg2/Distributed/EntangledJoint.lean` (`jointApplyAll`) | `entangled_diff.rs::atomicity_diff` |
| **2b. 2PC decision** (`evaluate_votes`) | `atomic.rs::Coordinator::evaluate_votes` (`:761-779`) | `Dregg2/Coord/TwoPhaseCommit.lean` | `coord_diff.rs::two_phase_commit_diff` |
| **3a. Per-agent / aggregate non-overspend** (static) | `shared_budget.rs::AgentAllowance::try_debit` | `EntangledJoint.lean` (`tryDebit_invariant`, `totalSpent_le_ceilings`) | `entangled_diff.rs::shared_budget_diff` |
| **3b. Shared-budget dynamics** (resolve/rebalance/ceiling) | `shared_budget.rs::{resolve_with_ordering, rebalance, compute_allowance_ceiling}` | `Dregg2/Coord/SharedBudgetDynamics.lean` | `coord_diff.rs::shared_budget_diff` |
| **3c. Stingray slice (within-epoch concurrent spend)** | `budget.rs::StingrayCounter` | `Dregg2/Proof/Stingray.lean` | (Stingray.lean `#guard`s) |

## What each NEW Lean model proves (the genuinely-uncovered parts this campaign added)

### `Dregg2/Coord/CausalOrder.lean` — Layer-1 happened-before (was UNMODELLED)
Faithful `Dag` (insertion-ordered entries + dep lists) + `insert` (the `MissingDeps`/`Duplicate`/
self-cycle gates of `causal.rs:94-143`); `happenedBefore` = transitive closure of the dependency
edges (= `CausalDag::happened_before`'s backward reachability). Proves:
* **`hb_irrefl` / `hb_trans` / `hb_asymm`** — happened-before is a STRICT PARTIAL ORDER (the
  causal-ordering invariant: a coordinated op is causally after its deps, never circularly before).
* **`insert_wf`** — the dep-presence gate preserves wellformedness (acyclicity) across the whole
  insertion history, not just a snapshot.
* **`hb_imp_index_lt`** — insertion order is a LINEAR EXTENSION of happened-before ⇒
  `topological_order` lists causes before effects (the deterministic Kahn-sort soundness).
* **`fresh_is_maximal`** — a freshly-inserted turn has no successors (the frontier property).

### `Dregg2/Coord/TwoPhaseCommit.lean` — Layer-2 decision machine (was UNMODELLED)
`evaluate` = `evaluate_votes` byte-for-byte over a `Tally` (yes/no/n/threshold). Proves:
* **`evaluate_not_commit_and_abort`** — NO CONFLICTING DECISION (the 2PC agreement): Commit and
  Abort are never both available; every honest replayer of `evaluate_votes` on the same QC reaches
  the same terminal decision.
* **`commit_needs_threshold`** / **`abort_no_late_commit`** — Commit ⇒ real quorum; Abort ⇒ the
  threshold is provably unreachable (max future Yes < threshold — proves `atomic.rs:773`'s comment).
* **`unanimous_commit_iff_all_yes`** — at `threshold = n`, Commit iff all Yes (the bridge to
  `EntangledJoint.jointApplyAll`: the all-or-none fold runs exactly when the 2PC commits).

### `Dregg2/Coord/SharedBudgetDynamics.lean` — Layer-3 dynamics (closes Stingray.lean's named-OPEN)
`resolveOrdered` = `resolve_with_ordering`; `rebalance`; `ceiling = balance*(f+1)/(2f+1)`. Proves:
* **`resolveOrdered_accepted_le_balance`** — TAU-RESOLUTION CONSERVATION (Σ accepted ≤ true balance):
  the property that makes optimistic overspend safe — even when agents collectively overspent, the
  tau-ordered first-wins resolution admits only a balance-respecting set. *This is the conservation
  across the coordination tree.* (`Proof/Stingray.lean` explicitly left this in the OPEN at its §9.)
* **`rebalance_conserves`** — the epoch-close exactly transfers reported spend out of the pool
  (`new_balance + totalReported = old_balance`); no value created/destroyed.
* **`ceiling_le_balance`** + **`overspend_bounded_by_f_ceiling`** — the Stingray Byzantine bound
  (`f * ceiling` worst-case undetected surplus; per-agent ceiling never exceeds the pool).

## Module wiring change (owned by the coord-Lean campaign)

`shared_budget` was an orphan source file (declared in no `lib.rs`). It is now `pub mod
shared_budget;` so the differential exercises the **genuine** `SharedResourceBudget::
resolve_with_ordering` (not a transcription). `coord/src/coord_diff.rs` is the new differential.

## Residual living only in Rust (precise + justified)

* **Ed25519 signature verification** (`Vote::verify_yes`, block-creator keys, spending certificates):
  the named crypto assumption on the Lean side (a cast vote / a report = a *verified* one). We model
  the counting/ordering the protocol does on verified inputs; we do not re-derive signature
  unforgeability. This is the standard, justified crypto residual.
* **Timeout/wall-clock paths** (`Coordinator::check_timeout`, `Participant::has_vote_timed_out`):
  liveness fallbacks keyed on `Instant`; the SAFETY content (abort is sound) is covered by
  `abort_no_late_commit`. Time is out of scope for the safety models.
* **Wire/serde + blocklace plumbing** (`serde_sig`, `extract_debit_for_resource`, virtual-chain
  scans): administrative encoding; the safety reduces to the amounts/verdicts the differential pins.
* **`budget.rs::FastUnlockManager`** (fast-unlock after 2PC abort): an optimization on the abort
  path; its safety is the same `abort_no_late_commit` non-amplification. Not separately modelled.

All Lean modules are `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no
`sorry`/`:=True`/`native_decide`. All differentials are real (run the genuine protocol objects), not
prose.
