# CI Invariants — the enforcing gate for the twin-deletion campaign

`scripts/ci-invariants.sh` institutionalizes the invariants the 2026-07-23/24 twin-deletion +
megaswarm-fix campaign fought for, so the gains become **un-regressable**. It is recommendation ①
of that campaign (`docs/TWIN-DELETION-MAP-2026-07-23.md`,
`docs/MEGASWARM-FLAW-BACKLOG-2026-07-23.md`; memory `project-twin-deletion-campaign`).

It enforces **four** invariants. Each is a hard failure with an actionable message; the script
exits `0` (all pass), `1` (an invariant failed), or `2` (environment problem — a registry or source
file moved, so the gate would otherwise check nothing).

```
scripts/ci-invariants.sh [ all | structural | build | falsifiers | no-ignore | no-twin ]
```

- `all` (default) — all four invariants.
- `structural` — invariants **3 + 4** plus registry existence, **no cargo build**. Runs in seconds;
  this is the always-on required PR check.
- `build`, `falsifiers`, `no-ignore`, `no-twin` — one invariant each.

Two checked-in registries drive it, both under `scripts/ci-invariants/`:

- `falsifiers.tsv` — the security falsifiers (invariants 2, 3).
- `lean-twins.tsv` — the Rust-twin regression guard (invariant 4).

Add a row to a registry to extend the gate; no code edit is needed.

---

## Invariant 1 — THE TREE BUILDS

`cargo check --workspace --all-targets --keep-going`. Zero non-compiling members. `--keep-going`
means the log names **every** failing crate, not just the first, and the gate lists them all. This
is the **dregg-analyzer / PlayerWorlds** class: a default workspace member that silently stops
compiling (co-tenant churn broke `dregg-analyzer` at HEAD during the campaign; a swept mid-flight
`PlayerWorlds` bricked a subtree). A plain `cargo check` stops at the first error and hides the
rest; this one enumerates.

- **Override:** `CI_INVARIANTS_BUILD_ARGS` replaces `--workspace --all-targets` — e.g.
  `CI_INVARIANTS_BUILD_ARGS="-p dregg-analyzer -p dregg-node"` to check a fast subset while the
  workspace build lock is contended.
- **Runtime:** a cold full-workspace check is the heaviest lane in this repo (tens of minutes; the
  same cost as `ci.yml`'s `check` job, which it mirrors). Warm/incremental is minutes. Do **not**
  run it while a co-tenant `cargo`/`lake` build holds the `target/` lock — narrow it with the
  override or run it in the CI job.
- **Do not** delete a crate from the workspace to make this green. A non-compiling member is the
  regression; fix the member.

## Invariant 2 — EVERY FALSIFIER RUNS AND PASSES

Every row of `falsifiers.tsv` **executes and passes** — not merely compiles. The gate:

1. **Existence** — asserts the `#[test] fn` still exists at the declared crate/target. A rename or
   delete is a **FAIL** (missing), never a skip.
2. **Not silenced** — an `#[ignore]` on a registered falsifier is a FAIL (folded from invariant 3).
3. **Runs green** — runs it via `cargo test` and parses libtest output. It must have **executed**
   and printed `... ok`. All of: filtered-to-zero, a compile error, a **setup panic** (the
   stale-fixture class — libtest prints `... FAILED`), or the test binary aborting → **FAIL**. A
   green that ran zero tests is a fail, not a pass.

The whole run forces `DREGG_ALLOW_UNAUDITED_PQ=1` so PQ-touching setups (`dregg-node`,
`dreggnet-game-board`) run their unaudited-PQ fallback instead of aborting in setup — this permits
the fallback to *run*; it weakens no falsifier's assertion (see `dregg-pq/src/audit.rs`).

- **Runtime:** dominated by compiling each distinct `(crate, target)` once (`dregg-node`'s lib +
  the integration-test crates are the heavy ones). Warm, the run itself is seconds per test.
  **Fast subset:** run one crate's falsifiers by temporarily filtering the registry, or just
  `cargo test -p <crate> --lib <fn>` directly.

### The registered falsifiers (22)

| Crate | Target | Test | Guards |
|---|---|---|---|
| dregg-credentials | tests/anonymity_soundness | `cross_credential_predicate_forgery_rejected` | CRITICAL predicate `x==x` forgery refused |
| dregg-turn | lib | `test_cross_asset_excess_netting_rejected` | CRITICAL asset-inflation (per-asset conservation on main path) |
| dregg-node | lib | `rust_tau_twin_forbidden_on_verified_full_node` | twin#8 tau twin forbidden on verified full node |
| dregg-node | lib | `rust_quorum_twin_forbidden_on_verified_full_node` | twin#11 quorum twin forbidden on verified full node |
| dregg-node | lib | `record_requires_root_agreement_not_bare_distinct_count` | quorum one-root agreement, not bare distinct count |
| dregg-intent | lib | `test_verify_fulfillment_rejects_cross_state_predicate_forgery` | intent cross-state predicate forgery refused |
| dregg-coord | tests/twin_fail_closed | `twoc_pc_fails_closed_without_gate` | twin#3 coord 2PC fails closed |
| dregg-coord | tests/twin_fail_closed | `causal_happened_before_fails_closed_without_gate` | twin#4 causal order fails closed |
| dregg-coord | tests/twin_fail_closed | `shared_budget_resolve_fails_closed_without_gate` | twin#5 shared-budget fails closed |
| dregg-federation | tests/twin_fail_closed | `strand_admission_fails_closed_to_seeds_without_gate` | twin#7 strand admission fails closed |
| dregg-node | lib | `f_crit_1_setup_gate_is_xff_aware_defended` | F-CRIT-1 WS setup gate XFF-aware |
| dregg-node | lib | `audit_f_crit_1_loopback_predicate` | F-CRIT-1 loopback predicate resolves real IP |
| dregg-node | lib | `f1_untrusted_xff_spoof_is_ignored_defended` | F1 untrusted XFF spoof ignored |
| dregg-node | lib | `f1_proxied_clients_get_distinct_buckets_defended` | F1 proxied clients distinct buckets |
| dregg-node | lib | `f1_xff_left_prepend_spoof_is_inert_defended` | F1 XFF left-prepend spoof inert |
| dregg-node | lib | `f1_real_limiter_isolates_proxied_clients_defended` | F1 real limiter isolates proxied clients |
| webauth-core | lib | `brute_force_over_uid_space_does_not_recover_uid_without_salt` | linked_platforms unlinkability |
| dreggnet-game-board | tests/board | `a_forged_proof_is_rejected_by_the_light_client` | game-board light-client teeth |
| dreggnet-game-board | tests/anchor_independence | `the_board_anchor_is_pinned_once_and_a_submission_cannot_recapture_it` | crown/board anchor binding |
| collective-choice | lib | `a_certified_winner_is_final_even_when_later_casts_shift_the_argmax` | collective finality |
| dreggnet-party | lib | `a_resolved_fork_is_final_and_later_votes_cannot_rewrite_it` | party finality |
| dreggnet-telegram | tests/multi_chat_same_message_id | `presses_in_two_chats_with_the_same_message_id_route_to_their_own_sessions` | telegram cross-chat misroute |

## Invariant 3 — NO SILENCED FALSIFIER

No falsifier-class test carries `#[ignore]`. Two passes:

- **Registered** (hard): none of the `falsifiers.tsv` rows is `#[ignore]`-decorated.
- **Taxonomy sweep** (heuristic, v1): across the falsifier + twin source files, any `#[ignore]`
  within 6 lines above a `fn` whose **name** matches the falsifier taxonomy is flagged. The taxonomy
  regex (case-insensitive) is:

  ```
  forgery | forbidden | fail[_-]?closed | fails_closed | _twin_ | twin_forbidden | soundness |
  unforge | conservation | _rejected | _rejects_ | light[_-]?client | no_gate | cross_credential |
  excess_netting | root_agreement | unlinkab | recapture | cannot_recapture
  ```

**How to tag a test as a registered falsifier:** (a) add it to `falsifiers.tsv` — the strong,
explicit route (existence + run + no-ignore all enforced); or (b) name it so it matches the
taxonomy above — the sweep then forbids `#[ignore]` on it. Prefer (a). The sweep is scoped to the
registry's source files to avoid false positives across the whole tree; widening the scope is a
follow-up, not something to do by loosening the regex.

## Invariant 4 — NO RUST TWIN OF A LEAN `@[export]`

The structural crown. A "twin" is a Rust function that **decides** accept/admit/conserve/finalize
where a Lean `@[export]` proves the same property, so the two can drift — the asset-inflation
CRITICAL *was* the per-asset-conservation twin drifting. The campaign routed all 11 live decisions
through their proven `@[export]` (fail-closed when absent) and left each Rust sibling only under
`#[cfg(test)]` as a differential mirror. This invariant is the canary that keeps it so.

It is a **heuristic grep-lint (v1), not a theorem**: it reads the source at HEAD and asserts the
*shape* of each twin site. It cannot prove semantic equivalence; it prevents the known regressions.
`lean-twins.tsv` rows carry one of three guards:

- `route` — a pattern that **must be present** in the file (the live decider still calls its
  verified export / fail-closed disposition). If it vanishes, a Lean decision was likely inlined
  in Rust.
- `forbid` — a pattern that **must not be present** (a deleted Rust twin — `rust_non_amplifying`,
  an `unwrap_or(native)` fallback — reappearing on the live path).
- `cfgtest` — a `fn <name>` that must be **`#[cfg(test)]`-gated**: the differential sibling
  (`evaluate_votes_native`, `resolve_ordered_native`, `admitted_rust`, …) may exist, but only in
  test builds — never on a live path.

If a twin site file moves/renames, the guard is a **FATAL** (exit 2, "would check nothing"), never a
silent green — re-point the row.

### The guarded twins (11) and their exports

The route-through surface (the `verified_*` / `shadow_*` FFI bridges in `dregg-lean-ffi`):
`verified_2pc_decide`, `verified_happened_before`, `shadow_coord_shared_budget`,
`verified_handoff_non_amplifying`, `verified_admits` (strand), `verified_tau_order`,
`shadow_decide_refines`, `shadow_record_kernel_step`, `verified_finalization_quorum`,
`shadow_constraint_admits`. Twin#1 (conservation) routes through `dregg_cross_cell_conserves`
(authored during the campaign — the only twin that needed a Lean evaluator written first).

| # | Live file | Guard(s) | Deleted twin it forbids |
|---|---|---|---|
| 1 | turn/src/executor/atomic.rs | route `dregg_cross_cell_conserves` | Rust `BlockConservation` as the live decider |
| 2 | cell/src/program/eval.rs | route `no_oracle_subset_disposition` | silent Rust `match` when no oracle |
| 3 | coord/src/atomic.rs | route `verified_decision` + cfgtest `evaluate_votes_native` | `evaluate_votes_native` live |
| 4 | coord/src/causal.rs | route `verified_happened_before` | native `dag.happened_before` live |
| 5 | coord/src/shared_budget.rs | route `verified_resolve_ordering` + cfgtest `resolve_ordered_native` | `resolve_ordered_native` live |
| 6 | captp/src/handoff.rs | route `verified_non_amplifying` + forbid `rust_non_amplifying` | `.unwrap_or(rust_non_amplifying)` |
| 7 | federation/src/admission.rs | route `lean_admitted` + cfgtest `admitted_rust` | `admitted_rust` live |
| 8 | node/src/finality_gate.rs | route `verified_tau_order` | `dregg_blocklace::ordering::tau` live |
| 9 | dregg-deploy/src/refine.rs | route `shadow_decide_refines` | `decide_refines_mirror` live |
| 10 | intent/src/verified_settle.rs | route `settle_leg_authoritative` | FFI as a skippable cross-check |
| 11 | node/src/finalization_votes.rs | route `verified_finalization_quorum` | bare `distinct_votes >= threshold` |

**How to extend:** to guard a new twin, add rows for its live file — a `route` for the export it
must call, a `cfgtest` for any native sibling that must stay test-only, and/or a `forbid` for the
exact deleted-decider shape. To guard a new `@[export]`, add a `route` row for the Rust site that
must call it.

---

## Wiring

`.github/workflows/ci-invariants.yml` runs it. The `structural` job (invariants 3+4, no build) is
the fast always-on gate; `tree-builds` (invariant 1, `--keep-going`) and `falsifiers` (invariant 2)
are the heavy jobs, mirroring `ci.yml`'s toolchain / system-deps / disk-reclaim / LFS setup. Run it
locally the same way: `scripts/ci-invariants.sh structural` before a push, `scripts/ci-invariants.sh
all` when you have the build lock.

## Self-test / non-vacuity

`CI_INVARIANTS_REG_DIR=<dir>` points the gate at a synthetic registry so its detections can be
exercised without touching the checked-in one. This is how the guards were verified to **fire** on a
regression (route-through removed, a forbidden twin present, a native decider un-gated, a silenced
falsifier-class test) — a green here is meant to mean something.
