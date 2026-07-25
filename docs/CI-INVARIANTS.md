# CI Invariants — the enforcing gate for the twin-deletion campaign

`scripts/ci-invariants.sh` institutionalizes the invariants the 2026-07-23/24 twin-deletion +
megaswarm-fix campaign fought for, so the gains become **un-regressable**. It is recommendation ①
of that campaign (`docs/TWIN-DELETION-MAP-2026-07-23.md`,
`docs/MEGASWARM-FLAW-BACKLOG-2026-07-23.md`; memory `project-twin-deletion-campaign`).

It enforces **six** invariants. Each is a hard failure with an actionable message; the script
exits `0` (all pass), `1` (an invariant failed), or `2` (environment problem — a registry or source
file moved, so the gate would otherwise check nothing).

```
scripts/ci-invariants.sh [ all | structural | build | falsifiers | no-ignore | no-twin | one-mathlib | no-fallthrough ]
```

- `all` (default) — all six invariants.
- `structural` — invariants **3 + 4 + 5 + 6** plus registry existence, **no cargo build**. Runs in
  seconds; this is the always-on PR check.
- `build`, `falsifiers`, `no-ignore`, `no-twin`, `one-mathlib`, `no-fallthrough` — one invariant each.

Two checked-in registries drive it, both under `scripts/ci-invariants/`:

- `falsifiers.tsv` — the security falsifiers (invariants 2, 3).
- `lean-twins.tsv` — the Rust-twin regression guard, by SYMBOL (invariant 4).
- `gate-dataflow.tsv` — the same twin sites, by DATAFLOW (invariant 6), driven by
  `gate-dataflow.py`.

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
| 1 | turn/src/executor/atomic.rs | route `dregg_cross_cell_conserves` + route `ConservationGateUnavailable` + route the fallback's `#[cfg(not(all(any(unix, windows), not(debug_assertions))))]` — **and invariant 6's dataflow row**, which is what actually catches a fallthrough | Rust `BlockConservation` as the live decider |
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

**And add a `gate-dataflow.tsv` row too.** These `route` rows are NAME-GREPS. Twin#1's was green
for the entire life of the conservation fallthrough — the symbol was present and the fall-open
sat two lines below it. Invariant 6 is where a new twin's no-gate DISPOSITION gets checked.

---

## Invariant 5 — ONE MATHLIB PROVISIONING PATH

Every CI mathlib provisioning must route through `scripts/ci-mathlib-cache.sh`. Checked (all
grep/awk, seconds, no build):

| Sub-check | Fails when |
|---|---|
| lakefile shape | `metatheory/lakefile.toml` regains a `path =` require, or loses its explicit 40-hex `rev =` (a float makes mathlib's prebuilt-olean cache unfindable). |
| no private path | any non-comment workflow line names `src/mathlib4` or clones `mathlib4` itself. |
| no inline fetch | an inline `lake exe cache get` reappears in a workflow instead of the script. |
| every Lean job provisions | a workflow installs the `metatheory/lean-toolchain` toolchain but calls neither `ci-mathlib-cache.sh` nor `bootstrap.sh` — that job would compile mathlib from source. |

**Why (2026-07-25).** Five provisioning sites (`ci.yml` × 3, `proof-integrity-canary.yml`, and both
`starbridge-v2-installers.yml` lanes) cloned mathlib to `$GITHUB_WORKSPACE/../../src/mathlib4` and
ran `lake exe cache get` there. That was correct only while the lakefile pinned
`path = "../../../src/mathlib4"`. `4ccee5bd71` (2026-07-05) made the require portable `git`+`rev`,
which lake resolves into `metatheory/.lake/packages/mathlib` — so the 8463-olean download landed
where nothing reads it and every Lean job recompiled the mathlib subset from source. **Measured** on
`ci.yml`'s "Zero-sorry guard" step: 20.9/23.6/21.9/21.1/31.0 min for the five runs before the pin,
**115.1 min on the pin commit's own run** (which touched no Lean proof), 99–111 min the next day.
It hid for 20 days because a from-source mathlib build is indistinguishable from a slow one in a
green log — the same reason this is now a gate and not a comment.

The two starbridge copies were worse than slow: they `sed`'d for the deleted `path = "…"` line, so
`MATHLIB_DIR` became `<repo>/metatheory` and `git clone` exited 128 — a hard red on every
`lean-cache` miss.

---

## Invariant 6 — NO ACCEPTING FALLTHROUGH ON A MISSING VERIFIED GATE

`no-fallthrough`. Registry `scripts/ci-invariants/gate-dataflow.tsv`, checker
`scripts/ci-invariants/gate-dataflow.py` (pure `python3` — no ast-grep, no cargo, no network, so the
always-on `structural` job stays checkout-plus-bash).

**Why it exists.** Invariant 4 is a NAME-GREP. Its `route` row for twin#1 asserts the symbol
`dregg_cross_cell_conserves` appears in `turn/src/executor/atomic.rs` — and that row was **green the
entire time** the file read:

```rust
if let Some(oracle) = installed_conservation_oracle() { return /* verified verdict */; }
Self::unverified_rust_conservation_fallback(entries, declared_supply)   // <- on NATIVE
```

A native node with a stale or absent `libdregg_lean.a` therefore answered the per-asset `Σδ = 0`
question — the **asset-inflation boundary**, the twin that already produced one CRITICAL bug — with
the unverified Rust `BlockConservation` decider, and said so only in a build warning. A
name-whitelist cannot see a fallthrough. This invariant asks the dataflow question instead.

**The check.** For each row (`file`, `fn`, `acquire`, `allow`, `note`): slice the non-`cfg(test)`
body of `fn`, find the gate acquisition matching `acquire`, extract the **gate-absent region** (the
`else` arm / the `None`|`Err(..)` match arm / a `let .. else` block / an `unwrap_or*` default / the
fallthrough after `if let Some(gate) { .. }` / `?`-propagation), resolve same-file helper calls two
levels deep, and require the region to REFUSE. An ACCEPTING terminal reachable there is RED.

**Carve-outs are declared, not implicit.** The `allow` column names the discriminators permitted to
guard a non-verified arm at that site — a cfg fragment (`debug_assertions`) or a named runtime escape
(`quorum_rust_fallback_allowed`) — and the non-exempt arm must *still* refuse. `narrow:<token>` marks
a site whose no-gate path is a deliberately narrowed local decision (federation's "only genesis
seeds"). So widening a carve-out is a reviewable TSV diff, declaring one the code does not contain is
still red, and every declared escape is printed in the CI log instead of hiding in a `match` arm.

**It fails closed.** An unparseable site, a moved `fn`, a missing `python3`, or a verdict it cannot
determine is RED — never a skipped check.

**It is not a theorem.** A structural dataflow check over the source at HEAD. It does not know
whether `false` means "refuse" for a given predicate's polarity, and it stops at depth 2. It exists
to make one known regression class impossible to land silently.

**Its precise blind spot, measured.** The checker verifies that the gate-absent region *reaches* a
refusal past a declared discriminator; it does NOT evaluate the discriminator. Twin#8b's row was
tested against a mutant whose `belt_gate_bypass_allowed` was replaced by a bare `true` — invariant 6
stayed **GREEN**. Widening a bypass predicate is therefore invisible here by construction. That is
why every registered site also needs a falsifier row (invariant 2) that asserts the predicate's own
quadrants: `finality_fails_closed_when_the_verified_gate_is_unavailable` pins
`belt_gate_bypass_allowed(true, false, false) == false`, and reddens on exactly the mutation
invariant 6 misses. **Invariants 2 and 6 are complements at each site, not alternatives.**

**Twin#8b — the second member of the class, found by the row above's own note.** Invariant 6
classified `node/src/finality_gate.rs::compute()` as `propagates` (a `?`-shaped gate whose disposition
belongs to the caller) and its PASS line says *"register the CALLER to check where it lands."* The
caller was `node/src/blocklace_sync.rs::poll_finalized_blocks`, it was unregistered, and it failed
OPEN: a missing / `ERR` / panicked `dregg_blocklace_finalize` made the belt gate a no-op with a
warning, and the poll went on to slice turns to the executor off the **un-gated** Rust
`ordering::tau`. The disposition is now the registered `finality_belt_disposition`, which refuses
(finalize nothing this poll). A `propagates` PASS is a POINTER, not a clean bill of health — chase it.

---

## Wiring

`.github/workflows/ci-invariants.yml` runs it (tracked, on `origin/main` since `c5a3a963e0`,
triggering on `push: main`, `pull_request`, and `workflow_dispatch`). The `structural` job
(invariants 3+4+5+6, no build) is
the fast always-on gate; `tree-builds` (invariant 1, `--keep-going`) and `falsifiers` (invariant 2)
are the heavy jobs, mirroring `ci.yml`'s toolchain / system-deps / disk-reclaim / LFS setup. Run it
locally the same way: `scripts/ci-invariants.sh structural` before a push, `scripts/ci-invariants.sh
all` when you have the build lock.

## Self-test / non-vacuity

`CI_INVARIANTS_REG_DIR=<dir>` points the gate at a synthetic registry so its detections can be
exercised without touching the checked-in one. This is how the guards were verified to **fire** on a
regression (route-through removed, a forbidden twin present, a native decider un-gated, a silenced
falsifier-class test) — a green here is meant to mean something.

Invariant 5 has no registry, so it is falsified by running the script against a **synthetic tree**
(`ROOT` is derived from the script's own location, so a scratch `scripts/ + metatheory/ +
.github/workflows/` skeleton is enough). All five of its sub-checks were verified to go red that
way on 2026-07-25: `path =` restored, `rev` dropped, a workflow naming `src/mathlib4`, an inline
`lake exe cache get`, and a Lean job that installs the toolchain and never provisions.

Invariant 6 carries its **own** non-vacuity proof and runs it on *every* invocation: `gate-dataflow.py`
checks itself against a synthetic fall-open decider (must go RED) and a synthetic fail-closed one
(must stay GREEN) before it looks at the tree, and the whole invariant fails if either verdict is
wrong. It was also demonstrated red against the real pre-fix `atomic.rs` on 2026-07-25 — 9 of 10
registered sites passing, the conservation twin the single failure — and green after the fail-closed
fix. `--self-test` runs just that part.

Twin#8b (the finality belt gate) was demonstrated red the same way on 2026-07-25, in a scratch tree
(`CI_INVARIANTS_ROOT` + `CI_INVARIANTS_DATAFLOW_TSV`, working tree untouched — no stash, no checkout),
three ways: (a) the pre-fix site as shipped, registered as `poll_finalized_blocks` /
`VerifiedFinality::compute`, is **FAIL `[UNPARSED]`** — the inline disposition is not a shape the
checker can slice, and it fails CLOSED rather than guessing; (b) the row as landed, against the
pre-fix source, is **FATAL (exit 2)** — "no non-`cfg(test)` `fn finality_belt_disposition`", i.e. a
deleted disposition is never a silent green; (c) the mutation canary — the post-fix tree with only the
refusal arm reverted to `return Ok(())` — is **FAIL: "gate-absent path reaches an ACCEPTING verdict
(`return Ok(`) … A MISSING VERIFIED GATE CAN ADMIT."** (c) is the one that matters: it is the defect's
semantics at the registered site. 11 of 11 sites pass post-fix.
