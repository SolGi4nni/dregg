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

### The registered falsifiers (38)

Generated from `scripts/ci-invariants/falsifiers.tsv` — the TSV is the registry, this table is
the reading copy. (It had drifted: it said 22 while the TSV carried the twin#1 / twin#8b /
twin#3b fail-closed rows too.)

| Crate | Target | Test | Guards |
|---|---|---|---|
| dregg-credentials | tests/anonymity_soundness | `cross_credential_predicate_forgery_rejected` | CRITICAL predicate STARK verified against its own commitment (x==x) cross-credential forgery is refused |
| dregg-turn | lib | `test_cross_asset_excess_netting_rejected` | CRITICAL asset-blind scalar excess netting (mint-from-nothing inflation) is refused by per-asset conservation on the … |
| dregg-turn | tests/conservation_fails_closed_without_gate | `conservation_fails_closed_without_gate` | CRITICAL twin#1 with NO conservation oracle the asset-inflation boundary is REFUSED (ConservationGateUnavailable), … |
| dregg-turn | tests/conservation_oracle_installed_poles | `conservation_gate_installed_admits_honest_and_refuses_violating` | twin#1 the OTHER pole: with a conservation gate installed an honest turn still passes and the cross-asset teleport … |
| dregg-node | lib | `rust_tau_twin_forbidden_on_verified_full_node` | twin#8 the Rust tau ordering twin is forbidden on a verified full node |
| dregg-node | lib | `rust_quorum_twin_forbidden_on_verified_full_node` | twin#11 the Rust finalization-quorum twin is forbidden on a verified full node |
| dregg-node | lib | `record_requires_root_agreement_not_bare_distinct_count` | quorum attested requires one-root agreement not a bare distinct-signer count |
| dregg-node | lib | `finality_fails_closed_when_the_verified_gate_is_unavailable` | twin#8b POLE A with the verified finality projection gate ARMED and UNANSWERABLE the poll REFUSES to advance … |
| dregg-node | lib | `poll_refuses_to_advance_finality_when_the_belt_gate_cannot_answer` | twin#8b BOTH POLES at the poll: honest finality still advances when the belt gate answers, NOTHING reaches the … |
| dregg-intent | lib | `test_verify_fulfillment_rejects_cross_state_predicate_forgery` | intent verify_fulfillment rejects a cross-state predicate forgery |
| dregg-coord | tests/twin_fail_closed | `twoc_pc_fails_closed_without_gate` | twin#3 coord 2PC fails closed (Abort) when the verified Lean gate is absent |
| dregg-coord | lib | `gate_absent_disposition_is_identical_under_cfg_test_and_in_production` | twin#3 the gate-absent disposition is the SAME fail-closed Abort under cfg(test) as in production (the cfg-divergent … |
| dregg-node | lib | `coord_decision_fails_closed_when_the_verified_gate_is_unavailable` | twin#3b POLE A with the verified 2PC gate ARMED and UNANSWERABLE the node REFUSES (CoordDecisionGateUnavailable => … |
| dregg-node | lib | `authoritative_decision_refuses_when_the_verified_2pc_gate_cannot_answer` | twin#3b BOTH POLES at the site: an honest unanimous tally still Commits when the gate answers or is bypassed, … |
| dregg-coord | tests/twin_fail_closed | `causal_happened_before_fails_closed_without_gate` | twin#4 coord causal happened-before fails closed without the gate |
| dregg-coord | tests/twin_fail_closed | `shared_budget_resolve_fails_closed_without_gate` | twin#5 coord shared-budget resolve fails closed without the gate |
| dregg-federation | tests/twin_fail_closed | `strand_admission_fails_closed_to_seeds_without_gate` | twin#7 strand admission fails closed to seeds-only without the gate |
| dregg-node | lib | `f_crit_1_setup_gate_is_xff_aware_defended` | F-CRIT-1 the WS setup gate is XFF-aware (no remote passphrase hijack behind a proxy) |
| dregg-node | lib | `audit_f_crit_1_loopback_predicate` | F-CRIT-1 the loopback predicate resolves the real client IP via the XFF resolver |
| dregg-node | lib | `f1_untrusted_xff_spoof_is_ignored_defended` | F1 an untrusted XFF spoof is ignored by the rate limiter |
| dregg-node | lib | `f1_proxied_clients_get_distinct_buckets_defended` | F1 proxied clients get distinct rate-limit buckets |
| dregg-node | lib | `f1_xff_left_prepend_spoof_is_inert_defended` | F1 an XFF left-prepend spoof is inert |
| dregg-node | lib | `f1_real_limiter_isolates_proxied_clients_defended` | F1 the real limiter isolates proxied clients |
| webauth-core | lib | `brute_force_over_uid_space_does_not_recover_uid_without_salt` | linked_platforms a brute force over the uid space does not recover the uid without the salt |
| dreggnet-game-board | tests/board | `a_forged_proof_is_rejected_by_the_light_client` | game-board a forged proof is rejected by the light client |
| dreggnet-game-board | tests/anchor_independence | `the_board_anchor_is_pinned_once_and_a_submission_cannot_recapture_it` | crown/board the anchor is pinned once and a submission cannot recapture it |
| collective-choice | lib | `a_certified_winner_is_final_even_when_later_casts_shift_the_argmax` | collective a certified winner is final even when later casts shift the argmax |
| dreggnet-party | lib | `a_resolved_fork_is_final_and_later_votes_cannot_rewrite_it` | party a resolved fork is final and later votes cannot rewrite it |
| dreggnet-telegram | tests/multi_chat_same_message_id | `presses_in_two_chats_with_the_same_message_id_route_to_their_own_sessions` | telegram presses in two chats with the same message_id route to their own sessions |
| dregg-pq | lib | `ml_dsa_verify_fails_closed_when_the_verified_core_cannot_answer` | twin#13 POLE A the ML-DSA-65 verify gate REFUSES when no verified core can answer (an Ok(()) in a no-bypass quadrant … |
| dregg-pq | lib | `ml_dsa_verify_length_gate_short_circuits_ahead_of_the_pq_gate` | twin#13 the VACUITY short-circuit: a malformed PQ half is refused BEFORE the gate (no verdict exists on any backend) … |
| dregg-pq | tests/unaudited_refusal | `require_lean_revokes_the_unaudited_opt_in_and_verify_refuses` | twin#13 THE REVOCATION POLE: DREGG_REQUIRE_LEAN=1 revokes DREGG_ALLOW_UNAUDITED_PQ=1 and the verify gate ABORTS … |
| dregg-pq | tests/unaudited_refusal | `genuine_signature_verifies_and_forgery_rejects_under_the_declared_bypass` | twin#13 THE OTHER POLE: under the declared bypass an honest signature still ACCEPTS and a forgery / tamper / … |
| dregg-pq | tests/unaudited_refusal | `verify_without_core_aborts_loudly` | twin#13 the unaudited fips204 crate must not decide a SECURITY accept/reject with no opt-in — uncatchable SIGABRT on … |
| dregg-pq | tests/unaudited_refusal | `sign_without_core_aborts_loudly` | twin#13 the SIGN arm: bytes that go on the wire under a pinned identity must not be produced by the unaudited crate … |
| dregg-pq | tests/unaudited_refusal | `encaps_without_core_aborts_loudly` | twin#13 the ML-KEM encaps arm of the same gate |
| dregg-pq | tests/unaudited_refusal | `decaps_without_core_aborts_loudly` | twin#13 the ML-KEM decaps arm (the other direction that can FAIL, so the one besides verify where a fall-open is a … |
| dregg-pq | tests/unaudited_refusal | `explicit_opt_in_permits_and_announces` | twin#13 the DECLARED bypass still works and still ANNOUNCES itself — an archive-less build (wasm / zkVM guest / dev … |

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

**Twin#3b — the third member, and a MEASURED WIDENING of what invariant 6 can catch.**
`node/src/coord_gate.rs::authoritative_decision` (the node-level 2PC commit/abort decision, fed by
`api.rs::atomic_vote` and by `blocklace_sync`'s co-turn tally) was unregistered and ended its
gate-absent arm with a bare `Err(_) => rust_decision`, logged at `debug!`. It was fail-closed only
**transitively** — `receive_vote -> evaluate_votes -> evaluate_votes_no_gate` happens to return
`Abort` — so the safety lived in a callee in another crate, undeclared at the site. Registering the
site *as shipped* printed exactly *"could not find ANY terminal verdict on the gate-absent path"*,
which is this guard telling the truth: there was no disposition here to check. It is now the
registered `coord_decision_disposition` (refuse ⇒ `Decision::Abort`).

That site also produced a **second blind spot, measured and then closed at the source**. The checker
short-circuits on the first region line naming a declared discriminator and then looks for a refusal
in the region *plus the inlined bodies of the helpers it calls*. Every sibling bypass predicate opens
`if require_lean { return false; }` — and that `return false` is a REFUSAL token the checker finds,
so the caller's real refusal arm is never read. Measured on twin#3b: with the early return, a mutant
that reverts the refusal arm to `Ok(())` stays **GREEN**; written as one boolean expression
(`!require_lean && (!export_linked || gate_disabled_by_operator)`) the same mutant goes **RED** —
*"the row DECLARES the carve-out but the gate-absent path has NO refusal on the non-exempt arm — the
declaration is decoration."* Prefer the expression form in new bypass predicates. The *other* blind
spot (a bypass predicate widened to bare `true`) is structural and stays green either way; that one
is invariant 2's job.

**Twin#13 — the PQ ACCEPT/REJECT gate, and A DIFFERENT FLAVOUR of the class.** `dregg-pq/src/mldsa.rs
::ml_dsa_verify` is the ML-DSA-65 accept/reject behind ~10 surfaces (token/revocation, lightclient,
cell-crypto, wire, turn/authorize, captp, blocklace/pq). Twins #1/#3b/#8b each had a **hand-written
Rust twin** as the fallback, so deleting or refusing was strictly an improvement. Here the fallback is
a **real, reputable third-party crate** (`fips204` 0.4 / `ml-kem` 0.2.3), and a blanket refusal would
brick every archive-less build — wasm, the zkVM guest, any dev box with no Lean archive, since
`dregg-pq` is a LIGHT leaf that never links the 156 MB archive and takes its verified cores as
injected `fn` pointers. So the requirement is not "refuse always". It is that the bypass be
**declared, visible and revocable**.

What was already true before this row (and worth not re-discovering): the fallback was **not silent**.
`dregg-pq/src/audit.rs` already `process::abort()`ed — uncatchably, so no `tokio` task boundary could
swallow it — on any PQ operation with no verified core and no `DREGG_ALLOW_UNAUDITED_PQ=1`, and
`dregg-pq/tests/unaudited_refusal.rs` already drove that abort as a real subprocess on four arms.
Three things were **not**:

1. **The opt-in was IRREVOCABLE.** `DREGG_REQUIRE_LEAN=1` — the tree-wide "I demand the verified
   artifact" switch that `turn::require_verified_conservation_gate`, twin#8b and twin#3b all honour —
   had **no effect on any PQ path at all**. An operator could demand the verified artifact and still
   have `fips204` deciding accept/reject. It now revokes the bypass
   (`audit::unaudited_pq_bypass_allowed`).
2. **Nothing was registered.** No `gate-dataflow.tsv` row for any of the seven PQ install sites, and
   — separately — **no `falsifiers.tsv` row for any of the five existing subprocess teeth**, so
   invariant 2 never ran them. One of them (`sign_without_core_aborts_loudly`) had been **RED,
   unobserved**, since keygen was itself gated in `c4f4b9cc3a`: the abort fired at KEYGEN and the test
   asserted SIGN needles against a KEYGEN message. A tooth with no row is a tooth nobody re-runs.
3. **The provenance was one process-global line.** A boot `warn!` per install site says an *export*
   was missing; it cannot say which implementation answered a given verification, or how often. Six
   `PqSite` counters (`dregg_pq::pq_provenance`, published as
   `dregg_pq_{verified_core,unaudited_crate}_answers_total{site="…"}` by
   `node::metrics::publish_pq_provenance`) now answer that, and the warning fires once PER SITE.

**And a THIRD blind spot, measured here.** A row registering the *site* —
`dregg-pq/src/mldsa.rs  ml_dsa_verify  LEAN_VERIFY_CORE_REAL  -` — printed **PASS
`[if-let-fallthrough]` "gate-absent path REFUSES immediately (`return false`)"** against the pre-fix
code that fell straight through to `vk.verify(..)`. The `return false` it found is the
**malformed-length** `let Ok(..) = .. else` guard further down the same region; strip that one line
and the same row goes **RED**. A refusal about a wrong-length key can therefore stand in for a
disposition about a missing verified core, so the row points at the extracted
`mldsa_verify_disposition` instead. **When a site's gate-absent region contains an input-validation
refusal ahead of the fallback, register the disposition, not the site.**

Twin#13's vacuity short-circuit is also a **DoS boundary**, not only an over-refusal guard: the
undeclared-bypass refusal is an uncatchable abort, so a gate placed ahead of `ml_dsa_verify`'s
length check would let any peer kill the process with one truncated signature.

**Twin#7b — the OPERATOR-ESCAPE flavour, and the first row whose own honest finding is that it is
DORMANT.** `node/src/strand_admission_gate.rs::admitted_participants` opened with
`if !strand_admission_gate_enabled() { return candidates.to_vec(); }` — the raw candidate list, with
no F-4 admission rule having decided it. Unregistered, unlogged (not one line of output on the bypass
path), unmetered, and **`DREGG_REQUIRE_LEAN=1` had no effect on it at all**, the same defect twin#13
found in the PQ path. Note the *gate-absent* path here was never the hole: `AdmissionRegistry::admitted`
degrades to twin#7's declared `narrow:is_seed`. It is the gate-**disabled** path that admitted
everything. So this row's declared bypass list is ONE entry, not two — **a missing Lean export is
deliberately NOT a bypass at this site**, because there is always an admission decision to route to.

Two things worth carrying forward from it:

1. **State the dormancy, do not let the fix read bigger than it is.** The only live caller
   (`blocklace_sync.rs:1450`) passes `admitted_participants(&raw, &raw)` — candidates == participants,
   so every candidate is a seed and the filter provably cannot drop anything (the "identity gate"
   finding already recorded in `docs/deos/CRATE-EXCELLENCE-PLAN.md` §P1(e)). On that call the bypass
   and the rule return the *same set*, so `DREGG_STRAND_ADMISSION_GATE=0` does **not** admit a Sybil
   today. The F-4 reopening is a property of the *function* and arms the moment a caller widens
   `candidates`. What changed now: `DREGG_REQUIRE_LEAN=1` has an effect on this path, the bypass
   announces itself, it has a metric, and the site is registered.
2. **A vacuity short-circuit can kill the guard it protects.** The tempting filter here was
   "short-circuit when no candidate lacks constitutional standing" — more correct-looking, and it would
   have made the refusal **unreachable from the only production caller**. A floor that cannot be
   reached is not a floor. The short-circuit is the narrow `candidate_count == 0` instead, and the
   would-be filter is kept as a logged diagnostic (`unvouched=`) so the dormancy is visible in the
   field rather than hidden in a comment. **Check that your vacuity short-circuit does not swallow
   your only reachable pole.**

**Twin#12 — the ATTESTATION flavour: the gated decision is not accept/reject but WHAT THE NODE
CLAIMS.** A bearer-delegated turn whose delegator pre-state cap root could not be resolved made
`blocklace_sync.rs` `warn!` *"proving WITHOUT the AUTHORITY leg (v1 fallback)"* and publish the v1
proof anyway.

⚑ **The question that had to be answered before the shape could be chosen — and it was, not guessed:
DOES A VERIFIER ACCEPT A v1 PROOF FOR A BEARER-DELEGATED TURN? Yes.** The refusal exists
(`sdk/src/full_turn_proof.rs::verify_full_turn_bound`, *"capability-gated turn carries no AUTHORITY
leg"*) and it works — but it fires only inside `if let Some(expected) = expected_cap_membership`, and
**the verification MODE is a caller-supplied argument, not a property derived from the turn**. The
signature takes no turn and no receipt (it does not even bind `turn_hash`); `verify_full_turn`, the
only entry point anyone outside the prover calls, hardcodes `None`; and a tree-wide grep for
`CapMembershipExpectation` finds exactly **one** non-test construction site — inside the prover, one
line after minting the proof. Zero in `lightclient/`, `eth-lightclient/`, `dreggnet-game-board/`,
`verifier/`, `net/`, `blocklace/`, the node API, or the discord bot (which re-verifies stored proofs
but reconstructs the component set from the proof's *own* labels and calls the `None` entry). Proof
bytes are never gossiped; each node re-executes and mints its own.

⚑ **And the scope qualifier, because calling it a forgery surface would be wrong.** It is **not** an
authorization bypass. `turn/src/executor/authorize.rs::verify_bearer_cap` independently checks the
delegator's Ed25519 signature, resolves the delegator cell, requires it to *actually hold* the
capability, and enforces expiry, the committed revocation registry, non-amplification and facet
attenuation — and every node re-executes the finalized turn before proving. An unauthorized bearer
turn never becomes a committed turn at all. The gap is in what is **attested**, not in what is
authorized: the proof under-claims. The site now refuses to publish rather than publish incomplete.

**The residual this row does NOT close, named rather than laundered:** nothing in the tree derives
"this turn needed an authority leg" from a receipt, so a *stripped* leg remains unnoticeable to every
consumer. Closing that means handing verifiers the receipt — a protocol change, not a disposition.

Twin#12 also surfaced a **routing-predicate misclassification** that the fail-closed disposition made
load-bearing. `bearer_consumed_cap` selected on `holder != agent` alone, ignoring the recorded
`ConsumedCapAuthPath`. The executor records a `Breadstuff` witness with `holder = *actor_cell_id`, and
that is the **parent action's target** for every non-root call-tree node — so a turn whose only
consumed capability sits at a nested breadstuff action satisfied `holder != agent` while carrying no
`Authorization::Bearer` anywhere. It was named "bearer-delegated", missed the delegator map by
construction, and warned about a delegation that did not exist. Under a refusing disposition that
would have withheld its proof. **When a fail-closed disposition is added behind a routing predicate,
re-derive the predicate from the recorded discriminant, not from a proxy for it.**

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
semantics at the registered site. 11 of 11 sites passed post-fix *at that time* (the registry has since
grown; see twin#3b below for the current count).

Twin#3b (the node-level 2PC decision gate) was demonstrated red the same way on 2026-07-25, same
scratch-tree method: (a) the pre-fix site as shipped, registered as `authoritative_decision` /
`verified_2pc_decide`, is **FAIL `[match-none-arm]` "could not find ANY terminal verdict on the
gate-absent path"** — the `Err(_) => rust_decision` arm states no disposition at all, and the guard
fails CLOSED rather than crediting the callee it happens to inherit safety from; (b) the row as
landed, against the pre-fix source, is **FATAL (exit 2)** — "no non-`cfg(test)` `fn
coord_decision_disposition`"; (c) the mutation canary (refusal arm ⇒ `return Ok(())`) is **FAIL "the
declaration is decoration"**, but only because the bypass predicate is one expression — see the
measured widening in invariant 6's section above. 12 of 12 sites pass post-fix and
`ci-invariants.sh structural` reports ALL ENFORCED INVARIANTS PASS.

Twin#13 (the PQ ML-DSA verify accept/reject gate) was demonstrated the same way on 2026-07-25, same
scratch-tree method (`CI_INVARIANTS_ROOT` + `CI_INVARIANTS_DATAFLOW_TSV`, working tree untouched — no
stash, no checkout), four ways: (a) the **site** registered as shipped (`ml_dsa_verify` /
`LEAN_VERIFY_CORE_REAL`) is **PASS — and that PASS is the blind spot**, credited to the
malformed-length `return false`; (b) the same row with the three `let Ok(..) = .. else { return false
}` guards removed is **FAIL** — proof that (a)'s green came from input validation, not from a
disposition; (c) the row as landed (`mldsa_verify_disposition`) against a tree with the refusal arm
reverted to `return Ok(())` is **FAIL "the row DECLARES the carve-out `mldsa_verify_bypass_allowed`
but the gate-absent path has NO refusal on the non-exempt arm — the declaration is decoration"**; and
(d) the **blinding counter-experiment** — the *same* mutant as (c) plus `if require_lean { return
false; }` restored at the top of the bypass predicate — is **GREEN**, reproducing `1736835f69`'s
finality-site measurement at a second site. `lean-twins.tsv` therefore carries a line-based `forbid`
on `^[[:space:]]*if require_lean \{` in both `dregg-pq/src/mldsa.rs` and `dregg-pq/src/audit.rs`.
13 of 13 sites pass post-fix and `ci-invariants.sh structural` reports ALL ENFORCED INVARIANTS PASS.

The 2-and-6 complementarity was demonstrated at twin#3b, not asserted: the pure decision logic was
extracted into a standalone `rustc --test` harness carrying the falsifier's own body verbatim, and
run against both mutants. Mutant A (refusal arm ⇒ `Ok(())`): invariant 6 RED, falsifier RED. Mutant B
(`coord_gate_bypass_allowed` ⇒ bare `true`): invariant 6 **GREEN**, falsifier RED with its FAIL-OPEN
message. Invariant 2 is therefore load-bearing at that site and not a duplicate of invariant 6.

Twin#7b (the node-level strand-admission escape) and twin#12 (the bearer AUTHORITY leg) were
demonstrated together on 2026-07-26, same scratch-tree method (`CI_INVARIANTS_ROOT` +
`CI_INVARIANTS_DATAFLOW_TSV`; working tree never stashed or checked out), and **both mutants were run
against the REAL falsifiers this time, not a transcribed harness**:

- **Mutant A** — both refusal arms (`return Err(StrandAdmissionGateUnavailable)`,
  `return Err(DelegatorCapRootUnresolvable)`) reverted to `return Ok(())`, in a scratch copy of the
  two files: invariant 6 **RED at both sites**, *"the row DECLARES the carve-out … but the gate-absent
  path has NO refusal on the non-exempt arm — the declaration is decoration."*
- **Mutant B** — both bypass predicates replaced by a bare `true`: invariant 6 **GREEN at both sites**
  (it does not evaluate the discriminator), while `cargo test -p dregg-node --lib` went **RED on all
  three disposition falsifiers**, each with its FAIL-OPEN message. Mutant B was applied to the real
  tree for the duration of that one run and reverted immediately.

15 of 15 sites pass post-fix. Both new bypass predicates are single boolean expressions, for the
reason `1736835f69` measured and twin#13 reproduced.
