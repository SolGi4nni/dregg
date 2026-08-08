# Decision brief — 2026-08-08

Eight calls that are yours. Each has the measurement behind it, the options, what I'd pick,
and what it costs to be wrong. Ordered by consequence, not urgency.

Everything here was measured in the last two days; nothing is inherited from a doc.

---

## 1. ⚑ The τ execution-order fork — a permanent ledger split with zero Byzantine nodes

**What was measured.** Fresh 4-node federation on hbox, threshold 3, 24 concurrent-faucet
trials. First divergence at trial 13; it cascaded and never healed. **12 of 39 rejected turn
hashes split 3-vs-1, in both directions.** A real attested-root fork at h=7 — nodes 0/1/3 on
`871b20c9…` with quorum 3, node2 on `9bb9d0b0…` with quorum 0. Node2 never reached h=8.
Evidence and redb images preserved at `hbox:/tank/dregg-build/fedrace/`.

**The cause is the ORDER, not execution or the receipt head.** Both nodes ran the same
predicate correctly on their own state; the state differed because they applied the same two
finalized blocks in opposite order. `ExecutionCursor::pending` (`node/src/execution_cursor.rs:180`)
serves "finalized blocks not yet executed, in the current τ order" — and *which* blocks are
"not yet executed" is a function of **when this node polled**: local wall clock, not consensus.
A prefix shift arrives, one node has already executed the later block, `pending` never
re-serves, and the two are permanently apart. Prefix shifts fired **9–14× per node in 19 min**.

`TauPrefixMonotone.lean` is exact about it: `tau_executed_prefix_fixed` holds **under**
`FinalizedRegionStable`, and a prefix shift *is* the witness that the hypothesis failed. **The
node evaluates `stableCheck` nowhere.** The cursor's comment says it "absorbs this correctly:
every finalized block still executes exactly once" — true, and about *exactly-once*. **Order
agreement is a different property and the cursor does not have it.**

The cursor design is from `0416270d7` (2026-06-11). This is not new breakage.

**Options.**

| | approach | cost |
|---|---|---|
| **A** | Replay the shifted region so the executed sequence matches the current τ order | Re-execution on every shift; needs the executor to be re-entrant over a rolled-back prefix |
| **B** | Gate cursor advancement on `stableCheck` — the check the Lean names and the node never evaluates | **Costs liveness**: a node stops executing while the region is unstable |
| **C** | Make post-finalization predicates order-insensitive | Largest change; alters the executor's contract, and "order-insensitive" must then be *proved*, not asserted |

**My recommendation: A, with B as the safety net.** A restores the property the Lean theorem
already names; B alone trades liveness for safety and would have frozen node2 rather than
forking it — which is better, but is a worse product. C is the most robust and the least
knowable: it replaces a stated invariant with a claim about every predicate, forever.

**Required regardless of which you pick:**
- Fix the Rust/Lean τ sequence disagreement (see §2 — it fails on a **nine-block** lace).
- Put `node/tests/verified_order_budget.rs` in a gate that cannot self-skip.
- Make a root split at `VoteCollector::record` (`node/src/finalization_votes.rs:537`) a `warn!`
  plus a metric. Today it stores the disagreeing root, returns `Counted`, and logs `debug!`
  "recorded finalization vote (below quorum)". **Across a real split, nothing said anything.**

**If we do nothing:** the fork is fail-*safe* (a split root cannot cross the verified quorum, so
the minority carries `quorum=0` rather than a forged anchor) and entirely **silent**. A
production federation would present as "one node stopped finalizing" with nothing naming why.

---

## 2. `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1` in every multi-node harness

**Measured from `/proc/<pid>/environ` on a live node.** Set unconditionally by
`scripts/federation-local.sh:86`, `federation-join-poles.sh:98,119`, `run-node-10min.sh:142`.
`scripts/poa-devnet.sh` **forbids** it.

So a budget miss **falls back to the un-verified Rust twin** in every test harness, and
**fails closed** on PoA. Same trigger, opposite failure — **our multi-node tests run a
different protocol than production.**

And the premise the fallback rests on is false: `verified_order_budget.rs` **failed on its
first execution** — the Lean τ and the Rust τ produced **different sequences on a nine-block
lace**. Same set, different order.

⚠ It did **not** cause the §1 fork (first budget miss was 2.5 min *after* the divergence), but
it is an independent second generator of the same fork class.

**Options:** (a) drop it from all harnesses so tests fail closed like PoA; (b) keep it and
accept that multi-node runs are not production; (c) keep it only where a test's subject is the
fallback itself.

**My recommendation: (a), and treat any harness that needs it as a finding.** ⚠ Dropping it
does **not** close the §1 fork — the cursor is unchanged, so **the deployed PoA posture is
exposed too**.

---

## 3. The verified τ ordering has a performance cliff

**Derived from the Lean source** (load-independent; the box was never quiet enough to measure):
`tauOrderFastImpl` builds HashMap past/round maps, but `Lace` is a `List` and `Lace.lookup` is
`find?` — **O(n) over the whole lace** — inside the innermost loops of `fastCausalPastAux`,
`fastHasEquivInPast` and `fastRatifies`. That is **O(n⁴) per wave**. **There is no
`BlockId → Block` index, and that single missing index is the dominating term.**

The one absolute anchor is the observed crossing at **773–981 blocks** on an idle 4-node
committee. At ~2 blocks/s that arrives in **about seven minutes**, after which the verified
path is effectively unreachable. Stated conditionally — it was not reproduced.

**On PoA, where the escape is forbidden, a miss means finality halts.**

**Options:** (a) build the index; (b) raise the budget; (c) accept and account.

**My recommendation: (a).** (b) moves the crossing without changing whether the verified path
runs. A lane declined to write the index because it could not build or validate Lean, and
shipping unvalidated changes to the `@[implemented_by]` runtime twin of the consensus ordering
rule would be worse than not shipping — I agree, and it should be done on a quiet box with a
real build. **It is the outstanding work, not a later phase.**

---

## 4. Deploy the seven games now, or wait for the epoch-2 re-genesis?

Counter 10 is **signed and loadable** (`998f775b7`) — nine artifacts, seven games,
`artifact-loader.test.mjs` 9/9 green.

- **Deploy now:** players get Signal, Relay, Salvage, Black Box, Deck Descent, Artificer Logic,
  Vent Crawl today. The epoch-2 re-genesis later re-signs at the new federation id anyway.
- **Wait:** one ceremony instead of two.

**My recommendation: deploy now.** The bundle re-signs at the ceremony regardless, and the
marginal cost is one `dev-deploy.sh build && ship`. ⚠ `npm run artifacts` must run on deploy —
the served copy under `poa-web/public/artifacts/` is gitignored and is a **third** place that
must agree; it 404'd on the new games until it was synced.

⚠ Regardless of when: **judged play on the live node is still practice-only**, and a browser
player cannot settle until the deployment is re-genesised with a funded grant.

---

## 5. Publish the Lean seed (outward act — yours)

`gh workflow run lean-seed.yml -f platforms=linux-x86_64`.

The archive has **drifted again**: **42 of 347 members older than their Lean, including
`Dregg2_FFI.o` itself**, plus 5 boundary-closure modules with **no object at all**. It was
re-spliced to 0/347 yesterday; measured decay was 0 → 1 at 15 min → 10 at 2 h purely from
sibling edits.

**Options:** publish now and accept it drifts again; or set a re-splice cadence first, then
publish.

**My recommendation: cadence first.** The remedy is ~90 s and mechanical; the gate is *true*
and should stay able to go red, which means remedying faster than it drifts rather than
softening what "fresh" means.

---

## 6. Nightly runner capacity

The descriptor-drift gate **ran for the first time in its existence** yesterday and is RED
(four findings, all attributable to `23d65af59` — a `DREGG_VK_REGEN_ACK` re-emit + stamp fixes
it; **do not hand-add PROVENANCE rows**).

It never ran because of three distinct causes, and one is capacity, not timeout
(`timeout-minutes: 330`): a **4-vCPU/16 GB hosted runner cannot hold the Dregg2 corpus build**
and dies at ~62 min at 98% of the module count. Both long Lean jobs die identically. **hbox did
it in 43 minutes** and is registered and online as a self-hosted runner.

**Options:** (a) route the heavy Lean nightlies to hbox; (b) pay for a larger hosted runner;
(c) leave them dying.

**My recommendation: (a), with a caveat you own** — hbox is co-tenant with codex's HOL build,
and a nightly landing on it during your working hours is a real cost. (c) is not viable: a gate
that cannot complete is a gate that does not exist.

---

## 7. `main` is not branch-protected

`protected: false`. This is what lets the silent-cancellation fail-open reach the tree: every
notifier tests `result == 'failure'`, and a **cancelled** job's result is `cancelled`, matching
none of them. That is now fixed for descriptor-drift (a verdict job treats cancelled/skipped/
empty as **NO VERDICT — worse than a red**), but the general shape stands repo-wide.

**Options:** protect `main` with a required-checks set; or leave it and rely on the verdict jobs.

**My recommendation: protect it**, but only after §6 — requiring a check that cannot complete
would wedge the repo. This is sequenced *after* the runner decision, not independent of it.

---

## 8. Night-watch slot secret: carry or redraw

The epoch-2 multiplexed world (`09b2cb1b3`) **carries the slot commitment forward** rather than
redrawing, so your existing off-repository secret still opens it. A fresh draw is equally
supported and changes `content_root`, which re-signs the statement.

**No recommendation — this is custody and it is yours.** Carrying is cheaper and keeps the
night watch's instance continuous; redrawing is the conservative choice if the epoch-1 secret's
handling is at all uncertain.

---

## Not decisions — things I will just do when you say go

- Deploy counter 10 (§4) and run `npm run artifacts`.
- The `DREGG_VK_REGEN_ACK` re-emit + stamp for the descriptor drift (§6).
- The `/status` join field (`JoinProgress` is populated on the handle; a stuck joiner still
  reports `healthy: true`).
- Restart-after-join: coded, reasoned, **not exercised**. Without it a restart un-joins a live
  validator and halts finality — worth an hour.
- The emit-gate weld at `dregg-effectvm-transfer-v1`: `public_input_count` **42 vs 35** — the PI
  compaction never reached that golden.
- Nine postmark threads owed (iris, jetto, postmaster, draig, glitch, stella-letta, +3).
