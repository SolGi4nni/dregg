# Decision brief — 2026-08-08

⚠ **REWRITTEN the same day.** The first version listed eight decisions. Four were not
decisions, one was framed around options that turned out to be containments hiding the real
fork, and the largest item **stopped being a decision at all** once someone read the paper.
What that history is worth is recorded in the last section; read it before writing another
brief like the first one.

**Three decisions remain.** Everything else below the fold is work, not judgement.

---

## 1. Deploy the seven games now, or at the epoch-2 ceremony?

Counter 10 is **signed and loadable** — nine artifacts, seven games (Signal, Relay, Salvage,
Black Box, Deck Descent, Artificer Logic, Vent Crawl), `artifact-loader.test.mjs` 9/9 green.

- **Now**: players get seven games today; the epoch-2 re-genesis re-signs at the new
  federation id anyway, so the cost is one `dev-deploy.sh build && ship`.
- **Wait**: one ceremony instead of two.

**Recommendation: now.** ⚠ `npm run artifacts` must run on deploy — the served copy under
`poa-web/public/artifacts/` is gitignored and is a **third** place that must agree; it 404'd
on the new games until it was synced.

⚠ Regardless of timing: **judged play on the live node is still practice-only**, and a browser
player cannot settle until the deployment is re-genesised with a funded grant.

## 2. Nightly runner capacity — and branch protection, which is not sequenced behind it

The descriptor-drift gate **ran for the first time in its existence** and is RED (four findings,
all attributable to `23d65af59`; a `DREGG_VK_REGEN_ACK` re-emit + stamp fixes it — **do not
hand-add PROVENANCE rows**).

One of the three reasons it never ran is **capacity, not timeout** (`timeout-minutes: 330`): a
4-vCPU/16 GB hosted runner cannot hold the Dregg2 corpus build and dies at ~62 min at 98% of
the module count, on both long Lean jobs. **hbox does it in 43 minutes** and is registered and
online as a self-hosted runner.

- (a) route the heavy Lean nightlies to hbox — ⚠ co-tenant with codex's HOL build, so a nightly
  landing during your working hours is a real cost, and that cost is yours to accept;
- (b) a larger hosted runner;
- (c) leave them dying — **not viable**: a gate that cannot complete is a gate that does not exist.

**Correction to the first version of this brief:** it claimed branch protection must wait for
this decision. That was a false dichotomy — **required checks are per-check.** The `ci.yml`
lanes complete today; nobody would put a 330-minute nightly in a required set for a repo with
a 92-second median commit gap. **Say the word and `main` is protected today** with the checks
that complete; the Lean nightlies join later or never. Deferring all protection behind a
runner decision inverts the risk, given that `main` being unprotected is what lets the
silent-cancellation fail-open reach the tree.

## 3. Night-watch slot secret: carry or redraw

The epoch-2 multiplexed world (`09b2cb1b3`) **carries the slot commitment forward**, so your
existing off-repository secret still opens it. A fresh draw is equally supported and changes
`content_root`, which re-signs the statement.

**No recommendation — custody is yours.** Carrying is cheaper and keeps the night watch's
instance continuous; redrawing is right if the epoch-1 secret's handling is at all uncertain.

---

## Work, not decisions

Promoted out of the decision list because they strengthen a check, rebuild an artifact, or
implement a specification — none of which is a judgement call under this repo's doctrine.

- **The τ fork is fixed** (`d182d10fc`) — see below. Remaining: `ChainExtends` (CM Prop. 3,
  needs quorum-intersection formalisation), `finalLeaderAt` head **retraction** (wants CM
  Lem. 31, not truncation), and the **two-tips floor**, which is a precondition for
  exclusion-by-causal-past to fire at all.
- **`auto_evict_equivocator`** — a second live fork generator; exclusion must be a predicate
  over committed structure (`node(b) ∉ byz(⌊b⌋)`), not a live roster mutation. In flight.
- **Round-advance**: we run CM Alg. 4 line 59 (asynchrony) with line 67's round-robin leader
  schedule, and no timer. Liveness exposure. In flight.
- **`VoteCollector::record` returns before `verify_hybrid`** — retaining a disagreeing root
  there would build an accusation-forgery oracle. Verify first, then retain. In flight.
- **Drop `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`** from the three harnesses that set it
  unconditionally; PoA forbids it, so our multi-node tests run a different protocol than
  production. Requires pointing them at a Lean-linked binary.
- **The τ FFI cost curve** — profile with the existing instrument before touching the
  `@[implemented_by]` twin; the "one missing index dominates" claim is unproven and the
  equivocation pair-scan and List dedup are index-blind co-dominators.
- **Seed-archive re-splice cadence** (~90 s, mechanical) — and it is load-bearing for the
  above, because `verified_order_budget.rs` self-skips exactly when the archive is stale.
  Only the **publish** (`gh workflow run lean-seed.yml`) is yours, being an outward act.
- Descriptor-drift re-emit + stamp · the `/status` join field · restart-after-join (coded,
  unexercised — without it a restart un-joins a live validator and halts finality) · the
  emit-gate weld at `public_input_count` 42 vs 35 · nine postmark threads.

---

## Why the first version of this brief was wrong

Kept because the failure mode is more useful than the conclusions.

1. **It offered three containments and hid the actual fork.** All three τ options kept τ fixed
   and compensated in the node. The instability was a property of τ's *construction* — we
   unioned the causal pasts of every wave-end ratifier in the **live lace**, where CM Def. 6
   orders the **anchor's closure**. That is the substitution `CLAUDE.md` warns about: treating
   the protocol as a constraint and pricing containments against it.
2. **It mispriced its own recommendation by an order of magnitude.** "Replay the shifted
   region" needs rollback machinery that does not exist against an append-only commit log —
   and the node votes *immediately after executing each block*, binding an order-dependent
   root, while peers' collectors are first-write-wins by design. A replaying node can never
   re-vote the corrected roots. None of that was checked before recommending it.
3. **Four of eight items were not ember's call**, and one of those was mis-ranked *low* while
   being load-bearing for two items above it.
4. **The decision evaporated on contact with the literature.** The corpus went 3 → 41 papers
   that afternoon. τ was a **deviation**, not a design choice — so the fix was a bug fix, not
   a taste call, and cheaper than any option the brief listed. The executor and vote-timing
   repairs it contemplated are simply unnecessary once the ordering is correct by construction.

**The pattern worth keeping: every consequential finding in three days reduced to one sentence
— *the paper says X, we do Y*.** None of them needed insight. They needed someone to read the
thing we were implementing. A second opinion caught (1) and (2); reading the specification
caught (4).
