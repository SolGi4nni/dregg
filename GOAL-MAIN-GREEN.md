<!-- ⚑⚑ This repo runs MULTIPLE concurrent /goal sessions. See GOALS-INDEX.md.
     This file is the **main-green** lane only. Edit only this one. -->

# GOAL — MAIN GREEN: CI good, more findings addressed

## The mission
`scripts/local-gates.sh` is the instrument (a GitHub verdict is a lottery ticket — 0/60 green,
92s median between commits against ~87min runs). **Get every gate green for a reason**, and burn
down the ranked residual index in `HORIZONLOG.md`.

⚠ The bar is NOT "the table is green". It is **"green because the thing is right"**. A gate made
to pass by widening an allowlist, baselining a live finding, or narrowing its own reader is a
regression dressed as progress — this lane has already found gates that were red-and-green
simultaneously, and one whose red-proof passed in the one state it existed to catch.

## Current thrust
Four gates red at adoption. Then the 25 LIVE residuals in `HORIZONLOG.md`'s index, top-ranked
first.

| gate | state at adoption |
|---|---|
| `doc-refs` | 23 DEAD — **all one concurrent lane's in-flight doc**, not mine to race |
| `dark-modules` | FAIL — a module declared by no `mod`, so rustc compiles none of it |
| `ratchet-darkness` | FAIL — 2118 `.lean`, 1931 in the ratchet |
| `ci-invariants-structural` | 1 FAILURE |

## ⚑ NEW THRUST (ember, 2026-07-29): PARE GITHUB, LEAN ON HBOX, KEEP KILLING BUGS
> *"our entire github setup is wayyyy too expensive/automatic. we should probably be paring things
> down a lot, before i start paying more for LFS etc. i mean, can't we just be running all things on
> hbox..?"*

**Measured, last 60 push runs: 562 billed minutes, ~9.4 min per push, 10 workflows** — on a repo with
a ~92-second commit median and **6,795 push runs** on record. Last 30: 16 failure, 8 success, 5
cancelled. And the standing measurement says GitHub CANNOT answer here (0/60 green, ~87min verdicts
against 92s commits) while `main` is not branch-protected, so **every gate reports and none blocks.**

- ✅ **Release artifacts off `push`** (`e52394521`) — `starbridge-v2-installers` (21 min/push) and
  `sel4-images` (6.3 min/push) were building a release artifact for EVERY main commit, consumed by
  nothing. Both files correctly explained why they could not use `paths:` (it gates tag pushes too) —
  but the remedy was never `paths`, it was dropping `branches: [main]`, which leaves the tag path
  untouched. **~27 min/push saved, releases unaffected.** `publish-sdk-*` were already tags-only.
- **CI paring dispatched** — 338 of the 562 minutes, 56 min/push, **28 jobs**, several duplicating
  local gates that run in seconds and already BLOCK at pre-push. Briefed: cut only where the same
  question is answered BETTER elsewhere, never merely because a job is slow or red; say what coverage
  goes with each cut; and get LFS off the critical path (a job pulling LFS it never reads is pure
  bill).
- **`dregg-exec-lean` 5 reds dispatched** — the seam where the verified producer actually decides.
  ⚠ Briefed that three of them are REFUSAL poles, so "the corpus lost a case" must be established
  rather than assumed: a failing refusal pole may mean the refusal broke.

## ⚑ BOX ROUTING — CORRECTED 2026-07-29 (measured, not inherited)
**hbox is NOT disk-critical.** `/` 49% (224 G free), `tank/dregg-build` **8% — 2.5 T free**. I have
been briefing lanes "both boxes disk-critical, prefer local" all night; that is false for hbox and
has been pushing builds onto the laptop for nothing.

- **`pbuild` routes to `/tank/dregg-build/<lane>` and was fixed TODAY** to measure the LANE dir
  rather than `$HOME` — previously a tank-resident lane was refused for a shortage on a disk it never
  touches, and two lanes escaped by lowering `HBUILD_MIN_FREE_GIB`. Use `pbuild`; it is correct now.
- **The leak is bare `cargo` in `~/dev/<tree>`** — 7 target dirs on root that never went through a
  lane. ember: *"we should be using /tank/dregg-build almost exclusively, for disk perf reasons."*
- Reclaimable in IDLE trees: ~8 GB of target output. The 25 G / 16 G / 19 G items are source + `.git`
  + `.lake`, so they are ember's call. `dregg-build.premigrate` (3.6 G, last touched Jul 23) is the
  pre-symlink leftover.

## ⚑ TEST LEDGER — measured 2026-07-29 (`--no-fail-fast`; the default TRUNCATES)
**256 `#[ignore]` attributes, every one carrying a reason** (the gate enforces it, two-sided).
⚠ A naive grep reads 441 — it counts comments, the same trap that once had a sibling gate claiming
174 bare ignores that were all prose.

**~55 failing, and more than half sit in one crate:**

| crate | failing | owner |
|---|---|---|
| `sdk` | **29** (23 in `full_turn_proof::tests` + 6) | lane dispatched |
| `dregg-discord-bot` | **18** | lane dispatched |
| `dregg-node` | ~6 + 1 timeout | — |
| `dregg-turn` · `dreggnet-party` | 1 each | known |
| `dregg-circuit` · `dregg-cell` · `dregg-coord` · `dregg-exec-lean` | **0** | closed today |

Closed today: 24 (`dregg-circuit` → 1222/1222), 5 (`dregg-exec-lean` → 122/122), 23
(`dreggnet-market` → 53/53). **~52 fixed against ~55 remaining**, and the remainder is concentrated
rather than scattered — which is the shape that yields to one-cause fixes.

⚑ Both dispatched lanes were briefed with the `dregg-circuit` precedent: **23 of its 24 were ONE
LINE** (a missing `refresh_commitment()`), so look for the shared producer-side call before assuming
N divergences. And both were warned that inherited diagnoses in this repo have been wrong — `git log
-S` what you are handed.

## Done since the ledger
- **Anchor stamp** (`dad9fd8db`) — `977e73b19` switched receipts to `consensus_state_commitment` and
  FOUR consumers never followed. `intent/src/fulfillment.rs` wrote the old BLAKE3 root on three LIVE
  paths, and **its test was green because it was self-consistent with the bug** — that is how it
  survived nine days. `spween-dregg` was not merely stale but **already RED**. ⚑ And the lane refuted
  the diagnosis I briefed: `lean_shadow`'s always-false leg was NOT the accumulator roots but wrong
  KIND *and* wrong SCOPE — `maybe_shadow_turn` was discarding a post-state ledger the executor
  already handed it. ⚠ Standing gap it named: **no test asserts `ShadowAgreement`'s strength**, which
  is why an always-red detector was invisible for nine days.
- **Fulfillment fixture** (`991c9d18d`) — payer and recipient in DIFFERENT asset columns for a
  same-currency payment; green only while the teleport was open. `dregg-intent` 441/443.
  ⚠ Attribution corrected: reported as fallout from my `47f4d5b7a`; `git log -S` puts it in
  `b1a370194`. **Second wrong inherited attribution in two days.**
- ⚑ **The two survivors are a DESIGN finding, not a fixture bug.** `drex_routing_e2e`'s ring holds
  `m_gold`/`m_art`/`m_usd` — **cross-asset by design**, so closing the teleport removed the mechanism
  the feature ran on. Dispatched with the instruction NOT to make the ring single-asset (that deletes
  the feature) and NOT to reopen the teleport (it is a correct security fix); a ring of locks should
  be same-asset legs whose cross-asset effect emerges from the CYCLE.

- ✅ **`dregg-intent` 444/444** (`de5f84a8e`) — and the cause was NOT the teleport. `route()` never
  invokes `TurnExecutor`, so that guard is unreachable from those tests; the real failure was
  `VerifiedSettleRefused("no verified gate registered")` from `e3f0e7b92` (07-24) — the UN-CALLED
  INITIALIZER class, same wound as `dreggnet-market`'s 22-of-23.
  ⚠ **The misattribution was MINE**: I ran ONE of three co-located failures, read its panic, and
  wrote the other two up as the same cause — overwriting `HORIZONLOG` D6, which had it RIGHT.
  `drex_clear.rs:220` had even predicted the misread verbatim. Memory extended.
  The ring was already legal (`DREX-ROUTING.md §2`: same-asset legs, cross-asset effect from the
  CYCLE) — no new verb, no Lean work, `b1a370194` untouched, fixture byte-identical.

- ⚑ **`dregg-sdk` 30 → 0** (`8ece3bd85`) — it was 30, not the 29 I briefed. **Six families, not
  thirty bugs**, found by DECODING each `failed constraints = [#N]` back through eval order and
  inverting the S2+E1 column deletions: 20 opaque row-0 panics collapsed to 2 causes. Fields-freeze
  band (11, harness) · non-canonical facet mask limb (9, harness — every red used `1<<16`, every green
  fit 16 bits, 100% predictive) · un-called revoked-set grow-gate (3, PRODUCER — the generator existed
  with zero callers, and `provability_scoreboard` had been printing `[UNPROVABLE] revokeDelegation`
  the whole time) · stale geometry (4) · **receipt anchor semantics (2 — a FIFTH consumer of
  `977e73b19`, found independently)** · a doc block (1).
  ⚑ No AIR, no re-emit, no VK rotation. No mutation window at all — the red-proof IS the pre-fix
  baseline, reproduced on two boxes with identical counts. Net +3 assertions.
- **Workspace compiles clean** (`3192a8dda`) — `--workspace --all-targets` was RED at 17, which is why
  the full-suite run died before executing a single test. Both breaks live in test targets **no
  per-crate check reaches**: `HeaderVerifyError` lacking `PartialEq` (16 asserts), and
  `NativeDescentMove::Take` — the verb from the Lean dungeon re-emit — with no arm. Same shape as the
  two `TurnError` arms I missed yesterday: **the compiler will tell you, but only if something asks.**

- ⚑ **discord-bot 19 reds — and the crate did not COMPILE at HEAD**, so the handed-down "487/18" came
  from nowhere reachable. `8ee7052f2` added a param, fixed its own four sites, missed an out-of-crate
  caller, and its "say what broke" never mentions it. Fixed at the cause: `dreggnet-compute`'s worker
  had no cell, so settlement had nobody to pay; `verify` now reads the WORKER'S BALANCE instead of
  trusting the `PAID` slot.
  ⚑ **Family A was not a deserializer bug — the Rust mover is a GENERATION behind the Lean program.**
  `CAP` is 7 in Lean and Rust said 8 (the mover admitted moves the executor refuses); `unlock` now
  leaves the key HUNG; `take` is a ninth verb Rust lacked entirely, so **no frontend could retrieve a
  hung key at all.**
  ⚑ **And a refusal pole was green for the wrong reason**: `matches!(err, NotConserving(_))` is
  satisfied by `FfiUnavailable("no verified gate registered")` exactly as well as by an overdraft —
  it passed through the whole outage while its honest twin died.
  ⚠ Residual MEASURED not documented: on a native RELEASE build the Descent's custody teeth REFUSE,
  because `DHeapAtom` has no transition table. Two teeth pin it, one of which **goes red the day the
  Lean arm lands.**
- ⚠ **DISK WAS FULL — 188 MiB of 7.3 TiB**, which is what my "17 workspace build errors" actually
  were (`failed to build archive`, `could not write output` = ENOSPC, not code). Freed 176 GiB by
  dropping `discord-bot/target`. ⚠ `target` is still 401 G and `~/Library` 644 G, `~/.cache` 311 G.

- ✅ **DISK: 215 MiB → 543 GiB free.** Cleared `target/` (405 G) and `.claude/worktrees` (5.4 G) on top
  of the earlier `discord-bot/target` (176 G) — **581 G of pure build output**, all rebuildable, no
  build processes running. ⚠ KEPT `metatheory/.lake` (4.9 G): that is the expensive Lean build, hours
  to regenerate, and it is not the problem.
  Remaining bulk is NOT build output and is ember's call: `~/.cache/huggingface` 277 G (model
  weights), `~/Library` 644 G. Other `~/dev` targets total ~18 G, biggest is tokeman's 12 G with its
  daemon live.
  ⚑ **This was the real cause of the "workspace build errors" I chased for an hour** — `failed to
  build archive` and `could not write output` are ENOSPC wearing a compiler's voice.

- ✅ **`lake build Dregg2` COMPLETES — 10,456 jobs, first clean root build in days** (`422abab0c`).
  One vacuous floor carrier had failed it since 07-27, and **three lanes reported it as "not mine"
  while nobody owned it** — the 24-circuit-reds shape again.
  ⚠ I tried RESTATING it first and that failed, which is the useful part: moving a floor from a named
  binder into an arrow's antecedent is the same logic. **Any "the old floor implies X" carries the
  old floor.** The file's own header already said "no declaration in this file assumes
  `Hash4NoCollision` any more" — false only because that theorem existed, so deleting it made the
  header true.
  ⚑ Sharpens the standing rule: **binder-class carriers sometimes restate and sometimes must be
  DELETED; `prop-body` carriers (a `def` whose BODY is the floor conjunction) genuinely cannot be
  restated**, which is why the two `ApexPremiseVacuity` rows legitimately hold baselines and this
  did not.

## Next 3 moves
1. **Lean catalog drift** dispatched — `EffectKind` has no `.mint`, colors `.burn` opposite to the
   executor, and cites a Rust function deleted today. ⚠ Briefed NOT to assume the executor is right.
2. **`test-gauntlet.sh` is invoked by nothing** — C2's surviving half. It owns the `--ignored`
   profiles, and 27 `[[test]]` targets behind unenabled `required-features` print nothing at all.
3. **The apex F1 fork** — still ember's, and still the largest single open decision.

## Superseded moves
1. **B3** dispatched — the sovereign carrier arm is dead TWO levels: neither the attach nor the drain
   has a production caller, while three production sites fill the stash.
2. **B5** dispatched — the solo finalization arm still finalizes any creator, the half `c6f00c228`
   deliberately left. ⚠ Its comment is right that a naive filter bricks solo cold start, so the lane
   is briefed to solve that tension rather than trade it away.
3. ~~The `declared_supply` seam~~ dispatched — verified: EVERY invocation passes `&[]`, production and test alike, so no test would notice it breaking. Original note: — `check_per_asset_conservation_by_asset` takes it for reconciling
   disclosed mint/burn against balance deltas; all four production callers pass `&[]`, both test
   callers too, and the verified Lean decider already implements the reconciliation with a `#guard`.

## Superseded moves
1. ~~A6~~ dispatched — briefed with the correction that its sibling forced: do NOT inherit my
   framing of the mechanism, since I named the wrong one for A7 and a wider key would have been a no-op.
2. **B3/B5** — the sovereign carrier-witness arm is dead two levels deep; the solo finalization arm
   still finalizes any creator (the half `c6f00c228` deliberately left).
3. **The `check_per_asset_conservation_by_asset` seam** — `declared_supply` exists for reconciling
   disclosed mint/burn against balance deltas, **all four production callers pass `&[]`**, both test
   callers too (so no test would notice a break), and the verified Lean decider already implements
   that reconciliation with a `#guard`. Sound today only because mint/burn happen to be well-paired.

## Superseded moves
1. **`dark-modules` + `ratchet-darkness`** — both are the gating-defaults-to-silence class this
   repo keeps finding; a dark module is code rustc never compiles and a dark `.lean` is a proof
   whose `#assert_axioms` run nowhere. Fix the wiring, not the ratchet.
2. **`ci-invariants-structural`** — read the FAIL line, fix the real thing.
3. **`HORIZONLOG.md` A1** — a revoked capability can be left live against a ledgerless light
   client (the two cap-open REMOVE members declare zero map-ops), while
   `sdk/src/full_turn_proof.rs:2378` asserts the opposite in the present tense.

## Done log
- (adopted) baseline: 4 gates red, 25 LIVE residuals indexed.
- `dark-modules` GREEN — 3 kimchi reality-gate extractors were dark; wired via a standalone
  `[workspace]` manifest pinned to the upstream rev their README records. Red-proved both ways.
  ⚠ the last step was tracking the manifest: `crate_roots()` reads `git ls-files`, so an
  untracked Cargo.toml is invisible — on disk is the author's state, tracked is everyone else's.
- `ratchet-darkness` GREEN — `Metatheory.ResearchRegime` (398 lines, 16 theorems, 0 sorries)
  landed without its import line, so its declarations were counted by nothing. Rooted beside
  its 13 siblings; all 14 are imported by `Dregg2.lean` and its own docstring builds on two.
- `ci-invariants-structural` GREEN — the carve-out was DECLARED but its row had rotted twice:
  the note named a symbol `22d9e0f3a` renamed, and `allow` named `debug_assertions` after the
  code deliberately moved that predicate into a named `const fn`. A registry can go stale too.
- `doc-refs` GREEN — 30 dead refs, 24 of them Lean module-relative cites colliding with the crate
  dir on case-insensitive APFS (the cause that took this gate 330 → 0 six weeks ago, walking back in
  via a new doc), 4 `scripts/*.ts` written relative to `bridge/mina-zkapp/`. Guarded the rewrite with
  `(?<![/\w])` after my first attempt double-prefixed 5 good refs into dead ones.
- **ALL FOUR ADOPTION GATES GREEN.** Now burning the residual index.
- A1 re-verified: I first checked the PLAIN cap-open revoke members and read it as fixed. WRONG —
  `is_forbidden_authority_only_cap_write_descriptor` forces the WRITE route, and the write wrappers
  are the ones with the dropped after-side gates. A1 is LIVE; dispatched as Lean work (declare the
  map-op so the tombstone zero-fold is forced in-circuit, re-emit, rotate the VK).
- `lean-orphans` 6 → 3 UNLISTED — rooted the 3 settled Mina wrap modules (1,987 lines, 86 decls,
  all elaborate clean). The other 3 are a live lane's untracked/modified WIP; left red on purpose,
  it is a message for their author.
- **`check-workspace-closure` got a carve-out mechanism** — it landed BLOCKING with none, and
  correctly flags `pickles-extractors` forever (path-deps on a sibling `mina-rust` checkout no
  commit can contain). Without a declared allowlist everyone would set the env escape and the gate
  would stop meaning anything. Two-sided ratchet + config-absent-is-a-fault. ⚠ Two scope bugs found
  building it: staleness must be judged per-INVOCATION not per-tree, and must not run at all in a
  mode that cannot match extract-only rows.
- **A12 CLOSED** — Lean's `reservedKeys` was 8 against Rust's `STATE_SLOTS = 16`, and it drove
  `isUserTailKey`, so keys 8..15 were fixed cells in Rust and committed tail keys in Lean. Corrected
  + 5 `#guard` fixtures moved above the band. The pin READS THE LEAN SOURCE from a Rust test, because
  a literal pins one side and the drift was the two sides moving independently.
- **ETH light client anchored** — the weak-subjectivity store existed since `27b15fa95` and nothing
  used it: `verify_finalized_update` kept bare args, so the un-anchored spelling stayed the shortest
  one. Now a `TrustedCommittee` witness; reverting a call site fails at COMPILE time. And the old
  suite implied the BLS floor was the defence — the new falsifier signs 512 attacker keys under the
  correct domain so every crypto check passes, and shows the unanchored drain SUCCEEDING.
- **`Effect` tag 63 collision fixed** — Mint and ShieldedTransfer shared a domain tag, and that
  primitive is what `canonical_effects_hash` (a sovereign signature) binds. 36 scattered literals
  replaced by one macro with a single absorb site; no VK rotation (grep-zero consumers in `circuit/`).
- **`node/prover` retired** — it forwarded nothing AND its OFF position did not compile, so the
  `not(prover)` tests existed in no buildable configuration. Un-gating found the only pin guarding
  the v1 retirement had a CASE MISMATCH and could never have passed.
- ⚑ **APEX VACUITY PROVED, AND IT IS WORSE THAN THE RESIDUAL SAID.** Both apexes are vacuous at
  EVERY parameter, not just deployed: the fifth binder `RestHashIffFrame` is refuted with NO
  hypotheses, by Cantor. The ratchet could not have caught it — not injectivity-shaped, not a
  sentinel floor, measured empirically. 17 defeats substantiated (residual said 11; the lane said
  plainly it could not map the two). `Verify/ApexPremiseVacuity.lean` landed, rooted, 16
  `#assert_axioms`. **F1 (digest the finite support) is ember's call — 234 binders, 85 modules.**
- ⚑ **`Games/DungeonCompleteness.lean` is 29 errors AT HEAD and clean in the tree** — a committed
  red, not WIP. It stops `lake build Dregg2`, so `#floor_ratchet` and `#teeth_wired` have been DARK
  for every lane, including the one that needed them to classify its own module. Dispatched.

- **C5 CLOSED** — in `local-gates.sh` a TIMEOUT was a `skip`, so a gate that could never finish left
  the table clean. It is a failure now, named separately in the summary, because "produced no
  verdict" and "found a defect" both have to fail and want opposite fixes. Red-proved with a 1s
  budget on a passing gate.
- **C6 CLOSED** — the red-proof-scaffold sweep AGENTS.md prescribes was a ritual: no script anywhere
  ran it, and nothing grepped for `MUTANT-` at all. `check-no-disarmed-guard.sh` now does, over 7,642
  tracked source files, red-proved by planting the real `Monotonic` scaffold back into `eval.rs`.
  ⚠ Scope: the first run found two vendored Jinja template strings — exempted with the measurement.

- ⚑ **A1 CLOSED, and it was the top-ranked live residual.** A prover could publish ANY 8-felt
  post-remove cap-root — including one leaving the revoked capability LIVE — and a ledgerless light
  client accepted it. Closed in Lean with `removeTombstoneConstraints` (16 `node8` + 8 `rootPinGate`
  + 8 constant pins to 0, because a tombstone commits a constant, not a leaf). Flag day: narrow
  1976→2119, wide 1878→2014, welded 1885→2021, all three FPs rotate. UNSAT at the prover, and the
  red-proof is IN-VALUE so no source was ever disarmed.
  ⚠ **My brief was wrong**: I said "declare the map-op". There is no map-op to declare — the INSERT
  siblings bind their post-root with a Merkle weld, and `MapInsertImtRepoint.lean` proves the
  `.insert` arm cannot force a write denotation. The lane followed the real mechanism.
- ⚠ **I opened a scaffold window and a lane saw it.** Red-proofing the disarmed-guard gate against
  the real `eval.rs` instance was visible to a concurrent lane, which correctly reported it and
  correctly did not touch it. Restored, byte-identical, gate clean — but the window is the hazard
  and I made one hours after writing the doctrine saying so. Mutate on a copy.

- **B1 REWRITTEN, not ticked** — the sweep stands (`DREGG_LEAN_SHADOW` set by nothing, verified four
  ways), the conclusion is refuted (it is the SUPERSEDED seam; `DREGG_LEAN_PRODUCER` is opt-OUT,
  default ON, and overrides in BOTH directions). ⚑ The real finding is worse: the dark gate was
  BROKEN — its veto restored the ledger but not the executor receipt head, so **one vetoed turn
  permanently bricked the agent**. Deleted; the tooth moved onto the armed seam.
- **C3 CLOSED** — `no_run` fences were never asked for a reason, though the script already knew the
  attribute and `REASON_RE` already accepted `NO_RUN:`. Armed; 29 of 43 reasonless, seeded to ratchet.
- **17 orphaned build-lane leases reaped** across both boxes. ⚠ Disk is NOT reclaimable by the
  sanctioned sweep — it is live lane targets (persvati `srot` alone is 100.6 GB), and
  `reclaim-space.sh --clean` races active builds. **persvati 98%, hbox 99% — ember's call.**

- Gate reading at checkpoint: `dark-modules` PASS · `ci-invariants-structural` PASS · `doc-refs` PASS
  · `no-disarmed-guard` PASS (7,642 files). `ratchet-darkness` RED on
  `Dregg2.Circuit.WholeImageFoldRealization` — **untracked, another lane's WIP** (570 lines, 29
  theorems). Left red on purpose: it is a message for its author, not a number to make go away.

- **A2 CLOSED** — five MCP tools could not commit because a RETIRED attestation was consulted as a
  gate. `require_effect_vm_proof` deleted (not made to return `Ok` — that launders the absence into
  presence); every commit path now routes through the same seam HTTP uses, onto the Lean-emitted
  rotated descriptor. ⚑ Two defects the wall was hiding: `dregg_bilateral_action` built
  `Authorization::Unchecked`, so every bilateral transfer the executor ever saw returned
  `PermissionDenied`; and the honest-path handoff fixture handed a RANDOM introducer key, so it
  "passed" by being refused for the wrong reason. RP1 also showed the old substring pole would have
  passed where the by-variant pole fails.

- **C7 CLOSED as a DETECTION** — the published Lean seed was 11 days behind the tree and nothing
  compared them, so the ~43 verified-gate tests it arms were reporting `ok` while asserting nothing.
  ⚠ Deliberately NOT re-adding `lean-seed.yml`'s push trigger: ember removed it 2026-07-25 with a
  measured reason (19-25 min full saturation of a triple-booked hbox, on the most-edited path in the
  repo). The gate REPORTS drift always and FAILS past 14 days, so staleness stops being invisible
  without overturning a cost decision.
- **B2 dispatched** — `Effect::linearity()` has 0 non-test Rust callers (verified; ⚠ a naive sweep
  reads 30 because `.claude/worktrees/` scratch pollutes it). But the residual's framing is
  incomplete: the LEAN theory is alive and PROVED (`Spec/Conservation.lean`, three theorems,
  `#assert_axioms`-pinned) with NO `@[export]`. So it is a proved spec, a dead Rust twin, and an
  executor using neither.

- ⚑ **`lake build Dregg2` UNBLOCKED** — and a second red was hiding behind the first.
  `DungeonDeployed.lean` (1466 lines) imports `DungeonCompleteness`, so Lean never elaborated it and
  its 21 errors were invisible: the root build had been red **two days, not one**, and "39 errors"
  was an undercount of **67 across two modules**. Every `sorryAx` gone BY BEING PROVED, all ten
  statements byte-identical. `dungeon_program.json` re-emitted (was a Jul-25 cache with no `take`).
  **First instrument reading in days**: `#teeth_wired` PASS, `#floor_ratchet` red on exactly one new
  foreign carrier — not grandfathered, since a baseline row is relaxing a gate.
  ⚑ It also settled the `ApexPremiseVacuity` question: two of my three baseline rows are class
  `prop-body` and LOAD-BEARING; the third was pure slack and is retired.
- **B2 CLOSED** — 403 lines of dead conservation twin deleted. The Lean theory is proved and
  SPEC-ONLY (no `@[export]`). Three findings beyond it: the MCP surface told third parties its table
  was "sourced from the real enum" (it is a hardcoded array) and that the classes were "the linearity
  the VERIFIED EXECUTOR enforces" (it enforced nothing); the Lean catalog has drifted from Rust in
  BOTH directions (52 vs 36, overlap 27, **9 Rust-only including `ShieldedTransfer` and `Mint`**);
  and `check_per_asset_conservation_by_asset` takes `declared_supply` while **all four production
  callers pass `&[]`**.
- **D5 CLOSED** — an OBSERVED debit is consumption that happened. `unattributed_spent` added and
  folded into `total_spent()`, so `is_overspent()` can fire on it. ⚠ The existing test asserted
  `total_spent() == 400` while its own comment described the hole — comment named it, assertion
  enshrined it. Now three assertions where there was one.

- **A7 CLOSED** — four heap-root builders silently MERGED two leaves at one address, so a removal
  left the anchor unmoved. ⚠ My brief's mechanism was WRONG: `as_u32()` is not a truncation
  (`BabyBear` is a canonical `u32`, `p < 2^32`), so "dedup on the full felt" would have been a
  no-op — the address is narrow because it is ONE ~31-bit felt. Reachability splits three ways:
  the per-cell heap is accident-only (but ~1 expected collision at depth-16 capacity), while
  `cells_root` and the four accumulators are **grindable offline — measured at 101,577 folds**.
  ⚑ The guard caught a LIVE one on its first run: `fold_bytes32_to_bb([0u8;32]) == SENTINEL_MIN`,
  so a nullifier folding to zero displaced the genesis sentinel every non-membership opening rests
  on. Trade stated: a silent soundness bug becomes a liveness one on the grindable surfaces.
- Flag-day residue from `30ff508fe`: 26 reds were attributed to it, **25 have since resolved**, and
  the survivor is `wide_notecreate_completion_lane_forge_verdict` — whose failing assertion is the
  test's own NON-VACUITY guard, so its forge pole is currently unfalsifiable. Dispatched; baselines
  recorded (`dregg-circuit --tests` 751/1, `dregg-cell` 846/0).

- **C9 CLOSED as a refusal** — `passkey.ts`'s BIP39 guard read `if (this.wasm.validate_mnemonic && …)`
  under a comment claiming "against the dregg bundle it is always present". The shipped bundle exports
  it **ZERO** times, so an invalid mnemonic enrolled silently on the custody path. Absence is a named
  refusal now; the bundle is still 18 days stale and that is now LOUD rather than silent.
  ⚠ Nearly a false green: my first typecheck ran `npx --no-install tsc`, which printed nothing because
  it did nothing. The real one is `./node_modules/.bin/tsc` — rc 0.

- **D3 CLOSED** — all four bounty payout surfaces carry a real `Transfer` now (the residual missed
  the CLI one). ⚑ The blocker was one level down and only running the code found it:
  `execute_tree.rs:1100` evaluates a touched cell's program over EVERY cell an effect touches, so
  `StrictMonotonic(STATE)` makes **a self-escrowing bounty cell inexpressible**. The reward is a
  PROMISE; both legs are roots of one turn so a refused payment takes the PAID stamp with it.
  ⚠ And its red-proof caught a vacuity in its OWN refusal pole: with the fix reverted the test stayed
  green because `InsufficientBalance` fired on the TURN FEE, so a test asserting only "insufficient
  balance" would have passed over a payout carrying no `Transfer` at all.
- **D2 marked STALE, not closed** — a concurrent lane repaired it; a production caller now exists at
  `pay.rs:649` and the recorded "10 test callers" was never right (15 at HEAD). Marked so nobody
  cites the old shape.
- **`compute-exchange` dispatched** — the same defect, live: a green `SETTLED` pill and a `"paid · "`
  binding over SetField+EmitEvent with no conserving effect, and no `Payable` impl in the crate.

- **The cap-open "residue" was not mine, refuted by measurement** — the wide `noteCreate` member is
  byte-identical across the flag day (JSON sha256 `f68b22bd96e759d1` both sides). The red predates it
  by five days: the E1 cutover moved the columns and the harness never followed. Neither a stale
  fixture nor a broken producer — a **stale HARNESS** indexing committed-geometry col 348 into a
  2936-column old-geometry row, where that column is a BEFORE-block limb. The guard fired correctly.
  ⚑ Both teeth had been dead since 07-23 — the second died at its HONEST pole — so the audit they
  exist to perform **had never once run on the wide member**.
- ⚠ **MY BASELINE WAS WRONG and this is the lesson of the day landing on me.** I recorded
  `dregg-circuit` as 751/1. nextest's default fail-fast **truncates at 750 of 1218 and reports "1
  failed"**. With `--no-fail-fast`: 26 before, 24 after. I have told every lane to read COUNTS rather
  than verdicts, and then read a truncated count as a complete one. **`--no-fail-fast` is not
  optional when quoting a baseline.**

### Known pre-existing reds — MEASURED, `--no-fail-fast`, 2026-07-28 12:32
`dregg-circuit`: **1218 run, 1194 passed, 24 failed, 10 skipped.** The 24 are
`gentian_discharge_vault_prove` ×11, `gentian_carrier_floor_prove` ×6,
`gentian_deployed_capacity_liveness` ×3, `settle_escrow_weld_prove` ×3,
`effect_vm_selector_gate_forgery` ×1 — all owned by a live lane in
`circuit/src/{descriptor_ir2,plonky3_prover,stark_zk}.rs`.
Elsewhere: `dregg-cell` 846/0 · `dregg-turn` 914/915 (`stark_kill_wire_roundtrip::dfa_routing_roundtrip`)
· `dregg-coord` 129/0 · `sdk full_turn_proof::tests` ×24 · `dreggnet-party` `depth == 3`.

- **D2 CLOSED** — the gauge falls by the run's own metered cost and the alarm fires from a drained
  tank. ⚠ Siblings open: the OTC desk and the liquidity swap have 0 production callers, so the
  documented pile→fuel path is test-only. That is why a refuel key was needed.
- ⚠ **I swept a lane's file.** `0ea777733` committed `discord-bot/src/commands/` as a DIRECTORY and
  caught the treasury lane's in-progress `admin.rs`, so the refuel flag day is not findable from that
  subject. Annotated with `git notes`; the rest landed as `1259679bf`. **Commit named paths, not
  directories** — AGENTS.md says so and I read a directory as one.
- **24 committed circuit reds dispatched** — they were being carried on every brief as "a live lane's
  uncommitted work", and all three named files are CLEAN and committed. Measurably nobody's.

- **D4 CLOSED** — wired, not retired, because retiring would have deleted the only real path. ⚑ The
  premise's verb was wrong: it does not prove per tick, and idle cost is ~0.19 % of one core. The
  waste was a shipped feature with no way in. And its E2E test had been standing in for the missing
  caller, which is exactly why `submit` could have 0 callers and a green suite.

- ⚑ **`dregg-circuit` is 1222/1222** — the 24 committed reds are two families, both closed.
  **Family A (23 of 24) is my own `460727e9f`'s SEVENTH site**: its commit message enumerates the six
  hand-repaired drift sites and `settle_carrier_trace` was the one it missed. One line.
  Family B was hiding two VACUOUS teeth — with the selector gate stripped, both "negative" arms are
  still UNSAT, so the module header's claim was false at HEAD. A new tooth isolates the gate by using
  a zero-amount Transfer, so one constraint is the whole difference between accept and refuse.
  ⚠ Neither my `413fc0bde` suspicion nor my compaction hypothesis was right; both were checked and
  refuted rather than inherited.
- **D3's sibling `compute-exchange` CLOSED** — and its executor blocker was MEASURED here rather than
  assumed from bounty-board: compute-exchange's `post` DOES advance STATE, so "fund inside the posting
  action" looked open, and it is not, because the executor snapshots per ACTION. Its `AffineEq` is
  not vacuous but constrains the wrong thing — a turn recording `PAID = 800` while transferring **1**
  is ACCEPTED, now measured by a test rather than described in a comment.
- ⚠ `starbridge-v2` is red right now on a live lane's uncommitted `TurnError::AssetClassCollision`
  with no arm in `debug.rs:235` — the same miss I made at 10:43. Theirs to finish; not touched.

- **A6 CLOSED** — and it corrected my framing in the OPPOSITE direction from its sibling. The
  truncation IS real here (28 of 32 bytes) but is NOT the binding constraint: mod-p from a 32-bit key
  is already surjective onto `[0,p)`, so a wider key buys 1.025× and zero classes. The width is in the
  DESTINATION TYPE — one PI slot, one AIR column. Same conclusion as A7, different reason, established
  not inherited. ⚑ Two new findings on top: the light-client leg's class is **prover-chosen outright,
  no grind needed**, and the ZERO class is an overloaded sentinel reachable by a ~27-CPU-minute
  targeted grind (checked: the native asset does not occupy it, now pinned).
- ⚠ I added the `starbridge-v2` match arm the new variant needed — the same omission I made with three
  CapTP variants at 10:43. `cargo check -p starbridge-v2` is 0.

- **B3 CLOSED — retired, not wired**, and it is dead FOUR levels, not two. Level 3: `attach_to_leg`
  takes a `RotatedParticipantLeg` and **the SDK constructs none anywhere**; the stash was declared
  "never serialized" so it could not reach the node-side mint, which in turn REFUSES to persist a leg
  carrying a witness. Level 4: the object it produced was never arm-admissible — measured through the
  deployed prover, the claim slice `[58..62)` overlaps the 16 anchor PIs of the only reachable
  (68-PI) leg.
  ⚑ **AND THE PIN CHECK ALONE WOULD HAVE ADMITTED IT.** `transferVmDescriptor2R24` has a genuine
  `PiBinding` at all four claim slots — because on a 68-PI leg those ARE the state anchors. Only the
  overlap arithmetic refuses. Had the gate been the pin half alone, a sovereign authority tuple would
  have folded against four lanes of the leg's own state commitment read as a key commitment. Two
  independent conditions is the whole difference, and nothing recorded that. It is a test now.
  ⚠ Residual, unchanged: the fold's `Sovereign` arm and every Lean theorem above it still describe an
  object no production path constructs. Retiring the wire removed what LOOKED like the producer.

- **B5 CLOSED — the ⚑⚑⚑⚑⚑ finality entry's last live half.** The arm consulted no rule at all, and the
  bootstrap tension its comment cited was RESOLVABLE rather than a trade: the boot path already
  derives the node's own hybrid id before any roster is committed, so the filter names exactly one
  key and widens nothing. ⚑ It also checked whether the arm could just call `tauOrder` — it cannot, a
  fresh solo lace finalizes nothing under it, so that route would brick cold start. Cold start driven
  on the real binary, through a restart, with zero fail-closed lines.
- ⚑ **Dispatched: no membership vote has ever counted on the live path.**
  `execute_finalized_membership` hands the HYBRID id to a `participants` map keyed by ed25519, and its
  replay twin passes ed25519 correctly — so the live path and its "pure twin" disagree, and the live
  one is fail-closed dead. Found only because a lane noticed its own change *could not regress the
  join flow*.

- **HORIZONLOG headlines corrected** — 20 residuals closed today, and the HEADLINE said LIVE on 17 of
  them while a `✅ FIXED` marker sat one line below. The headline is what a reader scans, so the
  burn-down was misreporting itself in the only field anybody skims. Third time today the index was
  wrong in a way that mattered, in both directions.
- **C2 HALF CLOSED** — the nightly adversarial verdict now runs in the cheap local set, which is the
  path work takes; `armed-teeth`'s own mirror was correct but fired only on `pull_request` while work
  lands on `main` directly at a ~92s median. ⚑ **It went red on its first run and the cause is not
  code**: two consecutive nightlies died in ~57s at checkout — *"This repository exceeded its LFS
  budget"*. Still live: `test-gauntlet.sh` is invoked by nothing.

- ⚑ **`declared_supply` was not unwired — it was an authority bypass.** A `DeclaredSupplyChange` row
  added `+magnitude` to the conserved sum **with no authority check of any kind**, while
  `Effect::Mint` requires a control-grade cap carrying `EFFECT_MINT`. Any caller that populated it
  would have minted straight past that gate. I dispatched this asking for it to be WIRED; the lane
  established it cannot be, because supply is disclosed as a paired ledger delta and the producer
  cannot exist by design. Deleted. Wire byte-identical, Lean rule untouched.
  ⚠ Both prior counts were wrong (mine 2+4, the index 4+2; real 4+5), and the struct was constructed
  exactly ONCE in the tree — inside its own test.
- ⚠ **A B2 follow-up, worse than recorded**: `CatalogInstances.lean`'s `EffectKind` has **no `.mint`
  at all** and colors `.burn` as disclosed non-conservation, while deployed `apply_burn` is a
  conserving holder→well move — and its docstring says it is transcribed verbatim from a Rust
  function **deleted today**. The Lean spec catalog mirrors something that no longer exists.

## Fable-5 lanes — the believed-true / too-much-work set (dispatched at ember's ask)
- **F1 satisfiability** — NOT the 85-module port. Prove the finite-support successor to
  `RestHashIffFrame` is SATISFIABLE, REFUTABLE and NOT PROVABLE, re-derive one downstream consumer
  through it, and price the port in binder positions. Turns ember's decision into a theorem.
  ⚠ Briefed: if the successor cannot be inhabited either, say so — that is the most valuable outcome.
- **The conservation composition theorem** — global conservation is six disjoint local invariants
  plus a pairwise proof nobody wrote. Briefed to **hunt the counterexample FIRST**, and told where I
  would look: (balance, notes), where a lossy 31-bit fold meets a `u64` asset type.
- **The FRI floor attachment** — 51 bits is a ledger number, not a bound on `verifyAlgo`. Briefed
  that an `axiom` would launder the exact thing the task exists to expose; the deliverable I want most
  is the precise statement of the first lemma the chain needs and does not have.

## Open for ember
0. ⚑ **THE GITHUB LFS BUDGET IS EXCEEDED**, so the adversarial suite has not run for at least two
   nights — `actions/checkout` with `lfs: true` fails in 57s. The staged registries are LFS-tracked,
   so every heavy job needs it. Nothing in code can fix this.
1. **F1?** — the only route that makes a successor to `RestHashIffFrame` satisfiable. Flag day:
   commitment epoch + descriptor re-emit + re-genesis, 234 binder positions across 85 modules.

