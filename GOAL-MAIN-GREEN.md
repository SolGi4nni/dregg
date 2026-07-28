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

## Next 3 moves
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

## Open for ember
1. **F1?** — the only route that makes a successor to `RestHashIffFrame` satisfiable. Flag day:
   commitment epoch + descriptor re-emit + re-genesis, 234 binder positions across 85 modules.

