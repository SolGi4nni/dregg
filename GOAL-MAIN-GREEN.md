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

## Open for ember
1. **F1?** — the only route that makes a successor to `RestHashIffFrame` satisfiable. Flag day:
   commitment epoch + descriptor re-emit + re-genesis, 234 binder positions across 85 modules.

