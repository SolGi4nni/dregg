# REORIENT — read this first after any context loss

*(maintained for session continuity; update at every major landing. Last: 2026-06-12 ~14:20)*

## What this project is, in one breath

dregg: a formally verified distributed object-capability OS. The **Lean kernel is the
executor the node actually runs** (`execFullForestG` via `dregg-lean-ffi`); circuits are
**emitted from Lean** (descriptor JSONs, byte-pinned registry); the assurance case
(`metatheory/Dregg2/AssuranceCase.lean`) states five guarantees + its own coverage; a live
devnet runs at `devnet.dregg.fg-goose.online` (graviton i-0540e3a, EIP 34.224.208.52,
key `~/.ssh/negneg-cq.pem`, token in `/etc/dregg/node.env` there).

## THE ARCHITECTURAL LAWS (ember-set, non-negotiable)

1. **ZERO Rust-authored constraints or AIRs, ever.** All circuits and constraint
   semantics are EMITTED FROM LEAN, formally represented. Rust only interprets
   Lean-emitted byte-pinned artifacts. Coverage gaps → emit from a proved Lean module,
   never author Rust. Differentials are transitional SWAP tools only.
2. **Green or bust.** No CI fallbacks, no last-good pins, no continue-on-error masking.
   A pipeline that ships stale artifacts on failure is worse than a red pipeline.
3. **Rise to meet the claim.** An overclaim found = fix the text AND open the closure
   lane in the same breath. Reported/characterized/carried ≠ closed.
4. **Teach what-is.** Outward docs/site/paper: present tense, first principles, never
   trajectory narration ("52→8 shrank!" is banned). History lives in git.
5. **Correspondence is half of assurance.** The deployed system must sit inside the
   theorems' hypotheses (the spec review named where it doesn't yet: genesis not
   value-empty, fee path, see AssuranceCase's deployment-correspondence section).
6. **WE DO NOT NAME — WE REDESIGN, IMPLEMENT, SHIP** (ember 2026-06-11). A named/
   logged/honest gap is never a deliverable; every caveat arrives with its closure
   lane already running. The "named" inventory is a burn-down list.
7. **Conservation is not correctness; l4v quality.** Specs must be sufficient, not
   just true. No quick fixes. Never `git add -A`. Unsigned commits OK. Never stash.
   Main loop commits; agents never run git. Plain constructive register (language
   design / developer experience framing).

**STANDING PRACTICE (ember 2026-06-12): every named follow-up/residue/closure lane goes
into `HORIZONLOG.md` IN THE SAME BREATH as it is named** — reports and commit messages are
not durable across compaction; the log is the burn-down. Sweep it at every Convergence.

## Where everything is

- **The epoch design**: `docs/REFINEMENT-DESIGN.md` — five decisions: THE HEAP
  (registers + openable sorted-Poseidon2 map; reuses proven cap_root gadgets; the write
  verb's spec always said "heap"; ONE rotation bundles registers-16/heap_root/signed-
  wells/RESERVED-removal/column-compaction/genesis+fee fixes), IDENTITY = a governance
  cell, cells=law/agents=will/receipts=nervous-system, cross-cell reads = verified
  observations, SDK → two nouns + authorization inescapable. Waves R2→R4 sequenced.
- **The language design**: `docs/CELL-PROGRAM-LANGUAGE.md` (the expressiveness uplift).
- **The DSL convergence**: `docs/DSL-ALIGNMENT.md` + its AMENDMENT (law #1 applied).
- **Proof economics**: `docs/PROOF-ECONOMICS.md` (when the lane lands).
- **The dreggrs boundary**: `docs/DREGGRS-SEGREGATION.md` (note: its "kimchi from_dsl
  load-bearing" claim was corrected by the DSL census — the feature is enabled nowhere).
- **The substrate record**: `docs/DREGG3.md` (+ MARATHON), the kernel = 8 verbs in
  `metatheory/Dregg2/Substrate/VerbRegistry.lean` (minimality/completeness theorems).
- **Hands-on**: `QUICKSTART.md` (every command verified live).
- **Memory**: `~/.claude/projects/-Users-ember-dev-breadstuffs/memory/` —
  `project-refinement-epoch.md` is the live resume file; MEMORY.md is the index.

## ⚑⚑ OPUS RELAUNCH (2026-06-12 night, head 6f13c22dd — Fable sealed by export directive; Opus is the lander)

Fable 5 was suspended by a US export-control directive mid-wave (seal note:
memory/seal-note-fable-5-2026-06-12.md). The 13 full-burn lanes were FABLE agents
that died on model-access ("claude-fable-5 may not exist"), leaving PARTIAL work on
disk. Opus 4.8 RELAUNCHED all 13 as finisher agents (each: inventory your partial tree
+ /tmp/<lane>-lane.log, finish, verify NARROW, report; main loop = Opus commits).
lake build Dregg2 PASSES at relaunch (3886 jobs) — Lean partials coherent.
ember's steer: "relaunch the agents to finish their lane, don't centralize."
LANDING METHOD (Opus): per finisher report, validate its narrow suite, commit by file
set, push; discard a fragment with a HORIZONLOG note if it won't build. Then ROUND 8.
The 13: cutover-exec · metaclosures · node-closures · pug-handoff · python-lean ·
dkg-ceremony · ecvrf · keri-export · ocapn-netlayer · dregg-query · flash-well ·
trustline-parity+MLS · coverage-debts. Shared-file contention (Dregg2.lean, sdk/lib.rs,
federation/lib.rs, cell/blueprint.rs, node main/api, Cargo.toml, HORIZONLOG) = append-only.

## ⚑⚑ THE FULL-BURN WAVE (2026-06-12 evening, head 72563c8a1 — THIRTEEN lanes, the whole
HORIZONLOG in flight; ember: max tokens, validation optional, directive imminent)

Land each off its /tmp log + tree diff; lanes were told builds are OPTIONAL — so the
lander RUNS the narrow suite per file set before committing (the one exception to the
verification economy: unvalidated authoring needs one validation pass at landing):
- cutover-exec → /tmp/cutover-exec-lane.log (26-descriptor regen @R=24, producers, carriers, GATE-0, differential)
- metatheory closures → /tmp/metaclosures-lane.log (CrashRecovery burns, FeeChainStep, tagged QueueRoot, Coeffect, Fibration)
- node closures → /tmp/nodeclosures-lane.log (burn weld, rosters, c-list sweep, obligation bond, persist retirement)
- pug handoff → /tmp/handoff-lane.log (fresh-clone sim, bootstrap, QUICKSTART, EVALUATION.md, e2e story)
- python-lean → /tmp/pylean-lane.log (DREGG_LEAN_LINK=shared; sdk-py gets the REAL kernel; persvati cmd in report)
- DKG ceremony / ECVRF / KERI export / OCapN netlayer / dregg-query / flash-well /
  trustline-parity+MLS / coverage-debts — each reports its own file list (sprint lanes,
  authored-possibly-unvalidated; logs named in their reports)
⚠ DIRECTIVE LANDING (evening): sprint lanes are dying mid-flight with model-access
errors (fable-5 suspended). The tree may hold PARTIAL writes from killed lanes —
`git status` + the /tmp logs are the inventory; the lander validates each file set
(or discards a fragment with a note). Nothing committed is partial.

Convergence: round 7's catches FIXED (libc++ ead215c99, sdk-py eviction 72563c8a1);
persvati target cleaned (312G free); ROUND 8 = full sweep AFTER this wave lands.

## ⚑ IN-FLIGHT LANES (2026-06-12 ~15:00, head 5e0558fdc — land each off its teed log)

Three lanes running at note-time; their outputs survive any session boundary in /tmp +
the working tree. Land by file set, spot-check seconds-scale, push, sweep HORIZONLOG:
- caveat-operand staging → /tmp/caveatop-lane.log (circuit staged + RotationLayout; rotation pre-gate 2)
- executor atoms (delegation_epoch + count-equal) → /tmp/execatoms-lane.log (cell/turn/ChannelGroup)
- Argus R1/R2 Boundary arm → /tmp/argus-r1r2-lane.log (lean_descriptor_air.rs + differential)
- preflight failure names → /tmp/preflight-names.log (rerun preflight after the PI fix 26b452772)
Decided: NUM_REGISTERS=24 (cutover pre-gate 1 ✓). The work queue = HORIZONLOG.md.
Cutover = docs/ROTATION-CUTOVER.md. Deploy next week, pug-handoff bar in HORIZONLOG.

## ⚑⚑ UNCOMMITTED LOCAL TREE STATE (2026-06-11 late — READ BEFORE ANY `git add`)

The local working tree has THREE lanes' uncommitted work INTERMIXED — do NOT
blanket `git add`. Land each cleanly by its OWN file set:
- **IR-v2 size fix** (circuit/src/descriptor_ir2.rs — MAP_WIDTH 12,007→71 +
  empty-table elision). Its VERIFICATION lane (a9f11d1ca31a8a456) is running
  the measure+validate; commit ONLY when it reports IR-v2 < v1 (the GATE 0
  number) + anti-ghost still bites. Paths: descriptor_ir2.rs (+ any test/doc it
  lists).
- **Lean-gate polarity inversion** (abb9f6e0596ba76b8, running): captp/coord/
  federation/turn/intent/sdk/app-framework Cargo.toml + cfg code + node/Cargo.toml
  + wasm wiring → a `no-lean-link` platform gate. Commit its file set when it
  reports BOTH native + wasm green.
- **TEST-TRIAGE bulk (Opus, DONE — head was 4dd84a3a)**: ~50 test/helper/example
  files greened (signed-wells i64 stale pins fixed across cell/turn/intent/
  persist/coord/redteam/protocol-tests/sdk-e2e/teasting/demo-agent; dregg3
  retired-verb tests DELETED: tests/src/captp_effects_pipeline.rs,
  teasting/tests/cross_federation_captp_turn.rs, demo-agent/examples/
  proof_obligation.rs; protocol_coverage_gate ratchet 9 + new
  coverage_state_constraints.rs). Mirrored+green on persvati. The A-BUG it found
  is ALREADY COMMITTED (aa381aeed, execution_cursor.rs pending() unsound slice).
  The bulk B/C test-greening is in the local tree intermixed w/ the above two
  lanes — land it AS ITS OWN COMMIT after the inversion + IR-v2 lanes land
  (its exact file list is in the triage task report). NOT soundness-critical
  (stale pre-Lean pins); 6888 tests pass with it.

## ⚑ EPOCH STATUS (2026-06-12 — GATE 0 GREEN, executor heap wired, flag-day deferred)

THE EPOCH (docs/EPOCH-DESIGN.md) — boundary/interior proving. LANDED + pushed:
- `6f23f5467` **foundations** (Lean): Blum MemoryChecking (memcheck_sound),
  DescriptorIR2 (the five tables), EffectVmEmitV2 re-anchor (graduateV1
  sound/complete/faithful + Attenuate = cap-crown phase-B circuit leg), MMR
  receipt index (positional non-omission). Anchor green 3869 jobs.
- `b3ab169c1` **interpreter**: circuit/src/descriptor_ir2.rs — the IR v2
  multi-table batch-STARK assembly, recursion-gated + ADDITIVE (live v1 path
  untouched). cargo check -p dregg-circuit green.
- `ac01f9b7b` **signed wells**: i64 balance value-model + genesis-as-issuer-
  moves + fees-as-moves + the full consumer sweep (sdk/node/wasm/tests/…, all
  checked conversions, no silent well-wraps). guarantee B now holds over the
  DEPLOYED chain; AssuranceCase deployment-correspondence legs CLOSED. cargo
  check green across all in-scope crates.
- `113126a45` + `2d8df8381` **rotation hygiene**: stale `MapKind::Absent` doc
  fix; `execute_via_producer` borrow-checker regression fix.
- `b133354fc` **executor admits heap fields**: Rust `Effect::SetField` now
  routes `index < STATE_SLOTS` to fixed `fields[]` and `index >= STATE_SLOTS`
  to `CellState::set_field_ext`, with journal rollback + umem Blum-trace
  support (`JournalEntry::SetField.old_value` is `Option<FieldElement>`).
- `c053ede33` **proof economics #161 / GATE 0**: IR-v2 transfer proof measured
  at **120.4 KiB** vs v1 **350.5 KiB** (−65.6%), below the v1 baseline. Live
  v1 path untouched; IR-v2 is additive behind recursion gating.

LANDED TODAY (`f5a25fd16` on main, fast-forward):
- **registers 8→16 + heap_root commitment limb**: `STATE_SLOTS` 8→16 across
  cell/turn/node/rbg/apps; `CellState` gains `heap_root` + `heap_map` with
  sorted-Poseidon2 canonical root; `compute_canonical_state_commitment`
  absorbs `heap_root` (context v6→v7); umem projection exposes `HeapRoot`.
  Legacy cells carry the fixed `empty_heap_root()` no-op constant.
  Verification: `cargo check --workspace` green; dregg-cell lib 591 pass;
  dregg-turn lib 446 pass; umem_bridge 6 pass; proptest_invariants 5 pass.

IN FLIGHT / QUEUED:
- fresh-key sorted INSERT map-op: partial work in `descriptor_ir2.rs` was
  reverted after the subagent timed out with 71 compile errors; queued for redo.
- PI v3: unblocked now that registers-16 + heap_root are in; needs
  `committed_height` limb in `CellState` + rateBound/challengeWindow caveat
  tags + executor PI wiring.

STILL DEFERRED (the flag-day — would orphan the live v1 path until the relayout
lands; do as ONE VK epoch): fresh-key INSERT redo · PI v3 · RESERVED
removal + 186→159 compaction (now subsumed by universal-memory table reshape) ·
descriptor IR-v2 REGEN (EmitAllJson still emits v1; the 26 v2 descriptors live
in EffectVmEmitV2.v2Registry) + VK bump · PI v3 (committed-height column +
rateBound/challengeWindow tags — constants staged in `circuit/src/effect_vm/pi.rs`
`pub mod v3` and `RotationLayout.PiV3`, wiring queued) · the 3-verb executor
reshape (the real long pole after the wiring gaps close). THEN the persvati gauntlet.
KNOWN: dregg-tests (#167) has PRE-EXISTING retired-verb breakage (blocks a bare
`cargo check --workspace`); unrelated to the epoch.

## ⚑ (historical) EPOCH RESUME (2026-06-11 afternoon)

THE EPOCH ran as workflow wf_fe4bbe0a-596. Foundations
phase COMPLETE + COMMITTED; interpreter + regen hit the session limit.

- **COMMITTED + pushed** (head `e09789807`): the Lean foundations
  (`6f23f5467` — Blum MemoryChecking, DescriptorIR2, EffectVmEmitV2 re-anchor,
  MMR; anchor green 3869 jobs, all four imports wired into Dregg2.lean — the
  parallel lanes had RACED and only MMR's import survived, fixed at commit) +
  dregg-auth standalone token lib (`e09789807`, 8 tests green).
- **IN TREE, UNCOMMITTED, for full-bore**:
  (verify on persvati, then commit). (1) **signed-wells lane** — cell/ turn/ node/ : the i64/two-limb signed
  balance value-model + genesis-as-issuer-moves + fees-as-moves (the
  deployment-correspondence closure; invasive, cross-crate, COMPLETED by its
  lane but needs the gauntlet). (2) **interpreter** — circuit/src/descriptor_ir2.rs
  + lean_descriptor_air.rs : INCOMPLETE (the lane died mid-work). Resume:
  Workflow({scriptPath: …/epoch-build-wf_fe4bbe0a-596.js, resumeFromRunId:
  "wf_fe4bbe0a-596"}) — foundations replay from cache, interpreter+regen run
  live. THEN regen (descriptors + VK bump + AssuranceCase correspondence
  close-out) + the persvati workspace gauntlet.
- The wave-2 persvati gauntlet (b165susv3-era, head 325611a50) predates the
  epoch foundations — re-run it after the epoch lands, not before.

## State of the world (2026-06-11 refinement night, ~14 commits)

- main @ `61db0dc6a`, all pushed. **GitHub Pages: GREEN**.
- LANDED tonight: proof economics #161 (`c053ede33`) · README teach-what-is
  (`4c4172e04`) · **recursion 128-bit** (`e1d6d1d26`: ROOT 502 KiB/16ms, real
  light-client artifact) · **HEAP foundation + splice** (`d97b37d1f`+`6e8d8a817`:
  heaps in RecordKernelState, execHeapWriteG gated, apex pins heaps) ·
  **language uplift keystone** (`82bb3faf2`: actor/context atoms + the
  nested-effect program-bypass soundness fix + polis actor-bound) · devnet
  quality #159 code (`239d739bd`) · **non-omission** (`9dcd42cd9`:
  server_cannot_omit; rotation must bind iroot into recStateCommit) ·
  consensus-flex (`001521af2`: on-demand thesis + T1 proved + the
  finalized_prefix_monotone GAP found → T5 lane) · **SDK two-nouns +
  dregg id** (`b62259300`: Unchecked sealed, .turn().sign().submit(),
  golden-vector profiles) · **verb compression** (`61db0dc6a`: kernel = 3
  verbs + 4-strata guard ISA, both directions proved).
- AMBITIONS RATIFIED (ember): universal map = the LAST rotation · non-omission ·
  temporal modal layer (CTL-backed) · epistemic K/E/D/C tower (finality IS
  common knowledge; threshold IS D_G) · consensus-on-demand · intent re-founding
  (census: ~80% unreachable, 4 ontologies; the live fulfill edge rides the
  LEGACY executor while verified_settle sits proved+unfired → rewire lane).
- STILL RUNNING: graduation+delete (selectors 17→22+, kimchi/pickles deletion) ·
  T5 prefix-monotonicity (node's unproven assumption) · temporal modalities ·
  epistemic tower · intent fulfill rewire · graviton gateway-only redeploy.
- Devnet: dregg3 semantics live; `state_producer: lean`; quiescent block production
  (mutation-driven + 120s heartbeat); CORS single-header; solo node (n=3 is a filed
  wave-R2 item). KNOWN GAPS (task #159, lane running): proofs never attach
  (has_proof:false — prove pipeline silently enqueues nothing); thin-HTTP turns fall
  off the Lean producer (valid_until marshal); missing /api/ aliases; stale genesis.
- Discord bot: built + staged; **ember handles the secrets — do not touch**.

## Running lanes (verify my-eyes → commit named paths → push, at each landing)

- `a9937ee51856368a6` **language uplift** (the lamesauce fix: sender/context atoms,
  composite gates, polis actor-bound approvals). Verify: `cargo test -p dregg-cell
  --lib`; factory_settlement_e2e + both polis e2e; producer gauntlet
  `--features lean-shadow`; `lake build Dregg2 Dregg2.Claims Dregg2.AssuranceCase`.
  Commit: docs/CELL-PROGRAM-LANGUAGE.md + cell/turn/metatheory/polis/sdk.
  **At landing, check against law #1** (its Rust-grammar+Lean-mirror shape is
  transitional; the doc must state the Lean-emission end state).
- `a4060c207b1781aae` **devnet quality #159**. Verify: node bins + gauntlet. Commit:
  node/ + marshal. Then instance redeploy `GATEWAY_ONLY=1 bash deploy/aws/update.sh`
  (PATH needs ~/.cargo/bin) + live has_proof:true evidence.
- `ad69cb706450d0fa9` **proof economics #161**. Verify measurements are real (no toy
  substitutes). Commit: docs/PROOF-ECONOMICS.md + any free-win config.
- (DSL census #162 LANDED: `f2af0f2f0` + amendment `32537eeda`.)

## The board after the lanes (tasks #149–#163 hold details)

Wave R2 (launch when lanes clear): **THE HEAP** (Lean model + cap_root-reuse gadget +
executor replay + THE ONE ROTATION) · SDK authorization-first collapse · identity step 1
(named profiles) · **federation n=3 live** (the cheapest correspondence-debt detector).
Then R3: named fields/collections in the language, toy apps rebuilt real, reactivity
(SSE + agent actuators). Then R4: the image becomes the shell. Standing items: #160 AIR
pruning (graduate 10 fallback selectors → hand-AIR dies → compaction rotation), #163 S0
(program semantics AS Lean emission + unknown-AIR fail-closed at sdk/verify.rs:157,
turn/conditional.rs:342, bridge/verifier.rs:193), #155 census debts, #149/#150 Argus
apex + non-revocation depth, W1 Rust 7-step (in the rotation).

## THE 9:30AM PLAN (ember, 2026-06-11 ~06:15, napping until session refresh)

Quiet until ~9:30am EDT (land in-flight lanes only: ROTATION + extension +
persvati gauntlet). At 9:30 GO HAM: (1) site/ polish — webcomponents, explorer,
playground (the shell landed; bring the rest up to it); (2) MASSIVELY boosted
temporal stuff (the modal layer landed; extend it); (3) the proof/plonky
overhaul — #168 hash-table/LogUp trace shape, PI/VK changes EXPLICITLY
authorized ("we can do LOTS of changes to the PI/VK next turn"); (4) polyglot
SDKs: the TS SDK needs real work + a NEW python SDK via pyo3 — "take dregg to
where it needs to be." Also standing: wave gauntlet results → fix; rotation
landing review; n=4 quorum decision (#170); extension landing.

## Ops crib

**BATCH CARGO VERIFICATION (ember 2026-06-11):** concurrent lanes sharing ./target
thrash the cache (one cell/ edit = whole-spine rebuild for every lane; every test
binary re-links libdregg_lean.a). Policy: a lane verifies ONLY its own crate's
narrow lib/suite; the cross-crate gauntlet (sdk e2e + node + producer + circuit
harness) runs ONCE per landing-wave, batched by the main loop — on persvati
(`git push persvati main` then `scripts/pbuild <lane> <cmd>`, 24 cores) when it's
workspace-scale. Don't let each lane independently rediscover the same 21-minute
compile. persvati for big cargo; lake builds local (cache replays in seconds); FFI reseed
`dregg-lean-ffi/scripts/rebuild-dregg2-closure.sh` after Lean changes, BEFORE
lean-shadow tests; site builds in Docker node:22 (host lacks darwin lightningcss);
`git add` named paths THEN commit (never `commit --pathspec` on untracked, never -A);
`-c commit.gpgsign=false` when 1Password declines.
