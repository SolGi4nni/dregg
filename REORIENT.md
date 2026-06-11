# REORIENT — read this first after any context loss

*(maintained for session continuity; update at every major landing. Last: 2026-06-11 ~01:00)*

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

## State of the world (2026-06-11, refinement night)

- main @ `d97b37d1f`, all pushed. **GitHub Pages: GREEN**.
- LANDED tonight: proof economics #161 (`c053ede33`, docs/PROOF-ECONOMICS.md —
  452 KiB per-turn = 92% FRI openings, 85% hash-site aux; ROOT is the external
  artifact) · README rewritten to teach what-is (`4c4172e04`) · **recursion config
  PRODUCTION strength** (`e1d6d1d26`: q=38+14 PoW = 128-bit conjectured, ROOT
  502 KiB / 16 ms / K-independent, in-circuit PoW check) · **THE HEAP Lean
  foundation** (`d97b37d1f`: Substrate/Heap.lean + HeapKernel.lean, root_injective
  anti-ghost, balance-neutral guarded step; splice plan in task #165 metadata).
- STILL RUNNING: language uplift (keystone) · devnet quality #159 ·
  graduate-all-selectors + DELETE hand-AIR fallback + kimchi/pickles backends.
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

## Ops crib

persvati for big cargo (`scripts/pbuild <lane> <cmd>`); lake builds local; FFI reseed
`dregg-lean-ffi/scripts/rebuild-dregg2-closure.sh` after Lean changes, BEFORE
lean-shadow tests; site builds in Docker node:22 (host lacks darwin lightningcss);
`git add` named paths THEN commit (never `commit --pathspec` on untracked, never -A);
`-c commit.gpgsign=false` when 1Password declines.
