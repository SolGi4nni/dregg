# REORIENT — read this first after any context loss

*(maintained for session continuity; update at every major landing. Last: 2026-06-20 — THE ASSURANCE EPOCH: soundness ground-truthed, goal = "safely live within dregg", VK-freedom era)*

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

## ⚑⚑⚑ CURRENT STATE (2026-06-20 — Opus 4.8 1M; THE ASSURANCE EPOCH — soundness ground-truthed, the goal = "safely live within dregg")

THE FLIP LANDED long ago (the 2026-06-14 block below is dead history). The work since is a deep ASSURANCE epoch:
the circuit-soundness reckoning closed (the byte-identity "differential" was hiding that `Satisfied2` didn't
denote the deployed verifier — now it does: kernel bridge `decideSatisfied2_iff`, the mapDec oracle DISCHARGED,
the differential runs REAL deployed machinery `Ir2Air::eval` + `verify_global_sum`, the floors proven non-vacuous,
the keystone made whole). A live cross-asset CONSERVATION hole was found + closed (executor path; light-client
bundle PI residual named). The ENMESHMENT CENSUS mapped the whole tower: executor↔spec is WELDED (43 keystones,
all 57 arms; the Lean executor IS production, Rust runs it via FFI), all 30 effects spec-welded, settlement welded
to the apex (one rung), the multi-turn stack now rests on the apex too (EngineSound weld). 72 orphans enmeshed
(their #assert_axioms pins now run); 8 rotted-but-hidden modules found, 2+6 being repaired.

THE LIVE GOAL: **"safely live within dregg"** (ember moving Claude into an autonomous harness inside dregg/deos).
Decomposes into two floors: (1) AUTHORITY — guarantee A circuit-FORCED (a circuit-descriptor edit reds the apex)
for ~26/30 effects + apex-wired for 13; the tail (3 frozen-face cap slots + receiptArchive + heapWrite) is
DRIVING NOW (VK-FREEDOM ERA — VK changes are no longer deploy-gated, just ship the truthful fix). (2) HUMAN/
RECOVERY ("cannot lose your OS") — durability core SOUND (upsert + fail-closed, both paths); the recovery→circuit
binding is the remaining weld. THE GENESIS REFRAME (ember): the persist durability "bug" is a CATEGORY ERROR —
build-time customization → the IMAGE (EROS factory, sealed+attestable ISO), runtime → a TURN; mid-session genesis
mutation can't exist. Phase 1 (dissolve) + Phase 2 (image-builder) building now.

⚑ THE DURABLE RECORD: HORIZONLOG.md top ~400 lines = the true frontier (the rest is closed-but-logged, sweepable).
The memory index + its flagged files. NOT the block below (dead epoch). The frontier is SMALL and fully named:
the soundness tail above + 6 peripheral rotted orphans + the l4v marshal translation-validation (own multi-week
lane) + the apexLowers distributed-modernization (own lane). Devnet redeploy: the SSH box was LOST (2026-06-20);
keep the artifact green + pushed to origin/main, redeploy when a box returns.

## ⚑⚑⚑ (SUPERSEDED ↑ 2026-06-20) CURRENT STATE (2026-06-14 — head `6fb9e8087`, Opus 1M; THE FLIP IS NOT YET READY (walls A/B/C + the wasm-prover decision) + ~16 overnight wide-safe commits)

**THE ROTATION DESCRIPTORS ARE CORRECT + GREEN — the magnesium PROOF work is DONE.** Every cohort effect's
rotated descriptor rotates, source-coherent, axiom-clean (lake `Dregg2` 3922 jobs axiom-clean; the
`effect_vm_rotation_flip` flip test 4/4). The model has STOPPED finding flip-blocking *descriptor* gates.
The night closed the last sub-descriptors: NOTE-SPEND (`cc1e1399c` — rotated nullifier at PI[38] + a
model-found single-spend double-spend guard), CAPABILITY (`f967f39b0` — real-Cell authority digest r23, the
over-grant tooth survives rotation), SETFIELD+BRIDGEMINT (`e9d6e357e` — 3 model-found descriptor mismodels
enforced-fixed), and SOURCE-COHERENCE (`05fe8a500` — the per-effect SetField/Mint SOURCE descriptors
reconciled to runtime, rotated tick-faces proved `:= rfl` EQUAL to source, JSON byte-identical so the live
wire is UNTOUCHED). `setFieldDynV3` is proven STRUCTURALLY UNREACHABLE (coherence-only, not a flip-blocker).

**THE FLIP IS NOT YET READY** (the flip-executor's honest inventory — the flip was ATTEMPTED and correctly
NOT TAKEN: the staged tree is GREEN, NO edits were made). The rotation descriptors being correct+green is
the magnesium PROOF being complete; it is NOT the LIVE-PATH cutover. The earlier "flip-safe, all gates
closed" was an OVER-CLAIM (rise-to-meet-the-claim correction) — §EXEC.3's "WHAT'S STILL GATED" was the
accurate read, and it is UNMET. Three walls + an architecture decision gate even C5-(1):
- **WALL A** — `prove_full_turn` (`sdk/src/full_turn_proof.rs:1042`) calls `generate_effect_vm_trace` (the
  v1 186-col AIR) UNCONDITIONALLY; the rotated leg is an ADDED sub-proof under `witness.rotation.is_some()`,
  and `CutoverFallback` (`:568`) is the live routing. FIX: make the rotated PI the composed-PI / VK-hash
  source so the v1 backbone can go; retire `CutoverFallback`.
- **WALL B** — `verify_aggregated_bundle` (`turn/src/aggregate_bilateral_prover.rs:185`) reads
  `wr.public_inputs[..ACTIVE_BASE_COUNT]` (the v1 PI slice). FIX: carry the 49-felt schedule block in the
  witnessed receipt so the bilateral verify stops reading `effect_vm::pi`.
- **WALL C** — the FLOW-B note-spend freshness arm (`node/src/blocklace_sync.rs:2667`, the
  `(None,Some(nullifier))` arm) calls `prove_and_verify_finalized_turn_freshness` with NO rotation. The
  descriptor is READY (`rotateV3WithNullifierPin`); the gap is the live node wiring + composed-PI binding.
  FIX: thread the rotated nullifier descriptor into that call site.
- **THE WASM-PROVER DECISION (ember's call)** — v1 is the `#[cfg(not(feature="recursion"))]` wasm
  verify+PROVE path; `wasm/src/runtime.rs:710` calls `generate_effect_vm_trace` directly (the in-browser
  prover uses v1, because the IR-v2 prover pulls p3-recursion/DFT crates that don't fit wasm). So C7
  grep-zero (deleting v1) is PROVABLY IMPOSSIBLE while wasm proves in-browser on v1 (134 live refs to
  `generate_effect_vm_trace`, 108 to `EffectVmAir`). **DECIDED (ember, 2026-06-14): Option A** — build a
  wasm-fittable rotated prover (replace the p3-recursion/DFT deps for the in-browser path) so wasm proves on
  rotated TOO → v1 dies EVERYWHERE, true grep-zero, the web keeps in-browser proving. A FRONTIER build added
  to the pre-C7 work (the DFT/recursion-in-wasm problem is real); C7 deletion waits on it.

These four are the REAL gate before C5 can open. A flip-executor agent inventoried (did NOT cut). **The
persvati workspace gauntlet + the held push (~30 commits) + the devnet redeploy remain HELD for ember at the
redeploy point-of-no-return** (the redeploy is ember's act — fresh genesis), behind the four above.

**S5 CLOSED (`ed35b23b2`):** the running node now COMMITS a turn through the ordering rule at n≥2 — finality
fires cross-node (`three_node_ordering_rule.rs` green under `REQUIRE_FINALITY=1`; n=3 CONVERGED `latest_height
1 1 1`). Four measured defects closed (Dandelion stem misroute · chain-not-round DAG · half-duplex gossip
connections [the root cause] · finalized-turn double-apply). This is the distributed thesis, RUNNING. A
faucet/finalized-execution production-hardening pass is the named follow-up (lane running; devnet-correct
today, NOT blocking).

**~16 OVERNIGHT WIDE-SAFE COMMITS** (while the flip is held, a 5-lane braid — each green by file set, each
naming its honest scope-limit in HORIZONLOG): cli `DREGG_HOME` hermetic config + preflight (`9427a18e5`/
`f9f93c43d`) · web-forward browser face + Worker-proving + browser-EXTENSION front door + N13 killer-demo
page (`95fe7cc61`/`2dcede9b3`/`8a8ab52ba`/`6fb9e8087`) · ADOS cockpit swarm-budget/narration-vs-truth/
coordination-graph + the four-surface N5 killer demo (`eeb5655f2`/`1535f46a7`) · the browser-extension &
ADOS panels · persist `compact_below` bounded WAL (`9f031f7e8`) · two apps (supply-chain-provenance
`a2998d519` single-custody-as-conservation; starbridge-swarm-orchestration `f8aec4aba`) · pg-dregg cookbook/
caps-as-rows-explorer/submit-queue-drainer/dev-mint (`407537e63`/`eaef6a214`/`929060662`) · pg18 native
features (`4bef409bb`) · the embedded-Servo + distributed-Servo + mixed-OS DESIGN corpus (`261bdf7ed`/
`b7ff641bc`/`0fc7912f7`/`2f3f47ad4`/`15fc03fb6`).

**MILESTONE STATUS:** silver / magnesium / gold **STRONG** (magnesium is **PROOF-complete** — descriptors
correct+green; the LIVE path is GATED on walls A/B/C + the wasm-prover decision before the graduated path
becomes the default). diamond **IN PROGRESS** — the named gap is the **l4v BINARY BRIDGE** (two
obligations: translation-validation of `dregg-lean-ffi/src/marshal.rs` as a THEOREM `marshal_turn_hosted =
encodeWWire ∘ lift`, the codec-in-TCB seam; + the Lean→C/`.a` link correspondence that the linked
`libdregg_lean.a` IS the `@[export]`ed Lean. Stage 0 = invert `turn/src/lean_apply.rs:~1143` to make Lean
authoritative, "no new mathematics"). devnet-golden **CLOSE** — the node commits at n>1; the redeploy is
held for ember. The forward work is captured in **`docs/NEXT-WAVE.md`** (ready-to-fire, each with its lever).

## ⚑⚑⚑ (SUPERSEDED ↑) CURRENT STATE (2026-06-13 LATE — head `d4adcc765`, Opus 1M; the REFINEMENT BRAID — 5 commits banked, cutover at C4, notify FINISHED)

ember's mode: **BRAIDS not waves** ([[feedback-braids-not-waves]]) — finish a cluster, immediately launch/integrate the obvious next; the main loop is a continuous launcher+integrator (commits agent drafts by file set); **proofs are subagent work**. A full 20-doc orientation pass is done (notify · pg-dregg · desktop-OS · seL4 · assurance-critique · cutover · starbridge).

**LANDED this session (5 commits, all green + axiom-clean):**
- `d51dc74df` **cross-cell imports** (`Authority/CrossCellImport.lean` — gap 6, "the deepest naturalness gap", DISSOLVED: an import cites a source receipt + the value its field held there; the crown `importValid_stable_under_source_advance` proves a past-snapshot import is I-CONFLUENT where a live read is not; tamper-evidence inherited from `Exec.Receipt.chain_tamper_evident`, HInj/HFresh stay named hyps) + **2 real integrator-wedge apps** (`Apps/{AgentOrchestrationBudget,EscrowDeskCouncil}.lean` — the six primitives buildr/builders/sig/simbi hand-roll, lamesauce refuted, teeth both polarities).
- `d70046a88` + `bae653495` **CUTOVER C4**: the two recursion consumers + the FLOW-B SDK leg rewired onto the rotated leaf-wrap; the **bilateral aggregation AIR EMITTED FROM LEAN** (`Circuit/Emit/EffectVmEmitBilateralAgg.lean` + a NEW two-row `windowGate` IR-v2 primitive in `DescriptorIR2.lean`; soundness teeth `agg_rejects_turn_mismatch`/`agg_rejects_bad_agent_count`).
- `3ffc3af0c` **cell-program language atoms** (`Exec/Program.lean`: `senderMemberOf` + `affineDeltaLe` + `balanceDeltaLe/Ge` — the apps-surfaced expressiveness; the flash-well `BalanceDeltaGte` twin now landed).
- `d4adcc765` **NOTIFY STEP 2 FINISHED** (staged — VK **BYTE-IDENTICAL**, no cap emits `[.notify]` yet): the `Auth.notify` ctor (`Authority/Positional.lean`) + α total on all 7 seL4 IPC authorities + NotifyAuthority re-bound onto the real Auth (`notifyCap_confers_no_edge`) + the full ripple (rise-to-the-claim: found 2 "every Auth" sites the divergence-finding missed) + `Firmament/SeL4Composition.lean` (a dregg turn in a PD preserves BOTH the seL4 cap-space invariant AND dregg non-amp, same grantOk witness). The VK-touching tail (cap-leaf badge-mask + verifier re-pin) rides the cutover's ONE VK epoch — `docs/NOTIFY-STEP2-VK-CHECKLIST.md`.

**LIVE BRAID (running):** cutover-tail relaunch (`a99329b58` — the bilateral Rust interpreter [decode `windowGate` + restructure the WR 49-felt schedule block + rewire `aggregate_bilateral_prover.rs`, retire `bilateral_aggregation_air.rs`] + node FLOW-B producer threading + the ~70 call-sites → C5 regen → **C7 delete v1 + grep-zero**; C5/C7 = the coordinated VK-epoch **SETTLE the main loop runs**, batching notify's felt-encoders) · apps-round-2 (rebuild weak toy apps on the new expressiveness).

**HELD for the cutover-settle:** starbridge-v2 **A2 swarm surface** (`swarm.rs` — the notify async edge; blocked ONLY by the known **p3-recursion fork seam** — starbridge-v2 + sel4 are separate workspaces lacking the breadstuffs `[patch]`; fix = push the fork `72ffc56` + retarget revs + drop the local patch) · the notify VK-batch · the dead-pg-dregg-agent draft (pg-dregg M3 is post-flip anyway, but M2+Tier-C are LIVE on pg18).

**THE l4v ROADMAP (post-cutover, `ASSURANCE-CRITIQUE.md` §5):** the Lean composition is strong (`deployed_system_secure` apex; unfoolability derives conservation). The distance to l4v-grade is the **binary bridge** — **Stage 0 = make the verified executor authoritative (invert `turn/src/lean_apply.rs:1143`, "no new mathematics")**; Stages 1-6 = spec→binary refinement / discharge `leaf_sound` / tie the apex to one turn / native UC / n>1 consensus (**S5-1** = the gossip-dissemination blocker, `docs/STAGE5-CONSENSUS-DEVAC.md`) / config-pin the crypto floor. seL4 step-4 is DONE (the verified executor runs a turn inside a booted PD).

## ⚑⚑⚑ (SUPERSEDED ↑) CURRENT STATE (2026-06-13, head db046eaf2 — Opus, +20 commits; CUTOVER C1+C2 LANDED · C3 WALLED+SCOPED · REORIENTING TO THE DESKTOP-MESHING DEVNET)

A long brave-fanout continuation (~18 commits, persvati-gauntlet-green incl. the v8→v9 cap-crown ripple).
Landed: the Gerwin-Klein critique (`docs/ASSURANCE-CRITIQUE.md`) + **Klein CRITICAL-2 (wire codec) CLOSED both
halves** (Lean `Refine.lean` export-refines-model + the Rust marshaller conformance-gated to the proof); the
composed `deployed_system_secure` apex + conserves-from-verification (#2/#3); **cap-crown #103 finished as the
cutover gate** — RevokeCapability graduated (in-circuit non-amp + cell-TOMBSTONE binding; cap-root v2→v3,
commitment v8→v9) + Custom graduated via a new **`ProofBind` recursive-binding IR constraint** → **THE ROTATION
RESIDUE IS EMPTY** (all ~36 effects rotate); **the verified Lean executor RUNS a real turn on aarch64**
(`3f188ef60` — ELF Lean runtime from lean4@d024af099, status:2 accepted, anti-ghost holds; remaining = host on
the seL4 root-task-with-std substrate); an n=3 consensus slice runs the ordering rule (frontier = gossip
dissemination, `docs/STAGE5-CONSENSUS-DEVAC.md`); pg-dregg PgSink + starbridge cipherclerk/⌘K-palette.

⚑⚑ THE CUTOVER — C1+C2 LANDED (`0db2e44e8`), C3 IS A REAL WALL (the recursion knot), and its closure lane is RUNNING.
The rotated path is PROVEN end-to-end (all 36 effects rotate; residue EMPTY) and the sovereign matched pair is
live-green with the MEASURED win (350.5 KiB → 120.4 KiB, −65.6%, verify 3.4×). **C1** = sovereign FLOW-A produce+verify
rotated (`cipherclerk::prove_sovereign_turn_rotated` ↔ `executor::verify_and_commit_proof_rotated`, hand-AIR retired
on that path; new default-on `recursion` feature, wasm `not(recursion)` keeps v1). **C2** = prover-free verify split
(`verifier` feature on dregg-circuit compiles `verify_vm_descriptor2` without the prove_batch/DFT link). **C3 = THE
HARD WALL** (NOT a disempowerment — confirmed by reading the code): the live full-turn proof and the recursion layer
are ONE KNOT. `prove_full_turn` mints the `EffectVmP3Proof` that THREE LIVE recursive surfaces re-prove as the v1
186-col statement — `circuit/src/ivc_turn_chain.rs:507` (lightclient WholeChainProof, in-circuit *uni*-STARK leaf-wrap),
`circuit/src/joint_turn_aggregation.rs:67/94` (aggregation AIR on `EffectVmAir::new` directly), `turn/src/
aggregate_bilateral_prover.rs` (node bilateral bundle). There is **no in-circuit verifier / leaf-wrap for the rotated
MULTI-TABLE `BatchProof`** in the recursion fork, so the live proof can't rotate and v1 can't be deleted while they
stand. THE DECISION (ember's): (a) build the batch-proof recursion wrap · (b) re-architect the whole-history recursion
· (c) freeze a v1 leaf for the recursion layer while the live single-turn path rotates (double-mint). **DECISION-ENABLER
RUNNING:** background workflow `wong1ps3v` (`c3-batchproof-recursion-scope`) — three readers (recursion-fork in-circuit
primitives · what `verify_batch` actually checks · the three consumers' minimal needs) → a tractability verdict
(bounded-build vs fork-surgery) + a/b/c recommendation. Read its result before making the call. (Advances Klein CRITICAL-1.)

⚑ THE REORIENTATION (2026-06-13): the desktop-meshing devnet does NOT need v1 deleted to ship — it runs on the live
path (v1 proofs are fine for a devnet) and flips to rotated the instant the knot releases. So: point attention at the
devnet (firmament `Target::Surface` + starbridge-v2 + the seL4 step-4 substrate, lane `ae3d052e` running), and let the
C3 scope verdict decide whether v1 dies BEFORE or AFTER first deploy. Only build the (c) double-mint if we want
rotated-live proofs before the (a) wrap lands. pg-dregg is now pg18-native (`db046eaf2`).

DONE-BUT-DEFERRED: pg-dregg LIVE pg17 confirm-run (code green, blocked on the local lock); the warnings-import
sweep (protocol-tests/tests/teasting unused imports); the cap-crown `EmitCapRoot` doc note + the Phase-D 4-ary-leg
ember-decision (HORIZONLOG). KLEIN §5 l4v roadmap: Stage 0 (executor authority) is next-after-cutover; Stages 1-6
in ASSURANCE-CRITIQUE.md §5.

## ⚑⚑⚑ (SUPERSEDED by CURRENT STATE above) head a0d0d45d3 — cutover-parked / cap-crown-the-gate snapshot

Resumed post-compaction; landed 8 commits by file set (each narrow-verified):
`34dbca54a` starbridge-v2 coverage · `29c51bde3` metatheory assurance frontiers + Klein #2/#3
(composed `deployed_system_secure` apex; conserves-from-verification — `StateChained` derived now;
the macaroon↔kernel-cap arrow `chainGateG⇒capAuthorityG`; host-correspondence) · `84e4409db` the
Gerwin-Klein assurance critique (`docs/ASSURANCE-CRITIQUE.md` — the deliverable; honest verdict:
abstract kernel sound / deployed-binary bridge unverified / NOT l4v-grade; §4 = a 16-item TCB
manifest; §5 = closure roadmap Stages 0-6) · `5df9a091a` flip G3 (r23 full-authority digest — a
real soundness fix) · `59eef48dd` flip G4 (cohort-general generator) · `231c70c39` pg-dregg M2
(node→pg verified mirror) · `fb2da3600` seL4 v0 source · `a0d0d45d3` cutover STEP 1 (rotated
v3Registry 26→34 + an EmitEvent sorryAx fix).

⚑ THE CUTOVER IS PARKED at step-1 by EMBER DECISION (2026-06-13): **"finish cap-crown #103 first."**
Step 2 (the live-path rewrite, ~70 call-sites + executor PI reconstruction) is NOT started. Full
v1-deletion is HARD-GATED on 2 residue effects: **RevokeCapability (sel 24)** — needs its in-circuit
cap-root advance from the cap-crown reshape (#103); **Custom (sel 8)** — needs a new accumulator
constraint kind the per-row IR lacks. Sequence: cap-crown #103 → unblocks RevokeCapability → ONE
clean cutover deletes v1 entirely (no fallback tail). A read-only cap-crown state-mapping agent is
running (A-F stages + the RevokeCapability critical path); plan/launch the cap-crown completion off it.
The parked cutover checkpoint is `a0d0d45d3`; ROTATION-CUTOVER.md §2c/§3 has the precise remaining steps.

UNCOMMITTED RESIDUE (tree not clean): a warnings-import sweep (protocol-tests/ + tests/ + teasting/,
unused-import removals — needs a `cargo check` before commit), sdk-ts/dist + wasm/Cargo.lock (DreggDL
dist/lock propagation). PENDING: a persvati workspace gauntlet on the committed tree + push (HELD —
the Rust tree had no full `cargo check --workspace` since the flip-G3/G4 + pg-dregg commits).

KLEIN ROADMAP (→ §5 of ASSURANCE-CRITIQUE.md; the post-cutover l4v program for ember to call):
Stage 0 make the executor authoritative (invert `lean_apply.rs:1143`) · Stage 1 spec→binary
refinement · Stage 2 derive `leaf_sound` + empty the hand-AIR partition · Stage 3 apex over one
turn/history · Stage 4 real UC (native CryptHOL-in-Lean) · Stage 5 n>1 consensus that runs the
ordering rule · Stage 6 config-pin the crypto floor. Other open: pg-dregg live-pg17 e2e + PgSink async
stub · seL4 walls (leanrt ELF runtime; net RX-ring → DHCP bind) in the per-PD WALL.md · starbridge
seal/destroy effect-gate.

## ⚑⚑⚑ LATE-NIGHT STATE (2026-06-13, ~32 commits — the swarm-of-surfaces wave + the TOY AUDIT)

After the rotation engine landed (`15353932c`, G1+G3 — the flip is now mechanical), ember
opened a broad surface wave (master-interface swarm, discord, pg-dregg/pg17, MCP, perf,
firmament, paper) AND forced a TOY AUDIT that found a real recurring failure:
- ⚠ **THE TOY DISEASE (caught + being repaired).** My swarm briefs said "don't edit
  Cargo.toml / build on existing deps" — which FORCES agents to REIMPLEMENT a real
  subsystem when the real thing is in an un-depended crate. Hit 3× in the starbridge-v2
  swarm: `cipherclerk.rs` reinvented `dregg_sdk::AgentCipherclerk` (FIXED — real now,
  `4bfbdef79`-era lane); `world.rs` reinvented `dregg_sdk::DreggEngine` (its own comment
  referenced it!); `edit.rs` reinvented `dregg-userspace-verify::analyze`. The scar +
  4-point fix is in memory [[feedback-argus-orchestration-method]]. **EVERY swarm brief now:
  name the real component, forbid reimplementation, "report a missing dep/route — never
  reinvent," main loop does the dep-add + wiring.**
- **STARBRIDGE INTEGRATION PASS (running, a1d1f9d — I REVIEW its diff before commit).**
  De-toys the foundation: world→DreggEngine, edit→real analyze, fixes replay.rs
  `fork.diverged()` (gpui-only bug), wires the 4 panels (debug/replay/cipherclerk/editor)
  into cockpit, builds native-full green + window opens. The 4 modules are on disk; cipherclerk
  is already real; dregg-sdk dep already added.
- **DISCORD SWARM (2 of 3 running; HELD for integration).** assets/protocol + identity-polis
  (DONE, real — `/council-approve` real turn, cipherclerk real macaroons) + explorer/ops.
  Crate currently RED on a sibling 1-liner `commands/handoff.rs:90` `short(&fed_id,24)` wrong
  arity — I FIX that + wire the reported main.rs registrations at the discord integration pass
  when all 3 land. (Note: `discord_caps.rs` is a CapTP action-registry, NOT a per-command gate;
  real authz = cipherclerk Ed25519 signing + executor enforcement.)

### ⚑⚑ THE AUTHORIZATION MODEL — the foundational thread (study running, a5056ab)
ember (2026-06-13): "we need to DEFINITELY figure out how to actually integrate these major
foundational aspects of the token/authorization model... we're supposed to have a dual
multiaspect **biscuit/macaroon/cap/zk**... something was missing somewhere and never worked
out enough." The cipherclerk audit (`docs/CIPHERCLERK-AUDIT.md`, `4bfbdef79`) found the seam:
the agent MACAROON layer (federation-membership tree) and the kernel CAP-CROWN (in-circuit
c-list `granted⊆held`, #103) are UNINTEGRATED — a token authorizes at the macaroon layer while
the cap-root knows nothing; non-amplification is told as TWO informal stories, not one proven
arrow. ⚑ ember GUARDRAILS (do not violate): (1) it's FOUR aspects, not "two trees to collapse"
— integrate, don't reduce; (2) **the cipherclerk IS a sovereign executor BY DESIGN** ("someone
needs to execute sovereign nodes, that's where they go") — the "overloaded clerk, split it"
audit point is RETRACTED; (3) DON'T prematurely foreclose what's been built. Study →
`docs/AUTHORIZATION-MODEL.md` (the 4-aspect map + recovered intent + seam diagnosis + staged
integration). This is the deepest open thread. Possible convergence extends #103.

### Commits since the 14-landing block (15→32)
ebaad4f14 shell · def4c3f6d playground · a7734efcc DreggDL · f4d0efa5d analyzer+members ·
152e6b3a5 seL4-scaffold · dc750e1d7 snapshot · fd9763dce starbridge-scaffold · 51850ee91
rotation-staged · 870bb0f7f demo · bfe802c1b pg-dregg-proposal · efa548ee1 pg-dregg-M1 ·
5eae45bd1 pg-dregg-storage · cfea479d5 pg-dregg-DX · 1366d6026 pg17 · e5303e958 starbridge-
master · 58ee5bbab Robigalia-v0-BOOTS · 485f682f8 firmament-STARK-heart · dcf7d2684
firmament-n=1-decision · 15353932c ROTATION-ENGINE-G1+G3 · 318342397 MCP · a5884dbce perf ·
4bfbdef79 cipherclerk-audit · (+ REORIENT/paper/pg17 doc commits). Deploy still HELD (flip
mechanical now but not walked; fresh-genesis redeploy is ember's call).

## ⚑⚑⚑ TONIGHT'S LANDINGS (2026-06-13 night, head 870bb0f7f — Opus, 14 commits)

The pug-worthiness + frontier waves LANDED green by file set (verification economy:
each lane verified its own narrow suite; no full-suite re-runs):
- axiom-ergonomics `48f535626` (the #93 answer: terse `#assert_clean`/`#assert_all_clean`,
  one `Dregg2.cleanAxioms` source-of-truth; demo modules 75→1 / 32→1 lines, and the batch
  pins MORE than the verbose blocks did).
- site ×5: front-door `72a3e267f` · studio `431f1f020` · learn `3b6a10d45` · shell
  `ebaad4f14` (the four organs surfaced live) · playground `def4c3f6d` (live organ demos +
  a browser-parsable SDK entry `sdk-ts/src/browser.ts`).
- DreggDL `a7734efcc` (`dregg-deploy/`: declarative deploy spec → userspace-verify; an
  over-grant is caught as in-forest amplification) · dregg-analyzer `f4d0efa5d` (forensic
  trace ATTESTATION via the real verifiers; activates dregg-deploy+dregg-analyzer members)
  · persist snapshot `dc750e1d7` (checkpoint⊕overlay=replay + root tooth; surfaced a node
  state.rs insert_cell-drops-overwrite latent bug → HORIZONLOG) · seL4 scaffold `152e6b3a5`
  (verifier proven Lean-free as a PD: `--features no-lean-link` links only libSystem, 14.4
  vs 27.2 MB) · starbridge-v2 scaffold `fd9763dce` · demo-modernization `870bb0f7f`.
- ⚡ **ROTATION STAGED LONG POLE** `51850ee91`: `turn/src/rotation_witness.rs` producers
  (cells_root/iroot-MMR/lifecycle/epoch/wire_commit) + `circuit/tests/effect_vm_rotation_flip.rs`
  (rotated trace + e2e prove/verify + **cell≡circuit differential HOLDS** + anti-ghost) —
  STAGED-ADDITIVE, v1 byte-identical, **NO VK bump**. Rotated R=24 transfer = 144.1 KiB.

### ⚠⚠ THE FLIP IS NOT MECHANICAL — G1.5 live-path rewrite UNBUILT (cutover lane RED #2, 2026-06-13)
SECOND refutation of "mechanical" from the code (the cutover lane STOPPED, zero edits, tree clean).
G1+G3 (`15353932c`) proved the rotated TRANSFER SHAPE (a triangle with TEST-fed turn-context), NOT
the live machinery. Three real blockers before any flip:
- **G2 is a verifier/executor REWRITE, not a flag-flip.** Live `prove_full_turn`/`verify_full_turn`/
  executor run IR-v1 186-col + a 204-PI reconstruction; rotated `prove_effect_vm_rotated_ir2` returns
  an `Ir2BatchProof` with a 38-PI layout (different AIR family) that won't verify under any v1 verifier.
  ~70 live call-sites on the v1 path. Flipping the default BRICKS verify_full_turn + executor + bilateral agg.
- **G4 generator is transfer-ONLY** (`circuit/src/effect_vm/trace_rotated.rs:182` hardcodes the transfer
  descriptor + caveat manifest) — the other 25 cohort effects have NO rotated generator.
- **cell v9 is not a drop-in:** `compute_canonical_state_commitment_v9` needs turn-context
  (cells_root/nullifier_root/iroot) the cell-local `Cell::state_commitment()`/`Ledger::hash_cell` DON'T
  have; and v9 (Poseidon2 felt) doesn't cover the authority state v8 (BLAKE3) commits — a design problem
  (rotated commitment must carry turn-context OR live at the turn layer, not cell-local).
THE REAL REMAINING BUILD = **G1.5**: rewrite the live effect-VM sub-proof path (prover routing +
`verify_effect_vm_proof_with_cutover` + executor `proof_verify.rs` PI reconstruction + producer-witness
wiring) onto the rotated 38-PI shape; widen `generate_rotated_effect_vm_trace` to all 26 cohort members;
resolve the cell-commitment-turn-context design. THEN regen/re-pin/VK-epoch/v1-delete is mechanical.
(Good news: the "201-vs-204 PI tear" is ALREADY reconciled — producer+verifier both 204; HORIZONLOG item
stale-closed.) v1 (IR-v1/186-col/v8) is the LIVE path, GREEN, deployable. STOP calling the flip mechanical
until the live path routes through the rotated shape. Deploy of the rotated system waits for G1.5. ⚑ COMMISSIONED 2026-06-13 (ember: "do ALL the remaining impl, EVERY rewrite — the old path is ROT, I want it GONE; finish the implementation and close out the flip"): the FULL build is running (lane a589bf5) — resolve the commitment design, widen the generator to all 26 effects, rewrite the live proof/verify/executor path onto the rotated 38-PI shape, regen+VK epoch, DELETE v1/v2 entirely. End state = ONE path. The main loop drives it across relaunches until v1/v2 is gone and the tree is green.

(historical: this section previously claimed "the flip is NOW genuinely mechanical (G1+G3)" — that was my
over-relay of the engine lane's report; refuted by the cutover lane on three axes above.)
✅ UPDATE: G1+G3 are BUILT, staged-additive, fully green (`15353932c`). The LIVE rotated trace
generator (`circuit/src/effect_vm/trace_rotated.rs`) + the cell v9 Poseidon2 commitment
(`cell/src/commitment.rs::compute_canonical_state_commitment_v9`) exist; the LIVE cell≡circuit
differential HOLDS (cell_v9 == circuit row-0 STATE_COMMIT == producer wire_commit); the
live-generated proof is 144.1 KiB proved+verified; anti-ghost bites. Live v1 byte-untouched,
all behind `DREGG_ROTATED_PROVER` + the `recursion` feature (off by default).

✅✅ UPDATE 2 (2026-06-13, Opus — TWO MORE staged-additive stages, fully green, v8/v1 untouched):
- **G3 AUTHORITY-DIGEST DESIGN CALL (the rotated-commitment authority coverage — the #1 scope item).**
  The v9 rotated commitment was DROPPING authority state (it bound only balance/nonce/fields[0..8]/
  roots/lifecycle/epoch/height — NOT permissions/VK/delegate/delegation/program/mode/token_id/
  visibility/commitments/proved/side-table-roots/fields[8..16]). FIXED: `compute_authority_digest_felt`
  (cell/src/commitment.rs) folds the FULL authority residue into register **r23** (the Lean welds leave
  r11..r23 free → the anti-ghost keystone `wireCommitR_binds`/`rotatedCommit_binds_reg` binds it with
  ZERO Lean change). Three-way agreement (cell v9 / producer rotation_witness / trace generator) holds —
  all derive r23 from the same fn. Tooth `v9_binds_full_authority_state` PASSES (two cells differing only
  in permissions/VK/high-field/proved/side-table/mode commit distinctly). Doc: ROTATION-CUTOVER §2a.
- **G4 COHORT-GENERAL GENERATOR (widened beyond transfer).** `rotated_descriptor_name_for_effect`
  (trace_rotated.rs) resolves any of the 26 cohort effects to its `*VmDescriptor2R24` (fail-closed
  otherwise); `effect_vm::trace::effect_selector` extracted as the single source of truth;
  `sdk::prove_effect_vm_rotated_ir2_with_caveat` is the cohort-general prover. Teeth:
  `resolvers_cover_exactly_the_rotated_registry` (=26), `non_cohort_effects_resolve_to_none`. Doc §2c.
- **VALIDATED with REAL proofs:** the flip test now proves+verifies BOTH transfer (144.5 KiB) AND
  burn (143.8 KiB) through the LIVE generator, cell v9 (FULL-authority) ≡ circuit STATE_COMMIT for
  both, anti-ghost bites. `lake build Dregg2` green (3890 jobs); dregg-cell 626 / dregg-circuit 951
  lib tests pass; all 11 descriptor drift guards pass; sdk `--features recursion` compiles.

⚠⚠ **NEWLY SURFACED BLOCKER for "v1 deleted, rotated is the ONLY path":** the rotated `v3Registry` is
ONLY the 26 v2-graduated effects. The LIVE path proves MORE — `MakeSovereign`/`CreateCell`/
`CreateCellFromFactory`/`SpawnWithDelegation`/`ReceiptArchive`/`CellUnseal`/`GrantCapability`/
`RevokeCapability`/`EmitEvent`/`Custom` are NOT in the rotated registry. Flipping to rotated-ONLY +
deleting v1 would BRICK these effects. GATE before "v1 deleted": extend the Lean `v3Registry` to emit
rotated descriptors for them (the same `rotateV3` lift) + re-pin the registry TSV. **Also: `columns::
rotation::NUM_REGISTERS` is the R=16 STAGED-PROBE module (drift-guarded `rotation_layout_matches_lean`
+ SHA pin) — NOT the live path. The LIVE rotated machinery is ALREADY R=24 (`trace_rotated`/`caveat`/v9).
The brief's "NUM_REGISTERS 16→24" is the staged-probe re-emit, a Lean act, not a standalone const bump
(doing it standalone breaks the drift guard + SHA pin).**

The remaining flip (the deep multi-day tail, NOT mechanical) = the live-path rewrite: route
`prove_full_turn` → rotated `Ir2BatchProof` (changes `AttachedSubProof` wire shape + `compose_aggregate`
+ ComposedProof effect-vm leg) · rewrite `verify_full_turn`/`verify_effect_vm_proof_with_cutover` to
the rotated verifier · rewrite executor `proof_verify.rs::verify_and_commit_proof` PI reconstruction
(v1 `pi::ACTIVE_BASE_COUNT` + bespoke `stark::verify` → rotated 38-PI Ir2BatchProof + v9 commitment) ·
`aggregate_bilateral_prover.rs` · reroute ~70 v1 call-sites · un-gate. THEN regen EmitAllJson→v3Registry
live · cell context v8→v9 · re-emit R=16 staged-probe→R=24 + re-pin ~58 artifacts/11 guards · VK epoch ·
DELETE v1 (effect_vm_p3_full_air.rs / lean_descriptor_air.rs v1 / CutoverFallback / ~40 test call-sites
in effect_vm_descriptor_cutover_harness.rs + effect_vm_{grant,attenuate}_non_amp.rs). Each gated green
before the next; persvati gauntlet before deploy. The HARD DESIGN CALLS (authority coverage, cohort
boundary) are DONE; what remains is the wide irreversible wire rewrite + Lean cohort extension.

--- (historical, for the record) ---
The earlier "mechanical tail" framing (from the staged-flip lane's report, which I
relayed) was REFUTED BY THE CODE before the irreversible epoch — caught the deferred hard core. The staged long pole (`51850ee91`) proved the rotated SHAPE
sound but does so by feeding the circuit a HAND-BUILT 311-col trace INSIDE the test
(`effect_vm_rotation_flip.rs` `fill_block`/`fill_caveat`). The LIVE machinery does not exist —
walking the door now would BRICK the live prover. The genuinely-hard, UNBUILT core (the
cutover lane's G1–G5, with a 59-artifact re-pin inventory captured in its report):
- **G1 (HARD, unbuilt)**: a LIVE rotated trace generator emitting 311 cols from a real turn +
  move SDK routing `prove_effect_vm_with_cutover` from IR-v1/186-col (`trace.rs:51`,
  `EFFECT_VM_WIDTH=186`) to IR-v2 `prove_vm_descriptor2` / 38-PI. Today the 311-col trace is
  test-only, hand-welded. THIS IS A REAL BUILD.
- **G3 (HARD, unbuilt)**: cell↔circuit commitment convergence — `cell/src/commitment.rs`
  commits with BLAKE3 `CANONICAL_COMMITMENT_CONTEXT "…v8"` (line 85); the flip needs cell to
  emit the circuit's Poseidon2 chained `wireCommit` (rotated absorption). NO v9/wire_commit/
  rotated path exists in `cell/`; the live-wire cell≡circuit differential is DEFERRED in the
  flip test (~line 264). Re-implementing the canonical commitment + re-pinning the golden-byte
  suite (`commitment.rs` ~573–1190).
- **G2 (mechanical, AFTER G1)**: `EmitAllJson`→`v3Registry` live + all 59 byte re-pins +
  `columns::rotation::NUM_REGISTERS` 16→24 (line 326; cosmetic, must NOT land alone).
- **G4**: executor PI v3 LIVE producer/verifier reconcile + `committed_height` read (the
  HORIZONLOG "producer emits 201" entry may be STALE — `aggregate_test_wr` already uses
  ACTIVE_BASE_COUNT 204; the real witness-path producer `materialize_blocklace_artifacts`
  node/src/blocklace_sync.rs:2619 needs the test RUN to confirm end-to-end).
- **G5**: VK/fingerprint epoch + a succession record (none exists today; "VK" = the 26+
  descriptor SHA fingerprints) + v1 deletion. Each gated green before the next; persvati
  gauntlet before deploy.
v1 is the LIVE path (IR-v1/186-col/BLAKE3-v8) and is GREEN. The rotation is staged-in-shape
only. DECISION PENDING (ember): commission the G1/G3/G4 core build, vs keep staged + deploy
the current green system modestly. Do NOT attempt the flip until G1+G3 are built+validated.

### RUNNING (2026-06-13 night) — land each by file set when it reports
- **pg-dregg M1** (postgres RLS extension; STANDALONE workspace `pg-dregg/`, own target —
  no ./target contention). ember decisions baked: INSTANT revocation in the default path
  (verified-credential LRU mandatory), credential-path leads, FFI-Lean tier deferred.
  Proposal already committed `bfe802c1b` (docs/PG-DREGG.md). Two-mode build: `cargo test`
  core (no pg) + `cargo pgrx` extension.
- **starbridge-v2 → THE MASTER INTERFACE** (ember reframe): REVERSES the scaffold's thin-
  client decision — now EMBEDS the real verified executor + is comprehensive for ALL data &
  actions + smalltalk-surpassing live visual cockpit. One codebase, two builds (`native-full`
  embeds executor/Lean = the cockpit; `sel4-thin` = the stripped client). Lane also tasked
  with actually getting gpui to RENDER here (Metal toolchain — brew/xcrun in scope).
- **seL4 → THE ROBIGALIA v0 DEMO** (ember reframe): Rust-userspace-dregg (the `rbg/` crate
  primitives) booting on seL4/Microkit in QEMU (aarch64 first → riscv), toward networking
  (virtio-net + smoltcp/lwIP) + a dregg TUI light client. Reproducible macOS-native
  toolchain preferred (brew freely), Docker Desktop fallback. Owns `sel4/` + a new
  `dregg-tui/` standalone crate.

NOTE: stashes exist (stash@{0..6}, old/deleted branches — NOT ours, never touch). On `main`.

## ⚑⚑⚑ THE FLIP IS GO + WAVE 2 (2026-06-13, head 2c37c50fc — ember's decisions)

ember decided: (1) #93 = NOT close — AUTOMATE the assert_axioms verbosity (a Tactics lane);
(2) ROTATION FLIP = EXECUTE NOW (the staging was done — R=24, both wire-shapes, regen
byte-pinned); (3) next wave = ALL fronts incl. lean-side HORIZONLOG followups.
RUNNING: THE FLIP (a1e5cf2 — owns circuit/ + metatheory/{Circuit,Exec} + turn/ producers;
builds the deferred cells_root/iroot/lifecycle-epoch producers, regen-to-default, VK bump,
v1→dormant-or-deleted; the cutover commit-train, docs/ROTATION-CUTOVER.md) · DreggDL/
dregg-deploy (the checkable-deployment-spec synthesis) · persist snapshot-shipping ·
demo receipt-chain modernization (pre-existing example rot, marketing-facing) ·
assert_axioms ergonomics (the #93 transform). HELD until the flip lands (collide w/ its
core): FlashWell Lean twin, private-participant Rust role, compute_marketplace multi-cell
reputation bug, the circuit note-spend DSL self-inconsistency (all 3 pre-existing, triaged).
Round 8 verdict: ZERO new regressions — all demo/preflight failures are pre-epoch rot.
ALL 8 pug-worthiness lanes LANDED (assurance/privacy/seL4-CapDL/site/protocol/uverify/
sdk-ts/apps; commits 91fbc97b8 1ee05da5c 10c60725d 2579afd70 2c37c50fc).

## ⚑⚑ PUG-WORTHINESS WAVE (2026-06-13, head b983458c7 — 8 lanes, ember's broad horizon)

After the 13 full-burn lanes landed, ember opened the breadth horizon (make it pug-worthy:
well-documented/packaged/thought-through for an outside evaluator's agents; deploy stays
LOW-priority to accumulate enhancements). 8 disjoint Opus lanes running, each verifies its
OWN narrow build (verification economy), lander commits by file set:
- TS SDK parity+packaging (sdk-ts/ → /tmp/ts-sdk-lane.log)
- Userspace-Verify toolkit for SDK-produced subgraphs — ember "vital, not-yet-addressed"
  (NEW dregg-userspace-verify/ → /tmp/uverify-lane.log)
- Site generator + education + shell/IDE coherence + extension (/tmp/site-lane.log)
- Privacy: offline-cell witnessless-ZK consensus participation (docs + new Lean → /tmp/privacy-lane.log)
- seL4/Robigalia bootable-image + CapDL-inspired "DreggDL" polyglot DX (docs → /tmp/sel4-lane.log)
- Assurance spec UNIFICATION + drift audit (docs/ASSURANCE.md + the #93 answer → /tmp/assurance-lane.log)
- Apps up-to-snuff + one new organ-composing verified app (starbridge-apps/ → /tmp/apps-lane.log)
- Protocol/network/persist/storage enhancement catalog + 1 concrete win (/tmp/protocol-lane.log)
ROUND 8 gauntlet still validating the converged tree (persvati). STILL PENDING (ember
reminder): the rotation FLIP + its preidentified followups (docs/ROTATION-CUTOVER.md);
devnet redeploy (low-priority).

## ⚑⚑ OPUS LANDING COMPLETE (2026-06-12 night — all 13 full-burn lanes home, head 5bf7adda3)

The export directive sealed Fable mid-wave; Opus 4.8 resumed all 13 dying lanes as finishers
and LANDED every one green. 7 substantive commits f554d34d2..475f19115 + HORIZONLOG residues:
  f554d34d2 handoff docs (bootstrap.sh + EVALUATION.md) · d20791e68 Lean batch (metatheory
  closures + 26-descriptor rotation regen STAGED) · 3a68e265d python-lean (sdk-py embeds the
  REAL kernel) · 740e2e273 persist (burn weld + rosters + dregg1 retirement) · 1a95623aa
  ocapn netlayer · 03c36c937 dregg-query · 475f19115 node cluster (DKG ceremony + ECVRF +
  KERI + flash-well + trustline parity + auth coverage 6→4).
Method that held: lander VALIDATES each finisher's narrow suite, commits by file set, never
forces a partial; the entangled node cluster got ONE convergence pass (all 4 gates green:
fed 185 + sdk 209 + node-bin check + coverage 9/9). The finishers caught REAL bugs the
unverified Fable drafts carried (flash-well laundered-vacuity refusals; channels PFS-vs-
determinism test; ecvrf RFC nibble typo; dregg-query serde tag collision; ocapn dial claim).
NEXT: ROUND 8 gauntlet on persvati (the converged tree's full validation + the python-lean
ELF proof + the DKG/KERI/roster e2e in a lock-free window) → the rotation FLIP when ready
(docs/ROTATION-CUTOVER.md, both wire-shapes staged + R=24 confirmed) → deploy.

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
